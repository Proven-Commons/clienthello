#!/usr/bin/env python3
"""Tests for the Lean TLS ClientHello parser and printer.

Three parts.

1. Fixed cases built by hand from RFC 8446 section 4.1.2,
   RFC 5246 and RFC 6066: one full TLS 1.3 style hello (SNI
   for a named host, ALPN h2 and http/1.1, supported versions
   0x0304 and 0x0303, key shares for x25519 and secp256r1
   with fixed key bytes, and one opaque extension), one
   minimal hello (supported versions only), and the named
   rejection shapes listed in SPEC.md, plus the pinned
   reading that a present but empty extensions block (length
   0) is accepted.

2. A differential run against a strict Python oracle written
   in this harness from the rules in SPEC.md: at least 3,000
   generated messages (varied record and legacy versions,
   session ids, cipher suite lists, compression lists,
   extension sets and orders, with defects injected from a
   menu), plus raw mutations of the full fixed hello (every
   truncation, single byte flips, random multi-byte changes)
   and fully random byte strings. The oracle settles every
   verdict; the tool must agree with it on each input.

3. Malformed request lines must be answered `error`.

Oracle availability, checked when this harness was written
and stated again in the results record: Python's ssl module
cannot build a ClientHello on demand. Go is not installed
(`go version` fails). Scapy 2.8.0 is importable from the
sibling dhcp project's venv and its TLS submodules import,
but building or dissecting a TLS record raises NameError
inside scapy's crypto support (HMAC is not defined), so
Scapy cannot serve as a byte source in this environment and
was not used. No captured ClientHello was fetched; the
fixed cases are built by hand from the RFCs.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests,
input written and closed, output drained until the process
exits. It builds the executable first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check
fails. It needs Python 3.11 or later.
"""

import argparse
import os
import platform
import random
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "clienthello"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"


# ----------------------------------------------------------------
# The oracle: an independent implementation of the SPEC rules.
# It parses bytes into a model and reprints the model; the
# reprint of an accepted message is the expected tool answer.
# ----------------------------------------------------------------

class Reject(Exception):
    pass


def take(bs, i, n):
    if i + n > len(bs):
        raise Reject()
    return bs[i:i + n], i + n


def u8(bs, i):
    bs2, i = take(bs, i, 1)
    return bs2[0], i


def u16(bs, i):
    bs2, i = take(bs, i, 2)
    return (bs2[0] << 8) | bs2[1], i


def u24(bs, i):
    bs2, i = take(bs, i, 3)
    return (bs2[0] << 16) | (bs2[1] << 8) | bs2[2], i


def be16(n):
    return bytes([(n >> 8) & 0xFF, n & 0xFF])


def be24(n):
    return bytes([(n >> 16) & 0xFF, (n >> 8) & 0xFF, n & 0xFF])


def oracle_sni(v):
    listlen, i = u16(v, 0)
    if listlen != len(v) - 2:
        raise Reject()
    entries = []
    seen = set()
    while i < len(v):
        t, i = u8(v, i)
        ln, i = u16(v, i)
        name, i = take(v, i, ln)
        if t in seen:
            raise Reject()
        seen.add(t)
        if t == 0 and len(name) == 0:
            raise Reject()
        entries.append((t, bytes(name)))
    if not entries:
        raise Reject()
    out = be16(listlen)
    for t, name in entries:
        out += bytes([t]) + be16(len(name)) + name
    return ("sni", entries), out


def oracle_alpn(v):
    listlen, i = u16(v, 0)
    if listlen != len(v) - 2:
        raise Reject()
    names = []
    while i < len(v):
        ln, i = u8(v, i)
        if ln < 1:
            raise Reject()
        name, i = take(v, i, ln)
        names.append(bytes(name))
    if not names:
        raise Reject()
    out = be16(listlen)
    for name in names:
        out += bytes([len(name)]) + name
    return ("alpn", names), out


def oracle_sv(v):
    ln, i = u8(v, 0)
    if ln != len(v) - 1 or ln % 2 != 0 or ln < 2:
        raise Reject()
    versions = []
    while i < len(v):
        ver, i = u16(v, i)
        versions.append(ver)
    out = bytes([ln])
    for ver in versions:
        out += be16(ver)
    return ("sv", versions), out


def oracle_ks(v):
    listlen, i = u16(v, 0)
    if listlen != len(v) - 2:
        raise Reject()
    shares = []
    seen = set()
    while i < len(v):
        group, i = u16(v, i)
        klen, i = u16(v, i)
        if klen < 1:
            raise Reject()
        key, i = take(v, i, klen)
        if group in seen:
            raise Reject()
        seen.add(group)
        shares.append((group, bytes(key)))
    # An empty list is allowed: RFC 8446 section 4.2.8, a
    # client asking for a HelloRetryRequest sends no shares.
    out = be16(listlen)
    for group, key in shares:
        out += be16(group) + be16(len(key)) + key
    return ("ks", shares), out


def oracle_ext_value(t, v):
    if t == 0:
        return oracle_sni(v)
    if t == 16:
        return oracle_alpn(v)
    if t == 43:
        return oracle_sv(v)
    if t == 51:
        return oracle_ks(v)
    return ("opaque", t, bytes(v)), bytes(v)


def oracle_exts(block):
    exts = []
    seen = set()
    i = 0
    while i < len(block):
        t, i = u16(block, i)
        ln, i = u16(block, i)
        v, i = take(block, i, ln)
        if t in seen:
            raise Reject()
        seen.add(t)
        ext, _ = oracle_ext_value(t, bytes(v))
        exts.append((t, ext))
    return exts


def print_ext(ext):
    kind = ext[0]
    if kind == "sni":
        body = b""
        for t, name in ext[1]:
            body += bytes([t]) + be16(len(name)) + name
        return be16(0) + be16(len(body) + 2) + be16(len(body)) + body
    if kind == "alpn":
        body = b""
        for name in ext[1]:
            body += bytes([len(name)]) + name
        return be16(16) + be16(len(body) + 2) + be16(len(body)) + body
    if kind == "sv":
        body = bytes([2 * len(ext[1])])
        for ver in ext[1]:
            body += be16(ver)
        return be16(43) + be16(len(body)) + body
    if kind == "ks":
        body = b""
        for group, key in ext[1]:
            body += be16(group) + be16(len(key)) + key
        return be16(51) + be16(len(body) + 2) + be16(len(body)) + body
    _, t, v = ext
    return be16(t) + be16(len(v)) + v


def oracle_parse(bs):
    """The canonical reprint of the message, or None."""
    try:
        return oracle_parse_go(bs)
    except Reject:
        return None


def oracle_parse_go(bs):
    ct, i = u8(bs, 0)
    if ct != 22:
        raise Reject()
    rv, i = take(bs, i, 2)
    rlen, i = u16(bs, i)
    # RFC 8446 section 5.1: the record length MUST NOT exceed
    # 2^14 bytes.
    if rlen > 16384:
        raise Reject()
    body, i = take(bs, i, rlen)
    if i != len(bs):
        raise Reject()
    htype, j = u8(body, 0)
    if htype != 1:
        raise Reject()
    hlen, j = u24(body, j)
    fields, j = take(body, j, hlen)
    if j != len(body):
        raise Reject()
    ver, k = take(fields, 0, 2)
    rand, k = take(fields, k, 32)
    slen, k = u8(fields, k)
    if slen > 32:
        raise Reject()
    sess, k = take(fields, k, slen)
    clen, k = u16(fields, k)
    if clen % 2 != 0 or clen < 2:
        raise Reject()
    cbytes, k = take(fields, k, clen)
    suites = []
    for off in range(0, clen, 2):
        suites.append((cbytes[off] << 8) | cbytes[off + 1])
    mlen, k = u8(fields, k)
    if mlen < 1:
        raise Reject()
    comps, k = take(fields, k, mlen)
    if 0 not in comps:
        raise Reject()
    elen, k = u16(fields, k)
    block, k = take(fields, k, elen)
    if k != len(fields):
        raise Reject()
    exts = oracle_exts(bytes(block))
    # RFC 8446 section 4.1.2: a hello that offers TLS 1.3 (its
    # supported_versions lists 0x0304) carries exactly one
    # compression method, null.
    offers13 = any(e[0] == "sv" and 0x0304 in e[1] for _, e in exts)
    if offers13 and bytes(comps) != b"\x00":
        raise Reject()
    out_fields = bytes(ver) + bytes(rand)
    out_fields += bytes([len(sess)]) + bytes(sess)
    pairs = b""
    for s in suites:
        pairs += be16(s)
    out_fields += be16(len(pairs)) + pairs
    out_fields += bytes([len(comps)]) + bytes(comps)
    block_out = b""
    for _, ext in exts:
        block_out += print_ext(ext)
    out_fields += be16(len(block_out)) + block_out
    out_body = bytes([1]) + be24(len(out_fields)) + out_fields
    return bytes([22]) + bytes(rv) + be16(len(out_body)) + out_body


# ----------------------------------------------------------------
# Builders: byte level construction of test messages, with
# knobs for the defect cases. The builders are not the oracle;
# every built message is judged by the oracle and the tool.
# ----------------------------------------------------------------

def sni_value(entries):
    body = b""
    for t, name in entries:
        body += bytes([t]) + be16(len(name)) + name
    return be16(len(body)) + body


def alpn_value(names):
    body = b""
    for name in names:
        body += bytes([len(name)]) + name
    return be16(len(body)) + body


def sv_value(versions):
    body = bytes([2 * len(versions)])
    for ver in versions:
        body += be16(ver)
    return body


def ks_value(shares):
    body = b""
    for group, key in shares:
        body += be16(group) + be16(len(key)) + key
    return be16(len(body)) + body


def ext_bytes(t, v):
    return be16(t) + be16(len(v)) + v


def build_hello(record_version=b"\x03\x01", legacy_version=b"\x03\x03",
                random_bytes=None, session_id=b"", suites=(0x1301,),
                comps=(0,), exts=(), ext_block=True,
                record_len_delta=0, hs_len_delta=0, trailing=b""):
    if random_bytes is None:
        random_bytes = bytes(range(32))
    fields = legacy_version + random_bytes
    fields += bytes([len(session_id)]) + session_id
    pairs = b""
    for s in suites:
        pairs += be16(s)
    fields += be16(len(pairs)) + pairs
    fields += bytes([len(comps)]) + bytes(comps)
    if ext_block:
        block = b""
        for t, v in exts:
            block += ext_bytes(t, v)
        fields += be16(len(block)) + block
    body = bytes([1]) + be24(len(fields) + hs_len_delta) + fields
    rec = bytes([22]) + record_version
    rec += be16(len(body) + record_len_delta) + body
    return rec + trailing


FULL_EXTS = [
    (0, sni_value([(0, b"example.com")])),
    (16, alpn_value([b"h2", b"http/1.1"])),
    (43, sv_value([0x0304, 0x0303])),
    (51, ks_value([(29, bytes(range(32))),
                   (23, b"\x04" + bytes(range(64)))])),
    (23, b""),
]
FULL_HELLO = build_hello(
    session_id=bytes(range(32)),
    suites=(0x1301, 0x1302, 0x1303, 0xC02F),
    exts=FULL_EXTS)
MIN_HELLO = build_hello(exts=[(43, sv_value([0x0304, 0x0303]))])
EMPTY_EXT_HELLO = build_hello(exts=[])


def raw_fields(suites_bytes, comps=(0,), exts=(), ext_block=True):
    fields = b"\x03\x03" + bytes(range(32)) + b"\x00"
    fields += be16(len(suites_bytes)) + suites_bytes
    fields += bytes([len(comps)]) + bytes(comps)
    if ext_block:
        block = b""
        for t, v in exts:
            block += ext_bytes(t, v)
        fields += be16(len(block)) + block
    body = bytes([1]) + be24(len(fields)) + fields
    return bytes([22, 3, 1]) + be16(len(body)) + body


def padded_hello(record_len, rng=None, base_exts=None):
    """A TLS 1.3 style hello whose record body is exactly
    record_len bytes, padded with a padding extension (21)."""
    exts = list(base_exts if base_exts is not None
                else [(43, sv_value([0x0304, 0x0303]))])
    probe = build_hello(exts=exts + [(21, b"")])
    pad = record_len - (len(probe) - 5)
    fill = (bytes(rng.randrange(256) for _ in range(pad))
            if rng else bytes(pad))
    out = build_hello(exts=exts + [(21, fill)])
    assert len(out) - 5 == record_len
    return out


def gen_near_limit(rng):
    """Hellos whose record length is within a few bytes of the
    2^14 limit, on both sides of it."""
    out = []
    for _ in range(60):
        n = rng.randrange(16376, 16393)
        exts = [(43, sv_value([0x0304]))]
        if rng.random() < 0.5:
            exts.append((51, ks_value([(29, bytes(32))])))
        out.append(padded_hello(n, rng, exts))
    return out


def named_cases():
    """(name, bytes, expected: True accept / False reject)."""
    cases = []
    cases.append(("full TLS 1.3 style hello", FULL_HELLO, True))
    cases.append(("minimal hello, supported versions only",
                  MIN_HELLO, True))
    cases.append(("duplicate extension type",
                  build_hello(exts=[(43, sv_value([0x0304])),
                                    (43, sv_value([0x0303]))]),
                  False))
    cases.append(("duplicate key share group",
                  build_hello(exts=[(51, ks_value(
                      [(29, b"\x01" * 32), (29, b"\x02" * 32)]))]),
                  False))
    overrun_block = be16(0) + be16(10) + b"\x02\x03\x04"
    fields = b"\x03\x03" + bytes(range(32)) + b"\x00"
    fields += be16(2) + b"\x13\x01" + b"\x01\x00"
    fields += be16(len(overrun_block)) + overrun_block
    body = bytes([1]) + be24(len(fields)) + fields
    cases.append(("extension length overrunning the block",
                  bytes([22, 3, 1]) + be16(len(body)) + body,
                  False))
    cases.append(("record length longer than the input",
                  build_hello(record_len_delta=5), False))
    cases.append(("handshake length not matching the body",
                  build_hello(hs_len_delta=1), False))
    bad = bytearray(MIN_HELLO)
    bad[0] = 23
    cases.append(("content type 23", bytes(bad), False))
    bad = bytearray(MIN_HELLO)
    bad[5] = 2
    cases.append(("handshake type 2", bytes(bad), False))
    cases.append(("session id length 33",
                  build_hello(session_id=b"\x07" * 33), False))
    cases.append(("odd cipher suite length",
                  raw_fields(b"\x13\x01\x13"), False))
    cases.append(("empty cipher suites",
                  build_hello(suites=()), False))
    cases.append(("compression methods without 0",
                  build_hello(comps=(1, 2)), False))
    cases.append(("TLS 1.3 hello with compression methods 01 00",
                  build_hello(comps=(1, 0),
                              exts=[(43, sv_value([0x0304]))]),
                  False))
    cases.append(("TLS 1.3 hello with compression methods 00 00",
                  build_hello(comps=(0, 0),
                              exts=[(43, sv_value([0x0304, 0x0303]))]),
                  False))
    cases.append(("TLS 1.2 hello (supported_versions 0x0303 only) "
                  "with compression methods 01 00, accepted",
                  build_hello(comps=(1, 0),
                              exts=[(43, sv_value([0x0303]))]),
                  True))
    cases.append(("hello without extensions, compression methods "
                  "01 00, accepted",
                  build_hello(comps=(1, 0)), True))
    cases.append(("missing extensions block",
                  build_hello(ext_block=False), False))
    cases.append(("supported versions odd length",
                  build_hello(exts=[(43, bytes([3, 3, 4, 3]))]),
                  False))
    cases.append(("supported versions length zero",
                  build_hello(exts=[(43, bytes([0]))]), False))
    cases.append(("ALPN empty name",
                  build_hello(exts=[(16, be16(1) + b"\x00")]),
                  False))
    alpn_bad = be16(9) + alpn_value([b"h2"])[2:]
    cases.append(("ALPN list length mismatch",
                  build_hello(exts=[(16, alpn_bad)]), False))
    cases.append(("ALPN empty list",
                  build_hello(exts=[(16, alpn_value([]))]),
                  False))
    cases.append(("SNI second host_name entry",
                  build_hello(exts=[(0, sni_value(
                      [(0, b"a.example"), (0, b"b.example")]))]),
                  False))
    sni_bad = be16(99) + sni_value([(0, b"example.com")])[2:]
    cases.append(("SNI list length mismatch",
                  build_hello(exts=[(0, sni_bad)]), False))
    cases.append(("SNI empty list",
                  build_hello(exts=[(0, sni_value([]))]),
                  False))
    cases.append(("key share empty key bytes",
                  build_hello(exts=[(51, ks_value([(29, b"")]))]),
                  False))
    cases.append(("key share empty list, accepted",
                  build_hello(exts=[(51, ks_value([]))]),
                  True))
    cases.append(("TLS 1.3 hello asking for a HelloRetryRequest "
                  "(supported_groups, supported_versions 0x0304, "
                  "empty key_share), accepted",
                  build_hello(exts=[
                      (10, be16(4) + be16(29) + be16(23)),
                      (43, sv_value([0x0304])),
                      (51, ks_value([])),
                      (13, be16(2) + b"\x04\x03")]),
                  True))
    cases.append(("trailing garbage after the record",
                  build_hello(trailing=b"\x00"), False))
    cases.append(("empty extensions block, length 0, accepted",
                  EMPTY_EXT_HELLO, True))
    cases.append(("record length 16384, the 2^14 limit, accepted",
                  padded_hello(16384), True))
    cases.append(("record length 16385, over the 2^14 limit",
                  padded_hello(16385), False))
    cases.append(("record length zero",
                  bytes([22, 3, 1, 0, 0]), False))
    cases.append(("input shorter than the record header",
                  bytes([22, 3]), False))
    cases.append(("empty input", b"", False))
    return cases


# ----------------------------------------------------------------
# The generated differential cases.
# ----------------------------------------------------------------

HOSTS = [b"example.com", b"a.b.example.org", b"x", b"host-name.example"]


def gen_sni(rng, defect):
    entries = [(0, rng.choice(HOSTS))]
    if rng.random() < 0.3:
        entries.append((rng.choice([1, 2, 3, 17]),
                        bytes(rng.randrange(256)
                              for _ in range(rng.randrange(1, 6)))))
    if defect == "sni-second-host":
        entries.append((0, b"other.example"))
    if defect == "sni-dup-type":
        entries.append((entries[-1][0], b"zz"))
    if defect == "sni-empty-host":
        entries[0] = (0, b"")
    v = sni_value(entries)
    if defect == "sni-list-len":
        v = be16(len(v)) + v[2:]
    return (0, v)


def gen_alpn(rng, defect):
    names = [bytes(rng.choice(b"abcdefg0123456789/.-")
                   for _ in range(rng.randrange(1, 9)))
             for _ in range(rng.randrange(1, 4))]
    if defect == "alpn-empty-name":
        names.insert(0, b"")
    v = alpn_value(names)
    if defect == "alpn-list-len":
        v = be16(len(v) + 2) + v[2:]
    return (16, v)


def gen_sv(rng, defect):
    versions = [rng.choice([0x0300, 0x0301, 0x0302, 0x0303,
                            0x0304, 0x7F1C])
                for _ in range(rng.randrange(1, 5))]
    if defect == "sv-odd":
        return (43, bytes([3, 3, 4, 3]))
    if defect == "sv-zero":
        return (43, bytes([0]))
    if defect == "sv-len-lie":
        v = sv_value(versions)
        return (43, bytes([v[0] + 2]) + v[1:])
    return (43, sv_value(versions))


def gen_ks(rng, defect):
    groups = rng.sample([29, 23, 24, 25, 256, 257],
                        rng.randrange(1, 4))
    shares = [(g, bytes(rng.randrange(256)
                        for _ in range(rng.choice([1, 32, 65]))))
              for g in groups]
    if defect == "ks-empty-list":
        shares = []
    if defect == "ks-dup-group":
        shares.append((shares[0][0], b"\x09" * 8))
    if defect == "ks-empty-key":
        shares[0] = (shares[0][0], b"")
    v = ks_value(shares)
    if defect == "ks-list-len":
        v = be16(len(v)) + v[2:]
    return (51, v)


def gen_opaque(rng, taken):
    choices = [t for t in [5, 10, 11, 13, 21, 23, 35, 42, 44,
                           45, 49, 50, 300, 1000, 65281]
               if t not in taken]
    t = rng.choice(choices)
    v = bytes(rng.randrange(256)
              for _ in range(rng.choice([0, 1, 4, 17, 40])))
    return (t, v)


DEFECTS = [None, None, None, "dup-ext", "no-ext-block",
           "trailing", "rec-len", "hs-len", "sess33",
           "suites-empty", "comps-no-null", "comps-empty",
           "sni-second-host", "sni-dup-type", "sni-empty-host",
           "sni-list-len", "alpn-empty-name", "alpn-list-len",
           "sv-odd", "sv-zero", "sv-len-lie", "ks-dup-group",
           "ks-empty-key", "ks-list-len", "ks-empty-list"]


def gen_message(rng):
    defect = rng.choice(DEFECTS)
    session_id = bytes(rng.randrange(256)
                       for _ in range(rng.choice([0, 0, 1, 8, 32])))
    if defect == "sess33":
        session_id = bytes(33)
    nsuites = rng.choice([1, 1, 2, 3, 4, 6])
    if defect == "suites-empty":
        nsuites = 0
    suites = [rng.randrange(65536) for _ in range(nsuites)]
    comps = [0]
    if rng.random() < 0.3:
        comps = [0, 1]
    if defect == "comps-no-null":
        comps = [1, 2]
    if defect == "comps-empty":
        comps = []
    builders = [gen_sni, gen_alpn, gen_sv, gen_ks]
    rng.shuffle(builders)
    nexts = rng.randrange(0, 5)
    chosen = builders[:nexts]
    exts = []
    taken = set()
    for b in chosen:
        e = b(rng, defect)
        exts.append(e)
        taken.add(e[0])
    if rng.random() < 0.5:
        e = gen_opaque(rng, taken)
        exts.insert(rng.randrange(len(exts) + 1), e)
        taken.add(e[0])
    if defect == "dup-ext" and exts:
        exts.append(exts[0])
    rng.shuffle(exts)
    return build_hello(
        record_version=bytes([rng.randrange(256),
                              rng.randrange(256)]),
        legacy_version=bytes([rng.randrange(256),
                              rng.randrange(256)]),
        random_bytes=bytes(rng.randrange(256) for _ in range(32)),
        session_id=session_id, suites=suites, comps=comps,
        exts=exts, ext_block=(defect != "no-ext-block"),
        record_len_delta=(5 if defect == "rec-len" else 0),
        hs_len_delta=(1 if defect == "hs-len" else 0),
        trailing=(b"\xaa" if defect == "trailing" else b""))


def gen_mutations(rng):
    out = []
    for i in range(len(FULL_HELLO)):
        out.append(FULL_HELLO[:i])
    for i in range(len(FULL_HELLO)):
        for d in (0x01, 0x80, 0xFF):
            b = bytearray(FULL_HELLO)
            b[i] ^= d
            out.append(bytes(b))
    for _ in range(300):
        b = bytearray(FULL_HELLO)
        for _ in range(rng.randrange(1, 9)):
            op = rng.randrange(3)
            pos = rng.randrange(len(b) + (1 if op == 1 else 0))
            if op == 0 and b:
                b[pos % len(b)] = rng.randrange(256)
            elif op == 1:
                b.insert(pos, rng.randrange(256))
            elif op == 2 and b:
                del b[pos % len(b)]
        out.append(bytes(b))
    return out


def gen_random_raw(rng):
    out = []
    for _ in range(300):
        n = rng.randrange(0, 320)
        b = bytes(rng.randrange(256) for _ in range(n))
        if n > 0 and rng.random() < 0.5:
            b = bytes([22]) + b[1:]
        out.append(b)
    return out


# ----------------------------------------------------------------
# The runner.
# ----------------------------------------------------------------

def run_batch(lines, timeout=120):
    """Run the tool on request lines; return answer lines."""
    proc = subprocess.Popen(
        [str(EXE)], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE)
    out_lines = []
    err = []

    def drain():
        try:
            data = proc.stdout.read()
            out_lines.extend(data.decode().splitlines())
        except Exception:
            pass

    t = threading.Thread(target=drain, daemon=True)
    t.start()
    try:
        proc.stdin.write(("\n".join(lines) + "\n").encode())
        proc.stdin.close()
    except BrokenPipeError:
        pass
    t.join(timeout)
    if t.is_alive():
        proc.kill()
        raise TimeoutError("tool did not finish in time")
    err = proc.stderr.read().decode()
    if err.strip():
        raise RuntimeError(f"tool wrote to stderr: {err[:400]}")
    return out_lines


def codes(bs):
    return ",".join(str(b) for b in bs)


def expected_answer(bs):
    rep = oracle_parse(bs)
    if rep is None:
        return "none"
    return "ok:" + codes(rep)


def check_batch(cases, label, failures):
    """cases: list of byte strings. Returns (run, agreed)."""
    lines = []
    for bs in cases:
        if bs:
            lines.append("parse " + codes(bs))
        else:
            lines.append("parse")
    answers = []
    chunk = 400
    for i in range(0, len(lines), chunk):
        answers.extend(run_batch(lines[i:i + chunk]))
    if len(answers) != len(cases):
        failures.append(
            f"{label}: got {len(answers)} answers for "
            f"{len(cases)} cases")
        return len(cases), 0
    agreed = 0
    for bs, got in zip(cases, answers):
        want = expected_answer(bs)
        if got == want:
            agreed += 1
        elif len(failures) < 25:
            failures.append(
                f"{label}: input {codes(bs)[:120]}... "
                f"tool said {got[:80]}, oracle said {want[:80]}")
    return len(cases), agreed


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261026)
    ap.add_argument("--count", type=int, default=3200)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    env = dict(os.environ)
    if not any(Path(p, "lake").exists()
               for p in env.get("PATH", "").split(":")):
        env["PATH"] = (str(Path.home() / ".elan" / "bin")
                       + ":" + env.get("PATH", ""))
    build = subprocess.run(
        ["lake", "build"], cwd=ROOT, capture_output=True,
        text=True, timeout=1200, env=env)
    if build.returncode != 0:
        print(build.stdout[-2000:])
        print(build.stderr[-2000:])
        print("lake build failed", file=sys.stderr)
        return 1

    failures = []
    tally = {}

    named = named_cases()
    agreed_named = 0
    named_lines = []
    named_want = []
    for name, bs, want_ok in named:
        rep = oracle_parse(bs)
        oracle_ok = rep is not None
        if oracle_ok != want_ok:
            failures.append(
                f"named case {name}: oracle "
                f"{'accepts' if oracle_ok else 'rejects'}, "
                f"the case expects "
                f"{'accept' if want_ok else 'reject'}")
        named_lines.append(bs)
        named_want.append(name)
    n, a = check_batch(named_lines, "named", failures)
    tally["named cases"] = (n, a)

    gen = [gen_message(rng) for _ in range(args.count)]
    n, a = check_batch(gen, "generated", failures)
    tally["generated messages"] = (n, a)
    gen_accepted = sum(1 for bs in gen
                        if oracle_parse(bs) is not None)

    mut = gen_mutations(rng)
    n, a = check_batch(mut, "mutations", failures)
    tally["mutations of the full hello"] = (n, a)

    raw = gen_random_raw(rng)
    n, a = check_batch(raw, "random raw", failures)
    tally["random raw byte strings"] = (n, a)

    near = gen_near_limit(rng)
    n, a = check_batch(near, "near the record limit", failures)
    tally["hellos near the 2^14 record limit"] = (n, a)

    malformed = ["parse 256", "parse 1,x", "parse 1,,2",
                 "peek 1,2", "parse -1", "parse 1 2",
                 "parse 999999999999"]
    bad_agreed = 0
    for line in malformed:
        got = run_batch([line])
        if got == ["error"]:
            bad_agreed += 1
        else:
            failures.append(
                f"malformed line {line!r}: got {got}")
    tally["malformed request lines"] = (len(malformed),
                                         bad_agreed)

    total = sum(n for n, _ in tally.values())
    agreed = sum(a for _, a in tally.values())

    lines = []
    lines.append("# ClientHello slice: test results")
    lines.append("")
    lines.append(f"Run: python3 tests/run_tests.py "
                 f"--seed {args.seed} --count {args.count}")
    lines.append(f"Seed: {args.seed}. "
                 f"Python {platform.python_version()}.")
    lines.append("")
    lines.append("## Oracles")
    lines.append("")
    lines.append("Every verdict is settled by the harness "
                 "oracle, a Python implementation of the rules "
                 "in SPEC.md written for these tests. The tool "
                 "must agree with the oracle on every input, "
                 "and an accepted message must reprint to the "
                 "oracle's canonical reprint byte for byte.")
    lines.append("")
    lines.append("Python's ssl module cannot build a "
                 "ClientHello on demand. Go is not installed "
                 "(`go version` fails). Scapy 2.8.0 is present "
                 "in the sibling dhcp project's venv and its "
                 "TLS submodules import, but building or "
                 "dissecting a TLS record raises NameError "
                 "inside scapy's crypto support (HMAC is not "
                 "defined), so Scapy could not be used as a "
                 "byte source. No capture was fetched; the "
                 "fixed cases are built by hand from the RFCs.")
    lines.append("")
    lines.append("## Counts")
    lines.append("")
    lines.append("| part | run | agreed |")
    lines.append("| --- | --- | --- |")
    for label, (n, a) in tally.items():
        lines.append(f"| {label} | {n} | {a} |")
    lines.append(f"| total | {total} | {agreed} |")
    lines.append("")
    lines.append(f"Of the {tally['generated messages'][0]} "
                 f"generated messages, the oracle accepts "
                 f"{gen_accepted} and rejects "
                 f"{tally['generated messages'][0] - gen_accepted}.")
    lines.append("")
    lines.append("## Named cases")
    lines.append("")
    for name, bs, want_ok in named:
        lines.append(f"- {name}: "
                     f"{'accept' if want_ok else 'reject'} "
                     f"({len(bs)} bytes)")
    lines.append("")
    lines.append("## Differences")
    lines.append("")
    if failures:
        lines.append(f"{len(failures)} failure(s):")
        lines.append("")
        for f in failures:
            lines.append(f"- {f}")
    else:
        lines.append("No disagreements between the tool and "
                     "the oracle, and every named case matched "
                     "its stated expectation.")
    lines.append("")
    RESULTS.write_text("\n".join(lines))
    print(f"run {total}, agreed {agreed}, "
          f"failures {len(failures)}")
    for f in failures:
        print("FAIL:", f)
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
