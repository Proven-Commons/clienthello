# clienthello: a TLS ClientHello parser and printer, with proved round trips

Status: in progress

A parser and printer for the TLS ClientHello message, in
Lean, following RFC 8446 section 4.1.2, with the legacy
fields carried from RFC 5246, the server name indication
from RFC 6066, and ALPN from RFC 7301. The definitions are
in `ClientHello/Value.lean` (the data model and the
printer) and `ClientHello/Parse.lean` (the parser). The
proofs are in `Proofs/RoundTrip.lean`. The rules are
written out in `SPEC.md`, and as one Lean predicate,
`Spec.WF`, in `Spec/Defs.lean`. This slice reads one TLS
record holding one ClientHello; it does no handshake
crypto and parses no certificates.

The statements a reviewer approves are in `Spec.lean`,
with the definition of a well formed message they use in
`Spec/Defs.lean`, and their proofs in
`Proofs/SpecProofs.lean`. No reviewer has approved them
yet, so this project is not called verified.

## How to run it

`lake build` builds the library, the proofs, and the
command line tool. The tool reads one request per line:
the word `parse`, a space, and the message as
comma-separated decimal byte codes. It answers `ok:` and
the byte codes of the canonical reprint when the message
parses, `none` when it is rejected, and `error` when the
request itself is malformed.

`python3 tests/run_tests.py` rebuilds, runs the fixed
cases, the named rejections, the differential run against
the harness oracle, and real ClientHellos built by OpenSSL
through Python's ssl module, and writes the outcome to
`tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

Statements about every input, or every input of one form:

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back. | `Spec.parse_print` |
| Printing a message the parser took gives the same bytes it was read from, and the message is well formed. | `Spec.print_parse` |
| A record whose length field is above 2^14 = 16384 is refused, whatever else the input holds. | `Spec.rejects_record_overflow` |
| A record of exactly 2^14 = 16384 bytes is accepted and writes back as the same bytes. The input is the hello of `Spec.accepts_supported_versions` with a padding extension (type 21) after its supported_versions, whose value is any 16324 bytes, and the lengths that cover it, 16389 bytes in all. | `Spec.accepts_record_at_limit` |
| Every accepted hello with a supported_versions extension that lists 0x0304, in any position (a hello that offers TLS 1.3), has exactly the compression methods [0]. | `Spec.tls13_compression_null` |
| In every accepted hello, no extension but the last has type 41: pre_shared_key, when present, is the last extension. | `Spec.psk_last` |

Together, the two round trips say that the parser accepts
exactly the printed forms of well formed messages, so
every rule that is part of well formedness (below) holds
for every accepted input. The statements after them state
the record limit from both sides and two more of those
rules on their own, so that each has a theorem of its own.

Single inputs. Each theorem below is about the one input
written out in `Spec.lean`, and each claim says what that
input is. Most refused inputs are an accepted input with
one field changed, so that the field's rule is what refuses
it. These theorems pin each rule to a concrete case; they
do not state the rule for every input.

| Claim | Theorem |
|-------|---------|
| A 52-byte hello with a present, empty extensions block is accepted and writes back as the same bytes. | `Spec.accepts_empty_extensions` |
| A 61-byte hello whose one extension is supported_versions [0x0304, 0x0303] is accepted and writes back as the same bytes. | `Spec.accepts_supported_versions` |
| An 83-byte TLS 1.3 hello whose key_share carries no entries, the form a client uses to ask for a HelloRetryRequest, is accepted and writes back as the same bytes. | `Spec.accepts_key_share_empty_list` |
| The hello of `Spec.accepts_empty_extensions` with compression methods [1, 0] is accepted and writes back as the same bytes: it does not offer TLS 1.3, so methods besides null may be listed. | `Spec.accepts_tls12_compression` |
| A hello whose extensions are supported_versions and then pre_shared_key is accepted and writes back as the same bytes. | `Spec.accepts_psk_last` |
| Empty input is refused. | `Spec.rejects_empty` |
| A 2-byte input, shorter than the record header, is refused. | `Spec.rejects_short_header` |
| A record header with length 0 and nothing after it is refused. | `Spec.rejects_record_length_zero` |
| The hello of `Spec.accepts_supported_versions` with content type 23 in place of 22 is refused. | `Spec.rejects_content_type` |
| A record whose length field (10) is longer than the 4 bytes that follow is refused. | `Spec.rejects_record_length_longer` |
| The hello of `Spec.accepts_empty_extensions` with one byte after the record is refused. | `Spec.rejects_trailing_bytes` |
| The hello of `Spec.accepts_supported_versions` with handshake type 2 in place of 1 is refused. | `Spec.rejects_handshake_type` |
| The hello of `Spec.accepts_empty_extensions` with a handshake length one more than the body holds is refused. | `Spec.rejects_handshake_length` |
| The hello of `Spec.accepts_empty_extensions` without its extensions block, ending after the compression methods, is refused. | `Spec.rejects_missing_extensions` |
| The hello of `Spec.accepts_supported_versions` with a 33-byte session id is refused. | `Spec.rejects_session_id_33` |
| The hello of `Spec.accepts_supported_versions` with a 3-byte cipher suite list is refused. | `Spec.rejects_odd_cipher_suites` |
| The hello of `Spec.accepts_supported_versions` with an empty cipher suite list is refused. | `Spec.rejects_empty_cipher_suites` |
| The hello of `Spec.accepts_empty_extensions` with compression methods [1], without the null method, is refused. | `Spec.rejects_compression_without_null` |
| The hello of `Spec.accepts_empty_extensions` with an empty compression method list is refused. (An empty list holds no null method, so the rule above refuses it too.) | `Spec.rejects_empty_compression` |
| The hello of `Spec.accepts_supported_versions`, which offers TLS 1.3, with compression methods [1, 0] is refused. | `Spec.rejects_tls13_compression` |
| The input of `Spec.rejects_tls13_compression` with its supported_versions list in the other order, [0x0303, 0x0304], is refused. | `Spec.rejects_tls13_compression_second` |
| A hello with two supported_versions extensions is refused. | `Spec.rejects_duplicate_extension` |
| The hello of `Spec.accepts_psk_last` with its two extensions in the other order, pre_shared_key first, is refused. | `Spec.rejects_psk_not_last` |
| A hello whose one extension declares 10 value bytes where its block holds 3 is refused. | `Spec.rejects_extension_overrun` |
| A hello whose key_share carries two entries for group 29 is refused. | `Spec.rejects_duplicate_key_share_group` |
| A hello whose key_share entry has empty key exchange bytes is refused. | `Spec.rejects_key_share_empty_key` |
| A hello whose one extension is supported_versions with the 4-byte value 3, 3, 4, 3 is refused: its list length byte is 3, which is odd, and 3 bytes follow it. | `Spec.rejects_supported_versions_odd` |
| A hello whose one extension is supported_versions with the 1-byte value 0 is refused: its list length byte is 0, so it lists no version. | `Spec.rejects_supported_versions_zero` |
| A hello whose ALPN value holds one protocol name of length 0 is refused. | `Spec.rejects_alpn_empty_name` |
| A hello whose server_name value holds two host_name entries is refused. | `Spec.rejects_sni_second_host_name` |
| A hello whose server_name list length (99) does not cover the rest of the value is refused. | `Spec.rejects_sni_list_length` |

A message is well formed (`Spec.WF`) when the record
version and the legacy version each fit two bytes; the
random holds exactly 32 bytes; the session id holds at
most 32 bytes; the cipher suites are nonempty, each fits
two bytes, and there are at most 32767 of them; the
compression methods are nonempty, contain the null method
0, number at most 255, and are exactly [0] when the hello
offers TLS 1.3 (its supported_versions lists 0x0304);
every extension is well formed (its lengths fit their
fields, SNI has distinct entry types and a nonempty host
name when present, ALPN names are nonempty, key share
groups are distinct with nonempty keys, and an opaque
extension's type is none of the four decoded types); no
extension type stands twice; no extension but the last has
type 41 (pre_shared_key); the printed extensions block
fits two bytes of length; and the printed handshake
message, its four header bytes and the body fields, is at
most 2^14 = 16384 bytes, the record limit of RFC 8446
section 5.1.

`Spec.WF` is in `Spec/Defs.lean`, which `bar.toml` lists
among the spec files. The approval covers it with
`Spec.lean`, so what the two round trips mean cannot
change without changing the approved text.

The two round trip theorems rest on the proofs in
`Proofs/RoundTrip.lean`, where they are
`ClientHello.Proofs.parse_print` and
`ClientHello.Proofs.print_parse`. Both check against the
standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), which a reader can confirm with
`#print axioms`; `Proofs/Verify.lean` prints them at
build time. The single-input theorems are checked in the
kernel with `decide +kernel`.

The command line tool in `Main.lean` calls
`ClientHello.parse` and `ClientHello.print` directly,
the same functions the theorems are about.

## What is not proved

- That the well formedness predicate, `Spec.WF`, is the
  same as the rules in `SPEC.md`. Relative to the
  predicate, the accepted inputs are fixed exactly: the
  parser accepts the printed forms of well formed messages
  and nothing else. That the predicate holds every rule of
  `SPEC.md`, and no other, is read by the reviewer and
  checked by the differential tests in `tests/`, not
  proved. The single-input theorems pin one input each.
- That the printer writes the byte layout the RFCs give.
  The round trips relate the parser and the printer to
  each other; the accepted examples pin some whole inputs,
  but no theorem names the bytes of each field.
- The meaning of any extension other than the four
  decoded ones. Every other extension is carried as its
  type and value bytes, and no per extension content rule
  is checked.
- Anything about the host name bytes beyond their being
  nonempty when present: no label rules, no case rules, no
  matching against a certificate. Name matching belongs
  to the hostname work.
- Anything about the rest of the handshake, the key
  schedule, or any other record or message type.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, which turns the proved definitions
  into the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies
  to trust beyond the Lean toolchain itself.
- That `SPEC.md` states the reading of the RFCs you
  intend. The proofs are about the parser and printer in
  this repo following each other exactly; the fidelity of
  the spec to the RFCs is a reading, pinned in SPEC.md
  where the RFCs leave a choice open.
- The test oracle in `tests/run_tests.py` is a second
  reading of the same rules, in Python, by the same
  authors. It is evidence, not proof. OpenSSL, through
  Python's ssl module, supplies real ClientHellos that must
  be accepted, but no outside TLS stack judges the
  malformed inputs.
- The line handling in `Main.lean` (splitting a request
  line, reading decimal codes). The tests drive it, and
  no proof covers it.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the
   named rejections, the differential run against the
   oracle, and the OpenSSL-built hellos, with the oracle,
   seed, input count and failures written to
   `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool
   build clean, and the build prints the axiom list for
   both round trip theorems.
4. Read `SPEC.md` against RFC 8446 section 4.1.2 and
   check the pinned readings are the ones you want.
