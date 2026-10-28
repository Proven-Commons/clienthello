# clienthello: a TLS ClientHello parser and printer, with proved round trips

Status: in-progress

A parser and printer for the TLS ClientHello message, in
Lean, following RFC 8446 section 4.1.2, with the legacy
fields carried from RFC 5246, the server name indication
from RFC 6066, and ALPN from RFC 7301. The definitions are
in `ClientHello/Value.lean` (the data model and the
printer) and `ClientHello/Parse.lean` (the parser). The
proofs are in `Proofs/RoundTrip.lean`. The rules are
written out in `SPEC.md`. This slice reads one TLS record
holding one ClientHello; it does no handshake crypto and
parses no certificates.

The statements a reviewer approves are in `Spec.lean`,
with their proofs in `Proofs/SpecProofs.lean`. No reviewer
has approved them yet, so this project is not called
verified.

## How to run it

`lake build` builds the library, the proofs, and the
command line tool. The tool reads one request per line:
the word `parse`, a space, and the message as
comma-separated decimal byte codes. It answers `ok:` and
the byte codes of the canonical reprint when the message
parses, `none` when it is rejected, and `error` when the
request itself is malformed.

`python3 tests/run_tests.py` rebuilds, runs the fixed
cases, the named rejections, and the differential run
against the harness oracle, and writes the outcome to
`tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back. | `Spec.parse_print` |
| Printing a message the parser took gives the same bytes it was read from, and the message is well formed. | `Spec.print_parse` |
| A hello with a present, empty extensions block is accepted and writes back as the same bytes. | `Spec.accepts_empty_extensions` |
| A minimal hello carrying only supported_versions is accepted and writes back as the same bytes. | `Spec.accepts_supported_versions` |
| A TLS 1.3 hello whose key_share carries no entries, the form a client uses to ask for a HelloRetryRequest, is accepted and writes back as the same bytes. | `Spec.accepts_key_share_empty_list` |
| A hello that does not offer TLS 1.3 may list compression methods besides null: one with [1, 0] and no extensions is accepted and writes back as the same bytes. | `Spec.accepts_tls12_compression` |
| Every accepted hello that offers TLS 1.3 (its supported_versions lists 0x0304) has exactly the compression methods [0]. | `Spec.tls13_compression_null` |
| Empty input is refused. | `Spec.rejects_empty` |
| Input shorter than the record header is refused. | `Spec.rejects_short_header` |
| A record length of 0 is refused. | `Spec.rejects_record_length_zero` |
| A content type other than 22 is refused. | `Spec.rejects_content_type` |
| A record length longer than the input is refused. | `Spec.rejects_record_length_longer` |
| A record whose length field is above 2^14 = 16384 is refused, whatever else the input holds. | `Spec.rejects_record_overflow` |
| Bytes after the record are refused. | `Spec.rejects_trailing_bytes` |
| A handshake type other than 1 is refused. | `Spec.rejects_handshake_type` |
| A handshake length that does not match the body is refused. | `Spec.rejects_handshake_length` |
| A body with no extensions block is refused. | `Spec.rejects_missing_extensions` |
| A session id length of 33 is refused. | `Spec.rejects_session_id_33` |
| A cipher suite list with an odd byte length is refused. | `Spec.rejects_odd_cipher_suites` |
| An empty cipher suite list is refused. | `Spec.rejects_empty_cipher_suites` |
| Compression methods without the null method 0 are refused. | `Spec.rejects_compression_without_null` |
| An empty compression method list is refused. | `Spec.rejects_empty_compression` |
| A hello that offers TLS 1.3 with compression methods [1, 0] is refused. | `Spec.rejects_tls13_compression` |
| An extension type standing twice is refused. | `Spec.rejects_duplicate_extension` |
| An extension length running past the block is refused. | `Spec.rejects_extension_overrun` |
| A key share group standing twice is refused. | `Spec.rejects_duplicate_key_share_group` |
| A key share entry with empty key bytes is refused. | `Spec.rejects_key_share_empty_key` |
| A supported_versions value with an odd length is refused. | `Spec.rejects_supported_versions_odd` |
| A supported_versions value with length 0 is refused. | `Spec.rejects_supported_versions_zero` |
| An ALPN value with an empty protocol name is refused. | `Spec.rejects_alpn_empty_name` |
| A server_name value with two host_name entries is refused. | `Spec.rejects_sni_second_host_name` |
| A server_name list length that does not cover the value is refused. | `Spec.rejects_sni_list_length` |

A message is well formed when the record version and the
legacy version each fit two bytes; the random holds
exactly 32 bytes; the session id holds at most 32 bytes;
the cipher suites are nonempty, each fits two bytes, and
there are at most 32767 of them; the compression methods
are nonempty, contain the null method 0, and number at
most 255, and are exactly [0] when the hello offers TLS 1.3
(its supported_versions lists 0x0304); every extension is well formed (its lengths fit
their fields, SNI has distinct entry types and a nonempty
host name when present, ALPN names are nonempty, key
share groups are distinct with nonempty keys, and an
opaque extension's type is none of the four decoded
types); no extension type stands twice; the printed
extensions block fits two bytes of length; and the
printed handshake message, its four header bytes and the
body fields, is at most 2^14 = 16384 bytes, the record
limit of RFC 8446 section 5.1.

The two round trip theorems rest on the proofs in
`Proofs/RoundTrip.lean`, where they are
`ClientHello.Proofs.parse_print` and
`ClientHello.Proofs.print_parse`. Both check against the
standard axioms only (`propext`, `Classical.choice`,
`Quot.sound`), which a reader can confirm with
`#print axioms`; `Proofs/Verify.lean` prints them at
build time. The example theorems are single inputs
checked in the kernel with `decide +kernel`.

The command line tool in `Main.lean` calls
`ClientHello.parse` and `ClientHello.print` directly,
the same functions the theorems are about.

## What is not proved

- That the parser accepts every message the rules in
  `SPEC.md` allow, and turns away every message they
  forbid. The round trips do not need either, and the
  example theorems pin single inputs only, so neither
  holds in general as a proof. The differential tests in
  `tests/` check that behaviour instead, and the results
  file records the outcome, including any failure.
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
  reading of the same rules, in Python. It is evidence,
  not proof.
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
   named rejections, and the differential run against
   the oracle, with counts and any failures written to
   `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool
   build clean, and the build prints the axiom list for
   both round trip theorems.
4. Read `SPEC.md` against RFC 8446 section 4.1.2 and
   check the pinned readings are the ones you want.
