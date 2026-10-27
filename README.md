# clienthello: a TLS ClientHello parser and printer, with proved round trips

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

Status: the specification has not been approved by a
reviewer, so do not call this verified. The statements a
reviewer approves (the bar's `Spec.lean`) have not been
added yet.

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

| Claim | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back. | `ClientHello.Proofs.parse_print` |
| Printing a message the parser took gives the same bytes it was read from. | `ClientHello.Proofs.print_parse` |

A message is well formed when the record version and the
legacy version each fit two bytes; the random holds
exactly 32 bytes; the session id holds at most 32 bytes;
the cipher suites are nonempty, each fits two bytes, and
there are at most 32767 of them; the compression methods
are nonempty, contain the null method 0, and number at
most 255; every extension is well formed (its lengths fit
their fields, SNI has distinct entry types and a nonempty
host name when present, ALPN names are nonempty, key
share groups are distinct with nonempty keys, and an
opaque extension's type is none of the four decoded
types); no extension type stands twice; the printed
extensions block fits two bytes of length; and the
printed body fields fit the three byte handshake length
with room to spare (at most 65531 bytes).

Both theorems check against the standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`), which a
reader can confirm with `#print axioms` on
`ClientHello.Proofs.parse_print` and
`ClientHello.Proofs.print_parse`; `Proofs/Verify.lean`
prints them at build time.

The command line tool in `Main.lean` calls these
functions directly.

## What is not proved

- That the parser accepts every message the rules in
  `SPEC.md` allow, and turns away every message they
  forbid. The round trips do not need either, so neither
  is proved. The differential tests in `tests/` check
  that behaviour instead, and the results file records
  the outcome, including any failure.
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

- The Lean toolchain (Lean 4.35.0) and its kernel.
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

## How to re-check it

1. `lake build`: the library, the proofs, and the tool
   build clean, and the build prints the axiom list for
   both theorems.
2. `python3 tests/run_tests.py`: the fixed cases, the
   named rejections, and the differential run against the
   oracle, with counts and any failures written to
   `tests/TEST-RESULTS.md`.
3. Read `SPEC.md` against RFC 8446 section 4.1.2 and
   check the pinned readings are the ones you want.
