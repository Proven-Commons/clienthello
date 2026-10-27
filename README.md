# clienthello

A Lean parser for the TLS ClientHello message. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification.

Status: not verified. No code has landed yet. Plan issue 1 holds the first slice, and it is unclaimed. The specification has not been approved by a reviewer, so do not call this verified.

## First slice

- The TLS record header plus the ClientHello, from RFC 8446 section 4.1.2, with legacy fields from RFC 5246.
- Version, random, session id, cipher suites, and compression methods.
- Extensions as a type length value list. Four are decoded: server name indication, application layer protocol negotiation, supported versions, and key share.
- Other extensions are carried as opaque bytes with length checks, not interpreted.

This is distinct from the hostname repo. ClientHello extracts the server name string. Matching that name against a certificate stays in the hostname repo.

## Main claim

The parser never reads past the end of the message. A duplicate extension type is rejected. A duplicate key share group is rejected. An extension length that runs past the message is rejected. Printing the parsed form gives the same bytes for the parsed subset.

## Test oracles

- Go crypto/tls.
- OpenSSL captures.
- Wireshark TLS dissectors.

## Score

15 out of 18, first pass score in mission issue 19, the round 4 sheet. Created at the org owner's direction on that sheet, on the judgement that the slice, claim, and oracles are sound and that it duplicates no existing repo.

## What is not in this slice

- The rest of the TLS handshake.
- Certificate parsing. That follows from the der repo.
- Any claim about a full TLS implementation.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
