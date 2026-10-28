/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use the definitions in `ClientHello/Value.lean` and
  `ClientHello/Parse.lean`, the code under proof named in `bar.toml`,
  and one definition of their own: `Spec.WF`, what a well formed
  message is, in `Spec/Defs.lean`. That file is a spec file too, so the
  approval fixes what the round trips mean.
-/

import ClientHello
import Spec.Defs

open ClientHello

/-! ## The round trips

The two statements the slice stands on. Each one is the statement of
the proved theorem of the same shape in `Proofs/RoundTrip.lean`, over
the well formedness predicate `Spec.WF` of `Spec/Defs.lean`. -/

/-- Parsing the printed form of a well formed message gives the
    message back. -/
theorem Spec.parse_print (m : Message) (hw : Spec.WF m) :
    parse (print m) = some m := sorry

/-- A message the parser took prints back to the bytes it was read
    from, and the message is well formed. So a printer that wrote
    nothing, or wrote something shorter, fails the first half. -/
theorem Spec.print_parse {bs : List UInt8} {m : Message}
    (hparse : parse bs = some m) :
    print m = bs ∧ Spec.WF m := sorry

/-! ## Rules every accepted message meets

Each of these follows from `Spec.print_parse`, since the well formedness
predicate includes the rule; it is stated on its own so that the claim on
the page names a theorem that says exactly that. -/

/-- An accepted hello that offers TLS 1.3, that is one with a
    supported_versions extension whose list holds 0x0304 (772) in any
    position, carries exactly one compression method, the null method 0
    (RFC 8446 section 4.1.2). The hypotheses name the extension and the
    version themselves, so what "offers TLS 1.3" means is fixed here and
    not by a definition in the code. -/
theorem Spec.tls13_compression_null {bs : List UInt8} {m : Message}
    {vs : List Nat}
    (hparse : parse bs = some m)
    (hsv : Extension.supportedVersions vs ∈ m.hello.extensions)
    (h13 : 772 ∈ vs) :
    m.hello.compressionMethods = [0] := sorry

/-- In an accepted hello, no extension but the last has type 41
    (pre_shared_key): when present, pre_shared_key is the last extension
    (RFC 8446 section 4.2.11). -/
theorem Spec.psk_last {bs : List UInt8} {m : Message}
    (hparse : parse bs = some m) :
    41 ∉ (m.hello.extensions.dropLast).map extType := sorry

/-! ## Accepted examples

Single inputs the parser accepts. Each one is stated in the form the
round trip gives for a single input: parsing the bytes and printing
the result gives the same bytes back. -/

/-- A hello whose extensions block is present and empty is accepted, and writes back as the same bytes. -/
theorem Spec.accepts_empty_extensions :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 43, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0] : List UInt8)).map print =
      some ([22, 3, 1, 0, 47, 1, 0, 0, 43, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0] : List UInt8) := sorry

/-- A minimal hello carrying only a supported_versions extension is accepted, and writes back as the same bytes. -/
theorem Spec.accepts_supported_versions :
    (parse ([22, 3, 1, 0, 56, 1, 0, 0, 52, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).map print =
      some ([22, 3, 1, 0, 56, 1, 0, 0, 52, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8) := sorry

/-- A TLS 1.3 hello whose key_share carries an empty client_shares list,
    the form a client sends to ask for a HelloRetryRequest (RFC 8446
    section 4.2.8), is accepted and writes back as the same bytes. Besides
    key_share it carries supported_groups [x25519, secp256r1],
    supported_versions [0x0304] and signature_algorithms. -/
theorem Spec.accepts_key_share_empty_list :
    (parse ([22, 3, 1, 0, 78, 1, 0, 0, 74, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 31, 0, 10, 0, 6, 0, 4, 0, 29, 0, 23, 0, 43, 0, 3, 2, 3, 4, 0, 51, 0, 2, 0, 0, 0, 13, 0, 4, 0, 2, 4, 3] : List UInt8)).map print =
      some ([22, 3, 1, 0, 78, 1, 0, 0, 74, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 31, 0, 10, 0, 6, 0, 4, 0, 29, 0, 23, 0, 43, 0, 3, 2, 3, 4, 0, 51, 0, 2, 0, 0, 0, 13, 0, 4, 0, 2, 4, 3] : List UInt8) := sorry

/-- A hello that does not offer TLS 1.3 (it has no extensions) may list
    compression methods besides null: here [1, 0]. It is accepted and writes
    back as the same bytes. -/
theorem Spec.accepts_tls12_compression :
    (parse ([22, 3, 1, 0, 48, 1, 0, 0, 44, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 2, 1, 0, 0, 0] : List UInt8)).map print =
      some ([22, 3, 1, 0, 48, 1, 0, 0, 44, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 2, 1, 0, 0, 0] : List UInt8) := sorry

/-- A hello whose last extension is pre_shared_key (type 41, its value
    carried opaque, here two bytes) after supported_versions is accepted
    and writes back as the same bytes. -/
theorem Spec.accepts_psk_last :
    (parse ([22, 3, 1, 0, 62, 1, 0, 0, 58, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 15, 0, 43, 0, 5, 4, 3, 4, 3, 3, 0, 41, 0, 2, 0, 0] : List UInt8)).map print =
      some ([22, 3, 1, 0, 62, 1, 0, 0, 58, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 15, 0, 43, 0, 5, 4, 3, 4, 3, 3, 0, 41, 0, 2, 0, 0] : List UInt8) := sorry

/-! ## The record limit, accept side

`Spec.rejects_record_overflow` refuses every record length above 2^14.
This is the other side of that limit: a record of exactly 2^14 bytes is
accepted, whatever the bytes that fill it. -/

/-- A record of exactly 2^14 = 16384 bytes, the most RFC 8446 section 5.1
    allows, is accepted and writes back as the same bytes. The input is
    the hello of `Spec.accepts_supported_versions` with a second extension
    after its supported_versions: type 21 (padding, RFC 7685, carried
    opaque) whose value is any 16324 bytes `v`. The lengths that cover it
    change to match: the record length field is 16384 (64, 0), the
    handshake length 16380, the extensions block 16337 and the padding
    value 16324. The input is 16389 bytes long. -/
theorem Spec.accepts_record_at_limit (v : List UInt8)
    (hv : v.length = 16324) :
    (parse (([22, 3, 1, 64, 0, 1, 0, 63, 252, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 63, 209, 0, 43, 0, 5, 4, 3, 4, 3, 3, 0, 21, 63, 196] : List UInt8) ++ v)).map print =
      some (([22, 3, 1, 64, 0, 1, 0, 63, 252, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 63, 209, 0, 43, 0, 5, 4, 3, 4, 3, 3, 0, 21, 63, 196] : List UInt8) ++ v) := sorry

/-! ## Refused inputs

Single inputs the parser refuses, one for each headline rule of
`SPEC.md`. The differential tests cover these rules on many more
inputs; these statements pin them so a reader of the specification
can check each rule against one concrete case. -/

/-- Empty input is refused: it is not a record with an empty body. -/
theorem Spec.rejects_empty :
    (parse ([] : List UInt8)).isSome = false := sorry

/-- Input shorter than the five byte record header is refused. -/
theorem Spec.rejects_short_header :
    (parse ([22, 3] : List UInt8)).isSome = false := sorry

/-- A record length of 0 is refused: an empty body cannot hold a ClientHello. -/
theorem Spec.rejects_record_length_zero :
    (parse ([22, 3, 1, 0, 0] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.accepts_supported_versions` with content type 23
    (application_data) in place of 22 is refused. -/
theorem Spec.rejects_content_type :
    (parse ([23, 3, 1, 0, 56, 1, 0, 0, 52, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).isSome = false := sorry

/-- A record whose length field (10) is longer than the 4 bytes that follow
    is refused. -/
theorem Spec.rejects_record_length_longer :
    (parse ([22, 3, 1, 0, 10, 1, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- A record whose length field, bytes 3 and 4 read big endian, is above
    2^14 = 16384 is refused, whatever the other header bytes are and
    whatever follows (RFC 8446 section 5.1: the length MUST NOT exceed
    2^14 bytes). -/
theorem Spec.rejects_record_overflow (ct v1 v2 a b : UInt8)
    (rest : List UInt8) (h : 16384 < a.toNat * 256 + b.toNat) :
    parse (ct :: v1 :: v2 :: a :: b :: rest) = none := sorry

/-- Bytes after the record are refused rather than ignored. -/
theorem Spec.rejects_trailing_bytes :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 43, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.accepts_supported_versions` with handshake type 2
    (server_hello) in place of 1 is refused. -/
theorem Spec.rejects_handshake_type :
    (parse ([22, 3, 1, 0, 56, 2, 0, 0, 52, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).isSome = false := sorry

/-- A handshake length that does not equal the remaining body length is refused. -/
theorem Spec.rejects_handshake_length :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 44, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- A body that ends after the compression methods, with no extensions block, is refused. -/
theorem Spec.rejects_missing_extensions :
    (parse ([22, 3, 1, 0, 45, 1, 0, 0, 41, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.accepts_supported_versions` with a 33-byte session
    id, one over the limit of 32, is refused. Only the session id and the
    lengths that cover it differ. -/
theorem Spec.rejects_session_id_33 :
    (parse ([22, 3, 1, 0, 89, 1, 0, 0, 85, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 0, 2, 19, 1, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.accepts_supported_versions` with a 3-byte cipher
    suite list (19, 1, 19), an odd length, is refused. -/
theorem Spec.rejects_odd_cipher_suites :
    (parse ([22, 3, 1, 0, 57, 1, 0, 0, 53, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 3, 19, 1, 19, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.accepts_supported_versions` with an empty cipher
    suite list is refused. -/
theorem Spec.rejects_empty_cipher_suites :
    (parse ([22, 3, 1, 0, 54, 1, 0, 0, 50, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 0, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.accepts_empty_extensions` with compression methods
    [1], which lack the null method 0, is refused. It offers no TLS 1.3,
    so only the null method rule applies. -/
theorem Spec.rejects_compression_without_null :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 43, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 1, 0, 0] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.accepts_empty_extensions` with an empty compression
    method list is refused. An empty list holds no null method, so the
    rule of `Spec.rejects_compression_without_null` refuses it as well. -/
theorem Spec.rejects_empty_compression :
    (parse ([22, 3, 1, 0, 46, 1, 0, 0, 42, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- A hello that offers TLS 1.3 and lists compression methods [1, 0] is
    refused: for TLS 1.3 the list must be exactly [0]. The input is the
    hello of `Spec.accepts_supported_versions` with that one field
    changed. -/
theorem Spec.rejects_tls13_compression :
    (parse ([22, 3, 1, 0, 57, 1, 0, 0, 53, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 2, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.rejects_tls13_compression` with its supported_versions
    list in the other order, [0x0303, 0x0304], is refused too: a hello
    offers TLS 1.3 when 0x0304 is anywhere in the list, not only first. -/
theorem Spec.rejects_tls13_compression_second :
    (parse ([22, 3, 1, 0, 57, 1, 0, 0, 53, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 2, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 3, 3, 4] : List UInt8)).isSome = false := sorry

/-- An extension type standing twice in one block is refused. -/
theorem Spec.rejects_duplicate_extension :
    (parse ([22, 3, 1, 0, 61, 1, 0, 0, 57, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 14, 0, 43, 0, 3, 2, 3, 4, 0, 43, 0, 3, 2, 3, 3] : List UInt8)).isSome = false := sorry

/-- The hello of `Spec.accepts_psk_last` with its two extensions in the
    other order, pre_shared_key first, is refused. -/
theorem Spec.rejects_psk_not_last :
    (parse ([22, 3, 1, 0, 62, 1, 0, 0, 58, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 15, 0, 41, 0, 2, 0, 0, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).isSome = false := sorry

/-- A hello whose one extension declares 10 value bytes where its block
    holds 3 is refused. -/
theorem Spec.rejects_extension_overrun :
    (parse ([22, 3, 1, 0, 54, 1, 0, 0, 50, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 7, 0, 0, 0, 10, 2, 3, 4] : List UInt8)).isSome = false := sorry

/-- A key share group standing twice in one key_share value is refused. -/
theorem Spec.rejects_duplicate_key_share_group :
    (parse ([22, 3, 1, 0, 63, 1, 0, 0, 59, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 16, 0, 51, 0, 12, 0, 10, 0, 29, 0, 1, 1, 0, 29, 0, 1, 2] : List UInt8)).isSome = false := sorry

/-- A key share entry with empty key exchange bytes is refused. -/
theorem Spec.rejects_key_share_empty_key :
    (parse ([22, 3, 1, 0, 57, 1, 0, 0, 53, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 10, 0, 51, 0, 6, 0, 4, 0, 29, 0, 0] : List UInt8)).isSome = false := sorry

/-- A hello whose one extension is supported_versions with the 4-byte
    value [3, 3, 4, 3] is refused. Its list length byte is 3, which is odd,
    and the 3 bytes after it match that length, so the odd length
    is what refuses it. -/
theorem Spec.rejects_supported_versions_odd :
    (parse ([22, 3, 1, 0, 55, 1, 0, 0, 51, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 8, 0, 43, 0, 4, 3, 3, 4, 3] : List UInt8)).isSome = false := sorry

/-- A hello whose one extension is supported_versions with the 1-byte
    value [0] is refused. Its list length byte is 0, so it lists no
    version. -/
theorem Spec.rejects_supported_versions_zero :
    (parse ([22, 3, 1, 0, 52, 1, 0, 0, 48, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 5, 0, 43, 0, 1, 0] : List UInt8)).isSome = false := sorry

/-- An ALPN value holding an empty protocol name is refused. -/
theorem Spec.rejects_alpn_empty_name :
    (parse ([22, 3, 1, 0, 54, 1, 0, 0, 50, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 7, 0, 16, 0, 3, 0, 1, 0] : List UInt8)).isSome = false := sorry

/-- A server_name value with two host_name entries is refused. -/
theorem Spec.rejects_sni_second_host_name :
    (parse ([22, 3, 1, 0, 77, 1, 0, 0, 73, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 30, 0, 0, 0, 26, 0, 24, 0, 0, 9, 97, 46, 101, 120, 97, 109, 112, 108, 101, 0, 0, 9, 98, 46, 101, 120, 97, 109, 112, 108, 101] : List UInt8)).isSome = false := sorry

/-- A server_name value whose list length does not cover the rest of the value is refused. -/
theorem Spec.rejects_sni_list_length :
    (parse ([22, 3, 1, 0, 67, 1, 0, 0, 63, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 20, 0, 0, 0, 16, 0, 99, 0, 0, 11, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109] : List UInt8)).isSome = false := sorry
