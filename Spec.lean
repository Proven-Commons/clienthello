/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use only the definitions in `ClientHello/Value.lean`
  and `ClientHello/Parse.lean`, the code under proof named in
  `bar.toml`. No definition of their own is needed, so this project
  has no `Spec/Defs.lean`.
-/

import ClientHello

open ClientHello

/-! ## The round trips

The two statements the slice stands on. Each one is the statement of
the proved theorem of the same shape in `Proofs/RoundTrip.lean`, over
the same well formedness predicate, `ClientHello.WF`. -/

/-- Parsing the printed form of a well formed message gives the
    message back. -/
theorem Spec.parse_print (m : Message) (hw : WF m) :
    parse (print m) = some m := sorry

/-- A message the parser took prints back to the bytes it was read
    from, and the message is well formed. So a printer that wrote
    nothing, or wrote something shorter, fails the first half. -/
theorem Spec.print_parse {bs : List UInt8} {m : Message}
    (hparse : parse bs = some m) :
    print m = bs ∧ WF m := sorry

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

/-- A content type other than 22 (handshake) is refused. -/
theorem Spec.rejects_content_type :
    (parse ([23, 3, 1, 0, 0] : List UInt8)).isSome = false := sorry

/-- A record length longer than the input is refused rather than read past the end. -/
theorem Spec.rejects_record_length_longer :
    (parse ([22, 3, 1, 0, 10, 1, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- Bytes after the record are refused rather than ignored. -/
theorem Spec.rejects_trailing_bytes :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 43, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- A handshake type other than 1 (client_hello) is refused. -/
theorem Spec.rejects_handshake_type :
    (parse ([22, 3, 1, 0, 4, 2, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- A handshake length that does not equal the remaining body length is refused. -/
theorem Spec.rejects_handshake_length :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 44, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- A body that ends after the compression methods, with no extensions block, is refused. -/
theorem Spec.rejects_missing_extensions :
    (parse ([22, 3, 1, 0, 45, 1, 0, 0, 41, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0] : List UInt8)).isSome = false := sorry

/-- A session id length of 33 is refused: the limit is 32. -/
theorem Spec.rejects_session_id_33 :
    (parse ([22, 3, 1, 0, 39, 1, 0, 0, 35, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33] : List UInt8)).isSome = false := sorry

/-- A cipher suite list with an odd byte length is refused. -/
theorem Spec.rejects_odd_cipher_suites :
    (parse ([22, 3, 1, 0, 41, 1, 0, 0, 37, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 3] : List UInt8)).isSome = false := sorry

/-- An empty cipher suite list is refused. -/
theorem Spec.rejects_empty_cipher_suites :
    (parse ([22, 3, 1, 0, 41, 1, 0, 0, 37, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 0] : List UInt8)).isSome = false := sorry

/-- Compression methods that do not contain the null method 0 are refused. -/
theorem Spec.rejects_compression_without_null :
    (parse ([22, 3, 1, 0, 45, 1, 0, 0, 41, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 1] : List UInt8)).isSome = false := sorry

/-- An empty compression method list is refused. -/
theorem Spec.rejects_empty_compression :
    (parse ([22, 3, 1, 0, 44, 1, 0, 0, 40, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 0] : List UInt8)).isSome = false := sorry

/-- An extension type standing twice in one block is refused. -/
theorem Spec.rejects_duplicate_extension :
    (parse ([22, 3, 1, 0, 61, 1, 0, 0, 57, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 14, 0, 43, 0, 3, 2, 3, 4, 0, 43, 0, 3, 2, 3, 3] : List UInt8)).isSome = false := sorry

/-- An extension length that runs past the end of the block is refused. -/
theorem Spec.rejects_extension_overrun :
    (parse ([22, 3, 1, 0, 54, 1, 0, 0, 50, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 7, 0, 0, 0, 10, 2, 3, 4] : List UInt8)).isSome = false := sorry

/-- A key share group standing twice in one key_share value is refused. -/
theorem Spec.rejects_duplicate_key_share_group :
    (parse ([22, 3, 1, 0, 63, 1, 0, 0, 59, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 16, 0, 51, 0, 12, 0, 10, 0, 29, 0, 1, 1, 0, 29, 0, 1, 2] : List UInt8)).isSome = false := sorry

/-- A key share entry with empty key exchange bytes is refused. -/
theorem Spec.rejects_key_share_empty_key :
    (parse ([22, 3, 1, 0, 57, 1, 0, 0, 53, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 10, 0, 51, 0, 6, 0, 4, 0, 29, 0, 0] : List UInt8)).isSome = false := sorry

/-- A key_share value with no entries is refused. -/
theorem Spec.rejects_key_share_empty_list :
    (parse ([22, 3, 1, 0, 53, 1, 0, 0, 49, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 6, 0, 51, 0, 2, 0, 0] : List UInt8)).isSome = false := sorry

/-- A supported_versions value with an odd byte length is refused. -/
theorem Spec.rejects_supported_versions_odd :
    (parse ([22, 3, 1, 0, 55, 1, 0, 0, 51, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 8, 0, 43, 0, 4, 3, 3, 4, 3] : List UInt8)).isSome = false := sorry

/-- A supported_versions value with a length of 0 is refused. -/
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
