/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The two round trips are the theorems proved in
  `Proofs/RoundTrip.lean`. The examples are single inputs, checked
  in the kernel with `decide +kernel`: no native evaluation, which
  the bar forbids.
-/

import ClientHello
import Proofs.RoundTrip

open ClientHello

theorem Spec.parse_print (m : Message) (hw : WF m) :
    parse (print m) = some m :=
  ClientHello.Proofs.parse_print m hw

theorem Spec.print_parse {bs : List UInt8} {m : Message}
    (hparse : parse bs = some m) :
    print m = bs ∧ WF m :=
  ClientHello.Proofs.print_parse hparse


theorem Spec.tls13_compression_null {bs : List UInt8} {m : Message}
    (hparse : parse bs = some m)
    (h13 : offersTls13 m.hello.extensions = true) :
    m.hello.compressionMethods = [0] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc13, _, _⟩ :=
    (ClientHello.Proofs.print_parse hparse).2
  exact hc13 h13

theorem Spec.accepts_empty_extensions :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 43, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0] : List UInt8)).map print =
      some ([22, 3, 1, 0, 47, 1, 0, 0, 43, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0] : List UInt8) := by
  decide +kernel


theorem Spec.accepts_supported_versions :
    (parse ([22, 3, 1, 0, 56, 1, 0, 0, 52, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).map print =
      some ([22, 3, 1, 0, 56, 1, 0, 0, 52, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8) := by
  decide +kernel


theorem Spec.accepts_key_share_empty_list :
    (parse ([22, 3, 1, 0, 78, 1, 0, 0, 74, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 31, 0, 10, 0, 6, 0, 4, 0, 29, 0, 23, 0, 43, 0, 3, 2, 3, 4, 0, 51, 0, 2, 0, 0, 0, 13, 0, 4, 0, 2, 4, 3] : List UInt8)).map print =
      some ([22, 3, 1, 0, 78, 1, 0, 0, 74, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 31, 0, 10, 0, 6, 0, 4, 0, 29, 0, 23, 0, 43, 0, 3, 2, 3, 4, 0, 51, 0, 2, 0, 0, 0, 13, 0, 4, 0, 2, 4, 3] : List UInt8) := by
  decide +kernel


theorem Spec.accepts_tls12_compression :
    (parse ([22, 3, 1, 0, 48, 1, 0, 0, 44, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 2, 1, 0, 0, 0] : List UInt8)).map print =
      some ([22, 3, 1, 0, 48, 1, 0, 0, 44, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 2, 1, 0, 0, 0] : List UInt8) := by
  decide +kernel


theorem Spec.rejects_empty :
    (parse ([] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_short_header :
    (parse ([22, 3] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_record_length_zero :
    (parse ([22, 3, 1, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_content_type :
    (parse ([23, 3, 1, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_record_length_longer :
    (parse ([22, 3, 1, 0, 10, 1, 0, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_record_overflow (ct v1 v2 a b : UInt8)
    (rest : List UInt8) (h : 16384 < a.toNat * 256 + b.toNat) :
    parse (ct :: v1 :: v2 :: a :: b :: rest) = none := by
  have hover : ¬ (u16 a b ≤ 16384) := by
    simp only [u16]
    omega
  unfold parse
  rw [ClientHello.Proofs.withU8_cons]
  by_cases hct : ct.toNat = 22
  · rw [if_pos hct, ClientHello.Proofs.withU16_cons,
      ClientHello.Proofs.withU16_cons, if_neg hover]
  · rw [if_neg hct]


theorem Spec.rejects_trailing_bytes :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 43, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_handshake_type :
    (parse ([22, 3, 1, 0, 4, 2, 0, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_handshake_length :
    (parse ([22, 3, 1, 0, 47, 1, 0, 0, 44, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_missing_extensions :
    (parse ([22, 3, 1, 0, 45, 1, 0, 0, 41, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_session_id_33 :
    (parse ([22, 3, 1, 0, 39, 1, 0, 0, 35, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_odd_cipher_suites :
    (parse ([22, 3, 1, 0, 41, 1, 0, 0, 37, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 3] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_empty_cipher_suites :
    (parse ([22, 3, 1, 0, 41, 1, 0, 0, 37, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_compression_without_null :
    (parse ([22, 3, 1, 0, 45, 1, 0, 0, 41, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 1] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_empty_compression :
    (parse ([22, 3, 1, 0, 44, 1, 0, 0, 40, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_tls13_compression :
    (parse ([22, 3, 1, 0, 57, 1, 0, 0, 53, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 2, 1, 0, 0, 9, 0, 43, 0, 5, 4, 3, 4, 3, 3] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_duplicate_extension :
    (parse ([22, 3, 1, 0, 61, 1, 0, 0, 57, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 14, 0, 43, 0, 3, 2, 3, 4, 0, 43, 0, 3, 2, 3, 3] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_extension_overrun :
    (parse ([22, 3, 1, 0, 54, 1, 0, 0, 50, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 7, 0, 0, 0, 10, 2, 3, 4] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_duplicate_key_share_group :
    (parse ([22, 3, 1, 0, 63, 1, 0, 0, 59, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 16, 0, 51, 0, 12, 0, 10, 0, 29, 0, 1, 1, 0, 29, 0, 1, 2] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_key_share_empty_key :
    (parse ([22, 3, 1, 0, 57, 1, 0, 0, 53, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 10, 0, 51, 0, 6, 0, 4, 0, 29, 0, 0] : List UInt8)).isSome = false := by
  decide +kernel



theorem Spec.rejects_supported_versions_odd :
    (parse ([22, 3, 1, 0, 55, 1, 0, 0, 51, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 8, 0, 43, 0, 4, 3, 3, 4, 3] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_supported_versions_zero :
    (parse ([22, 3, 1, 0, 52, 1, 0, 0, 48, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 5, 0, 43, 0, 1, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_alpn_empty_name :
    (parse ([22, 3, 1, 0, 54, 1, 0, 0, 50, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 7, 0, 16, 0, 3, 0, 1, 0] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_sni_second_host_name :
    (parse ([22, 3, 1, 0, 77, 1, 0, 0, 73, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 30, 0, 0, 0, 26, 0, 24, 0, 0, 9, 97, 46, 101, 120, 97, 109, 112, 108, 101, 0, 0, 9, 98, 46, 101, 120, 97, 109, 112, 108, 101] : List UInt8)).isSome = false := by
  decide +kernel


theorem Spec.rejects_sni_list_length :
    (parse ([22, 3, 1, 0, 67, 1, 0, 0, 63, 3, 3, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 0, 0, 2, 19, 1, 1, 0, 0, 20, 0, 0, 0, 16, 0, 99, 0, 0, 11, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109] : List UInt8)).isSome = false := by
  decide +kernel
