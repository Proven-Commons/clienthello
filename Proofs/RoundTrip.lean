/-
  The round trip proofs.

  Two claims are proved here, matching the plan's main claim
  and its mirror:

  - `parse_print`: for every well formed message, parsing its
    printed form gives the message back.
  - `print_parse`: for every byte list the parser takes,
    printing the parsed message gives the same bytes back.
    The printer is canonical and the parser takes exactly the
    canonical forms: every length is recomputed from the
    value, and the value holds every byte the message
    carried, so nothing is lost or added.

  No theorem here says the parser never reads past the end
  of its input. In this list model every reader is a total
  function, so there is no out of bounds read to rule out: a
  read from input too short for its field gives `none`. The
  statement about the bytes is `print_parse`: every byte of
  an accepted input is accounted for in the message.
-/

import ClientHello
import Spec.Defs

namespace ClientHello.Proofs

open ClientHello
-- `WF` and `ExtWF` below are `Spec.WF` and `Spec.ExtWF`, the
-- well formedness predicate of the specification (`Spec/Defs.lean`).
open Spec (WF ExtWF)

/-! ## Byte and number basics -/

/-- A byte printed from a number reads back as the number
    modulo 256. -/
theorem toUInt8_toNat (n : Nat) : (n.toUInt8).toNat = n % 256 := rfl

/-- A byte's value fits in 256. -/
theorem toNat_lt (b : UInt8) : b.toNat < 256 := UInt8.toNat_lt_size b

/-- A byte rebuilt from its value is the byte. -/
theorem toNat_toUInt8 (b : UInt8) : b.toNat.toUInt8 = b := by
  apply UInt8.toNat_inj.mp
  show (b.toNat.toUInt8).toNat = b.toNat
  rw [toUInt8_toNat]
  exact Nat.mod_eq_of_lt (toNat_lt b)

/-- Two bytes printed from a value below 2^16 read back as
    the value. -/
theorem u16_be16 (n : Nat) (h : n < 65536) :
    u16 (n / 256).toUInt8 n.toUInt8 = n := by
  simp only [u16, toUInt8_toNat]
  omega

/-- The bytes read as a two byte value print back to those
    bytes. -/
theorem be16_u16 (a b : UInt8) : be16 (u16 a b) = [a, b] := by
  have ha := toNat_lt a
  have hb := toNat_lt b
  have e1 : u16 a b / 256 = a.toNat := by
    simp only [u16]; omega
  have e2 : (u16 a b).toUInt8 = b := by
    apply UInt8.toNat_inj.mp
    show ((u16 a b).toUInt8).toNat = b.toNat
    rw [toUInt8_toNat]; simp only [u16]; omega
  simp only [be16, e1, e2, toNat_toUInt8]

/-- Three bytes printed from a value below 2^24 read back as
    the value. -/
theorem u24_be24 (n : Nat) (h : n < 16777216) :
    u24 (n / 65536).toUInt8 (n / 256).toUInt8 n.toUInt8 = n := by
  simp only [u24, toUInt8_toNat]
  omega

/-- The bytes read as a three byte value print back to those
    bytes. -/
theorem be24_u24 (a b c : UInt8) :
    be24 (u24 a b c) = [a, b, c] := by
  have ha := toNat_lt a
  have hb := toNat_lt b
  have hc := toNat_lt c
  have e1 : u24 a b c / 65536 = a.toNat := by
    simp only [u24]; omega
  have e2 : (u24 a b c / 256).toUInt8 = b := by
    apply UInt8.toNat_inj.mp
    show ((u24 a b c / 256).toUInt8).toNat = b.toNat
    rw [toUInt8_toNat]; simp only [u24]; omega
  have e3 : (u24 a b c).toUInt8 = c := by
    apply UInt8.toNat_inj.mp
    show ((u24 a b c).toUInt8).toNat = c.toNat
    rw [toUInt8_toNat]; simp only [u24]; omega
  simp only [be24, e1, e2, e3, toNat_toUInt8]

/-! ## The readers, on printed forms and on read forms -/

/-- Reading two bytes off the front of a printed value and
    what follows it. -/
theorem getU16_be16 (n : Nat) (h : n < 65536) (r : List UInt8) :
    getU16 (be16 n ++ r) = some (n, r) := by
  show getU16 ((n / 256).toUInt8 :: n.toUInt8 :: r) = some (n, r)
  show some (u16 (n / 256).toUInt8 n.toUInt8, r) = some (n, r)
  rw [u16_be16 n h]

/-- Bytes read by the two byte reader print back as those
    bytes, and the value fits two bytes. -/
theorem getU16_inv {bs : List UInt8} {n : Nat} {r : List UInt8}
    (h : getU16 bs = some (n, r)) :
    bs = be16 n ++ r ∧ n < 65536 := by
  cases bs with
  | nil => simp [getU16] at h
  | cons a bs' =>
    cases bs' with
    | nil => simp [getU16] at h
    | cons b r' =>
      have hstep : getU16 (a :: b :: r') = some (u16 a b, r') := rfl
      rw [hstep] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · simp only [be16_u16, List.cons_append, List.nil_append]
      · have ha := toNat_lt a
        have hb := toNat_lt b
        simp only [u16]; omega

/-! The continuation readers. Each lemma below is stated for
any continuation `k`, so a proof uses it by rewriting: the
continuation in the goal is matched as it stands, and what is
left is its body, applied to the field read. -/

/-- A printed two byte value, as its two bytes in front of
    what follows it. -/
theorem be16_append (n : Nat) (r : List UInt8) :
    be16 n ++ r = (n / 256).toUInt8 :: n.toUInt8 :: r := rfl

/-- A printed three byte value, as its three bytes in front
    of what follows it. -/
theorem be24_append (n : Nat) (r : List UInt8) :
    be24 n ++ r =
      (n / 65536).toUInt8 :: (n / 256).toUInt8 :: n.toUInt8 :: r :=
  rfl

/-- One step of the one byte reader. -/
theorem withU8_cons {α : Type} (b : UInt8) (r : List UInt8)
    (k : Nat → List UInt8 → Option α) :
    withU8 (b :: r) k = k b.toNat r := rfl

/-- One step of the two byte reader. -/
theorem withU16_cons {α : Type} (a b : UInt8) (r : List UInt8)
    (k : Nat → List UInt8 → Option α) :
    withU16 (a :: b :: r) k = k (u16 a b) r := rfl

/-- One step of the three byte reader. -/
theorem withU24_cons {α : Type} (a b c : UInt8) (r : List UInt8)
    (k : Nat → List UInt8 → Option α) :
    withU24 (a :: b :: c :: r) k = k (u24 a b c) r := rfl

/-- The two byte reader on a printed value reads the value. -/
theorem withU16_be16 {α : Type} {n : Nat} (h : n < 65536)
    (r : List UInt8) (k : Nat → List UInt8 → Option α) :
    withU16 (be16 n ++ r) k = k n r := by
  rw [be16_append, withU16_cons, u16_be16 n h]

/-- The three byte reader on a printed value reads the
    value. -/
theorem withU24_be24 {α : Type} {n : Nat} (h : n < 16777216)
    (r : List UInt8) (k : Nat → List UInt8 → Option α) :
    withU24 (be24 n ++ r) k = k n r := by
  rw [be24_append, withU24_cons, u24_be24 n h]

/-- The block reader on a block of the length it asks for
    reads the block. -/
theorem withBytes_app {α : Type} {n : Nat} {v : List UInt8}
    (hv : v.length = n) (r : List UInt8)
    (k : List UInt8 → List UInt8 → Option α) :
    withBytes n (v ++ r) k = k v r := by
  unfold withBytes
  have ht : (v ++ r).take n = v := by
    rw [← hv]; exact List.take_left
  have hd : (v ++ r).drop n = r := by
    rw [← hv]; exact List.drop_left
  rw [ht, hd, ite_eq_left hv]

/-- A block read at exactly its own length gives the block
    and nothing after it. -/
theorem withBytes_self {α : Type} (bs : List UInt8)
    (k : List UInt8 → List UInt8 → Option α) :
    withBytes bs.length bs k = k bs [] := by
  have h := withBytes_app (v := bs) rfl [] k
  rw [List.append_nil] at h
  exact h

/-- A successful one byte read: the input was the byte and
    the rest, and the value fits a byte. -/
theorem withU8_inv {α : Type} {bs : List UInt8}
    {k : Nat → List UInt8 → Option α} {x : α}
    (h : withU8 bs k = some x) :
    ∃ n r, bs = n.toUInt8 :: r ∧ n < 256 ∧ k n r = some x := by
  cases bs with
  | nil =>
    have h0 : withU8 ([] : List UInt8) k = none := rfl
    rw [h0] at h
    cases h
  | cons b r =>
    rw [withU8_cons] at h
    exact ⟨b.toNat, r, by rw [toNat_toUInt8], toNat_lt b, h⟩

/-- A successful two byte read: the input was the printed
    value and the rest, and the value fits two bytes. -/
theorem withU16_inv {α : Type} {bs : List UInt8}
    {k : Nat → List UInt8 → Option α} {x : α}
    (h : withU16 bs k = some x) :
    ∃ n r, bs = be16 n ++ r ∧ n < 65536 ∧ k n r = some x := by
  cases bs with
  | nil =>
    have h0 : withU16 ([] : List UInt8) k = none := rfl
    rw [h0] at h
    cases h
  | cons a bs' =>
    cases bs' with
    | nil =>
      have h0 : withU16 [a] k = none := rfl
      rw [h0] at h
      cases h
    | cons b r =>
      rw [withU16_cons] at h
      refine ⟨u16 a b, r, ?_, ?_, h⟩
      · rw [be16_u16]
        rfl
      · have ha := toNat_lt a
        have hb := toNat_lt b
        simp only [u16]; omega

/-- A successful three byte read: the input was the printed
    value and the rest, and the value fits three bytes. -/
theorem withU24_inv {α : Type} {bs : List UInt8}
    {k : Nat → List UInt8 → Option α} {x : α}
    (h : withU24 bs k = some x) :
    ∃ n r, bs = be24 n ++ r ∧ n < 16777216 ∧ k n r = some x := by
  cases bs with
  | nil =>
    have h0 : withU24 ([] : List UInt8) k = none := rfl
    rw [h0] at h
    cases h
  | cons a bs' =>
    cases bs' with
    | nil =>
      have h0 : withU24 [a] k = none := rfl
      rw [h0] at h
      cases h
    | cons b bs'' =>
      cases bs'' with
      | nil =>
        have h0 : withU24 [a, b] k = none := rfl
        rw [h0] at h
        cases h
      | cons c r =>
        rw [withU24_cons] at h
        refine ⟨u24 a b c, r, ?_, ?_, h⟩
        · rw [be24_u24]
          rfl
        · have ha := toNat_lt a
          have hb := toNat_lt b
          have hc := toNat_lt c
          simp only [u24]; omega

/-- A successful block read: the block holds `n` bytes, and
    the input was the block and the rest. -/
theorem withBytes_inv {α : Type} {n : Nat} {bs : List UInt8}
    {k : List UInt8 → List UInt8 → Option α} {x : α}
    (h : withBytes n bs k = some x) :
    ∃ v r, v.length = n ∧ bs = v ++ r ∧ k v r = some x := by
  unfold withBytes at h
  by_cases hc : (bs.take n).length = n
  · rw [ite_eq_left hc] at h
    exact ⟨bs.take n, bs.drop n, hc,
      (List.take_append_drop n bs).symm, h⟩
  · rw [ite_eq_right hc] at h
    cases h

/-! ## Two byte value lists: the cipher suites and the
       supported versions -/

/-- The printed length of a two byte value list. -/
theorem printPairs_length (vs : List Nat) :
    (printPairs vs).length = 2 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [printPairs, be16, List.length_append,
      List.length_cons, List.length_nil, ih]
    omega

/-- Printed two byte values read back as the values. -/
theorem parsePairs_printPairs :
    ∀ {vs : List Nat}, (∀ v ∈ vs, v < 65536) →
    parsePairs (printPairs vs) = some vs := by
  intro vs
  induction vs with
  | nil => intro _; rfl
  | cons v vs ih =>
    intro hw
    have hv : v < 65536 := hw v (by simp)
    have htail : ∀ x ∈ vs, x < 65536 :=
      fun x hx => hw x (List.mem_cons_of_mem v hx)
    show parsePairs (be16 v ++ printPairs vs) = some (v :: vs)
    show parsePairs ((v / 256).toUInt8 :: v.toUInt8 ::
      printPairs vs) = some (v :: vs)
    show (parsePairs (printPairs vs)).map
        (fun vs' => u16 (v / 256).toUInt8 v.toUInt8 :: vs')
      = some (v :: vs)
    rw [ih htail, u16_be16 v hv]
    rfl

/-- Two byte values a successful read gives print back to
    the bytes they were read from, and each fits two bytes.
    The induction is on the byte count, two at a time, since
    the reader takes two bytes per value. -/
theorem parsePairs_inv_aux : ∀ (n : Nat) (bs : List UInt8)
    (vs : List Nat), bs.length = n → parsePairs bs = some vs →
    printPairs vs = bs ∧ ∀ v ∈ vs, v < 65536
  | 0, bs, vs, hlen, h => by
    cases bs with
    | nil =>
      have h1 : parsePairs ([] : List UInt8) = some [] := rfl
      rw [h1] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp⟩
    | cons a bs' => simp at hlen
  | 1, bs, vs, hlen, h => by
    cases bs with
    | nil => simp at hlen
    | cons a bs' =>
      cases bs' with
      | nil => simp [parsePairs] at h
      | cons b rest => simp at hlen
  | n + 2, bs, vs, hlen, h => by
    cases bs with
    | nil => simp at hlen
    | cons a bs' =>
      cases bs' with
      | nil => simp at hlen
      | cons b rest =>
        have hrest : rest.length = n := by
          simp only [List.length_cons] at hlen
          omega
        have hstep : parsePairs (a :: b :: rest)
            = (parsePairs rest).map
              (fun vs' => u16 a b :: vs') := rfl
        rw [hstep] at h
        obtain ⟨vs', hrec, hvs⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hprint, hlt⟩ :=
          parsePairs_inv_aux n rest vs' hrest hrec
        refine ⟨?_, ?_⟩
        · show printPairs vs = a :: b :: rest
          rw [← hvs]
          show printPairs (u16 a b :: vs') = a :: b :: rest
          simp only [printPairs, be16_u16, List.cons_append,
            List.nil_append, hprint]
        · rw [← hvs]
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · have ha := toNat_lt a
            have hb := toNat_lt b
            simp only [u16]; omega
          · exact hlt x hx

/-- Two byte values a successful read gives print back to
    the bytes they were read from, and each fits two
    bytes. -/
theorem parsePairs_inv {bs : List UInt8} {vs : List Nat}
    (h : parsePairs bs = some vs) :
    printPairs vs = bs ∧ ∀ v ∈ vs, v < 65536 :=
  parsePairs_inv_aux bs.length bs vs rfl h

/-- The count of values a successful two byte read gives,
    from the byte count it read. -/
theorem parsePairs_length {bs : List UInt8} {vs : List Nat}
    (h : parsePairs bs = some vs) :
    bs.length = 2 * vs.length := by
  have h1 := (parsePairs_inv h).1
  rw [← h1, printPairs_length]

/-! ## Server name entries -/

/-- The printed length of a server name entry list, one entry
    at a time. -/
theorem printNameEntries_length_cons (t : Nat)
    (bs : List UInt8) (es : List (Nat × List UInt8)) :
    (printNameEntries ((t, bs) :: es)).length
      = bs.length + 3 + (printNameEntries es).length := by
  simp only [printNameEntries, be16, List.length_append,
    List.length_cons, List.length_nil]
  omega

/-- One step of the server name entry reader, stated for
    rewriting. -/
theorem parseNameEntriesGo_step (f : Nat) (t : UInt8)
    (rest : List UInt8) :
    parseNameEntriesGo (f + 1) (t :: rest) =
      getU16 rest >>= fun (n, r1) =>
      if (r1.take n).length = n then
        parseNameEntriesGo f (r1.drop n) >>= fun es =>
        if t.toNat ∈ es.map Prod.fst then none
        else some ((t.toNat, r1.take n) :: es)
      else none := rfl

/-- Printed server name entries read back as the entries. -/
theorem parseNameEntriesGo_print :
    ∀ (es : List (Nat × List UInt8)) (fuel : Nat),
    (∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535) →
    List.Nodup (es.map Prod.fst) →
    (printNameEntries es).length < fuel →
    parseNameEntriesGo fuel (printNameEntries es) = some es := by
  intro es
  induction es with
  | nil =>
    intro fuel _ _ hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rfl
  | cons e es ih =>
    intro fuel hw hnodup hf
    obtain ⟨t, bs⟩ := e
    have hhead : t < 256 ∧ bs.length ≤ 65535 :=
      hw (t, bs) (by simp)
    have htail : ∀ x ∈ es, x.1 < 256 ∧ x.2.length ≤ 65535 :=
      fun x hx => hw x (List.mem_cons_of_mem (t, bs) hx)
    have hnodup' : List.Nodup (es.map Prod.fst) := by
      have h2 : ((t, bs) :: es).map Prod.fst
          = t :: es.map Prod.fst := rfl
      rw [h2] at hnodup
      exact (List.nodup_cons.mp hnodup).2
    have hnotin : t ∉ es.map Prod.fst := by
      have h2 : ((t, bs) :: es).map Prod.fst
          = t :: es.map Prod.fst := rfl
      rw [h2] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hf' : (printNameEntries es).length < f := by
      have hflen : (printNameEntries ((t, bs) :: es)).length
          = bs.length + 3 + (printNameEntries es).length :=
        printNameEntries_length_cons t bs es
      omega
    have ht : (t.toUInt8).toNat = t := by
      rw [toUInt8_toNat]
      exact Nat.mod_eq_of_lt hhead.1
    show parseNameEntriesGo (f + 1)
        ((t.toUInt8 :: (be16 bs.length ++ bs)) ++
          printNameEntries es)
      = some ((t, bs) :: es)
    have hform : (t.toUInt8 :: (be16 bs.length ++ bs)) ++
          printNameEntries es
        = t.toUInt8 :: (bs.length / 256).toUInt8 ::
          bs.length.toUInt8 :: (bs ++ printNameEntries es) := by
      simp only [be16, List.cons_append, List.nil_append]
    rw [hform, parseNameEntriesGo_step]
    show (getU16 ((bs.length / 256).toUInt8 ::
        bs.length.toUInt8 :: (bs ++ printNameEntries es)) >>=
      fun (n, r1) =>
      if (r1.take n).length = n then
        parseNameEntriesGo f (r1.drop n) >>= fun es' =>
        if (t.toUInt8).toNat ∈ es'.map Prod.fst then none
        else some (((t.toUInt8).toNat, r1.take n) :: es')
      else none) = some ((t, bs) :: es)
    have hg : getU16 ((bs.length / 256).toUInt8 ::
        bs.length.toUInt8 :: (bs ++ printNameEntries es))
        = some (bs.length, bs ++ printNameEntries es) := by
      show some (u16 (bs.length / 256).toUInt8
        bs.length.toUInt8, bs ++ printNameEntries es) = _
      rw [u16_be16 bs.length (by omega)]
    rw [hg]
    simp only []
    show (if ((bs ++ printNameEntries es).take bs.length).length
        = bs.length then
      parseNameEntriesGo f ((bs ++ printNameEntries es).drop
        bs.length) >>= fun es' =>
      if (t.toUInt8).toNat ∈ es'.map Prod.fst then none
      else some (((t.toUInt8).toNat,
        (bs ++ printNameEntries es).take bs.length) :: es')
      else none) = some ((t, bs) :: es)
    rw [List.take_left, List.drop_left, ite_eq_left rfl,
      ih f htail hnodup' hf']
    show (if (t.toUInt8).toNat ∈ es.map Prod.fst then none
      else some (((t.toUInt8).toNat, bs) :: es))
      = some ((t, bs) :: es)
    rw [ite_eq_right (by rw [ht]; exact hnotin), ht]

/-- Printed server name entries read back, at the top
    level. -/
theorem parseNameEntries_print {es : List (Nat × List UInt8)}
    (hw : ∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535)
    (hn : List.Nodup (es.map Prod.fst)) :
    parseNameEntries (printNameEntries es) = some es := by
  show parseNameEntriesGo ((printNameEntries es).length + 1)
    (printNameEntries es) = some es
  exact parseNameEntriesGo_print es _ hw hn (Nat.lt_succ_self _)

/-- Server name entries a successful read gives print back
    to the bytes they were read from, each name type fits
    one byte, each name fits two length bytes, and no name
    type stands twice. -/
theorem parseNameEntriesGo_inv :
    ∀ (f : Nat) (bs : List UInt8)
      (es : List (Nat × List UInt8)),
    parseNameEntriesGo f bs = some es →
    printNameEntries es = bs ∧
    (∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535) ∧
    List.Nodup (es.map Prod.fst) := by
  intro f
  induction f with
  | zero =>
    intro bs es h
    simp [parseNameEntriesGo] at h
  | succ f ih =>
    intro bs es h
    cases bs with
    | nil =>
      have h1 : parseNameEntriesGo (f + 1) ([] : List UInt8)
          = some [] := rfl
      rw [h1] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp, by simp⟩
    | cons t rest =>
      rw [parseNameEntriesGo_step] at h
      obtain ⟨⟨n, r1⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
      change (if (r1.take n).length = n then
          parseNameEntriesGo f (r1.drop n) >>= fun es' =>
          if t.toNat ∈ es'.map Prod.fst then none
          else some ((t.toNat, r1.take n) :: es')
        else none) = some es at h
      obtain ⟨hrest, hnlt⟩ := getU16_inv hn
      by_cases hc : (r1.take n).length = n
      · rw [ite_eq_left hc] at h
        obtain ⟨es', hrec, h⟩ :=
          Option.bind_eq_some_iff.mp h
        obtain ⟨hprint, hprops, hnodup⟩ := ih _ _ hrec
        by_cases hd : t.toNat ∈ es'.map Prod.fst
        · rw [ite_eq_left hd] at h
          simp at h
        · rw [ite_eq_right hd] at h
          simp only [Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_, ?_⟩
          · show printNameEntries ((t.toNat, r1.take n) :: es')
              = t :: rest
            have htake : (r1.take n).length = n := hc
            show ((t.toNat.toUInt8 ::
                (be16 (r1.take n).length ++ r1.take n)) ++
              printNameEntries es') = t :: rest
            rw [htake, hprint, toNat_toUInt8, hrest]
            show (t :: ((be16 n ++ r1.take n) ++ r1.drop n))
              = t :: (be16 n ++ r1)
            rw [List.append_assoc, List.take_append_drop]
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact ⟨toNat_lt t, by rw [hc]; omega⟩
            · exact hprops x hx
          · have h2 : ((t.toNat, r1.take n) :: es').map Prod.fst
                = t.toNat :: es'.map Prod.fst := rfl
            rw [h2]
            exact List.nodup_cons.mpr ⟨hd, hnodup⟩
      · rw [ite_eq_right hc] at h
        simp at h

/-- Server name entries a successful read gives print back,
    at the top level. -/
theorem parseNameEntries_inv {bs : List UInt8}
    {es : List (Nat × List UInt8)}
    (h : parseNameEntries bs = some es) :
    printNameEntries es = bs ∧
    (∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535) ∧
    List.Nodup (es.map Prod.fst) :=
  parseNameEntriesGo_inv _ _ _ h

/-- The server name value check holds for a list the printer
    can write: nonempty, and every host_name entry
    nonempty. -/
theorem validNames_of {es : List (Nat × List UInt8)}
    (hne : es ≠ [])
    (hhost : ∀ e ∈ es, e.1 = 0 → e.2 ≠ []) :
    validNames es = true := by
  unfold validNames
  rw [Bool.and_eq_true]
  constructor
  · cases es with
    | nil => exact absurd rfl hne
    | cons e es' => rfl
  · rw [List.all_eq_true]
    intro e he
    simp only [decide_eq_true_eq]
    by_cases h0 : e.1 = 0
    · exact Or.inr (hhost e he h0)
    · exact Or.inl h0

/-- A server name list that passes the value check is
    nonempty, and its host_name entries are nonempty. -/
theorem validNames_true {es : List (Nat × List UInt8)}
    (h : validNames es = true) :
    es ≠ [] ∧ ∀ e ∈ es, e.1 = 0 → e.2 ≠ [] := by
  have hne : es ≠ [] := by
    cases es with
    | nil => simp [validNames] at h
    | cons e es' => simp
  have hall : ∀ e ∈ es, e.1 ≠ 0 ∨ e.2 ≠ [] := by
    have h2 : es.all
        (fun e => decide (e.1 ≠ 0 ∨ e.2 ≠ [])) = true := by
      have h' : (!es.isEmpty &&
          es.all (fun e => decide (e.1 ≠ 0 ∨ e.2 ≠ [])))
          = true := h
      rw [Bool.and_eq_true] at h'
      exact h'.2
    rw [List.all_eq_true] at h2
    intro e he
    have h3 := h2 e he
    simpa only [decide_eq_true_eq] using h3
  exact ⟨hne, fun e he h0 =>
    (hall e he).elim (fun hn => absurd h0 hn) id⟩

/-! ## The server_name value -/

/-- A printed server_name value reads back as the
    extension. -/
theorem parseSNI_print {es : List (Nat × List UInt8)}
    (hne : es ≠ [])
    (hw : ∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535 ∧
      (e.1 = 0 → e.2 ≠ []))
    (hnodup : List.Nodup (es.map Prod.fst))
    (hlen : (printNameEntries es).length ≤ 65533) :
    parseSNI (printExtValue (.serverName es))
      = some (.serverName es) := by
  have hw' : ∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535 :=
    fun e he => ⟨(hw e he).1, (hw e he).2.1⟩
  show parseSNI (be16 (printNameEntries es).length ++
      printNameEntries es) = some (Extension.serverName es)
  unfold parseSNI
  rw [getU16_be16 _ (by omega)]
  simp only []
  show (if (printNameEntries es).length
        = (printNameEntries es).length then
      parseNameEntries (printNameEntries es) >>= fun es' =>
      if validNames es' then some (Extension.serverName es') else none
    else none) = some (Extension.serverName es)
  rw [ite_eq_left rfl, parseNameEntries_print hw' hnodup]
  show (if validNames es then some (Extension.serverName es)
    else none) = some (Extension.serverName es)
  rw [ite_eq_left (validNames_of hne (fun e he => (hw e he).2.2))]

/-- A server_name value a successful read gives is the
    printed form of the extension it gives, and the
    extension is well formed. The value length bound comes
    from the caller: an extension value fits two length
    bytes. -/
theorem parseSNI_inv {v : List UInt8} {e : Extension}
    (hv : v.length ≤ 65535) (h : parseSNI v = some e) :
    ∃ es, e = .serverName es ∧
      printExtValue (.serverName es) = v ∧
      ExtWF (.serverName es) := by
  unfold parseSNI at h
  obtain ⟨⟨n, rest⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
  change (if rest.length = n then
      parseNameEntries rest >>= fun es =>
      if validNames es then some (.serverName es) else none
    else none) = some e at h
  obtain ⟨hrest, hnlt⟩ := getU16_inv hn
  by_cases hc : rest.length = n
  · rw [ite_eq_left hc] at h
    obtain ⟨es, hrec, h⟩ := Option.bind_eq_some_iff.mp h
    by_cases hval : validNames es = true
    · rw [ite_eq_left hval] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hprint, hprops, hnodup⟩ := parseNameEntries_inv hrec
      obtain ⟨hne, hhost⟩ := validNames_true hval
      refine ⟨es, rfl, ?_, ?_⟩
      · show be16 (printNameEntries es).length ++
          printNameEntries es = v
        rw [hprint, hc, hrest]
      · exact ⟨hne, fun x hx =>
          ⟨(hprops x hx).1, (hprops x hx).2, hhost x hx⟩,
          hnodup, by
          have h2 : (printNameEntries es).length = rest.length := by
            rw [hprint]
          have hvlen : v.length = rest.length + 2 := by
            rw [hrest]; simp [be16]
          omega⟩
    · rw [ite_eq_right hval] at h
      simp at h
  · rw [ite_eq_right hc] at h
    simp at h

/-! ## ALPN protocol names -/

/-- The printed length of an ALPN name list, one name at a
    time. -/
theorem printAlpnNames_length_cons (n : List UInt8)
    (ns : List (List UInt8)) :
    (printAlpnNames (n :: ns)).length
      = n.length + 1 + (printAlpnNames ns).length := by
  simp only [printAlpnNames, List.length_append,
    List.length_cons]

/-- One step of the ALPN name reader, stated for
    rewriting. -/
theorem parseAlpnGo_step (f : Nat) (len : UInt8)
    (rest : List UInt8) :
    parseAlpnGo (f + 1) (len :: rest) =
      if len.toNat = 0 then none
      else if (rest.take len.toNat).length = len.toNat then
        (parseAlpnGo f (rest.drop len.toNat)).map
          (fun ns => (rest.take len.toNat) :: ns)
      else none := rfl

/-- Printed ALPN names read back as the names. -/
theorem parseAlpnGo_print :
    ∀ (ns : List (List UInt8)) (fuel : Nat),
    (∀ n ∈ ns, n ≠ [] ∧ n.length ≤ 255) →
    (printAlpnNames ns).length < fuel →
    parseAlpnGo fuel (printAlpnNames ns) = some ns := by
  intro ns
  induction ns with
  | nil =>
    intro fuel _ hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rfl
  | cons n ns ih =>
    intro fuel hw hf
    have hhead : n ≠ [] ∧ n.length ≤ 255 := hw n (by simp)
    have htail : ∀ x ∈ ns, x ≠ [] ∧ x.length ≤ 255 :=
      fun x hx => hw x (List.mem_cons_of_mem n hx)
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hf' : (printAlpnNames ns).length < f := by
      have hflen : (printAlpnNames (n :: ns)).length
          = n.length + 1 + (printAlpnNames ns).length :=
        printAlpnNames_length_cons n ns
      omega
    have hlen : (n.length.toUInt8).toNat = n.length := by
      rw [toUInt8_toNat]
      exact Nat.mod_eq_of_lt (by omega)
    show parseAlpnGo (f + 1)
        ((n.length.toUInt8 :: n) ++ printAlpnNames ns)
      = some (n :: ns)
    have hform : (n.length.toUInt8 :: n) ++ printAlpnNames ns
        = n.length.toUInt8 :: (n ++ printAlpnNames ns) := by
      simp only [List.cons_append]
    rw [hform, parseAlpnGo_step, hlen,
      ite_eq_right (by
        intro hcon
        cases n with
        | nil => exact hhead.1 rfl
        | cons b bs => simp at hcon),
      List.take_left, List.drop_left, ite_eq_left rfl, ih f htail hf']
    rfl

/-- Printed ALPN names read back, at the top level. -/
theorem parseAlpnNames_print {ns : List (List UInt8)}
    (hw : ∀ n ∈ ns, n ≠ [] ∧ n.length ≤ 255) :
    parseAlpnNames (printAlpnNames ns) = some ns := by
  show parseAlpnGo ((printAlpnNames ns).length + 1)
    (printAlpnNames ns) = some ns
  exact parseAlpnGo_print ns _ hw (Nat.lt_succ_self _)

/-- ALPN names a successful read gives print back to the
    bytes they were read from, and each name is nonempty
    and fits one length byte. -/
theorem parseAlpnGo_inv :
    ∀ (f : Nat) (bs : List UInt8) (ns : List (List UInt8)),
    parseAlpnGo f bs = some ns →
    printAlpnNames ns = bs ∧
    ∀ n ∈ ns, n ≠ [] ∧ n.length ≤ 255 := by
  intro f
  induction f with
  | zero =>
    intro bs ns h
    simp [parseAlpnGo] at h
  | succ f ih =>
    intro bs ns h
    cases bs with
    | nil =>
      have h1 : parseAlpnGo (f + 1) ([] : List UInt8)
          = some [] := rfl
      rw [h1] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp⟩
    | cons len rest =>
      rw [parseAlpnGo_step] at h
      by_cases h0 : len.toNat = 0
      · rw [ite_eq_left h0] at h
        simp at h
      · rw [ite_eq_right h0] at h
        by_cases hc : (rest.take len.toNat).length = len.toNat
        · rw [ite_eq_left hc] at h
          obtain ⟨ns', hrec, hns⟩ := Option.map_eq_some_iff.mp h
          obtain ⟨hprint, hprops⟩ := ih _ _ hrec
          refine ⟨?_, ?_⟩
          · show printAlpnNames ns = len :: rest
            rw [← hns]
            show printAlpnNames ((rest.take len.toNat) :: ns')
              = len :: rest
            have htake : (rest.take len.toNat).length
                = len.toNat := hc
            show ((rest.take len.toNat).length.toUInt8 ::
                rest.take len.toNat) ++ printAlpnNames ns'
              = len :: rest
            rw [htake, toNat_toUInt8, hprint]
            show len :: (rest.take len.toNat ++ rest.drop len.toNat)
              = len :: rest
            rw [List.take_append_drop]
          · intro x hx
            rw [← hns] at hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · refine ⟨?_, by rw [hc]; have h := toNat_lt len; omega⟩
              intro hcon
              rw [hcon] at hc
              simp at hc
              omega
            · exact hprops x hx
        · rw [ite_eq_right hc] at h
          simp at h

/-- ALPN names a successful read gives print back, at the
    top level. -/
theorem parseAlpnNames_inv {bs : List UInt8}
    {ns : List (List UInt8)}
    (h : parseAlpnNames bs = some ns) :
    printAlpnNames ns = bs ∧
    ∀ n ∈ ns, n ≠ [] ∧ n.length ≤ 255 :=
  parseAlpnGo_inv _ _ _ h

/-- A printed ALPN value reads back as the extension. -/
theorem parseALPN_print {ns : List (List UInt8)}
    (hne : ns ≠ [])
    (hw : ∀ n ∈ ns, n ≠ [] ∧ n.length ≤ 255)
    (hlen : (printAlpnNames ns).length ≤ 65533) :
    parseALPN (printExtValue (.alpn ns)) = some (.alpn ns) := by
  show parseALPN (be16 (printAlpnNames ns).length ++
      printAlpnNames ns) = some (Extension.alpn ns)
  unfold parseALPN
  rw [getU16_be16 _ (by omega)]
  simp only []
  show (if (printAlpnNames ns).length
        = (printAlpnNames ns).length then
      parseAlpnNames (printAlpnNames ns) >>= fun ns' =>
      if ns'.isEmpty then none else some (Extension.alpn ns')
    else none) = some (Extension.alpn ns)
  rw [ite_eq_left rfl, parseAlpnNames_print hw]
  show (if ns.isEmpty then none else some (Extension.alpn ns))
    = some (Extension.alpn ns)
  rw [ite_eq_right (by
    cases ns with
    | nil => exact absurd rfl hne
    | cons n ns' => simp)]

/-- An ALPN value a successful read gives is the printed
    form of the extension it gives, and the extension is
    well formed. -/
theorem parseALPN_inv {v : List UInt8} {e : Extension}
    (hv : v.length ≤ 65535) (h : parseALPN v = some e) :
    ∃ ns, e = .alpn ns ∧
      printExtValue (.alpn ns) = v ∧ ExtWF (.alpn ns) := by
  unfold parseALPN at h
  obtain ⟨⟨n, rest⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
  change (if rest.length = n then
      parseAlpnNames rest >>= fun ns =>
      if ns.isEmpty then none else some (.alpn ns)
    else none) = some e at h
  obtain ⟨hrest, hnlt⟩ := getU16_inv hn
  by_cases hc : rest.length = n
  · rw [ite_eq_left hc] at h
    obtain ⟨ns, hrec, h⟩ := Option.bind_eq_some_iff.mp h
    by_cases hemp : ns.isEmpty = false
    · rw [ite_eq_right (by
        intro hcon
        rw [hcon] at hemp
        simp at hemp)] at h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hprint, hprops⟩ := parseAlpnNames_inv hrec
      have hne : ns ≠ [] := by
        cases ns with
        | nil => simp at hemp
        | cons n' ns' => simp
      refine ⟨ns, rfl, ?_, ?_⟩
      · show be16 (printAlpnNames ns).length ++
          printAlpnNames ns = v
        rw [hprint, hc, hrest]
      · exact ⟨hne, hprops, by
          have h2 : (printAlpnNames ns).length = rest.length := by
            rw [hprint]
          have hvlen : v.length = rest.length + 2 := by
            rw [hrest]; simp [be16]
          omega⟩
    · have hemp2 : ns.isEmpty = true := by
        cases h' : ns.isEmpty with
        | true => rfl
        | false => exact absurd h' hemp
      rw [ite_eq_left hemp2] at h
      simp at h
  · rw [ite_eq_right hc] at h
    simp at h

/-! ## The supported_versions value -/

/-- A printed supported_versions value reads back as the
    extension. -/
theorem parseSV_print {vs : List Nat}
    (hne : vs ≠ []) (hw : ∀ v ∈ vs, v < 65536)
    (hlen : vs.length ≤ 127) :
    parseSV (printExtValue (.supportedVersions vs))
      = some (.supportedVersions vs) := by
  show parseSV ((printPairs vs).length.toUInt8 ::
      printPairs vs) = some (.supportedVersions vs)
  have hlen2 : ((printPairs vs).length.toUInt8).toNat
      = (printPairs vs).length := by
    rw [toUInt8_toNat, printPairs_length]
    have : 2 * vs.length < 256 := by omega
    exact Nat.mod_eq_of_lt this
  have hcond : (printPairs vs).length
        = ((printPairs vs).length.toUInt8).toNat ∧
      ((printPairs vs).length.toUInt8).toNat % 2 = 0 ∧
      2 ≤ ((printPairs vs).length.toUInt8).toNat := by
    rw [hlen2, printPairs_length]
    refine ⟨rfl, by omega, by
      cases vs with
      | nil => exact absurd rfl hne
      | cons v vs' => simp; omega⟩
  show (if (printPairs vs).length
        = ((printPairs vs).length.toUInt8).toNat ∧
      ((printPairs vs).length.toUInt8).toNat % 2 = 0 ∧
      2 ≤ ((printPairs vs).length.toUInt8).toNat then
      parsePairs (printPairs vs) >>= fun vs' =>
        some (Extension.supportedVersions vs')
    else none) = some (Extension.supportedVersions vs)
  rw [ite_eq_left hcond, parsePairs_printPairs hw]
  rfl

/-- A supported_versions value a successful read gives is
    the printed form of the extension it gives, and the
    extension is well formed. -/
theorem parseSV_inv {v : List UInt8} {e : Extension}
    (h : parseSV v = some e) :
    ∃ vs, e = .supportedVersions vs ∧
      printExtValue (.supportedVersions vs) = v ∧
      ExtWF (.supportedVersions vs) := by
  cases v with
  | nil => simp [parseSV] at h
  | cons n rest =>
    have hstep : parseSV (n :: rest) =
        if rest.length = n.toNat ∧ n.toNat % 2 = 0 ∧
            2 ≤ n.toNat then
          parsePairs rest >>= fun vs =>
            some (.supportedVersions vs)
        else none := rfl
    rw [hstep] at h
    by_cases hc : rest.length = n.toNat ∧ n.toNat % 2 = 0 ∧
        2 ≤ n.toNat
    · rw [ite_eq_left hc] at h
      obtain ⟨vs, hrec, h⟩ := Option.bind_eq_some_iff.mp h
      simp only [Option.some.injEq] at h
      subst h
      obtain ⟨hprint, hlt⟩ := parsePairs_inv hrec
      have hlen := parsePairs_length hrec
      refine ⟨vs, rfl, ?_, ?_⟩
      · show (printPairs vs).length.toUInt8 :: printPairs vs
          = n :: rest
        rw [hprint]
        have hbyte : (rest.length).toUInt8 = n := by
          apply UInt8.toNat_inj.mp
          show ((rest.length).toUInt8).toNat = n.toNat
          rw [toUInt8_toNat, hc.1]
          exact Nat.mod_eq_of_lt (toNat_lt n)
        rw [hbyte]
      · refine ⟨?_, hlt, by
          have h1 := hc.1
          have h2 := toNat_lt n
          omega⟩
        cases vs with
        | nil =>
          intro hcon
          have h5 := (parsePairs_inv hrec).1
          simp only [printPairs] at h5
          have hz : rest.length = 0 := by
            rw [← h5]
            simp
          have h1 := hc.1
          have h3 := hc.2.2
          omega
        | cons v' vs' => intro hcon; cases hcon
    · rw [ite_eq_right hc] at h
      simp at h

/-! ## Key share entries -/

/-- The printed length of a key share entry list, one entry
    at a time. -/
theorem printShares_length_cons (g : Nat) (k : List UInt8)
    (ss : List (Nat × List UInt8)) :
    (printShares ((g, k) :: ss)).length
      = k.length + 4 + (printShares ss).length := by
  show ((be16 g ++ (be16 k.length ++ k)) ++
    printShares ss).length = _
  rw [List.length_append, List.length_append,
    List.length_append]
  simp only [be16, List.length_cons, List.length_nil]
  omega

/-- One step of the key share entry reader, stated for
    rewriting. -/
theorem parseSharesGo_step (f : Nat) (x y : UInt8)
    (rest : List UInt8) :
    parseSharesGo (f + 1) (x :: y :: rest) =
      getU16 (x :: y :: rest) >>= fun (g, r1) =>
      getU16 r1 >>= fun (n, r2) =>
      if n = 0 then none
      else if (r2.take n).length = n then
        parseSharesGo f (r2.drop n) >>= fun ss =>
        if g ∈ ss.map Prod.fst then none
        else some ((g, r2.take n) :: ss)
      else none := rfl

/-- Printed key share entries read back as the entries. -/
theorem parseSharesGo_print :
    ∀ (ss : List (Nat × List UInt8)) (fuel : Nat),
    (∀ s ∈ ss, s.1 < 65536 ∧ s.2 ≠ [] ∧ s.2.length ≤ 65535) →
    List.Nodup (ss.map Prod.fst) →
    (printShares ss).length < fuel →
    parseSharesGo fuel (printShares ss) = some ss := by
  intro ss
  induction ss with
  | nil =>
    intro fuel _ _ hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rfl
  | cons s ss ih =>
    intro fuel hw hnodup hf
    obtain ⟨g, k⟩ := s
    have hhead : g < 65536 ∧ k ≠ [] ∧ k.length ≤ 65535 :=
      hw (g, k) (by simp)
    have htail : ∀ x ∈ ss, x.1 < 65536 ∧ x.2 ≠ [] ∧
        x.2.length ≤ 65535 :=
      fun x hx => hw x (List.mem_cons_of_mem (g, k) hx)
    have hnodup' : List.Nodup (ss.map Prod.fst) := by
      have h2 : ((g, k) :: ss).map Prod.fst
          = g :: ss.map Prod.fst := rfl
      rw [h2] at hnodup
      exact (List.nodup_cons.mp hnodup).2
    have hnotin : g ∉ ss.map Prod.fst := by
      have h2 : ((g, k) :: ss).map Prod.fst
          = g :: ss.map Prod.fst := rfl
      rw [h2] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hf' : (printShares ss).length < f := by
      have hflen : (printShares ((g, k) :: ss)).length
          = k.length + 4 + (printShares ss).length :=
        printShares_length_cons g k ss
      omega
    show parseSharesGo (f + 1)
        ((be16 g ++ (be16 k.length ++ k)) ++ printShares ss)
      = some ((g, k) :: ss)
    have hform : (be16 g ++ (be16 k.length ++ k)) ++
          printShares ss
        = be16 g ++ (be16 k.length ++ (k ++ printShares ss)) := by
      simp only [← List.append_assoc]
    rw [hform]
    show parseSharesGo (f + 1) ((g / 256).toUInt8 ::
        g.toUInt8 :: ((k.length / 256).toUInt8 ::
        k.length.toUInt8 :: (k ++ printShares ss)))
      = some ((g, k) :: ss)
    rw [parseSharesGo_step]
    have hg : getU16 ((g / 256).toUInt8 :: g.toUInt8 ::
        ((k.length / 256).toUInt8 :: k.length.toUInt8 ::
          (k ++ printShares ss)))
        = some (g, (k.length / 256).toUInt8 ::
            k.length.toUInt8 :: (k ++ printShares ss)) := by
      show some (u16 (g / 256).toUInt8 g.toUInt8, _) = _
      rw [u16_be16 g hhead.1]
    rw [hg]
    simp only []
    show (getU16 ((k.length / 256).toUInt8 ::
        k.length.toUInt8 :: (k ++ printShares ss)) >>=
        fun (n, r2) =>
        if n = 0 then none
        else if (r2.take n).length = n then
          parseSharesGo f (r2.drop n) >>= fun ss' =>
          if g ∈ ss'.map Prod.fst then none
          else some ((g, r2.take n) :: ss')
        else none) = some ((g, k) :: ss)
    have hk : getU16 ((k.length / 256).toUInt8 ::
        k.length.toUInt8 :: (k ++ printShares ss))
        = some (k.length, k ++ printShares ss) := by
      show some (u16 (k.length / 256).toUInt8
        k.length.toUInt8, _) = _
      rw [u16_be16 _ (by omega)]
    rw [hk]
    simp only []
    show (if k.length = 0 then none
        else if ((k ++ printShares ss).take k.length).length
            = k.length then
          parseSharesGo f ((k ++ printShares ss).drop
            k.length) >>= fun ss' =>
          if g ∈ ss'.map Prod.fst then none
          else some ((g, (k ++ printShares ss).take
            k.length) :: ss')
        else none) = some ((g, k) :: ss)
    rw [ite_eq_right (by
        intro hcon
        cases k with
        | nil => exact hhead.2.1 rfl
        | cons b bs => simp at hcon),
      List.take_left, List.drop_left, ite_eq_left rfl,
      ih f htail hnodup' hf']
    show (if g ∈ ss.map Prod.fst then none
      else some ((g, k) :: ss)) = some ((g, k) :: ss)
    rw [ite_eq_right hnotin]

/-- Printed key share entries read back, at the top
    level. -/
theorem parseShares_print {ss : List (Nat × List UInt8)}
    (hw : ∀ s ∈ ss, s.1 < 65536 ∧ s.2 ≠ [] ∧
      s.2.length ≤ 65535)
    (hn : List.Nodup (ss.map Prod.fst)) :
    parseShares (printShares ss) = some ss := by
  show parseSharesGo ((printShares ss).length + 1)
    (printShares ss) = some ss
  exact parseSharesGo_print ss _ hw hn (Nat.lt_succ_self _)

/-- Key share entries a successful read gives print back to
    the bytes they were read from, each group fits two
    bytes, each key is nonempty and fits two length bytes,
    and no group stands twice. -/
theorem parseSharesGo_inv :
    ∀ (f : Nat) (bs : List UInt8)
      (ss : List (Nat × List UInt8)),
    parseSharesGo f bs = some ss →
    printShares ss = bs ∧
    (∀ s ∈ ss, s.1 < 65536 ∧ s.2 ≠ [] ∧
      s.2.length ≤ 65535) ∧
    List.Nodup (ss.map Prod.fst) := by
  intro f
  induction f with
  | zero =>
    intro bs ss h
    simp [parseSharesGo] at h
  | succ f ih =>
    intro bs ss h
    cases bs with
    | nil =>
      have h1 : parseSharesGo (f + 1) ([] : List UInt8)
          = some [] := rfl
      rw [h1] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp, by simp⟩
    | cons b1 rest =>
      cases rest with
      | nil => simp [parseSharesGo, getU16] at h
      | cons b2 rest =>
        rw [parseSharesGo_step] at h
        obtain ⟨⟨g, r1⟩, hg, h⟩ := Option.bind_eq_some_iff.mp h
        change (getU16 r1 >>= fun (n, r2) =>
          if n = 0 then none
          else if (r2.take n).length = n then
            parseSharesGo f (r2.drop n) >>= fun ss =>
            if g ∈ ss.map Prod.fst then none
            else some ((g, r2.take n) :: ss)
          else none) = some ss at h
        obtain ⟨⟨n, r2⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
        change (if n = 0 then none
          else if (r2.take n).length = n then
            parseSharesGo f (r2.drop n) >>= fun ss' =>
            if g ∈ ss'.map Prod.fst then none
            else some ((g, r2.take n) :: ss')
          else none) = some ss at h
        obtain ⟨hbs, hglt⟩ := getU16_inv hg
        obtain ⟨hr1, hnlt⟩ := getU16_inv hn
        by_cases h0 : n = 0
        · rw [ite_eq_left h0] at h
          simp at h
        · rw [ite_eq_right h0] at h
          by_cases hc : (r2.take n).length = n
          · rw [ite_eq_left hc] at h
            obtain ⟨ss', hrec, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨hprint, hprops, hnodup⟩ := ih _ _ hrec
            by_cases hd : g ∈ ss'.map Prod.fst
            · rw [ite_eq_left hd] at h
              simp at h
            · rw [ite_eq_right hd] at h
              simp only [Option.some.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              refine ⟨?_, ?_, ?_⟩
              · have htake : (r2.take n).length = n := hc
                show ((be16 g ++ (be16 (r2.take n).length ++
                    r2.take n)) ++ printShares ss')
                  = b1 :: b2 :: rest
                rw [htake, hprint, hbs, hr1]
                simp only [List.append_assoc]
                rw [List.take_append_drop]
              · intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · exact ⟨hglt, by
                    intro hcon
                    change r2.take n = [] at hcon
                    rw [hcon] at hc
                    exact h0 hc.symm, by
                    change (r2.take n).length ≤ 65535
                    rw [hc]; omega⟩
                · exact hprops x hx
              · have h2 : ((g, r2.take n) :: ss').map Prod.fst
                    = g :: ss'.map Prod.fst := rfl
                rw [h2]
                exact List.nodup_cons.mpr ⟨hd, hnodup⟩
          · rw [ite_eq_right hc] at h
            simp at h

/-- Key share entries a successful read gives print back,
    at the top level. -/
theorem parseShares_inv {bs : List UInt8}
    {ss : List (Nat × List UInt8)}
    (h : parseShares bs = some ss) :
    printShares ss = bs ∧
    (∀ s ∈ ss, s.1 < 65536 ∧ s.2 ≠ [] ∧
      s.2.length ≤ 65535) ∧
    List.Nodup (ss.map Prod.fst) :=
  parseSharesGo_inv _ _ _ h

/-- A printed key_share value reads back as the
    extension. The list may be empty. -/
theorem parseKS_print {ss : List (Nat × List UInt8)}
    (hw : ∀ s ∈ ss, s.1 < 65536 ∧ s.2 ≠ [] ∧
      s.2.length ≤ 65535)
    (hnodup : List.Nodup (ss.map Prod.fst))
    (hlen : (printShares ss).length ≤ 65533) :
    parseKS (printExtValue (.keyShare ss))
      = some (.keyShare ss) := by
  show parseKS (be16 (printShares ss).length ++
      printShares ss) = some (Extension.keyShare ss)
  unfold parseKS
  rw [getU16_be16 _ (by omega)]
  simp only []
  show (if (printShares ss).length
        = (printShares ss).length then
      parseShares (printShares ss) >>= fun ss' =>
        some (Extension.keyShare ss')
    else none) = some (Extension.keyShare ss)
  rw [ite_eq_left rfl, parseShares_print hw hnodup]
  rfl

/-- A key_share value a successful read gives is the
    printed form of the extension it gives, and the
    extension is well formed. -/
theorem parseKS_inv {v : List UInt8} {e : Extension}
    (hv : v.length ≤ 65535) (h : parseKS v = some e) :
    ∃ ss, e = .keyShare ss ∧
      printExtValue (.keyShare ss) = v ∧
      ExtWF (.keyShare ss) := by
  unfold parseKS at h
  obtain ⟨⟨n, rest⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
  change (if rest.length = n then
      parseShares rest >>= fun ss => some (.keyShare ss)
    else none) = some e at h
  obtain ⟨hrest, hnlt⟩ := getU16_inv hn
  by_cases hc : rest.length = n
  · rw [ite_eq_left hc] at h
    obtain ⟨ss, hrec, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨hprint, hprops, hnodup⟩ := parseShares_inv hrec
    refine ⟨ss, rfl, ?_, ?_⟩
    · show be16 (printShares ss).length ++
        printShares ss = v
      rw [hprint, hc, hrest]
    · exact ⟨hprops, hnodup, by
        have h2 : (printShares ss).length = rest.length := by
          rw [hprint]
        have hvlen : v.length = rest.length + 2 := by
          rw [hrest]; simp [be16]
        omega⟩
  · rw [ite_eq_right hc] at h
    simp at h

/-! ## Extension values, dispatched by type -/

/-- The type of a well formed extension fits two bytes. -/
theorem extType_lt {e : Extension} (h : ExtWF e) :
    extType e < 65536 := by
  rcases e with ⟨es⟩ | ⟨ns⟩ | ⟨vs⟩ | ⟨ss⟩ | ⟨t, v⟩
  · show (0 : Nat) < 65536; omega
  · show (16 : Nat) < 65536; omega
  · show (43 : Nat) < 65536; omega
  · show (51 : Nat) < 65536; omega
  · have h' : ¬ (t = 0 ∨ t = 16 ∨ t = 43 ∨ t = 51) ∧
        t < 65536 ∧ v.length ≤ 65535 := h
    exact h'.2.1

/-- The printed value of a well formed extension fits two
    length bytes. -/
theorem printExtValue_length_le {e : Extension}
    (h : ExtWF e) : (printExtValue e).length ≤ 65535 := by
  rcases e with ⟨es⟩ | ⟨ns⟩ | ⟨vs⟩ | ⟨ss⟩ | ⟨t, v⟩
  ·
    have h' : es ≠ [] ∧
        (∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535 ∧
          (e.1 = 0 → e.2 ≠ [])) ∧
        List.Nodup (es.map Prod.fst) ∧
        (printNameEntries es).length ≤ 65533 := h
    show (be16 (printNameEntries es).length ++
      printNameEntries es).length ≤ 65535
    rw [List.length_append]
    simp [be16]
    omega
  · have h' : ns ≠ [] ∧
        (∀ n ∈ ns, n ≠ [] ∧ n.length ≤ 255) ∧
        (printAlpnNames ns).length ≤ 65533 := h
    show (be16 (printAlpnNames ns).length ++
      printAlpnNames ns).length ≤ 65535
    rw [List.length_append]
    simp [be16]
    omega
  · have h' : vs ≠ [] ∧ (∀ v ∈ vs, v < 65536) ∧
        vs.length ≤ 127 := h
    show ((printPairs vs).length.toUInt8 ::
      printPairs vs).length ≤ 65535
    rw [List.length_cons, printPairs_length]
    omega
  · have h' : (∀ s ∈ ss, s.1 < 65536 ∧ s.2 ≠ [] ∧
          s.2.length ≤ 65535) ∧
        List.Nodup (ss.map Prod.fst) ∧
        (printShares ss).length ≤ 65533 := h
    show (be16 (printShares ss).length ++
      printShares ss).length ≤ 65535
    rw [List.length_append]
    simp [be16]
    omega
  · have h' : ¬ (t = 0 ∨ t = 16 ∨ t = 43 ∨ t = 51) ∧
        t < 65536 ∧ v.length ≤ 65535 := h
    exact h'.2.2

/-- A printed extension value reads back as the extension,
    at its own type. -/
theorem parseExtValue_printExtValue (e : Extension)
    (h : ExtWF e) :
    parseExtValue (extType e) (printExtValue e) = some e := by
  rcases e with ⟨es⟩ | ⟨ns⟩ | ⟨vs⟩ | ⟨ss⟩ | ⟨t, v⟩
  ·
    have h' : es ≠ [] ∧
        (∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535 ∧
          (e.1 = 0 → e.2 ≠ [])) ∧
        List.Nodup (es.map Prod.fst) ∧
        (printNameEntries es).length ≤ 65533 := h
    show parseExtValue 0 (printExtValue
      (Extension.serverName es)) = some (Extension.serverName es)
    unfold parseExtValue
    rw [ite_eq_left rfl]
    exact parseSNI_print h'.1 h'.2.1 h'.2.2.1 h'.2.2.2
  · have h' : ns ≠ [] ∧
        (∀ n ∈ ns, n ≠ [] ∧ n.length ≤ 255) ∧
        (printAlpnNames ns).length ≤ 65533 := h
    show parseExtValue 16 (printExtValue
      (Extension.alpn ns)) = some (Extension.alpn ns)
    unfold parseExtValue
    rw [ite_eq_right (by decide), ite_eq_left rfl]
    exact parseALPN_print h'.1 h'.2.1 h'.2.2
  · have h' : vs ≠ [] ∧ (∀ v ∈ vs, v < 65536) ∧
        vs.length ≤ 127 := h
    show parseExtValue 43 (printExtValue
      (Extension.supportedVersions vs))
      = some (Extension.supportedVersions vs)
    unfold parseExtValue
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
    exact parseSV_print h'.1 h'.2.1 h'.2.2
  · have h' : (∀ s ∈ ss, s.1 < 65536 ∧ s.2 ≠ [] ∧
          s.2.length ≤ 65535) ∧
        List.Nodup (ss.map Prod.fst) ∧
        (printShares ss).length ≤ 65533 := h
    show parseExtValue 51 (printExtValue
      (Extension.keyShare ss)) = some (Extension.keyShare ss)
    unfold parseExtValue
    rw [ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_left rfl]
    exact parseKS_print h'.1 h'.2.1 h'.2.2
  · have h' : ¬ (t = 0 ∨ t = 16 ∨ t = 43 ∨ t = 51) ∧
        t < 65536 ∧ v.length ≤ 65535 := h
    have hn := not_or.mp h'.1
    have hn2 := not_or.mp hn.2
    have hn3 := not_or.mp hn2.2
    show parseExtValue t (printExtValue
      (Extension.opaque t v)) = some (Extension.opaque t v)
    unfold parseExtValue
    rw [ite_eq_right hn.1, ite_eq_right hn2.1, ite_eq_right hn3.1,
      ite_eq_right hn3.2]
    rfl

/-- An extension value a successful read gives is the
    printed form of the extension it gives, the extension
    carries the type it was read under, and the extension
    is well formed. -/
theorem parseExtValue_inv {t : Nat} {v : List UInt8}
    {e : Extension}
    (ht : t < 65536) (hv : v.length ≤ 65535)
    (h : parseExtValue t v = some e) :
    extType e = t ∧ printExtValue e = v ∧ ExtWF e := by
  unfold parseExtValue at h
  by_cases h0 : t = 0
  · rw [ite_eq_left h0] at h
    obtain ⟨es, he, hprint, hwf⟩ := parseSNI_inv hv h
    refine ⟨?_, ?_, ?_⟩
    · rw [he]; exact h0.symm
    · rw [he]; exact hprint
    · rw [he]; exact hwf
  · rw [ite_eq_right h0] at h
    by_cases h16 : t = 16
    · rw [ite_eq_left h16] at h
      obtain ⟨ns, he, hprint, hwf⟩ := parseALPN_inv hv h
      refine ⟨?_, ?_, ?_⟩
      · rw [he]; exact h16.symm
      · rw [he]; exact hprint
      · rw [he]; exact hwf
    · rw [ite_eq_right h16] at h
      by_cases h43 : t = 43
      · rw [ite_eq_left h43] at h
        obtain ⟨vs, he, hprint, hwf⟩ := parseSV_inv h
        refine ⟨?_, ?_, ?_⟩
        · rw [he]; exact h43.symm
        · rw [he]; exact hprint
        · rw [he]; exact hwf
      · rw [ite_eq_right h43] at h
        by_cases h51 : t = 51
        · rw [ite_eq_left h51] at h
          obtain ⟨ss, he, hprint, hwf⟩ := parseKS_inv hv h
          refine ⟨?_, ?_, ?_⟩
          · rw [he]; exact h51.symm
          · rw [he]; exact hprint
          · rw [he]; exact hwf
        · rw [ite_eq_right h51] at h
          simp only [Option.some.injEq] at h
          subst h
          refine ⟨rfl, rfl, ?_⟩
          exact ⟨fun hc => by
            rcases hc with rfl | rfl | rfl | rfl
            · exact h0 rfl
            · exact h16 rfl
            · exact h43 rfl
            · exact h51 rfl, ht, hv⟩

/-! ## The extensions block -/

/-- The printed length of one extension: four bytes of type
    and length, then the value. -/
theorem printExt_length (e : Extension) :
    (printExt e).length = (printExtValue e).length + 4 := by
  show (be16 (extType e) ++ be16 (printExtValue e).length ++
    printExtValue e).length = _
  rw [List.length_append, List.length_append]
  have h1 : (be16 (extType e)).length = 2 := rfl
  have h2 : (be16 (printExtValue e).length).length = 2 := rfl
  omega

/-- One step of the extension reader, stated for
    rewriting. -/
theorem parseExtsGo_step (f : Nat) (x y : UInt8)
    (rest : List UInt8) :
    parseExtsGo (f + 1) (x :: y :: rest) =
      getU16 (x :: y :: rest) >>= fun (t, r1) =>
      getU16 r1 >>= fun (n, r2) =>
      if (r2.take n).length = n then
        parseExtValue t (r2.take n) >>= fun e =>
        parseExtsGo f (r2.drop n) >>= fun es =>
        if extType e ∈ es.map extType then none
        else some (e :: es)
      else none := rfl

/-- Printed extensions read back as the extensions. -/
theorem parseExtsGo_print :
    ∀ (es : List Extension) (fuel : Nat),
    (∀ e ∈ es, ExtWF e) →
    List.Nodup (es.map extType) →
    (printExts es).length < fuel →
    parseExtsGo fuel (printExts es) = some es := by
  intro es
  induction es with
  | nil =>
    intro fuel _ _ hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rfl
  | cons e es ih =>
    intro fuel hw hnodup hf
    have hwe : ExtWF e := hw e (by simp)
    have htail : ∀ x ∈ es, ExtWF x :=
      fun x hx => hw x (List.mem_cons_of_mem e hx)
    have hnodup' : List.Nodup (es.map extType) := by
      have h2 : (e :: es).map extType
          = extType e :: es.map extType := rfl
      rw [h2] at hnodup
      exact (List.nodup_cons.mp hnodup).2
    have hnotin : extType e ∉ es.map extType := by
      have h2 : (e :: es).map extType
          = extType e :: es.map extType := rfl
      rw [h2] at hnodup
      exact (List.nodup_cons.mp hnodup).1
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hf' : (printExts es).length < f := by
      have hflen : (printExts (e :: es)).length
          = (printExt e).length + (printExts es).length := by
        show ((printExt e) ++ printExts es).length = _
        rw [List.length_append]
      have h2 := printExt_length e
      omega
    show parseExtsGo (f + 1)
        ((be16 (extType e) ++
          (be16 (printExtValue e).length ++
            printExtValue e)) ++ printExts es)
      = some (e :: es)
    have hform : (be16 (extType e) ++
          (be16 (printExtValue e).length ++
            printExtValue e)) ++ printExts es
        = (extType e / 256).toUInt8 :: (extType e).toUInt8 ::
          ((printExtValue e).length / 256).toUInt8 ::
          (printExtValue e).length.toUInt8 ::
          (printExtValue e ++ printExts es) := by
      simp only [be16, List.cons_append,
        List.nil_append]
    rw [hform, parseExtsGo_step]
    have hg : getU16 ((extType e / 256).toUInt8 ::
        (extType e).toUInt8 ::
        ((printExtValue e).length / 256).toUInt8 ::
        (printExtValue e).length.toUInt8 ::
        (printExtValue e ++ printExts es))
        = some (extType e,
          ((printExtValue e).length / 256).toUInt8 ::
          (printExtValue e).length.toUInt8 ::
          (printExtValue e ++ printExts es)) := by
      show some (u16 (extType e / 256).toUInt8
        (extType e).toUInt8, _) = _
      rw [u16_be16 _ (extType_lt hwe)]
    rw [hg]
    simp only []
    show (getU16 (((printExtValue e).length / 256).toUInt8 ::
        (printExtValue e).length.toUInt8 ::
        (printExtValue e ++ printExts es)) >>=
        fun (n, r2) =>
        if (r2.take n).length = n then
          parseExtValue (extType e) (r2.take n) >>= fun e' =>
          parseExtsGo f (r2.drop n) >>= fun es' =>
          if extType e' ∈ es'.map extType then none
          else some (e' :: es')
        else none) = some (e :: es)
    have hk : getU16 (((printExtValue e).length / 256).toUInt8 ::
        (printExtValue e).length.toUInt8 ::
        (printExtValue e ++ printExts es))
        = some ((printExtValue e).length,
          printExtValue e ++ printExts es) := by
      show some (u16 ((printExtValue e).length / 256).toUInt8
        (printExtValue e).length.toUInt8, _) = _
      rw [u16_be16 _ (by
        have h2 := printExtValue_length_le hwe
        omega)]
    rw [hk]
    simp only []
    show (if ((printExtValue e ++ printExts es).take
          (printExtValue e).length).length
        = (printExtValue e).length then
      parseExtValue (extType e)
        ((printExtValue e ++ printExts es).take
          (printExtValue e).length) >>= fun e' =>
      parseExtsGo f ((printExtValue e ++ printExts es).drop
        (printExtValue e).length) >>= fun es' =>
      if extType e' ∈ es'.map extType then none
      else some (e' :: es')
    else none) = some (e :: es)
    rw [List.take_left, List.drop_left, ite_eq_left rfl,
      parseExtValue_printExtValue e hwe]
    show (parseExtsGo f (printExts es) >>= fun es' =>
      if extType e ∈ es'.map extType then none
      else some (e :: es')) = some (e :: es)
    rw [ih f htail hnodup' hf']
    show (if extType e ∈ es.map extType then none
      else some (e :: es)) = some (e :: es)
    rw [ite_eq_right hnotin]

/-- Printed extensions read back, at the top level. -/
theorem parseExts_print {es : List Extension}
    (hw : ∀ e ∈ es, ExtWF e)
    (hn : List.Nodup (es.map extType)) :
    parseExts (printExts es) = some es := by
  show parseExtsGo ((printExts es).length + 1)
    (printExts es) = some es
  exact parseExtsGo_print es _ hw hn (Nat.lt_succ_self _)

/-- Extensions a successful read gives print back to the
    bytes they were read from, each extension is well
    formed, and no type stands twice. -/
theorem parseExtsGo_inv :
    ∀ (f : Nat) (bs : List UInt8) (es : List Extension),
    parseExtsGo f bs = some es →
    printExts es = bs ∧
    (∀ e ∈ es, ExtWF e) ∧
    List.Nodup (es.map extType) := by
  intro f
  induction f with
  | zero =>
    intro bs es h
    simp [parseExtsGo] at h
  | succ f ih =>
    intro bs es h
    cases bs with
    | nil =>
      have h1 : parseExtsGo (f + 1) ([] : List UInt8)
          = some [] := rfl
      rw [h1] at h
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨rfl, by simp, by simp⟩
    | cons b1 rest =>
      cases rest with
      | nil =>
        have h1 : parseExtsGo (f + 1) [b1] = none := rfl
        rw [h1] at h
        simp at h
      | cons b2 rest =>
        rw [parseExtsGo_step] at h
        obtain ⟨⟨t, r1⟩, ht, h⟩ := Option.bind_eq_some_iff.mp h
        change (getU16 r1 >>= fun (n, r2) =>
          if (r2.take n).length = n then
            parseExtValue t (r2.take n) >>= fun e =>
            parseExtsGo f (r2.drop n) >>= fun es =>
            if extType e ∈ es.map extType then none
            else some (e :: es)
          else none) = some es at h
        obtain ⟨⟨n, r2⟩, hn, h⟩ := Option.bind_eq_some_iff.mp h
        change (if (r2.take n).length = n then
            parseExtValue t (r2.take n) >>= fun e =>
            parseExtsGo f (r2.drop n) >>= fun es' =>
            if extType e ∈ es'.map extType then none
            else some (e :: es')
          else none) = some es at h
        obtain ⟨hbs, htlt⟩ := getU16_inv ht
        obtain ⟨hr1, hnlt⟩ := getU16_inv hn
        by_cases hc : (r2.take n).length = n
        · rw [ite_eq_left hc] at h
          obtain ⟨e, hev, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨es', hrec, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨hprint, hprops, hnodup⟩ := ih _ _ hrec
          obtain ⟨htype, hvalue, hwe⟩ := parseExtValue_inv htlt
            (by rw [hc]; omega) hev
          by_cases hd : extType e ∈ es'.map extType
          · rw [ite_eq_left hd] at h
            simp at h
          · rw [ite_eq_right hd] at h
            simp only [Option.some.injEq] at h
            subst h
            refine ⟨?_, ?_, ?_⟩
            · show printExts (e :: es') = b1 :: b2 :: rest
              have htake : (r2.take n).length = n := hc
              show (printExt e ++ printExts es')
                = b1 :: b2 :: rest
              show ((be16 (extType e) ++
                  be16 (printExtValue e).length ++
                  printExtValue e) ++ printExts es')
                = b1 :: b2 :: rest
              rw [htype, hvalue, htake, hprint, hbs, hr1]
              simp only [List.append_assoc]
              rw [List.take_append_drop]
            · intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · exact hwe
              · exact hprops x hx
            · have h2 : (e :: es').map extType
                  = extType e :: es'.map extType := rfl
              rw [h2]
              exact List.nodup_cons.mpr ⟨hd, hnodup⟩
        · rw [ite_eq_right hc] at h
          simp at h

/-- Extensions a successful read gives print back, at the
    top level. -/
theorem parseExts_inv {bs : List UInt8}
    {es : List Extension}
    (h : parseExts bs = some es) :
    printExts es = bs ∧
    (∀ e ∈ es, ExtWF e) ∧
    List.Nodup (es.map extType) :=
  parseExtsGo_inv _ _ _ h

/-! ## The body fields -/

/-- The printed body fields, with each field in front of the
    rest, in the shape the readers take them apart. -/
theorem printBodyFields_eq (h : Hello) :
    printBodyFields h =
      be16 h.legacyVersion ++ (h.random ++
      (h.sessionId.length.toUInt8 :: (h.sessionId ++
      (be16 (printPairs h.cipherSuites).length ++
      (printPairs h.cipherSuites ++
      (h.compressionMethods.length.toUInt8 ::
      (h.compressionMethods ++
      (be16 (printExts h.extensions).length ++
      printExts h.extensions)))))))) := by
  simp only [printBodyFields, List.append_assoc, List.cons_append]

/-- A list holding a supported_versions extension whose list holds
    0x0304 offers TLS 1.3, wherever the extension and the version
    stand. -/
theorem offersTls13_of_mem {exts : List Extension} {vs : List Nat}
    (h : Extension.supportedVersions vs ∈ exts) (h13 : 772 ∈ vs) :
    offersTls13 exts = true := by
  induction exts with
  | nil => simp at h
  | cons e es ih =>
    rcases List.mem_cons.mp h with rfl | h'
    · simp [offersTls13, h13]
    · cases e <;> simp [offersTls13, ih h']

/-- A list that offers TLS 1.3 holds a supported_versions
    extension whose list holds 0x0304. -/
theorem mem_of_offersTls13 {exts : List Extension}
    (h : offersTls13 exts = true) :
    ∃ vs, Extension.supportedVersions vs ∈ exts ∧ 772 ∈ vs := by
  induction exts with
  | nil => simp [offersTls13] at h
  | cons e es ih =>
    cases e with
    | supportedVersions vs =>
      simp only [offersTls13, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨vs, List.mem_cons_self, by simpa using h⟩
      · obtain ⟨ws, hm, h7⟩ := ih h
        exact ⟨ws, List.mem_cons_of_mem _ hm, h7⟩
    | _ =>
      obtain ⟨ws, hm, h7⟩ := ih (by simpa [offersTls13] using h)
      exact ⟨ws, List.mem_cons_of_mem _ hm, h7⟩

/-- The printed body fields read back as the hello. -/
theorem parseBodyFields_print (m : Message) (hw : WF m) :
    parseBodyFields (printBodyFields m.hello) = some m.hello := by
  obtain ⟨_, hver, hrand, hsess, hsuites_ne, hsuites_lt,
    hsuites_len, hcomp_ne, hcomp0, hcomp_len, hext_wf,
    hnodup, hpsk, h13sv, hext_len, _⟩ := hw
  have h13 : offersTls13 m.hello.extensions = true →
      m.hello.compressionMethods = [0] := fun ho =>
    let ⟨vs, hm, h7⟩ := mem_of_offersTls13 ho
    h13sv vs hm h7
  have hsuites_len1 : 1 ≤ m.hello.cipherSuites.length := by
    cases hcs : m.hello.cipherSuites with
    | nil => exact absurd hcs hsuites_ne
    | cons v vs' => simp
  have hcomp_len1 : 1 ≤ m.hello.compressionMethods.length := by
    cases hcc : m.hello.compressionMethods with
    | nil => exact absurd hcc hcomp_ne
    | cons c cs' => simp
  have hsb : (m.hello.sessionId.length.toUInt8).toNat
      = m.hello.sessionId.length := by
    rw [toUInt8_toNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hcb : (m.hello.compressionMethods.length.toUInt8).toNat
      = m.hello.compressionMethods.length := by
    rw [toUInt8_toNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hpl := printPairs_length m.hello.cipherSuites
  have hguard : (printPairs m.hello.cipherSuites).length % 2 = 0 ∧
      2 ≤ (printPairs m.hello.cipherSuites).length :=
    ⟨by omega, by omega⟩
  rw [printBodyFields_eq]
  unfold parseBodyFields
  rw [withU16_be16 hver, withBytes_app hrand, withU8_cons, hsb,
    ite_eq_left hsess, withBytes_app rfl, withU16_be16 (by omega),
    ite_eq_left hguard, withBytes_app rfl,
    parsePairs_printPairs hsuites_lt, Option.bind_some,
    withU8_cons, hcb, ite_eq_left hcomp_len1, withBytes_app rfl,
    ite_eq_left hcomp0, withU16_be16 (by omega), withBytes_self,
    ite_eq_left rfl, parseExts_print hext_wf hnodup, Option.bind_some,
    ite_eq_left hpsk, ite_eq_left h13]

/-- A parsed hello prints back to the input bytes, and every
    field satisfies the well formedness bounds. -/
theorem parseBodyFields_inv {bs : List UInt8} {h : Hello}
    (hparse : parseBodyFields bs = some h) :
    printBodyFields h = bs ∧
    h.legacyVersion < 65536 ∧ h.random.length = 32 ∧
    h.sessionId.length ≤ 32 ∧
    h.cipherSuites ≠ [] ∧
    (∀ v ∈ h.cipherSuites, v < 65536) ∧
    h.cipherSuites.length ≤ 32767 ∧
    h.compressionMethods ≠ [] ∧
    (0 : UInt8) ∈ h.compressionMethods ∧
    h.compressionMethods.length ≤ 255 ∧
    (∀ e ∈ h.extensions, ExtWF e) ∧
    List.Nodup (h.extensions.map extType) ∧
    41 ∉ (h.extensions.dropLast).map extType ∧
    (offersTls13 h.extensions = true →
      h.compressionMethods = [0]) ∧
    (printExts h.extensions).length ≤ 65535 := by
  unfold parseBodyFields at hparse
  obtain ⟨ver, r1, hbs, hver, hp⟩ := withU16_inv hparse
  obtain ⟨rand, r2, hrand, hr1, hp⟩ := withBytes_inv hp
  obtain ⟨slen, r3, hr2, _, hp⟩ := withU8_inv hp
  by_cases hs : slen ≤ 32
  case neg => rw [ite_eq_right hs] at hp; cases hp
  rw [ite_eq_left hs] at hp
  obtain ⟨sess, r4, hsesslen, hr3, hp⟩ := withBytes_inv hp
  obtain ⟨clen, r5, hr4, hclen_lt, hp⟩ := withU16_inv hp
  by_cases hg : clen % 2 = 0 ∧ 2 ≤ clen
  case neg => rw [ite_eq_right hg] at hp; cases hp
  rw [ite_eq_left hg] at hp
  obtain ⟨cbytes, r6, hcbyteslen, hr5, hp⟩ := withBytes_inv hp
  obtain ⟨suites, s7, hp⟩ := Option.bind_eq_some_iff.mp hp
  obtain ⟨mlen, r7, hr6, hmlen_lt, hp⟩ := withU8_inv hp
  by_cases hm : 1 ≤ mlen
  case neg => rw [ite_eq_right hm] at hp; cases hp
  rw [ite_eq_left hm] at hp
  obtain ⟨comps, r8, hcomplen, hr7, hp⟩ := withBytes_inv hp
  by_cases h0 : (0 : UInt8) ∈ comps
  case neg => rw [ite_eq_right h0] at hp; cases hp
  rw [ite_eq_left h0] at hp
  obtain ⟨elen, r9, hr8, helen_lt, hp⟩ := withU16_inv hp
  obtain ⟨ebytes, r10, hebyteslen, hr9, hp⟩ := withBytes_inv hp
  by_cases hr : r10 = []
  case neg => rw [ite_eq_right hr] at hp; cases hp
  rw [ite_eq_left hr] at hp
  obtain ⟨exts, s12, hp⟩ := Option.bind_eq_some_iff.mp hp
  by_cases hpsk : 41 ∉ (exts.dropLast).map extType
  case neg => rw [ite_eq_right hpsk] at hp; cases hp
  rw [ite_eq_left hpsk] at hp
  by_cases h13 : offersTls13 exts = true → comps = [0]
  case neg => rw [ite_eq_right h13] at hp; cases hp
  rw [ite_eq_left h13] at hp
  simp only [Option.some.injEq] at hp
  subst hp
  have hpp : printPairs suites = cbytes := (parsePairs_inv s7).1
  have hsuites_lt : ∀ v ∈ suites, v < 65536 :=
    (parsePairs_inv s7).2
  have hplen : cbytes.length = 2 * suites.length :=
    parsePairs_length s7
  have hpe : printExts exts = ebytes := (parseExts_inv s12).1
  have hext_wf : ∀ e ∈ exts, ExtWF e := (parseExts_inv s12).2.1
  have hnodup : (exts.map extType).Nodup :=
    (parseExts_inv s12).2.2
  have hsess_le : sess.length ≤ 32 := by omega
  have hsuites_ne : suites ≠ [] := by
    intro hcon
    rw [hcon, List.length_nil] at hplen
    omega
  have hsuites_len : suites.length ≤ 32767 := by omega
  have hcomp_ne : comps ≠ [] := by
    intro hcon
    rw [hcon] at hcomplen
    simp at hcomplen
    omega
  have hcomp_len : comps.length ≤ 255 := by omega
  have hext_len : (printExts exts).length ≤ 65535 := by
    rw [hpe, hebyteslen]
    omega
  have hprint : printBodyFields
      ⟨ver, rand, sess, suites, comps, exts⟩ = bs := by
    rw [printBodyFields_eq]
    show be16 ver ++ (rand ++
      (sess.length.toUInt8 :: (sess ++
      (be16 (printPairs suites).length ++
      (printPairs suites ++
      (comps.length.toUInt8 :: (comps ++
      (be16 (printExts exts).length ++
      printExts exts)))))))) = bs
    rw [hsesslen, hcomplen, hpp, hcbyteslen, hpe, hebyteslen,
      hbs, hr1, hr2, hr3, hr4, hr5, hr6, hr7, hr8, hr9, hr,
      List.append_nil]
  exact ⟨hprint, hver, hrand, hsess_le, hsuites_ne, hsuites_lt,
    hsuites_len, hcomp_ne, h0, hcomp_len, hext_wf, hnodup, hpsk,
    h13, hext_len⟩

/-! ## The handshake message and the record -/

/-- The printed handshake message is four bytes longer than
    the printed body fields. -/
theorem printBody_length (h : Hello) :
    (printBody h).length = (printBodyFields h).length + 4 := by
  simp [printBody, be24]

/-- The printed handshake message, as its type byte in front
    of the rest. -/
theorem printBody_eq (h : Hello) :
    printBody h = (1 : UInt8) ::
      (be24 (printBodyFields h).length ++ printBodyFields h) :=
  rfl

/-- The printed handshake message reads back as the hello. -/
theorem parseBody_print (m : Message) (hw : WF m) :
    parseBody (printBody m.hello) = some m.hello := by
  have hwf : WF m := hw
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hflen⟩ := hw
  rw [printBody_eq]
  unfold parseBody
  rw [withU8_cons, ite_eq_left (by decide : ((1 : UInt8).toNat = 1)),
    withU24_be24 (by omega), withBytes_self, ite_eq_left rfl]
  exact parseBodyFields_print m hwf

/-- A parsed handshake message prints back to the input
    bytes, and every field satisfies the bounds. -/
theorem parseBody_inv {body : List UInt8} {h : Hello}
    (hparse : parseBody body = some h) :
    printBody h = body ∧
    h.legacyVersion < 65536 ∧ h.random.length = 32 ∧
    h.sessionId.length ≤ 32 ∧
    h.cipherSuites ≠ [] ∧
    (∀ v ∈ h.cipherSuites, v < 65536) ∧
    h.cipherSuites.length ≤ 32767 ∧
    h.compressionMethods ≠ [] ∧
    (0 : UInt8) ∈ h.compressionMethods ∧
    h.compressionMethods.length ≤ 255 ∧
    (∀ e ∈ h.extensions, ExtWF e) ∧
    List.Nodup (h.extensions.map extType) ∧
    41 ∉ (h.extensions.dropLast).map extType ∧
    (offersTls13 h.extensions = true →
      h.compressionMethods = [0]) ∧
    (printExts h.extensions).length ≤ 65535 := by
  unfold parseBody at hparse
  obtain ⟨htype, r1, hbody1, _, hp⟩ := withU8_inv hparse
  by_cases ht : htype = 1
  case neg => rw [ite_eq_right ht] at hp; cases hp
  rw [ite_eq_left ht] at hp
  obtain ⟨hlen, r2, hr1, _, hp⟩ := withU24_inv hp
  obtain ⟨fbs, r3, hfbs, hr2, hp⟩ := withBytes_inv hp
  by_cases hr : r3 = []
  case neg => rw [ite_eq_right hr] at hp; cases hp
  rw [ite_eq_left hr] at hp
  have hfi := parseBodyFields_inv hp
  have hbyte : htype.toUInt8 = (1 : UInt8) := by
    rw [ht]
    decide
  have hprint : printBody h = body := by
    rw [printBody_eq, hfi.1, hfbs, hbody1, hbyte, hr1, hr2, hr,
      List.append_nil]
  exact ⟨hprint, hfi.2⟩

/-- The whole printed message, as its content type byte in
    front of the rest. -/
theorem print_eq (m : Message) :
    print m = (22 : UInt8) :: (be16 m.recordVersion ++
      (be16 (printBody m.hello).length ++ printBody m.hello)) :=
  rfl

/-- The whole printed message reads back as the message. -/
theorem parse_print (m : Message) (hw : WF m) :
    parse (print m) = some m := by
  have hwf : WF m := hw
  obtain ⟨hrv, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hflen⟩ := hw
  have hblt : (printBody m.hello).length < 65536 := by
    rw [printBody_length]
    omega
  have hble : (printBody m.hello).length ≤ 16384 := by
    rw [printBody_length]
    omega
  rw [print_eq]
  unfold parse
  rw [withU8_cons, ite_eq_left (by decide : ((22 : UInt8).toNat = 22)),
    withU16_be16 hrv, withU16_be16 hblt, ite_eq_left hble,
    withBytes_self, ite_eq_left rfl, parseBody_print m hwf,
    Option.map_some]

/-- A parsed message prints back to the input bytes, and the
    message is well formed. -/
theorem print_parse {bs : List UInt8} {m : Message}
    (hparse : parse bs = some m) :
    print m = bs ∧ WF m := by
  unfold parse at hparse
  obtain ⟨ct, r1, hbs1, _, hp⟩ := withU8_inv hparse
  by_cases hct : ct = 22
  case neg => rw [ite_eq_right hct] at hp; cases hp
  rw [ite_eq_left hct] at hp
  obtain ⟨rv, r2, hr1, hrv, hp⟩ := withU16_inv hp
  obtain ⟨rlen, r3, hr2, hrlen, hp⟩ := withU16_inv hp
  by_cases hrl : rlen ≤ 16384
  case neg => rw [ite_eq_right hrl] at hp; cases hp
  rw [ite_eq_left hrl] at hp
  obtain ⟨body, r4, hbodylen, hr3, hp⟩ := withBytes_inv hp
  by_cases hr : r4 = []
  case neg => rw [ite_eq_right hr] at hp; cases hp
  rw [ite_eq_left hr] at hp
  obtain ⟨hh, hpb, hp⟩ := Option.map_eq_some_iff.mp hp
  subst hp
  obtain ⟨hbody_eq, hver, hrand, hsess, hsne, hslt, hslen, hcne,
    hc0, hclen, hewf, hnod, hpsk, h13, helen⟩ := parseBody_inv hpb
  have hctb : ct.toUInt8 = (22 : UInt8) := by
    rw [hct]
    decide
  have hflen : (printBodyFields hh).length ≤ 16380 := by
    have h1 := printBody_length hh
    rw [hbody_eq] at h1
    omega
  have hprint : print ⟨rv, hh⟩ = bs := by
    rw [print_eq]
    show (22 : UInt8) :: (be16 rv ++
      (be16 (printBody hh).length ++ printBody hh)) = bs
    rw [hbody_eq, hbodylen, hbs1, hctb, hr1, hr2, hr3, hr,
      List.append_nil]
  exact ⟨hprint, hrv, hver, hrand, hsess, hsne, hslt, hslen,
    hcne, hc0, hclen, hewf, hnod, hpsk,
    fun vs hm h7 => h13 (offersTls13_of_mem hm h7), helen, hflen⟩
