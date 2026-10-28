/-
  The TLS ClientHello parser. It reads one record holding
  one ClientHello and returns the message, or `none` when the
  bytes break any of the rules in SPEC.md. Every read is
  length checked: a field read from input too short for it
  gives `none`. The rules:

  - The record header is five bytes: content type 22, a
    legacy record version carried unchecked, and a two byte
    length of at most 2^14 = 16384 (RFC 8446 section 5.1).
    The body is exactly that many bytes, and no bytes may
    follow the record. A body of length 0 cannot hold a
    handshake header, so it is turned away by the body read.
  - The handshake header is a type byte, which must be 1,
    and a three byte length that must cover the rest of the
    record body exactly.
  - The body fields follow their length rules: session id at
    most 32 bytes; cipher suites an even byte count of at
    least 2; compression methods at least one byte and the
    null method 0 among them, and exactly the one byte 0
    when supported_versions lists TLS 1.3 (0x0304). A body
    that ends before the extensions length is turned away:
    the extensions block must be present, though it may be
    empty.
  - The extensions block is consumed exactly. Each extension
    is a type, a length, and that many value bytes; a length
    running past the block turns the message away, and a
    type standing twice turns it away. pre_shared_key (41)
    may only stand last.
  - Four extension values are decoded. In each, the inner
    length must cover the rest of the value exactly. Server
    name entries may not repeat a name type, and a host_name
    entry must be nonempty. ALPN names must be nonempty.
    supported_versions in a hello is a list of two byte
    versions of even, nonzero byte length. Key share entries
    may not repeat a group, and key exchange bytes must be
    nonempty. Every other type is carried opaque.

  The variable length lists are read with a fuel count, one
  more than the length of the input at the top level, which
  is always enough, since every step takes bytes. A hostile
  input is rejected, never looped on.
-/

import ClientHello.Value

namespace ClientHello

/-- Read two bytes as a big endian value, with the rest of
    the input. Fewer than two bytes gives `none`. -/
def getU16 : List UInt8 → Option (Nat × List UInt8)
  | a :: b :: rest => some (u16 a b, rest)
  | _ => none

/-! The record, the handshake header and the body fields are
read with the four readers below. Each one reads a field off
the front of the input and goes on with the field's value
and the rest of the input, or gives `none` when the input is
too short. Writing the top of the parser this way keeps each
proof step a rewrite with one of the reader lemmas, which
every kernel bundled with Lean checks quickly. -/

/-- Read one byte, then go on with its value and the rest of
    the input. No byte gives `none`. -/
def withU8 {α : Type} (bs : List UInt8)
    (k : Nat → List UInt8 → Option α) : Option α :=
  match bs with
  | b :: rest => k b.toNat rest
  | [] => none

/-- Read two bytes as a big endian value, then go on with the
    value and the rest of the input. Fewer than two bytes give
    `none`. -/
def withU16 {α : Type} (bs : List UInt8)
    (k : Nat → List UInt8 → Option α) : Option α :=
  match bs with
  | a :: b :: rest => k (u16 a b) rest
  | _ => none

/-- Read three bytes as a big endian value, then go on with
    the value and the rest of the input. Fewer than three bytes
    give `none`. -/
def withU24 {α : Type} (bs : List UInt8)
    (k : Nat → List UInt8 → Option α) : Option α :=
  match bs with
  | a :: b :: c :: rest => k (u24 a b c) rest
  | _ => none

/-- Read `n` bytes as a block, then go on with the block and
    the rest of the input. Fewer than `n` bytes give `none`. -/
def withBytes {α : Type} (n : Nat) (bs : List UInt8)
    (k : List UInt8 → List UInt8 → Option α) : Option α :=
  if (bs.take n).length = n then k (bs.take n) (bs.drop n)
  else none

/-- Read a list of two byte values from bytes that must be
    consumed exactly. An odd trailing byte gives `none`. -/
def parsePairs : List UInt8 → Option (List Nat)
  | [] => some []
  | a :: b :: rest =>
    (parsePairs rest).map (fun vs => u16 a b :: vs)
  | _ => none

/-- Read server name entries with a fuel count. A name type
    standing twice in the list gives `none`; the repeat
    check is made against the entries that follow. -/
def parseNameEntriesGo :
    Nat → List UInt8 → Option (List (Nat × List UInt8))
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, t :: rest =>
    getU16 rest >>= fun (n, r1) =>
    if (r1.take n).length = n then
      parseNameEntriesGo f (r1.drop n) >>= fun es =>
      if t.toNat ∈ es.map Prod.fst then none
      else some ((t.toNat, r1.take n) :: es)
    else none

/-- Read server name entries, with enough fuel for the whole
    input. -/
def parseNameEntries (bs : List UInt8) :
    Option (List (Nat × List UInt8)) :=
  parseNameEntriesGo (bs.length + 1) bs

/-- The server name value check that stands outside the
    entry grammar: the list is nonempty, and every host_name
    entry (type 0) carries at least one byte. -/
def validNames (es : List (Nat × List UInt8)) : Bool :=
  !es.isEmpty &&
  es.all (fun e => decide (e.1 ≠ 0 ∨ e.2 ≠ []))

/-- Read the server_name value: a two byte list length that
    covers the rest of the value, then the entries, then
    the value check. -/
def parseSNI (v : List UInt8) : Option Extension :=
  getU16 v >>= fun (n, rest) =>
  if rest.length = n then
    parseNameEntries rest >>= fun es =>
    if validNames es then some (.serverName es) else none
  else none

/-- Read ALPN protocol names with a fuel count. An empty
    name gives `none`. -/
def parseAlpnGo : Nat → List UInt8 → Option (List (List UInt8))
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, len :: rest =>
    if len.toNat = 0 then none
    else if (rest.take len.toNat).length = len.toNat then
      (parseAlpnGo f (rest.drop len.toNat)).map
        (fun ns => (rest.take len.toNat) :: ns)
    else none

/-- Read ALPN protocol names, with enough fuel for the whole
    input. -/
def parseAlpnNames (bs : List UInt8) :
    Option (List (List UInt8)) :=
  parseAlpnGo (bs.length + 1) bs

/-- Read the ALPN value: a two byte list length that covers
    the rest of the value, then at least one name. -/
def parseALPN (v : List UInt8) : Option Extension :=
  getU16 v >>= fun (n, rest) =>
  if rest.length = n then
    parseAlpnNames rest >>= fun ns =>
    if ns.isEmpty then none else some (.alpn ns)
  else none

/-- Read the supported_versions value, in the ClientHello
    form: a one byte length, even and at least 2, then that
    many bytes as two byte versions. -/
def parseSV (v : List UInt8) : Option Extension :=
  match v with
  | n :: rest =>
    if rest.length = n.toNat ∧ n.toNat % 2 = 0 ∧ 2 ≤ n.toNat
      then parsePairs rest >>= fun vs =>
        some (.supportedVersions vs)
    else none
  | [] => none

/-- Read key share entries with a fuel count. Empty key
    exchange bytes give `none`, and a group standing twice
    in the list gives `none`. -/
def parseSharesGo :
    Nat → List UInt8 → Option (List (Nat × List UInt8))
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, bs =>
    getU16 bs >>= fun (g, r1) =>
    getU16 r1 >>= fun (n, r2) =>
    if n = 0 then none
    else if (r2.take n).length = n then
      parseSharesGo f (r2.drop n) >>= fun ss =>
      if g ∈ ss.map Prod.fst then none
      else some ((g, r2.take n) :: ss)
    else none

/-- Read key share entries, with enough fuel for the whole
    input. -/
def parseShares (bs : List UInt8) :
    Option (List (Nat × List UInt8)) :=
  parseSharesGo (bs.length + 1) bs

/-- Read the key_share value, in the client form: a two
    byte list length that covers the rest of the value, then
    the entries. The list may be empty: RFC 8446 section
    4.2.8 lets a client send no shares, to ask for a
    HelloRetryRequest. -/
def parseKS (v : List UInt8) : Option Extension :=
  getU16 v >>= fun (n, rest) =>
  if rest.length = n then
    parseShares rest >>= fun ss => some (.keyShare ss)
  else none

/-- Read one extension value, by its type. The four decoded
    types go to their readers; every other type is carried
    opaque, as the type and the value bytes as they stood. -/
def parseExtValue (t : Nat) (v : List UInt8) :
    Option Extension :=
  if t = 0 then parseSNI v
  else if t = 16 then parseALPN v
  else if t = 43 then parseSV v
  else if t = 51 then parseKS v
  else some (.opaque t v)

/-- Read the extensions of a block that must be consumed
    exactly, with a fuel count. An extension length running
    past the block gives `none`, and a type standing twice
    gives `none`. -/
def parseExtsGo : Nat → List UInt8 → Option (List Extension)
  | 0, _ => none
  | _ + 1, [] => some []
  | f + 1, bs =>
    getU16 bs >>= fun (t, r1) =>
    getU16 r1 >>= fun (n, r2) =>
    if (r2.take n).length = n then
      parseExtValue t (r2.take n) >>= fun e =>
      parseExtsGo f (r2.drop n) >>= fun es =>
      if extType e ∈ es.map extType then none
      else some (e :: es)
    else none

/-- Read an extensions block, with enough fuel for the
    whole block. -/
def parseExts (bs : List UInt8) : Option (List Extension) :=
  parseExtsGo (bs.length + 1) bs

/-- Read the body fields from bytes that are exactly the
    fields: legacy version, random, session id, cipher
    suites, compression methods, and the extensions block,
    which must be present and must run to the end. -/
def parseBodyFields (bs : List UInt8) : Option Hello :=
  withU16 bs fun ver r1 =>
  withBytes 32 r1 fun rand r2 =>
  withU8 r2 fun slen r3 =>
  if slen ≤ 32 then
    withBytes slen r3 fun sess r4 =>
    withU16 r4 fun clen r5 =>
    if clen % 2 = 0 ∧ 2 ≤ clen then
      withBytes clen r5 fun cbytes r6 =>
      (parsePairs cbytes).bind fun suites =>
      withU8 r6 fun mlen r7 =>
      if 1 ≤ mlen then
        withBytes mlen r7 fun comps r8 =>
        if (0 : UInt8) ∈ comps then
          withU16 r8 fun elen r9 =>
          withBytes elen r9 fun ebytes r10 =>
          if r10 = [] then
            (parseExts ebytes).bind fun exts =>
            -- RFC 8446 section 4.2.11: pre_shared_key (41)
            -- must be the last extension.
            if 41 ∉ (exts.dropLast).map extType then
              -- RFC 8446 section 4.1.2: a TLS 1.3 ClientHello
              -- carries exactly one compression method, null.
              if offersTls13 exts = true → comps = [0] then
                some ⟨ver, rand, sess, suites, comps, exts⟩
              else none
            else none
          else none
        else none
      else none
    else none
  else none

/-- Read the handshake message from a record body: the type
    byte must be 1, and the three byte length must cover the
    rest of the body exactly. -/
def parseBody (body : List UInt8) : Option Hello :=
  withU8 body fun htype r1 =>
  if htype = 1 then
    withU24 r1 fun hlen r2 =>
    withBytes hlen r2 fun fbs r3 =>
    if r3 = [] then parseBodyFields fbs else none
  else none

/-- Parse a whole message: one record, holding one
    ClientHello, with no bytes after the record. The record
    length may not exceed 2^14 = 16384 bytes (RFC 8446
    section 5.1). -/
def parse (bs : List UInt8) : Option Message :=
  withU8 bs fun ct r1 =>
  if ct = 22 then
    withU16 r1 fun rv r2 =>
    withU16 r2 fun rlen r3 =>
    if rlen ≤ 16384 then
      withBytes rlen r3 fun body r4 =>
      if r4 = [] then (parseBody body).map fun h => ⟨rv, h⟩
      else none
    else none
  else none

end ClientHello
