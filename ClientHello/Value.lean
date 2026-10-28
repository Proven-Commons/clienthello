/-
  The TLS ClientHello data model and the canonical printer.

  A message is one TLS record holding one ClientHello, in the
  shape of RFC 8446 section 4.1.2 with the legacy fields of
  RFC 5246. The record header carries a content type, which
  must be 22 (handshake), a legacy record version, which is
  carried unchecked, and a length. Inside it, a handshake
  header carries the message type, which must be 1
  (client_hello), and a three byte length. The body holds the
  legacy version, the 32 byte random, the legacy session id,
  the cipher suites, the legacy compression methods, and the
  extensions.

  Four extensions are decoded: server_name (0, RFC 6066
  section 3), ALPN (16, RFC 7301), supported_versions (43),
  and key_share (51). Every other extension is carried as its
  type and its raw value bytes, length checked and not read.

  Numbers are held as plain natural numbers. Byte blocks are
  held as byte lists. Printing recomputes every length from
  the value it prints, so a printed message is the canonical
  form of the value.
-/

namespace ClientHello

/-- A value as two bytes, big endian. The value is taken
    modulo 2^16; callers only pass values below that. -/
def be16 (n : Nat) : List UInt8 :=
  [ (n / 256).toUInt8, n.toUInt8 ]

/-- The value of two bytes read big endian. -/
def u16 (a b : UInt8) : Nat :=
  a.toNat * 256 + b.toNat

/-- A value as three bytes, big endian. The value is taken
    modulo 2^24; callers only pass values below that. -/
def be24 (n : Nat) : List UInt8 :=
  [ (n / 65536).toUInt8, (n / 256).toUInt8, n.toUInt8 ]

/-- The value of three bytes read big endian. -/
def u24 (a b c : UInt8) : Nat :=
  a.toNat * 65536 + b.toNat * 256 + c.toNat

/-- One extension. The four decoded forms are distinct from
    the opaque form, which carries a type the slice does not
    decode and the value bytes as they stood. A server name
    entry is a name type and its bytes; a key share entry is
    a group and its key exchange bytes. -/
inductive Extension where
  | serverName (entries : List (Nat × List UInt8)) : Extension
  | alpn (names : List (List UInt8)) : Extension
  | supportedVersions (versions : List Nat) : Extension
  | keyShare (shares : List (Nat × List UInt8)) : Extension
  | opaque (extType : Nat) (value : List UInt8) : Extension
  deriving DecidableEq, Repr

/-- The wire type of an extension. -/
def extType : Extension → Nat
  | .serverName _ => 0
  | .alpn _ => 16
  | .supportedVersions _ => 43
  | .keyShare _ => 51
  | .opaque t _ => t

/-- Two byte values in printed form, one after another. -/
def printPairs : List Nat → List UInt8
  | [] => []
  | v :: vs => be16 v ++ printPairs vs

/-- Server name entries in printed form: a name type byte, a
    two byte length, and the name bytes. -/
def printNameEntries : List (Nat × List UInt8) → List UInt8
  | [] => []
  | (t, bs) :: es =>
    (t.toUInt8 :: (be16 bs.length ++ bs)) ++ printNameEntries es

/-- ALPN protocol names in printed form: a one byte length
    and the name bytes. -/
def printAlpnNames : List (List UInt8) → List UInt8
  | [] => []
  | n :: ns => (n.length.toUInt8 :: n) ++ printAlpnNames ns

/-- Key share entries in printed form: a two byte group, a
    two byte length, and the key exchange bytes. -/
def printShares : List (Nat × List UInt8) → List UInt8
  | [] => []
  | (g, k) :: ss =>
    (be16 g ++ (be16 k.length ++ k)) ++ printShares ss

/-- The value bytes of an extension, as the printer writes
    them. Three of the decoded forms open with a length that
    covers the rest of the value: two bytes for server_name
    and key_share, one byte for supported_versions in a
    ClientHello. -/
def printExtValue : Extension → List UInt8
  | .serverName es =>
    be16 (printNameEntries es).length ++ printNameEntries es
  | .alpn ns =>
    be16 (printAlpnNames ns).length ++ printAlpnNames ns
  | .supportedVersions vs =>
    (printPairs vs).length.toUInt8 :: printPairs vs
  | .keyShare ss =>
    be16 (printShares ss).length ++ printShares ss
  | .opaque _ v => v

/-- One extension in printed form: type, length, value. -/
def printExt (e : Extension) : List UInt8 :=
  be16 (extType e) ++ be16 (printExtValue e).length ++
    printExtValue e

/-- The extension list in printed form. -/
def printExts : List Extension → List UInt8
  | [] => []
  | e :: es => printExt e ++ printExts es

/-- The ClientHello body fields, in wire order. -/
structure Hello where
  /-- The legacy version, two bytes. Carried unchecked. -/
  legacyVersion : Nat
  /-- The random: 32 bytes in a well formed message. -/
  random : List UInt8
  /-- The legacy session id: at most 32 bytes in a well
      formed message. -/
  sessionId : List UInt8
  /-- The cipher suites, as two byte codes. A well formed
      message holds at least one. -/
  cipherSuites : List Nat
  /-- The legacy compression methods. A well formed message
      holds at least one, and the null method 0 is among
      them. -/
  compressionMethods : List UInt8
  /-- The extensions, in wire order. No type stands twice in
      a well formed message. -/
  extensions : List Extension
  deriving DecidableEq, Repr

/-- One record holding one ClientHello. -/
structure Message where
  /-- The legacy record version, two bytes. Carried
      unchecked. -/
  recordVersion : Nat
  /-- The ClientHello the record holds. -/
  hello : Hello
  deriving DecidableEq, Repr

/-- The body fields in printed form, without the handshake
    header: legacy version, random, session id with its one
    byte length, cipher suites with their two byte length,
    compression methods with their one byte length, and the
    extensions with their two byte length. -/
def printBodyFields (h : Hello) : List UInt8 :=
  be16 h.legacyVersion ++ h.random ++
  (h.sessionId.length.toUInt8 :: h.sessionId) ++
  (be16 (printPairs h.cipherSuites).length ++
    printPairs h.cipherSuites) ++
  (h.compressionMethods.length.toUInt8 ::
    h.compressionMethods) ++
  (be16 (printExts h.extensions).length ++
    printExts h.extensions)

/-- The handshake message in printed form: type 1, a three
    byte length, and the body fields. -/
def printBody (h : Hello) : List UInt8 :=
  (1 : UInt8) :: (be24 (printBodyFields h).length ++
    printBodyFields h)

/-- The whole message in printed form: content type 22, the
    legacy record version, a two byte length, and the
    handshake message. -/
def print (m : Message) : List UInt8 :=
  (22 : UInt8) :: (be16 m.recordVersion ++
    (be16 (printBody m.hello).length ++ printBody m.hello))

/-- Whether an extension list offers TLS 1.3: it holds a
    supported_versions extension that lists 0x0304 (772). Such
    a hello is a TLS 1.3 ClientHello in the sense of RFC 8446
    section 4.1.2, whatever older versions it also lists. -/
def offersTls13 : List Extension → Bool
  | [] => false
  | .supportedVersions vs :: es => vs.contains 772 || offersTls13 es
  | _ :: es => offersTls13 es

/-- Well formedness of one extension, at the level the
    printer needs: every length it writes fits the field that
    holds it, and the checks the parser makes on the value
    hold. -/
def ExtWF : Extension → Prop
  | .serverName es =>
    es ≠ [] ∧
    (∀ e ∈ es, e.1 < 256 ∧ e.2.length ≤ 65535 ∧
      (e.1 = 0 → e.2 ≠ [])) ∧
    List.Nodup (es.map Prod.fst) ∧
    (printNameEntries es).length ≤ 65533
  | .alpn ns =>
    ns ≠ [] ∧
    (∀ n ∈ ns, n ≠ [] ∧ n.length ≤ 255) ∧
    (printAlpnNames ns).length ≤ 65533
  | .supportedVersions vs =>
    vs ≠ [] ∧ (∀ v ∈ vs, v < 65536) ∧ vs.length ≤ 127
  | .keyShare ss =>
    (∀ s ∈ ss, s.1 < 65536 ∧ s.2 ≠ [] ∧
      s.2.length ≤ 65535) ∧
    List.Nodup (ss.map Prod.fst) ∧
    (printShares ss).length ≤ 65533
  | .opaque t v =>
    ¬ (t = 0 ∨ t = 16 ∨ t = 43 ∨ t = 51) ∧
    t < 65536 ∧ v.length ≤ 65535

/-- A well formed message: every number fits the field that
    holds it, every byte block holds the length its field
    demands, the cipher suites and compression methods meet
    their rules, every extension is well formed, no
    extension type stands twice, pre_shared_key (type 41)
    stands last if present (RFC 8446 section 4.2.11), a
    hello that offers TLS 1.3 carries exactly the null
    compression method (RFC 8446 section 4.1.2), and the
    handshake message
    (four header bytes and the body fields) fits a record of
    at most 2^14 = 16384 bytes (RFC 8446 section 5.1). -/
def WF (m : Message) : Prop :=
  m.recordVersion < 65536 ∧
  m.hello.legacyVersion < 65536 ∧
  m.hello.random.length = 32 ∧
  m.hello.sessionId.length ≤ 32 ∧
  m.hello.cipherSuites ≠ [] ∧
  (∀ v ∈ m.hello.cipherSuites, v < 65536) ∧
  m.hello.cipherSuites.length ≤ 32767 ∧
  m.hello.compressionMethods ≠ [] ∧
  (0 : UInt8) ∈ m.hello.compressionMethods ∧
  m.hello.compressionMethods.length ≤ 255 ∧
  (∀ e ∈ m.hello.extensions, ExtWF e) ∧
  List.Nodup (m.hello.extensions.map extType) ∧
  41 ∉ (m.hello.extensions.dropLast).map extType ∧
  (offersTls13 m.hello.extensions = true →
    m.hello.compressionMethods = [0]) ∧
  (printExts m.hello.extensions).length ≤ 65535 ∧
  (printBodyFields m.hello).length ≤ 16380

end ClientHello
