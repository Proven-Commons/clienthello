/-
  What a well formed message is: the one definition the statements in
  `ClientHello/Spec.lean` use besides the code under proof.

  This file is part of the specification. `bar.toml` lists it among the
  spec files, so a reviewer approves it with `ClientHello/Spec.lean` and `SPEC.md`,
  and the approval hash pins it. `ClientHello.Spec.parse_print` and
  `ClientHello.Spec.print_parse` take their meaning from `ClientHello.Spec.WF`: together they
  say the parser accepts exactly the printed forms of the messages
  `ClientHello.Spec.WF` describes. If the predicate sat in the code, a change to the
  parser together with the same change to the predicate would leave
  every statement true and the hash unchanged.

  It reads the data model and the printer of `ClientHello/Value.lean`
  (the types, `extType`, and the lengths of printed blocks), which are
  code under proof, and nothing of the parser.
-/

import ClientHello.Value

namespace ClientHello.Spec

open ClientHello

/-- Well formedness of one extension, at the level the
    printer needs: every length it writes fits the field that
    holds it, and the rules `SPEC.md` gives for the value
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
    hello with a supported_versions extension that lists
    0x0304 (772), that is one that offers TLS 1.3, carries
    exactly the null compression method (RFC 8446 section
    4.1.2), and the handshake message (four header bytes and
    the body fields) fits a record of at most 2^14 = 16384
    bytes (RFC 8446 section 5.1). -/
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
  (∀ vs, Extension.supportedVersions vs ∈ m.hello.extensions →
    772 ∈ vs → m.hello.compressionMethods = [0]) ∧
  (printExts m.hello.extensions).length ≤ 65535 ∧
  (printBodyFields m.hello).length ≤ 16380

end ClientHello.Spec
