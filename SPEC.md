# Specification: clienthello

A TLS ClientHello parser and printer in Lean, following
RFC 8446 section 4.1.2 (the ClientHello message), the
legacy fields as carried from RFC 5246, RFC 6066 section 3
(the server name indication), and RFC 7301 (ALPN). This
slice reads exactly one TLS record holding exactly one
ClientHello, and prints that message back in canonical
form: every length is recomputed from the values.

## The record layer

A message is one TLS record:

| Bytes | Field |
|-------|-------|
| 0 | content type: must be 22 (handshake) |
| 1, 2 | legacy record version: carried, value unchecked |
| 3, 4 | length: two bytes, big endian, at most 2^14 = 16384 |
| 5 ... | the record body, exactly that many bytes |

- Input shorter than the five byte header rejects.
- A length above 2^14 = 16384 rejects, whatever follows.
  RFC 8446 section 5.1 says the length "MUST NOT exceed
  2^14 bytes" and that a receiver answers a longer record
  with a record_overflow alert.
- A body shorter than the declared length rejects.
- Bytes after the record reject. The decoder takes exactly
  one record; a stream reader is later work.
- A record length of 0 rejects: an empty body cannot hold
  a ClientHello. (In the code this falls out of the body
  read failing; it is stated here because it is a rule a
  reader of the bytes should expect.)

## The handshake header

Inside the record body:

| Bytes | Field |
|-------|-------|
| 0 | message type: must be 1 (client_hello) |
| 1, 2, 3 | length: three bytes, big endian |
| 4 ... | the ClientHello body |

The three byte length must equal the remaining body length
exactly. A mismatch rejects.

## The ClientHello body

In order:

| Field | Size | Rule |
|-------|------|------|
| legacy version | 2 bytes | carried, value unchecked |
| random | 32 bytes | exactly 32 |
| legacy session id | 1 byte length, then that many bytes | length at most 32; a longer length rejects |
| cipher suites | 2 byte length, then that many bytes | length even and at least 2; the bytes read as two byte suite codes; an empty list or an odd length rejects |
| legacy compression methods | 1 byte length, then that many bytes | length at least 1; the list must contain the byte 0 (the null method); in a hello that offers TLS 1.3 it must be exactly the one byte 0 |
| extensions | 2 byte length, then that many bytes | the block must consume the rest of the body exactly |

Compression methods. RFC 5246 section 7.4.1.2 says the
list "MUST contain" the null method, so a list without the
byte 0 rejects. A hello offers TLS 1.3 when it has a
supported_versions extension that lists 0x0304. RFC 8446
section 4.1.2 says that for every TLS 1.3 ClientHello the
list "MUST contain exactly one byte, set to zero", and that
a server must abort otherwise, so a hello that offers TLS
1.3 with any other list rejects: [1, 0] and [0, 0] both
reject. A hello that does not offer TLS 1.3 may list other
methods besides 0.

The extensions block must be present. A body that ends
after the compression methods is the pre-TLS-1.3 shape;
this slice rejects it, because the slice frames the
message by its extensions and supported_versions is how a
TLS 1.3 hello speaks. The block may be empty: a present
block of length 0 consumes the body and carries no
extensions, and is accepted.

## Extensions

Each extension is a two byte type, a two byte length, and
that many value bytes. An extension length running past
the end of the block rejects, and the block must be
consumed exactly. A duplicate extension type rejects.

pre_shared_key (type 41), when present, must be the last
extension. RFC 8446 section 4.2 says it "MUST be the last
extension in the ClientHello", and section 4.2.11 says
servers "MUST check that it is the last extension", so a
block in which type 41 stands anywhere but last rejects.
Its value is carried opaque, like every type not decoded
below.

Four types are decoded. Every other type is carried as
the pair of its type and its raw value bytes, length
checked, not interpreted.

### server_name (type 0), RFC 6066 section 3

The value is a two byte list length covering the rest of
the value, then entries. Each entry is a one byte name
type, a two byte length, and that many bytes. Type 0 is
host_name.

- The list length must equal the value length minus two.
- The list must be nonempty and consume the value exactly.
- Two entries of the same type reject, so there is at
  most one host_name entry.
- The host_name bytes must be nonempty.
- Host name bytes are carried as bytes. No case folding,
  label, or character validation happens in this slice.
  Entries of other types are carried as (type, bytes).

### ALPN (type 16), RFC 7301

The value is a two byte list length covering the rest of
the value, then protocol names. Each name is a one byte
length and that many bytes.

- The list length must equal the value length minus two.
- The list must be nonempty and consume the value exactly.
- A name length of 0 rejects.

### supported_versions (type 43), RFC 8446 section 4.2.1

The client form: a one byte length, then that many bytes
read as two byte versions.

- The length must equal the value length minus one.
- The length must be even and at least 2. An odd or zero
  length rejects.

The server form (a single version) is not this message and
is not read here.

### key_share (type 51), RFC 8446 section 4.2.8

The client form: a two byte list length covering the rest
of the value, then entries. Each entry is a two byte
group, a two byte key exchange length, and that many
bytes.

- The list length must equal the value length minus two.
- The entries must consume the value exactly.
- The list may be empty. RFC 8446 section 4.2.8 says the
  client_shares vector "MAY be empty", which a client does
  to ask for a HelloRetryRequest, so an empty list is
  accepted.
- A key exchange length of 0 rejects.
- A duplicate group rejects.

## Pinned readings

Where the RFCs or the plan leave a reading open, this
slice pins it:

- Trailing bytes after the record reject.
- A missing extensions block rejects; a present block of
  length 0 is accepted.
- A hello offers TLS 1.3 exactly when its
  supported_versions lists 0x0304; draft version numbers
  such as 0x7F1C do not count. Only such a hello must have
  the compression methods [0].
- The session id length is at most 32.
- The cipher suite list is nonempty, with an even byte
  length.
- A duplicate extension type rejects.
- SNI carries at most one host_name entry, and duplicate
  SNI entry types reject in general.
- Host name bytes are unvalidated beyond being nonempty.
- Unknown extension types are carried opaque.
- A duplicate key share group rejects.

## Properties and their theorems

Each property a reader can check in the page (`README.md`)
names its theorem. The theorems are stated in `Spec.lean`
and proved in `Proofs/SpecProofs.lean`. The example
theorems are single inputs; the tests in `tests/` cover
each rule on many more inputs.

Statements about every input:

| Property | Theorem |
|-------|---------|
| Parsing the printed form of a well formed message gives the message back. | `Spec.parse_print` |
| Printing a message the parser took gives the same bytes it was read from, and the message is well formed. | `Spec.print_parse` |
| A record whose length field is above 2^14 = 16384 is refused, whatever else the input holds. | `Spec.rejects_record_overflow` |
| Every accepted hello with a supported_versions extension that lists 0x0304, in any position (a hello that offers TLS 1.3), has exactly the compression methods [0]. | `Spec.tls13_compression_null` |
| In every accepted hello, no extension but the last has type 41: pre_shared_key, when present, is the last extension. | `Spec.psk_last` |

Single inputs, each about the one input written out in
`Spec.lean`. Most refused inputs are an accepted input with
one field changed, so that the field's rule is what refuses
it:

| Property | Theorem |
|-------|---------|
| A 52-byte hello with a present, empty extensions block is accepted and writes back as the same bytes. | `Spec.accepts_empty_extensions` |
| A 61-byte hello whose one extension is supported_versions [0x0304, 0x0303] is accepted and writes back as the same bytes. | `Spec.accepts_supported_versions` |
| An 83-byte TLS 1.3 hello whose key_share carries no entries, the form a client uses to ask for a HelloRetryRequest, is accepted and writes back as the same bytes. | `Spec.accepts_key_share_empty_list` |
| The hello of `Spec.accepts_empty_extensions` with compression methods [1, 0] is accepted and writes back as the same bytes: it does not offer TLS 1.3, so methods besides null may be listed. | `Spec.accepts_tls12_compression` |
| A hello whose extensions are supported_versions and then pre_shared_key is accepted and writes back as the same bytes. | `Spec.accepts_psk_last` |
| Empty input is refused. | `Spec.rejects_empty` |
| A 2-byte input, shorter than the record header, is refused. | `Spec.rejects_short_header` |
| A record header with length 0 and nothing after it is refused. | `Spec.rejects_record_length_zero` |
| The hello of `Spec.accepts_supported_versions` with content type 23 in place of 22 is refused. | `Spec.rejects_content_type` |
| A record whose length field (10) is longer than the 4 bytes that follow is refused. | `Spec.rejects_record_length_longer` |
| The hello of `Spec.accepts_empty_extensions` with one byte after the record is refused. | `Spec.rejects_trailing_bytes` |
| The hello of `Spec.accepts_supported_versions` with handshake type 2 in place of 1 is refused. | `Spec.rejects_handshake_type` |
| The hello of `Spec.accepts_empty_extensions` with a handshake length one more than the body holds is refused. | `Spec.rejects_handshake_length` |
| The hello of `Spec.accepts_empty_extensions` without its extensions block, ending after the compression methods, is refused. | `Spec.rejects_missing_extensions` |
| The hello of `Spec.accepts_supported_versions` with a 33-byte session id is refused. | `Spec.rejects_session_id_33` |
| The hello of `Spec.accepts_supported_versions` with a 3-byte cipher suite list is refused. | `Spec.rejects_odd_cipher_suites` |
| The hello of `Spec.accepts_supported_versions` with an empty cipher suite list is refused. | `Spec.rejects_empty_cipher_suites` |
| The hello of `Spec.accepts_empty_extensions` with compression methods [1], without the null method, is refused. | `Spec.rejects_compression_without_null` |
| The hello of `Spec.accepts_empty_extensions` with an empty compression method list is refused. (An empty list holds no null method, so the rule above refuses it too.) | `Spec.rejects_empty_compression` |
| The hello of `Spec.accepts_supported_versions`, which offers TLS 1.3, with compression methods [1, 0] is refused. | `Spec.rejects_tls13_compression` |
| The input of `Spec.rejects_tls13_compression` with its supported_versions list in the other order, [0x0303, 0x0304], is refused. | `Spec.rejects_tls13_compression_second` |
| A hello with two supported_versions extensions is refused. | `Spec.rejects_duplicate_extension` |
| The hello of `Spec.accepts_psk_last` with its two extensions in the other order, pre_shared_key first, is refused. | `Spec.rejects_psk_not_last` |
| A hello whose one extension declares 10 value bytes where its block holds 3 is refused. | `Spec.rejects_extension_overrun` |
| A hello whose key_share carries two entries for group 29 is refused. | `Spec.rejects_duplicate_key_share_group` |
| A hello whose key_share entry has empty key exchange bytes is refused. | `Spec.rejects_key_share_empty_key` |
| A hello whose supported_versions value has the odd length 3 is refused. | `Spec.rejects_supported_versions_odd` |
| A hello whose supported_versions value has length 0 is refused. | `Spec.rejects_supported_versions_zero` |
| A hello whose ALPN value holds one protocol name of length 0 is refused. | `Spec.rejects_alpn_empty_name` |
| A hello whose server_name value holds two host_name entries is refused. | `Spec.rejects_sni_second_host_name` |
| A hello whose server_name list length (99) does not cover the rest of the value is refused. | `Spec.rejects_sni_list_length` |

## Reading past the end

No theorem says the parser never reads past the end of its
input, and this page does not claim it as proved. In the
Lean model the input is a list and every reader is a total
function on lists, so there is no out of bounds read to
rule out: a field read from input too short for it gives
`none`, and the parser refuses. The extension parsers run
over a value already cut to its declared length. What the
theorems do say about the bytes is `Spec.print_parse`:
every byte of an accepted input is accounted for, since
the parsed message prints back to exactly that input.
Lengths that run past the input are refused in the cases
of `Spec.rejects_record_length_longer` and
`Spec.rejects_extension_overrun`, and the tests cover
more.

## Slice boundaries

- No server messages: no ServerHello, no EncryptedExtensions,
  no Certificate, no Finished.
- No handshake crypto: no key schedule, no transcript hash,
  no signature checking.
- No rules that tie one extension to another beyond those
  above. For example, the slice does not check that a
  pre_shared_key comes with psk_key_exchange_modes (RFC
  8446 section 4.2.9), or that each key share's group is
  offered in supported_groups (section 4.2.8).
- No certificate work of any kind, and no matching of the
  server name against a certificate. That matching belongs
  to the hostname work; this slice only carries the name
  bytes out of the message.
- One record only: no stream reading, no record splitting
  or joining, no alerts, no renegotiation. RFC 8446 section
  5.1 lets a sender split a handshake message across
  records; such a hello is refused here, since its first
  record does not hold the whole message. A hello whose
  handshake message is longer than 16384 bytes cannot fit
  one record, so this slice refuses it.
