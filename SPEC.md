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
| 3, 4 | length: two bytes, big endian |
| 5 ... | the record body, exactly that many bytes |

- Input shorter than the five byte header rejects.
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
| legacy compression methods | 1 byte length, then that many bytes | length at least 1; the list must contain the byte 0 (the null method) |
| extensions | 2 byte length, then that many bytes | the block must consume the rest of the body exactly |

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
- Compression methods must contain the byte 0.
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

| Property | Theorem |
|----------|---------|
| Parsing the printed form of a well formed message gives the message back | `Spec.parse_print` |
| A message the parser took prints back to the bytes it was read from, and is well formed | `Spec.print_parse` |
| A present, empty extensions block is accepted | `Spec.accepts_empty_extensions` |
| A minimal hello with only supported_versions is accepted | `Spec.accepts_supported_versions` |
| A TLS 1.3 hello whose key_share carries no entries, as a client asking for a HelloRetryRequest sends it, is accepted | `Spec.accepts_key_share_empty_list` |
| Empty input is refused | `Spec.rejects_empty` |
| Input shorter than the record header is refused | `Spec.rejects_short_header` |
| A record length of 0 is refused | `Spec.rejects_record_length_zero` |
| A content type other than 22 is refused | `Spec.rejects_content_type` |
| A record length longer than the input is refused | `Spec.rejects_record_length_longer` |
| Bytes after the record are refused | `Spec.rejects_trailing_bytes` |
| A handshake type other than 1 is refused | `Spec.rejects_handshake_type` |
| A handshake length that does not match the body is refused | `Spec.rejects_handshake_length` |
| A body with no extensions block is refused | `Spec.rejects_missing_extensions` |
| A session id length over 32 is refused | `Spec.rejects_session_id_33` |
| A cipher suite list with an odd byte length is refused | `Spec.rejects_odd_cipher_suites` |
| An empty cipher suite list is refused | `Spec.rejects_empty_cipher_suites` |
| Compression methods must contain the null method 0 | `Spec.rejects_compression_without_null` |
| An empty compression method list is refused | `Spec.rejects_empty_compression` |
| A duplicate extension type is refused | `Spec.rejects_duplicate_extension` |
| An extension length running past the block is refused | `Spec.rejects_extension_overrun` |
| A duplicate key share group is refused | `Spec.rejects_duplicate_key_share_group` |
| A key share entry with empty key bytes is refused | `Spec.rejects_key_share_empty_key` |
| A supported_versions value with an odd length is refused | `Spec.rejects_supported_versions_odd` |
| A supported_versions value with length 0 is refused | `Spec.rejects_supported_versions_zero` |
| An ALPN value with an empty protocol name is refused | `Spec.rejects_alpn_empty_name` |
| A server_name value with two host_name entries is refused | `Spec.rejects_sni_second_host_name` |
| A server_name list length that does not cover the value is refused | `Spec.rejects_sni_list_length` |

## Safety

The parser never reads past the end of its input. Every
read goes through the length checked readers (getU8,
getU16, getU24, getBytes): a read either takes bytes that
are present, checked against the remaining length, or
fails. The extension parsers run over a value already cut
to its declared length, so the same check bounds them.
This is the reader model used across the sibling slices.

## Slice boundaries

- No server messages: no ServerHello, no EncryptedExtensions,
  no Certificate, no Finished.
- No handshake crypto: no key schedule, no transcript hash,
  no signature checking.
- No certificate work of any kind, and no matching of the
  server name against a certificate. That matching belongs
  to the hostname work; this slice only carries the name
  bytes out of the message.
- One record only: no stream reading, no record splitting
  or joining, no alerts, no renegotiation.
