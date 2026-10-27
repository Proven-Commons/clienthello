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
- The list must be nonempty and consume the value exactly.
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
