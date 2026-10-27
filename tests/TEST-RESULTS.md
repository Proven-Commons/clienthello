# ClientHello slice: test results

Run: python3 tests/run_tests.py --seed 20261026 --count 3200
Seed: 20261026. Python 3.12.3.

## Oracles

Every verdict is settled by the harness oracle, a Python implementation of the rules in SPEC.md written for these tests. The tool must agree with the oracle on every input, and an accepted message must reprint to the oracle's canonical reprint byte for byte.

Python's ssl module cannot build a ClientHello on demand. Go is not installed (`go version` fails). Scapy 2.8.0 is present in the sibling dhcp project's venv and its TLS submodules import, but building or dissecting a TLS record raises NameError inside scapy's crypto support (HMAC is not defined), so Scapy could not be used as a byte source. No capture was fetched; the fixed cases are built by hand from the RFCs.

## Counts

| part | run | agreed |
| --- | --- | --- |
| named cases | 29 | 29 |
| generated messages | 3200 | 3200 |
| mutations of the full hello | 1308 | 1308 |
| random raw byte strings | 300 | 300 |
| malformed request lines | 7 | 7 |
| total | 4844 | 4844 |

Of the 3200 generated messages, the oracle accepts 1125 and rejects 2075.

## Named cases

- full TLS 1.3 style hello: accept (252 bytes)
- minimal hello, supported versions only: accept (61 bytes)
- duplicate extension type: reject (66 bytes)
- duplicate key share group: reject (130 bytes)
- extension length overrunning the block: reject (59 bytes)
- record length longer than the input: reject (52 bytes)
- handshake length not matching the body: reject (52 bytes)
- content type 23: reject (61 bytes)
- handshake type 2: reject (61 bytes)
- session id length 33: reject (85 bytes)
- odd cipher suite length: reject (53 bytes)
- empty cipher suites: reject (50 bytes)
- compression methods without 0: reject (53 bytes)
- missing extensions block: reject (50 bytes)
- supported versions odd length: reject (60 bytes)
- supported versions length zero: reject (57 bytes)
- ALPN empty name: reject (59 bytes)
- ALPN list length mismatch: reject (61 bytes)
- ALPN empty list: reject (58 bytes)
- SNI second host_name entry: reject (82 bytes)
- SNI list length mismatch: reject (72 bytes)
- SNI empty list: reject (58 bytes)
- key share empty key bytes: reject (62 bytes)
- key share empty list: reject (58 bytes)
- trailing garbage after the record: reject (53 bytes)
- empty extensions block, length 0, accepted: accept (52 bytes)
- record length zero: reject (5 bytes)
- input shorter than the record header: reject (2 bytes)
- empty input: reject (0 bytes)

## Differences

No disagreements between the tool and the oracle, and every named case matched its stated expectation.
