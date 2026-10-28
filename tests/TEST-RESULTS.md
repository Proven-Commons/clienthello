# ClientHello slice: test results

- Oracle: the harness oracle in tests/run_tests.py, a second reading of SPEC.md in Python 3.13.17, for every input; and OpenSSL 3.0.13 30 Jan 2024 through Python's ssl module, which built 24 of the inputs as real ClientHellos that must be accepted and printed back byte for byte
- Seed: 20261026
- Inputs: 4939
- Failures: 0
- Command: python3 tests/run_tests.py --seed 20261026 --count 3200

## Oracles

Every verdict is settled by the harness oracle, a Python implementation of the rules in SPEC.md written for these tests. It is a second reading by the same authors, not an independent implementation. The tool must agree with it on every input, and an accepted message must print back to the oracle's canonical form byte for byte.

Python's ssl module builds real ClientHellos in memory: a client SSLObject over two MemoryBIOs writes its hello on the first do_handshake(). The run makes 24 of them with OpenSSL 3.0.13 30 Jan 2024, two under each of 12 settings (TLS 1.2 only, TLS 1.3 only, both; with and without SNI and ALPN; a cipher list, a single group, post-handshake auth). Each must be accepted and printed back unchanged. Their random bytes and key shares differ from run to run; their count and settings do not. OpenSSL is a source of real accepted inputs here, not a verdict oracle: no TLS stack is asked to judge the malformed inputs, so the verdicts on those rest on the harness oracle alone. The other fixed cases are built by hand from the RFCs.

## Counts

| part | run | agreed |
| --- | --- | --- |
| named cases | 40 | 40 |
| generated messages | 3200 | 3200 |
| mutations of the full hello | 1308 | 1308 |
| random raw byte strings | 300 | 300 |
| hellos near the 2^14 record limit | 60 | 60 |
| ClientHellos built by OpenSSL | 24 | 24 |
| malformed request lines | 7 | 7 |
| total | 4939 | 4939 |

Of the 3200 generated messages, the oracle accepts 1266 and rejects 1934.

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
- TLS 1.3 hello with compression methods 01 00: reject (60 bytes)
- TLS 1.3 hello with compression methods 00 00: reject (62 bytes)
- TLS 1.3 hello listing 0x0304 second, supported_versions [0x0303, 0x0304], with compression methods 01 00: reject (62 bytes)
- TLS 1.2 hello (supported_versions 0x0303 only) with compression methods 01 00, accepted: accept (60 bytes)
- hello without extensions, compression methods 01 00, accepted: accept (53 bytes)
- pre_shared_key last, after key_share, accepted: accept (157 bytes)
- pre_shared_key before key_share: reject (157 bytes)
- pre_shared_key first of two: reject (109 bytes)
- missing extensions block: reject (50 bytes)
- supported versions value 03 03 04 03: list length byte 3, odd: reject (60 bytes)
- supported versions value 00: list length byte 0: reject (57 bytes)
- ALPN empty name: reject (59 bytes)
- ALPN list length mismatch: reject (61 bytes)
- ALPN empty list: reject (58 bytes)
- SNI second host_name entry: reject (82 bytes)
- SNI list length mismatch: reject (72 bytes)
- SNI empty list: reject (58 bytes)
- key share empty key bytes: reject (62 bytes)
- key share empty list, accepted: accept (58 bytes)
- TLS 1.3 hello asking for a HelloRetryRequest (supported_groups, supported_versions 0x0304, empty key_share), accepted: accept (83 bytes)
- trailing garbage after the record: reject (53 bytes)
- empty extensions block, length 0, accepted: accept (52 bytes)
- record length 16384, the 2^14 limit, accepted: accept (16389 bytes)
- record length 16385, over the 2^14 limit: reject (16390 bytes)
- record length zero: reject (5 bytes)
- input shorter than the record header: reject (2 bytes)
- empty input: reject (0 bytes)

## Differences

No disagreements between the tool and the oracle, and every named case matched its stated expectation.
