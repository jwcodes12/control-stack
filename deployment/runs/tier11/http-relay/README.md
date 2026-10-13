# G7: HTTP delivery as an outbox relay (2026-10-13)

`tools/http_relay.py` forwards the **receipt-verified** sink files of a broker database to a **local** HTTP destination.
It is outside the pinned trusted slice and outside the deployment claim: the claimed effect stays the local-file publication.
The relay opens the broker database read-only, requires `release_log_problems(...) == []` for the whole log, sends only releases
that have a `publication_receipts` row whose digest equals the sink file, and records acknowledgements in its own append-only
SQLite file. It never writes the broker database.

`result.json` is a run against the archived live-container evidence `containers-hardened/clean/final` (two real broker
releases and their sink bytes) with a loopback destination (`tools/http_sink.py`) that stores one copy per `Idempotency-Key`.
The first request was made to lose its acknowledgement after the bytes were stored (fault `drop_ack`):

- the relay re-sent release 1 (three requests for two releases: **at-least-once**),
- the destination stored exactly one copy per key (**idempotent effect**),
- the second relay run sent nothing (`already_acked: 2`).

What this does not show: a destination that ignores `Idempotency-Key` would receive a duplicate after a crash between the
POST and the acknowledgement record; no TLS, no authentication to the destination, and no third-party endpoint was contacted
(destinations are literal loopback unless `--allow-host` is passed). The tests are in `tools/test_http_relay.py` (9 tests: verify
before sending, tampered sink stops everything, unreceipted release not sent, lost ack retried with one stored copy, 500 / wrong
echo / redirect never acknowledged, append-only acks, broker database byte-identical, no-release-log database refused,
loopback-only destinations).
