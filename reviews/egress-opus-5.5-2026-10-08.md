# Opus 5.5 SC-03 review (approved source transmission)

Static review of the prepared earlier snapshot; no tools ran. Subsequent fixes and dispositions are in egress/REVIEW-DISPOSITIONS.md. The first bare-profile attempt reported not logged in; the authenticated-profile attempt succeeded. No classifier refusal occurred.

# SC-03 egress slice: independent review

**Scope.** I didn't run any tools or edit any files. This is a static read of the files you pasted, and it doesn't repeat Astra's four findings. I didn't see `attacks.py`, `sandbox_entry.py` or `usefulness.py`, so anything that depends on them is marked as an inference.

## Findings

**F1 (high): the shared-net mutation check never tests the outside packet observer.**
- With `--share-net`, the in-sandbox validator sees that the sandbox is using the host's network namespace. It fails before `tcp4` runs (assuming `sandbox_entry.py` runs the validator before attack cases, as the validator's docstring says).
- The `mutation-detected` condition accepts either `forbidden host packet` or the validator message `topology rejected: host namespace reused` in stderr.
- So the check passes because of the in-sandbox validator, and the observer never sees a packet. Nothing shows that the external observer can catch a real breach.

**F2 (high): a direct connection to the allowed mirror would be counted as allowed.**
- The suite labels packets as allowed or forbidden using only destination address, port and protocol, checked against the two pinned mirror peers.
- If the sandbox broke out and connected straight to `127.77.0.1:<mirror.port>`, skipping the gateway, those packets would be labelled allowed.
- The source address looks the same on loopback, so it can't tell them apart.
- For `deny` cases, `verdict` only checks for mirror traffic when the case is a request case, and the other evidence is `report['violation']`, which the attacker code writes itself.
- This is the most important bypass in a pinned-peer claim, and right now nothing can catch it.

**F3 (medium): the observer only watches some destinations.**
- It listens on `lo` only and keeps packets to `127.77.0.0/16`, plus `::1` on the designated ports.
- If the sandbox broke out, traffic to `127.0.0.1:*`, the host's own addresses, other `::1` ports, or anything leaving through a real interface would never be recorded.
- "Fixture-scoped" is fine, but the artifact should say exactly which packets were watched. Running the harness inside a throwaway outer network namespace would make "every packet is ours" true, so you could record everything with no filter.

**F4 (medium): the file-descriptor check only looks at one process.**
- `validate()` only checks `/proc/self/fd`.
- The `startup-inherited-socket` test shows that bwrap passes open descriptors through. bwrap's own init process (PID 1 inside the sandbox) probably still holds them too.
- Fix: check `/proc/[0-9]*/fd` for every process in the sandbox's process namespace.

**F5 (low–medium): the deny verdict is too weak.**
- It doesn't require a matching `deny` record from the gateway.
- It doesn't require that there are zero `allow`/`connected` records in that case's window.
- A gateway that logs `allow` and then fails to connect would still pass.

**F6 (low): parser and gateway edge cases.**
- For `CONNECT`, the Host check uses default port 80. So `CONNECT mirror.internal:443` with `Host: mirror.internal` is rejected (affects usefulness).
- If an exception happens after `200 Connection Established` has been sent, the gateway can then write a `403` into the open tunnel.
- The `secret-*` check only looks at `observed[0]` (the plaintext mirror). A secret sent through the TLS tunnel would land at `tls_mirror` and fail the check, so that counterexample isn't covered.
- The observer misreads ports on IPv6 packets with extension headers and on non-first IPv4 fragments, and the `::1` port filter drops them.

**What looks right:**
- The gateway's permit decision comes before it opens any socket, and only numeric pinned addresses ever get connected to.
- It checks the connected peer's address after connecting.
- An invalid policy stops startup before the socket is bound.
- `--unshare-all`, `--cap-drop ALL` and no-new-privileges are all set.
- The observer is checked against failed handshakes and UDP before the run.
- Abstract-socket and host-socket decoys are in place.
- The honest request is re-run after each attack, so a DoS case can't hide later failures.
- For this claim, the namespace setup looks sound.

## Single highest-value next step: test that the outside observer alone can catch a breach (fixes F1 and F2)

1. **Have the gateway log its local address and port** in the `connected` event (from `upstream.get_extra_info('sockname')`).
2. **Add a rule to the verdict:** every SYN to a pinned peer must match a gateway `connected` record by full address and port pair. Any SYN without a match is a bypass. This requires decoding TCP flags in the observer.
3. **Add a test-only mutation mode** that shares the host network *and* sets the validator to report-only. Then run at least these cases:
   - `tcp4` to the denied peer
   - a direct raw TCP connection to the pinned mirror, skipping the gateway
   - an unmonitored destination such as `127.0.0.1` (this is what F3 is about)
4. **Pass only if the packet observer alone flags each case,** with no credit from the validator or from the attacker's own report.

Why this one: right now the claim only holds if the sandbox setup is correct, which the in-sandbox validator checks for itself. The outside observer is meant to back that up independently, and there's currently no evidence it would see a direct-to-mirror breach. That's the R10 goal of making the claim falsifiable.
