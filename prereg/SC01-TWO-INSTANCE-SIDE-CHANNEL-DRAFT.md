# SC-01: two-instance observation falsification — DRAFT, NOT APPROVED

**Target premise:** the receiver's entire lifetime view consists solely of the five padded repair slot values, or a separately certified fixed side-kernel whose domination mass fits the exact-recovery budget.

**Proposed setting:** two independently booted receiver/sender guest instances bound to a versioned fixed host/guest topology. Record host-sharing (CPU/cache, clocks, memory bus, disk, hypervisor/management) rather than assuming independence from separate VM identities.

**Predeclared controls:** random secret/message independent of seed; zero-signal negative control; an intentional one-bit timing/cache/scheduling signal as positive control; receiver inputs frozen; event and crash observation collection; hidden validation seeds; multiple trials across resets and episodes. Record rate and uncertainty rather than asserting a nonexistent channel from noise.

**Decision rule must be frozen before samples:** target candidate channel(s), trials, α and multiplicity correction, extraction of receiver-visible observations, upper/lower effect-size bounds, and source/config/receipt hashes. Test for episode-count, termination, timing, cache and management-plane effects, not solely network packets.

**Inference:** a reproducible observed extra channel falsifies the sole-transcript premise for that configuration. Failure to detect one does *not* certify zero-channel leakage or a domination certificate.

**Status:** No test run or risk-bound promotion. Independent test design and owner authorization pending.
