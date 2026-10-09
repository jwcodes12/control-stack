# SC-08 supplementary receipt checker: execution-witness scope

This document applies to `scenarios/SC-08/harness/reconcile_v2.py`. It does not change the frozen v1 experiment or its checker.

The checker now requires nonempty launcher and sentinel streams. The former empty/empty success was vacuous: equality of two empty digest multisets does not establish that any execution was observed. This is a **witnessed-execution** certificate; a legitimate idle interval cannot be certified by this interface. Callers that need idle-interval certification must provide an independently authenticated interval boundary and a separately reviewed no-execution proof rather than weakening the requirement.

Synthetic negative controls cover absent launcher records, absent sentinel records, and both absent; the existing suite covers digest mismatches, missing fields, sequence gaps, nonzero exits and pin-directory mismatch. The checker assumes trusted inputs. An attacker controlling both streams can forge a matching transcript; no statement here establishes completeness of syscall interception, interpreter execution-byte identity, or OS-level enforcement.

Next bounded work: require authenticated provenance for each launcher/sentinel record; tie the receipt to a trusted execution instance and independently measured event; test forged matching streams, truncation, replay, symlink swap, same-UID file-descriptor access and inherited descriptors. Run those tests only in isolated disposable environments, preserving all preregistered evidence. For any Lean refinement, regenerate theorem registry and source-normalized catalog and run the pinned kernel with `#print axioms`.
