Tier 11 (source generation r2-v8): persisted release log, observed-hash publication receipts, per-agent staging quota,
bounded receiver lock retry. Run 2026-10-13 on the box (OL 9.8 aarch64, Docker 29.8, SELinux enforcing), from a normal clone.

Environment needed in the invoking shell (attempts 1 and 2 failed for lack of it; see attempt*-NOTE.txt):
  export PATH=$HOME/.elan/bin:/usr/sbin:/sbin:$PATH      # lake for the kernel checks, getenforce for the SELinux capture

Commands (repo root; each image is removed by its harness; resources use the cstack-r2- prefix):
  python3 deployment/pins.py snapshot r2-v8 && python3 tools/build_deployment_fixtures.py &&
    python3 deployment/pins.py vault-templates && python3 tools/build_deployment_golden.py     # the pins recipe
  python3 tools/build_deployment_container_image.py --output deployment/runs/tier11/build --tag cstack-r2-v8:offline
  python3 deployment/run_containers.py --output deployment/runs/tier11/containers-hardened \
      --pin deployment/runs/tier11/build/image-pin.json --hardened          # 5 safe cases, PASS, 2m55s
  python3 deployment/check_container_run.py deployment/runs/tier11/containers-hardened   # independent check, reads release_log
  python3 tools/cstack.py demo --output deployment/runs/tier11/demo-dev-clone           # PASS, 1m05s
  python3 deployment/check_remediated.py deployment/runs/tier11/demo-dev-clone/remediated

Docker afterwards: only postgres:16-alpine and the unrelated crafty-controller container.
No bypass case (writable sink, role-UID collision) was launched live: defensive scope. Failed attempts are kept.
Not independent attestation: the daemon inventory, the receiver's own hash and the sink bytes are read by checkers that
trust the daemon and the receiver (TCB). No independent human review.
