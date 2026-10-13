Attempt 1 (kept as evidence): rootfs = stock `ubuntu:24.04` + `apt-get install python3`. The fresh scan on GitHub-hosted Ubuntu 24.04 x86-64
returned UNASSURED for the `clean` case (runtime snapshots all MATCH, but `image-python-startup-hooks` and `image-setuid-setgid-binaries` are
UNASSESSED for every service; the Lean kernel check is REFUTED on that configuration), so `run_containers.py` stopped at its CONDITIONAL
assertion before launching any agent. The scanner is doing its job: a general-purpose image carries setuid binaries and `.pth` startup hooks that the
minimal reference rootfs of the primary host does not. Attempt 2 removes both classes from the rootfs before importing it (see the workflow).
