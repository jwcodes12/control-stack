# One two-agent local-file assurance case

The fixtures pin the offline imported image by its immutable Docker content ID in
`image-pin.json`. Its broker/receiver sources and experiment entry point are baked
in, with source hashes and an import archive hash. `clean.compose.json` was run as
real containers, then scanned with inventory captured from `docker inspect`.
The matching archive is in `deployment-evidence/containers/clean`. The daemon is a
trusted source, not independent attestation. Other `.runtime.json` files here are
synthetic static controls, including configurations that must never be launched.

The experiment removed its image, containers, network and scratch directories.
To reproduce offline, first import the existing local rootfs using
`python3 tools/build_deployment_container_image.py --output <build-directory>`.
Copy the generated image/source manifest to `image-pin.json`, retain its declared
`host_root` inside your clone, regenerate with `tools/build_deployment_fixtures.py`,
then run `tools/run_deployment_containers.py --output <new-evidence-directory>`.
The harness only launches clean, writable-sink and UID-collision cases, prepares
private directories, uses `docker compose up --pull never`, captures daemon facts,
and reads sink files independently. Remove the imported image with `docker image
rm <image-id>` afterward. Never launch runtime-socket, privileged or host-network
fixtures. These are static negative controls.

Run the complete static scan/verify/report matrix:

```sh
lake build ControlStack.Deployment.Contracts
python3 tools/run_deployment_matrix.py --output /tmp/slice-matrix --lean
python3 tools/cstack.py check --fast --only deployment
python3 tools/check_deployment_container_evidence.py deployment-evidence/containers
```

Exit codes: scan/report 0 on valid output; verify 0 for CONDITIONAL, 1 for
UNASSURED; all commands 2 on invalid input, mismatched pins or unavailable requested
kernel checking. **Without `--lean`, verification always yields UNASSURED**.
Lean checks a documented strict subset; Python-only checks remain necessary.
Bundles list both sets and retain separate faithful-extraction and full protocol
refinement premises. The 200 seeded differential mutations intentionally disclose
75 subset differences; those configurations are UNASSURED through Python checks.

The real-container result covers mounts and UIDs under Docker defaults. Landlock
is inactive here. A writable mount still needs writable DAC permissions to allow
the demonstrated direct write; the mutation explicitly records mode 0777. A UID
collision grants the agent admin HALT authority through the socket; no direct sink
write is claimed for a container without a sink mount.
