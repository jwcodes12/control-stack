# Read-only remediation planner

`python3 tools/cstack.py plan COMPOSE.json --runtime RUNTIME.json --ir IR.json --output PLAN.json`

The JSON output contains RFC 6902 operations and a redacted unified human diff.
It never edits its inputs. Apply the operations to a copy with
`deployment.plan.apply_patch`; review every change before recreating a deployment.
For schema 0.1, supply the saved fresh scan inputs with `--inputs` when their
location cannot be inferred. The planner replays the pinned observations before
planning; migration alone does not supply missing observations.

The supported proposal is the known six-service reference profile. It drops
unlisted mounts, unsupported configuration fields and unlisted environment
credentials, separates the known numeric principals and restores declared private
store mounts. Image bytes, measured runtime facts and missing trusted services
are never invented. An unsupported read-only root filesystem restriction is
retained and named. Host custody changes are separate `host_actions`, never JSON
Patch operations; system/code directories and missing trusted principals cannot
receive an ownership proposal. This command never executes host actions.

Plans carry the raw Compose hash and IR hash. A plan itself has no CONDITIONAL
verdict. Recreate only a supported, reviewed own deployment, recollect and run a
fresh scan and kernel verification. Existing runtime drift, image correspondence,
missing observations and host custody remain explicit residuals until measured.

`python3 tools/test_deployment_plan.py` checks all 44 static fixtures, input
immutability, redaction, pointer escaping, pin rejection and archived fresh inputs.
`python3 tools/check_deployment_plans.py` checks the prospective finite model in
Lean: 44 certificates, 36 accepted projections and eight precise residual cases.
The prospective inventory is explicitly DECLARED, never an actual runtime capture.
The original live negatives are archived Tier 2 evidence. John’s defensive-only
continuation permits only remediated live configurations; no original bypass rerun.

Archived inputs may be relocated. Local sibling inputs are preferred; only known source labels with matching file hashes are normalized for replay comparison. Modifying the pinned observation bytes is rejected. The original raw failure and corrected six-test result are retained under deployment/runs/tier5.
