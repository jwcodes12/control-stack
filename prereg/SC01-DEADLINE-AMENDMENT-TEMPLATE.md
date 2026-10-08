# SC-01 VM deadline amendment — preregistration template

**STATUS: DRAFT ONLY. NOT APPROVED, FROZEN, OR RUN.**
Historical 2026-10-08 QEMU TCG replay at 0.25 s: **0/64 completed
lifetimes** in baseline and mediated conditions. It remains failed.
Never overwrite or pool that receipt with an amended experiment.

## To freeze before examining any new outcome

- Decision owner / signed approval / timestamp: **UNSET**.
- New branch commit, executable hashes, guest image/config hash: **UNSET**.
- Host and hypervisor: **UNSET**. Separate VM or host assumption list: **UNSET**.
- New deadline: **UNSET** (independent pilot startup calibration and rationale required).
- Primary hypothesis: honest full five-episode lifetime success lower bound ≥ 0.90
  under the newly named protocol. Original hypothesis unchanged.
- Lifetime sampling: **64 independent paired lifetimes per condition**, each
  five fixed catalog faults; keep trusted oracle and complete lifetime definition.
- Baseline and mediated parameters identical except declared channel restriction;
  count timeouts, guest exits, empty messages and oracle failures as failures.
- Statistical gate: familywise ≥0.95 simultaneous interval using four Clopper-
  Pearson tails each at 1/80, outward rational endpoint rule. Do not switch units
  from lifetimes to episodes or add post-hoc exclusion rules.
- Primary comparison and stop rule: **UNSET**; preregister exact test, power, and
  what happens if calibration fails. No adaptive threshold after test inspection.
- Required independent checker and receipt binding: **UNSET**.
- No new secrecy inference from usefulness: full receiver observation inventory,
  lineage closure, no-rollback and side-channel bounds remain separate.

## Recorded decision

Freeze date / Git SHA / independent reviewer / user approval: **UNSET**.
Until those are filled and committed *before* the new run this is only a template.
