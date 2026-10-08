# SC-13 correspondence (not fully established)

| Axis / premise | Proposed concrete enforcement | Evidence or limitation | Current status |
|---|---|---|---|
| proof | When every workflow effect is dispatched by an independent gate, a trusted audit record precedes dispatch. | Existing Lean theorem checks reported in legacy manifest; not executed by lint. | historical |
| evidence | Dispatcher-first SQL audit transaction; does not cover external completion | Historical evidence is referenced, not independently reexecuted. | historical |
| applicability | Whole-environment refinement and bypass inventory required | Exclusive trusted dispatcher, credential separation and exactly-once external effects not established. | unresolved |
| usefulness | Freeze approved honest tasks and acceptance floor | Honest usefulness requires task-specific measurement, not a generic proof. | unresolved |

The matcher of a formal action/observation to a real effect must identify every entrypoint, deputy, inherited capability and persistence path. Missing paths remain assumptions, never automatically tested by a proof.
