# Full acceptance is not monotone under the requested edge removal

T4.2 as stated cannot be proved. In all three kernel-checked countermodels,
`clean` is Accepted, the node list and protected-resource bindings are unchanged,
the smaller edge list is a subset, and receiver-to-sink remains. Removing both DB
writers, only the broker DB writer, or only the receiver DB writer makes the smaller
IR fail the required shared-database usefulness witnesses. Exact statements are
`requested_monotonicity_counterexample`, `missing_broker_writer_counterexample`
and `missing_receiver_writer_counterexample` in R2Contracts.lean.

The full acceptance rules remain intact. Their useful positive witnesses cannot
be dropped solely to make this requested theorem true. The literal task is BLOCKED
by these checked counterexamples, rather than by unavailable resources.

The safety property does have a monotonic proof: `path_edge_subset` transfers every
path avoiding broker/receiver to a graph containing its edges, and
`accepted_path_safety_monotone` excludes sink/DB paths in the smaller graph when the
larger is Accepted. Node lists and broker/receiver/sink/database bindings are fixed.
`accepted_no_avoided_path` proves reachability soundness from the finite closure
certificate. These are universal graph theorems, separate from seeded Python tests.
