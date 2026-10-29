# Conditional sampling between two improving targets

This bounded QICLean contribution is based on checked standalone common
`f66483f26612b978ddac2028452e5efe610e7a82`. It proves
`Submodule.exists_isViable_nested_randomSubspace_finrank_le_half`.
It does not prove the physical low-density bootstrap or its count/suppression
calibration.

The theorem takes two explicit 1/200 comparisons, from the original upper
target to the upper improving target and from the lower improving target to
the original lower target. A fixed family of D^2 actual linear operators is
chosen before the input W; its improving implication is an explicit premise.
For 4D^2<=p<=dim W, the sample size is the NATURAL quotient p/(2D^2).
The theorem constructs a literal successful unitary and the existing actual
Haar-coordinate sample of W, with exact sample dimension s and inclusion in W.
Its actual operator-image span has dimension at most p/2, also natural division.
No image-dimension oracle, replacement sample, or independently chosen output
subspace occurs.

The input's 3/200 error is transferred to the upper improving target before
sampling, giving 1/25. The sampled overlap alpha is positive, and its corrected
complex-sphere failure bound is a stated hypothesis. Improvement is applied to
that same actual sample before returning to the original lower target. The
exact final error is 2(Delta/alpha^2+1/200). The separate explicit premise
Delta/alpha^2<=1/400 gives the final 3/200 error. The small-p branch belongs to
the later physical dimension-threshold argument; no zero sample is used here.

The proof reuses the existing subspace, closeness, Haar-coordinate sampling,
finite-image and dimension APIs. It adds no competing definitions, tactics,
compatibility aliases or source hypotheses hidden in a physical theorem.
The existing bootstrap gap note records the strict-decrease correction in
source lines1115/1125, the .15/.015 typo and the inconsistent logarithmic power
as local repairs. Its pre-existing region restriction remains unchanged.
The physical coupled count and suppression estimate remains explicitly open:
padding the operator count does not by itself preserve D^12 Delta.

## Verification

The actual named production module passed the strict private runner with
implicit variables disabled, Mathlib standard linters and warnings as errors.
Time:10.141seconds. The exact source SHA256 is
`c0aa42cadadb0e7edaec6ee082a81b79fd59d5bcced19f3fc8b9de5e68f0ded6`.
All13 transitive QICLean source/object pairs, the module source, build inputs
and Mathlib sentinel were hashed before and after the check. The imported
foundation inspection included the new module as the14th pair and reports
only propext, Classical.choice and Quot.sound. Its strict run passed in15.170s.

Source blueprint synchronization, newly added prose and whitespace checks pass.
The pattern scan used the existing TNLean scanner read-only on QICLean because
QICLean has no copy of that script; the relevant two-occurrence composition is
recorded in the ledger. The sole new public theorem has a matching blueprint
entry with all conditional premises. No permanent inspection/test fixture is
included; manual commands and objects remain under /tmp.

The source-only worktree has no .lake. No provider source, package, cache or
object was changed or copied. No ordinary build or Mathlib source build was
started. The strict command used only standalone QICLean f664 artifacts; it did
not depend on the simultaneously advancing TNLean package. Ordinary/full-library
checks and compiled-blueprint/timing gates remain integration obligations.

Evidence:
- /tmp/qiclean-alvv-nested-sampling-final-check.log
- /tmp/qiclean-alvv-nested-sampling-foundation-audit.log
- /tmp/qiclean-alvv-nested-sampling-20261029/ViableSubspaceNestedSampling-guards.json
- /tmp/qiclean-alvv-nested-sampling-20261029/NestedSamplingAudit-guards.json
- /tmp/qiclean-alvv-nested-sampling-blueprint-sync.json
- /tmp/qiclean-alvv-two-target-sampling-draft-20261029.md

The early incremental checks intentionally stopped at unresolved goals while
constructing the proof. A natural sample-size annotation and one final line-wrap
were corrected before the completed strict check. No unresolved goal, proof hole
or debug command remains in the production module.
