# Closed spectral cutoff mass

The two statements in `QICLean/Analysis/SpectralCutoffMass.lean` are independently
formalized numerical consequences of the defect-mass passage in the September
24 OpenAI area-law manuscript, Section 7, lines 421–438. For a positive
semidefinite D, they prove b(I-P_b) <= D for every real b, and mass(P_b,v) >=
1-firstMoment(D,v)/b for a unit vector and b > 0. P_b is the actual closed
spectral cutoff defined by the characteristic-function calculus of D.
They do not construct the replica defect count or assert its Hamiltonian gap,
symmetry, or auxiliary-label compatibility.

The mathematical source is frozen at
`8f0020f9670356b79727bb6f23383f9c952c93a5`. Its complete file and both final
statements pass the canonical target build (3,120 jobs), strict whole-file
check, and strict kernel audit. Both reports use only `propext`,
`Classical.choice`, and `Quot.sound`. The new original-provenance shard passes
the pinned TNLean policy validator against immutable source and raw command
log bindings. Every parent production file remains unchanged.

The independent review confirms that the closed cutoff includes equality,
that the operator bound remains valid when b <= 0, and that division in the
mass estimate requires exactly b > 0. The local continuity argument is on the
finite matrix spectrum; no global continuity of the indicator is asserted.
The proof-pattern ledger records the new consumer and reuse of `cfc_le_iff`.

`strict-first-exit.json` and `strict-first.log` are preserved as exploratory
results. They predate two final formatting edits and have no immutable
whole-file binding; they are excluded from the successful final provenance.
The final checks were recaptured at the frozen revision.

`source-freeze.json`, `mathematical-review.json`, and `checks.json` record
review and source-bound evidence. The subsequent integration record completes
library and blueprint inclusion checks.
