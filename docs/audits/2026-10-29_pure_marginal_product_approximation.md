# Product approximation from an actual nearly pure marginal

The public `Matrix.exists_unit_product_approx_of_pure_marginal` takes a unit bipartite
Euclidean vector Ω, a prescribed unit system vector φ, and the full nuclear-norm bound
on the actual marginal tr_E |Ω><Ω| − |φ><φ|. It derives a unit environment vector η
in the unchanged environment space with Euclidean distance at most sqrt(2 ε).
There is no environment-dimension requirement or strict upper bound on ε.

The coefficient row a=φ†C is derived from the actual vector. Its squared norm p is
tr(|φ><φ|ρ). The existing fixed-effect trace-distance estimate gives 1−p≤ε.
Normalize a when it is nonzero. Otherwise ε≥1, and a unit coordinate vector exists
because Ω is normalized. No overlap, purification, product or decoupling conclusion
is supplied as a hypothesis.

This is a derived elementary estimate supporting the full trace-norm pure-state
criterion in Piroli, Styliaris and Cirac, arXiv:2103.13367v3, “Phases of matter”.
It is not presented as a named statement of that article or a protocol classification.
The positive-part trace estimate follows the existing development of Wolf, Section 8.1.

## Existing fixed-effect lemma moved to its general owner

`Matrix.re_trace_mul_sub_le_traceDistance` moves verbatim from
`QICLean/Entropy/SpectralTail.lean` to `QICLean/Analysis/TraceDistance.lean`.
Its public name, finite index universes, hypotheses and proof are preserved.
The former owner already imports the new owner, so existing import clients retain
access. The move avoids both duplicating its Jordan-part proof and importing
entropy and patch regulators into a generic channel approximation module.

## Source and validation boundary

Base accepted QICLean main: 86b3159b98a1608c5e66a875fa670a9687c9867d.
Its lean-toolchain, lakefile and manifest are byte-identical to TNLean’s pinned
acda92aa70e69b37507e422bceb5414036859fe6. The relevant matrix/trace APIs are unchanged.
The primary QICLean worktree and its untracked material were preserved.

No local Lean/Lake build, elaboration or checkdecls is run, as requested.
The new Blueprint statement and proof remain `notready`; source review and native
checks do not establish compiled correctness. A downstream TNLean candidate pin
must remain an explicit draft dependency gate until accepted upstream.
