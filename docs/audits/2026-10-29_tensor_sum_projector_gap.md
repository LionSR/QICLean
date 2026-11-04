# Projector-gap lower bounds for two tensor factors

`Analysis/DoubledSystemGap.lean` now proves the positive-defect identity for
arbitrary finite factor dimensions. The original doubled-Hamiltonian identity
and lower-gap theorem retain their statements and follow by specialization.

For arbitrary matrices A,B, vectors u,v and real energies E,F, define
Pᵤ=|u><u|, Qᵤ=I−Pᵤ, and similarly for v. The actual identity is

\[
A\otimes I+I\otimes B-(E+F)I-\delta(I-P_u\otimes P_v)
 =R_A\otimes I+I\otimes R_B+\delta Q_u\otimes Q_v,
\]

where R_A=A−EI−δQᵤ and R_B=B−FI−δQᵥ.
The identity requires no normalization or eigenvector hypothesis.
When u,v are unit, R_A,R_B are positive and δ≥0, the right side is positive.
Thus the same projector-gap lower bound passes to the tensor sum.
The theorem asserts no equality of spectral gaps and imposes no equality of
the two factor dimensions, matrices or reference energies.

A separate monotonicity theorem weakens a projector-gap lower bound from δ
to any δ′≤δ. The positive correction is (δ−δ′)Qᵤ. Neither parameter is
required to be positive for this monotonicity statement.

These are algebraic ingredients for product-state ancillary padding of the
successive viable-set construction in LVV13, arXiv:1307.5143v1,
`algo53.tex`, final induction, lines652–678. They do not construct the
physical on-site ancillary penalties, identify their actual sum, transfer
prefix viability, or establish arbitrary-accuracy approximation on their
own. Those tensor-network-specific steps remain downstream in TNLean.
No running-time claim is made.

## Verification

The branch based on QICLean `a2f54b6f` passes the ordinary Lake build of
`QICLean.Analysis.DoubledSystemGap` after fetching the pinned prebuilt
Mathlib artifacts. The module also passes separate elaboration with both
automatic implicit options disabled, warnings treated as errors, the
standard Mathlib linters and the package synthesis-depth limit.
Blueprint/source synchronization passes. Full-library and compiled
blueprint verification are recorded in the pull request.
