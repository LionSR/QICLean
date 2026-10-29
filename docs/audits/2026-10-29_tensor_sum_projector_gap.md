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

## Exact checks

Production SHA256:
`c2288eee962b5984030107d69191cee2e39e846612950d66d8f5353f571c6bed`.

The complete actual named module passes private strict checking in 4.21 seconds,
with strict implicit arguments, Mathlib standard linters, warnings as errors
and default heartbeats. Imported foundation inspection in 2.68 seconds checks all
three new public declarations and both refactored doubled declarations:

- `Matrix.PosSemidef.gap_mono`;
- `Matrix.tensorSum_gap_eq`;
- `Matrix.PosSemidef.tensorSum_gap`;
- `Matrix.doubledHamiltonian_gap_eq`;
- `Matrix.PosSemidef.doubled_gap`.

Each reports only `propext`, `Classical.choice` and `Quot.sound`.
The manual inspection source and outputs remain under `/tmp`; no permanent
inspection fixture is introduced.

The source-only worktree starts at checked QICLean 4175de302e6b580d1bbb4a022f57424ab9f05e73.
Private checks use the read-only 4175 package artifacts of the fully verified
TNLean mathematical snapshot f5e011c2e551b318e6df7f7d6e5e81725dedea7a.
The exact successor 4bdda88ad1455106fd05ba6d874ecd1aca53aadb changes only
module-docstring wrapping in an unrelated TNLean module. Its diff and all
captured imported hashes were inspected before accepting it.
The generic module has five QICLean imports in its transitive closure and
no TNLean import. The common selected-source guard additionally verifies
405 TNLean/QICLean sources and ordinary objects, manifest and toolchain.
The changed source and fresh private object are separately hash-checked
before and after manual foundation inspection.

No dependency, cache, provider object or Mathlib artifact is copied or
modified. The source-only worktree has no `.lake` directory, and no ordinary
build is queued here. Ordinary companion-library and compiled-blueprint
checks remain for integration.
