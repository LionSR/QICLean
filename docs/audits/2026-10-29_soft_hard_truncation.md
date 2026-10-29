# Soft truncation and a hard spectral cap

For every real scale t > 0, integer order m ≥ 1, and x ≥ 0, the finite
soft-truncation series satisfies

\[
\min\{x,t/2\}-(t/2)2^{-m}\le h_{m,t}(x)\le x.
\]

The proof is uniform in x. Below t/2, the geometric remainder and
0 ≤ 1 − exp(−x/t) ≤ x/t ≤ 1/2 give the lower bound. Above t/2, monotonicity
reduces the assertion to the endpoint. Monotonicity itself follows term by
term from the finite positive-power series; it holds also at order zero.

For a positive semidefinite complex matrix A, functional calculus on the
nonnegative spectrum of this same matrix gives

\[
\operatorname{min}(A,(t/2)I)-(t/2)2^{-m}I\le h_{m,t}(A)\le A.
\]

No monotonicity between functions of different noncommuting matrices is
asserted. The result holds for every finite matrix index type, including
the empty type. The scalar comparison allows m = 1 and does not require
t ≥ m. The published definition uses the narrower range t ≥ m ≥ 1.

## Source and mathematical scope

The series is the one in Arad–Landau–Vazirani–Vidick,
arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, lines 1152–1173. The regional
soft truncation is Definition `def:soft-trunc`, lines 1178–1185; the hard
truncation is Definition `def:hard-trunc`, lines 873–886.
The local source file has SHA256
`19d37facb8bf8da6ea5555cd7185c054d251ad4a06c2f44fcb92593235ad6b92`.
The comparison proved here is an auxiliary bound. It is not the printed
uniform energy estimate in equation `eq:exp-approx-0`, nor a claim that
that estimate has been repaired in its original form.

The source's approximate regional ground energy e′ satisfies
e − 10 ≤ e′ ≤ e. Applying the comparison to A = H_J − e′I therefore gives
a hard cap at e′ + t/2. A uniform cap relative to the true regional ground
energy is e + t/2 − 10. In particular, the diagonal choice t = m gives
hard threshold m/2 − 10, rather than m/2. The affine-shift comparison and
its composition with a physical regional hard-truncation theorem are
subsequent steps; they are not declarations of this contribution.

An order sandwich yields ordered-eigenvalue comparisons. Spectral-subspace
closeness still requires a separate residual or projection argument. The
physical low-energy spectral theorem, cluster construction, and matrix
product operator bounds are not concluded here.

## Declarations and verification

The new public declarations are:

- `Real.monotoneOn_softTruncation`;
- `Real.softTruncation_hard_bounds`;
- `Matrix.PosSemidef.softTruncation_hard_bounds`.

The first two extend the existing scalar module. The matrix theorem lives
in `Analysis/SoftHardTruncation.lean` and reuses `Matrix.energyTruncation`,
Mathlib's `cfc_mono`, and continuity on the finite matrix spectrum. The
proof introduces no alternative truncation definition.

Private checks used the clean TNLean provider
`1604ed2ffc831a4f6afba70150024edd3ca19d6c` and its checked QICLean package
`afcf986970504f1d370e475f0617256ca83b160d`. These share the mathematical
source of QICLean `1aa1011b4f5518d59de4ef462b71d84ad4ec33ea`; the common
QICLean documentation head is `df17465b0795156c22ff8ca36ffe17ae1431422d`.
Source and provider-object hashes were checked before and after private
elaboration. All new objects were written under `/tmp`; no provider
source, dependency, object, or cache was changed, and no Mathlib source
was rebuilt.

Both actual modules passed the strict package checks. The final measured
elaboration times were 7.30 seconds for the extended scalar module and
5.13 seconds for the matrix module. An independent importing module
checked all three public declarations and found only `propext`,
`Classical.choice`, and `Quot.sound` among their foundations. The prose
check and repeated-tactic scan passed. The complete blueprint chapter
compiled as a standalone two-page document, with resolved references and
no overfull boxes; its new comparison statements were visually inspected.

Ordinary common-library compilation and the compiled blueprint declaration
check remain integration checks. The private source patch contains no
persistent proof-audit fixture or command.
