# Typical-spectrum entropy estimates

The independently written formalization proves the two estimates labelled
`comparator:typical-entropies` in OpenAI's September 24, 2026 manuscript,
*A two-dimensional area law from a global spectral gap*. The mathematical source
is pinned to commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`build/sections/07-comparators.tex`, lines 39–55.

For a finite selected set of positive weights of total mass (z>0), lying between
\(e^{-S-w}\) and \(e^{-S+w}\), the normalized weights have total mass one, and

\[
\bigl|\log|E|-S\bigr|\le w+|\log z|,
\qquad
\bigl|S(p|E)-S\bigr|\le w+|\log z|.
\]

The proof first establishes the sharper intervals centered at \(S+\log z\).
No assumptions are imposed on weights outside the selected set. In particular,
zero marginal eigenvalues remain allowed. The inequalities in the source imply
positivity of each selected weight, and positive mass implies nonemptiness.

This component does not construct the typical set from the Hamiltonian and its
gap, select a common auxiliary Schur sector, or prove the four auxiliary norm
comparisons of Proposition 8.1. Those results remain separate tasks.

The proofs and mathematical account were prepared with OpenAI Codex. No OpenAI
Lean proof text was read, copied, or adapted for these declarations. Human
mathematical review remains required.

Verification uses an independent Lake cache, cloned from an idle compatible
QICLean worktree. The canonical Mathlib prebuilt cache was verified before any
build; Mathlib was not built from source. The linter-bearing module build and
all exported theorem axiom checks are recorded in `build.log` and `axioms.log`.
The full library build and global blueprint declaration check are deferred to
the combined integration branch.
