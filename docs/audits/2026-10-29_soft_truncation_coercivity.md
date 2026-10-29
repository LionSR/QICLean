# Centered soft-truncation coercivity

This contribution proves two auxiliary estimates for the reverse soft spectral comparison in Arad–Landau–Vazirani–Vidick, arXiv:1602.08828v2. The relevant source passages are `def:hard-trunc` (lines 873–886), `def:soft-trunc` (lines 1178–1185), and `lem:exp-approx` (lines 1195–1255).

For a finite family of Hermitian matrices bounded below by specified scalar energies, replace one term by its actual shifted soft truncation. If the approximate selected energy lies within ten below its specified lower bound, the resulting centered sum, after adding

\[
\alpha=(t/2)2^{-m},
\]

is positive and dominates the selected high-energy projection multiplied by its threshold. The threshold may be any number between zero and \(t/2-10\). The proof uses the shifted soft/hard comparison and the existing high-projection order theorem. The scalar error is added once, independently of the number of summands. No commutativity or attainment of the specified lower energies is required.

The second estimate chooses a threshold for a later reverse-window argument. With \(t=m\), \(-\alpha\le E\le2\), \(\eta\ge0\), and \(0\le C\le4\), the explicit condition

\[
m/2\ge17+\eta+\alpha
\]

places \(u=E+\alpha+\eta+C+1\) below the hard threshold and gives \(u-(E+\alpha+\eta)-C=1\).

These are matrix-order and scalar auxiliaries, rather than a physical spectral comparison. In the physical application, the actual soft ground energy and its bounds, the boundary constant, the relevant commutation identities, and the soft low-energy subspace must still be constructed from the Hamiltonian. The original-window residual and the reverse soft-window estimate remain distinct assertions. This contribution does not establish the source spectral comparison or complete the low-density or tree constructions.

## Verification

The source-only branch is based on QICLean commit `15a60a1bebe726ee6536ae75570e8243b9f310c4`. Private strict checks used the read-only, fully built QICLean provider at `4175de302e6b580d1bbb4a022f57424ab9f05e73`, the documentation-only successor of checked mathematical revision `a81cad04c854c6816788abdd3c4bdaab414501fa`. The new module took 18.836 seconds and produced no warnings or errors. Its SHA-256 is `94118bb9821a71b13ea58ea1e5c7f96b2bd44f9d448e4a1382d33c1801f8d799`.

An imported-object foundation audit checked both public declarations. Each depends only on `propext`, `Classical.choice`, and `Quot.sound`. Source and imported-object hashes were guarded before and after elaboration. The private check records are `/tmp/qiclean-alvv-soft-coercivity-current-checks.json` and `/tmp/qiclean-alvv-soft-coercivity-foundations.json`.

The source worktree has no local `.lake` directory. All new objects were written to temporary directories; existing dependency objects were read without copying or modifying them. No TNLean objects were used, and no Mathlib source was compiled. The common ordinary build and compiled blueprint checks remain integration gates.
