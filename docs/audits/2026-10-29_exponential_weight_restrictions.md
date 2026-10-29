# Exponential weights and soft remainders on a subspace

The two exponential-weight estimates and the soft-remainder factorization are finite-dimensional matrix analysis. They have no chain, locality, or Hamiltonian hypothesis. They therefore belong to QICLean, while the physical constructions supplying their inputs remain in TNLean.

The proof text is moved from the previously private auxiliaries in TNLean's regional exponential-moment and physical soft-residual modules. Apart from the namespace, public names, and documentation, the proof bodies are unchanged. The small domain-restriction norm estimate remains private beside its only consumer. Mathlib's composition norm inequality and submodule inclusion bound provide that estimate; the spectral exponential contraction is reused from QICLean. No compatibility aliases are introduced for the previously private declarations.

The three public results state that a high-energy restriction bound controls the whole exponential weight, that changing the scalar origin contributes its scalar exponential, and that the equal-order-and-scale soft remainder satisfies

\[
\|[A-h_{m,m}(A)]|_G\|\le16e^{-m/16}\|e^{A/8}|_G\|
\]

for every positive matrix and every subspace. These are supporting estimates for ALVV, arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx`, lines 1178–1255. A physical application must derive its actual high-energy restriction or exponential moment. These lemmas do not establish a physical spectral comparison or the printed uniform energy estimate.

## Verification

Private strict checks used the read-only provider at QICLean `4175de302e6b580d1bbb4a022f57424ab9f05e73`, a documentation-only successor of checked mathematical revision `a81cad04c854c6816788abdd3c4bdaab414501fa`. The source-only branch follows the separately frozen coercivity commit `0f223f2d`.

The remainder module passed in 36.921 seconds; its SHA-256 is `2007c26772a50abf2bc146916e96af92656de752ae522d543a59ff1f28a78e56`. The weight module passed in 18.815 seconds; its SHA-256 is `e55b42600115285dcb9e9d3da017603bd79643563668a23db16082b405515f35`. An imported-object audit checked all three public declarations: each uses only `propext`, `Classical.choice`, and `Quot.sound`. Source and imported-object hashes remained fixed throughout.

The private evidence is recorded in `/tmp/qiclean-alvv-soft-residual-analysis-checks.json` and `/tmp/qiclean-alvv-soft-residual-analysis-foundations.json`. No local Lake environment was initialized, no dependency artifacts were copied or changed, and no Mathlib source was compiled. Common ordinary builds and compiled blueprint checks remain integration gates.
