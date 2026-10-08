# Rectangular Hermitian intertwiners and exponential paths

## Mathematical content

For a rectangular complex matrix F and Hermitian L, the new equivalence is

Commute L (F F†) ↔ ∃ K, K.IsHermitian ∧ F K = L F.

Write G=FF† and let S be its existing positive-semidefinite support inverse.
Commutation passes to S by continuous functional calculus. The choice
K=F†SLF is Hermitian and satisfies FK=GSLF=LGSF=LF. It vanishes on ker F.
The converse follows by taking adjoints. Rectangular, singular, and empty-index
cases are retained; no injectivity or full-support assumption is imposed.

For any nonscalar complex square matrix K, exp(i t K) is nonscalar throughout
a sufficiently small punctured real neighborhood of zero. Choose a matrix
unit B not commuting with K. The curve B exp(i t K)−exp(i t K) B vanishes
at zero and has nonzero derivative i(BK−KB); its slope is therefore nonzero
near zero. For Hermitian K the path is unitary, continuous, and additive in
the parameter, and is also packaged as a unitary-valued group homomorphism.

The tensor-factor exponential identity is

exp(X⊗I + I⊗Y) = exp(X)⊗exp(Y).

The proof uses continuous ring homomorphisms and the exponential of commuting
sums. In particular exp(i t (H⊗I−I⊗conjugate H)) equals
exp(i t H)⊗conjugate(exp(i t H)).

## Ownership, scouting, and simplification

These are generic matrix-analysis results. Their tensor-specific physical
symmetry and string-order consumers belong in TNLean. No pseudoinverse,
polar-factor, matrix-norm, group-representation, or support-predicate parallel
was introduced. The implementation reuses supportInv, support projections,
IsSelfAdjoint.commute_cfc, Matrix.exp_transpose, NormedSpace.map_exp,
HasDerivAt.tendsto_slope, and the existing scalar-center criterion on matrix
units. There is no eigenvalue enumeration or new trigonometric framework.

The rectangular exponential-transport theorem remains in its existing
CoisometricCompression owner. Its import closure proved inexpensive in actual
checks, so this batch does not relocate it opportunistically. A draft-only
unused exponential wrapper was removed rather than retained as a new API.
Unused decidability hypotheses were removed, with classical decidability
introduced only where support calculus needs it. The rectangular Hermiticity
helper also drops its unused right-hand Fintype instance.

A focused tactic-pattern scan of the new sources found no repeated pattern at
the repository threshold of three occurrences. Import minimization with Lake
shake was not run during direct isolated validation; no import-minimality claim
is made. No changes are made to unrelated existing hypotheses or declarations.

## Validation

Base QIC revision: 8d5389d23c8e675a0117442e1a0d2c683a4bad41.
Lean v4.35.0-rc3 and Mathlib c55e6e786f49471c72fbddbec5415808896aec1e.

All three new modules and both regression files passed direct Lean elaboration
with package options, the Mathlib standard linter set, warnings-as-errors,
and one thread. Every invocation had a 90-second wall bound; the final new
modules took 2.9–3.2 seconds and the tests 2.0–2.8 seconds. No heartbeat or
recursion limit was increased. The 18 public declaration guards report only
propext, Classical.choice, and Quot.sound. There are no placeholder proofs.

Regressions cover complex Pauli Y, unitary/additive path identities, small-time
nonscalarity, Kronecker exponentiation, a singular 2×3 map, rectangular zero
maps, and both empty-index directions. The source/artifact hashes and exact
options are in the accompanying validation JSON.

Generated import manifests have been regenerated and checked. CI now builds
the focused modules and runs the strict regressions. The isolated checks are
not a claim that the entire aggregate library, Lake integration, or blueprint
render/checkdecls has already passed. Those remain integration gates.
