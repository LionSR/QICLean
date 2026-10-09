/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchurLabelCommutation
import QICLean.Representation.SchurSurprisal
import QICLean.Representation.MergeDimensions

/-!
# Exponentials of merge deficits

For two commuting permutation actions and their pointwise product, the actual
three-label projections form a joint orthogonal resolution. The exponential
of the sum of the separate logarithmic label dimensions minus the combined
one is therefore the corresponding sum of powers of dimension ratios.
Taking its trace against any complex matrix gives the exact finite-label
expression used in the merge-moment argument.

These identities are the spectral expansion underlying *A two-dimensional
area law from a global spectral gap*, `05-replicas.tex`, lines 112–115,
`replicas:merge-moment`, and `07-comparators.tex`, lines 501–549,
`comparator:merge-moments`. All real exponents and empty ambient coordinate
sets are included. The numerical moment estimate is a subsequent result.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation
open scoped BigOperators Matrix.Norms.Operator

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  {φQ φE φQE : G →* Equiv.Perm X}

/-- The actual separate and combined label projections form a joint resolution.
OpenAI area-law manuscript, `05-replicas.tex`, lines 112–115, and
`07-comparators.tex`, lines 501–549. -/
private theorem mergeResolution (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) :
    IsOrthogonalResolution fun p : (IrrepLabel G × IrrepLabel G) × IrrepLabel G =>
      labelProj φQ p.1.1 * labelProj φE p.1.2 * labelProj φQE p.2 := by
  classical
  refine ((isOrthogonalResolution_labelProj φQ).prod
    (isOrthogonalResolution_labelProj φE) (fun l μ => ?_)).prod
    (isOrthogonalResolution_labelProj φQE) (fun p ν => ?_)
  · exact commute_groupAlgebraRep_of_commute φQ φE hcomm _ _
  · apply Commute.mul_left
    · exact commute_groupAlgebraRep_of_eq_mul φQ φE φQE hprod hcomm
        (IrrepLabel.centralIdem_mem_center p.1) _
    · exact commute_groupAlgebraRep_of_eq_mul φE φQ φQE
        (fun g => by rw [hprod, (hcomm g g).eq])
        (fun g h => (hcomm h g).symm) (IrrepLabel.centralIdem_mem_center p.2) _

/-- The first marginal of the joint label resolution gives the first label observable.
OpenAI area-law manuscript, `05-replicas.tex`, lines 112–115, and
`07-comparators.tex`, lines 501–549. -/
private theorem mergeResolution_hom_left (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) :
    (mergeResolution hcomm hprod).hom (fun p => (Real.log p.1.1.dim : ℂ)) =
      labelEntropy φQ := by
  classical
  let R := (isOrthogonalResolution_labelProj φQ).prod
    (isOrthogonalResolution_labelProj φE)
    (fun l μ => commute_groupAlgebraRep_of_commute φQ φE hcomm _ _)
  exact (R.prod_hom_fst (isOrthogonalResolution_labelProj φQE)
    (mergeResolution hcomm hprod) (fun p => (Real.log p.1.dim : ℂ))).trans
      (((isOrthogonalResolution_labelProj φQ).prod_hom_fst
        (isOrthogonalResolution_labelProj φE) R (fun l => (Real.log l.dim : ℂ))).trans
          (labelObservable_eq_hom φQ (fun l => Real.log l.dim)).symm)

/-- The second marginal of the joint label resolution gives the second label observable.
OpenAI area-law manuscript, `05-replicas.tex`, lines 112–115, and
`07-comparators.tex`, lines 501–549. -/
private theorem mergeResolution_hom_middle (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) :
    (mergeResolution hcomm hprod).hom (fun p => (Real.log p.1.2.dim : ℂ)) =
      labelEntropy φE := by
  classical
  let R := (isOrthogonalResolution_labelProj φQ).prod
    (isOrthogonalResolution_labelProj φE)
    (fun l μ => commute_groupAlgebraRep_of_commute φQ φE hcomm _ _)
  exact (R.prod_hom_fst (isOrthogonalResolution_labelProj φQE)
    (mergeResolution hcomm hprod) (fun p => (Real.log p.2.dim : ℂ))).trans
      (((isOrthogonalResolution_labelProj φQ).prod_hom_snd
        (isOrthogonalResolution_labelProj φE) R (fun l => (Real.log l.dim : ℂ))).trans
          (labelObservable_eq_hom φE (fun l => Real.log l.dim)).symm)

/-- The combined marginal of the joint label resolution gives the combined label observable.
OpenAI area-law manuscript, `05-replicas.tex`, lines 112–115, and
`07-comparators.tex`, lines 501–549. -/
private theorem mergeResolution_hom_right (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) :
    (mergeResolution hcomm hprod).hom (fun p => (Real.log p.2.dim : ℂ)) =
      labelEntropy φQE := by
  classical
  let R := (isOrthogonalResolution_labelProj φQ).prod
    (isOrthogonalResolution_labelProj φE)
    (fun l μ => commute_groupAlgebraRep_of_commute φQ φE hcomm _ _)
  exact (R.prod_hom_snd (isOrthogonalResolution_labelProj φQE)
    (mergeResolution hcomm hprod) (fun l => (Real.log l.dim : ℂ))).trans
      (labelObservable_eq_hom φQE (fun l => Real.log l.dim)).symm

/-- The exponential of a logarithmic dimension difference is a real power of its ratio.
OpenAI area-law manuscript, `05-replicas.tex`, lines 112–115, and
`07-comparators.tex`, lines 501–549. -/
private theorem exp_mergeScalar (x y z b : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    Complex.exp ((b : ℂ) * ((Real.log x : ℂ) + (Real.log y : ℂ) - (Real.log z : ℂ))) =
      ((x * y / z) ^ b : ℝ) := by
  rw [← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, Real.rpow_def_of_pos (div_pos (mul_pos hx hy) hz),
    Real.log_div (mul_pos hx hy).ne' hz.ne', Real.log_mul hx.ne' hy.ne', mul_comm]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, replicas:merge-moment and comparator:merge-moments.
-/

/-- The exponential of the actual merge deficit is the finite sum over the
actual three-label projections, with dimension-ratio powers as coefficients.
The separate actions commute and the combined action is their literal
pointwise product. Every real exponent is allowed.
*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
lines 112–115, and `07-comparators.tex`, lines 501–549. -/
theorem exp_mergeDeficit_eq_sum (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) (b : ℝ) :
    NormedSpace.exp ((b : ℂ) • (labelEntropy φQ + labelEntropy φE - labelEntropy φQE)) =
      ∑ l, ∑ μ, ∑ ν,
        (((((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b : ℝ) : ℂ) •
          (labelProj φQ l * labelProj φE μ * labelProj φQE ν) := by
  classical
  let R := mergeResolution hcomm hprod
  have hD : (b : ℂ) • (labelEntropy φQ + labelEntropy φE - labelEntropy φQE) =
      R.hom (fun p => (b : ℂ) *
        ((Real.log p.1.1.dim : ℂ) + (Real.log p.1.2.dim : ℂ) - (Real.log p.2.dim : ℂ))) := by
    rw [← mergeResolution_hom_left hcomm hprod, ← mergeResolution_hom_middle hcomm hprod,
      ← mergeResolution_hom_right hcomm hprod]
    rw [← map_add, ← map_sub, ← map_smul]
    congr 1
  rw [hD, R.exp_hom, Matrix.IsOrthogonalResolution.hom_apply,
    Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun μ _ => ?_
  refine Finset.sum_congr rfl fun ν _ => ?_
  dsimp only
  rw [exp_mergeScalar _ _ _ _ (by exact_mod_cast l.dim_pos)
    (by exact_mod_cast μ.dim_pos) (by exact_mod_cast ν.dim_pos), Nat.cast_mul]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, replicas:merge-moment and comparator:merge-moments.
-/

/-- The real trace pairing with the exponential of the actual merge deficit
is the corresponding dimension-ratio-weighted sum of actual joint label
trace pairings. The matrix in the trace is arbitrary; every real exponent
is allowed.
*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
lines 112–115, and `07-comparators.tex`, lines 501–549. -/
theorem re_trace_mul_exp_mergeDeficit_eq_sum
    (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) (b : ℝ) (ρ : Matrix X X ℂ) :
    (ρ * NormedSpace.exp ((b : ℂ) •
      (labelEntropy φQ + labelEntropy φE - labelEntropy φQE))).trace.re =
      ∑ l, ∑ μ, ∑ ν,
        (ρ * (labelProj φQ l * labelProj φE μ * labelProj φQE ν)).trace.re *
          (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b := by
  rw [exp_mergeDeficit_eq_sum hcomm hprod]
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, mul_comm]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, replicas:merge-dimensions and comparator:merge-decomposition.
-/

open scoped ComplexOrder in
/-- The actual logarithmic merge deficit is positive semidefinite. The separate
permutation actions commute and the combined action is their pointwise product;
no compatibility assumption on labels is supplied. Zero ambient dimension is
included. OpenAI, *A two-dimensional area law from a global spectral gap*,
Lemma 6.1(3), `05-replicas.tex`, equation `replicas:merge-dimensions`, and
`07-comparators.tex`, lines 501–508, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem posSemidef_mergeDeficit (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) :
    (labelEntropy φQ + labelEntropy φE - labelEntropy φQE).PosSemidef := by
  classical
  let R := mergeResolution hcomm hprod
  have hD : labelEntropy φQ + labelEntropy φE - labelEntropy φQE =
      R.hom (fun p => ((Real.log p.1.1.dim + Real.log p.1.2.dim - Real.log p.2.dim : ℝ) : ℂ)) := by
    rw [← mergeResolution_hom_left hcomm hprod, ← mergeResolution_hom_middle hcomm hprod,
      ← mergeResolution_hom_right hcomm hprod, ← map_add, ← map_sub]
    congr 1
    funext p
    simp only [Pi.add_apply, Pi.sub_apply, Complex.ofReal_add, Complex.ofReal_sub]
  rw [hD]
  refine R.posSemidef_hom_of_ne_zero (fun p => ?_) fun p hp => ?_
  · have hQE := commute_groupAlgebraRep_of_commute φQ φE hcomm
        (IrrepLabel.centralIdem p.1.1) (IrrepLabel.centralIdem p.1.2)
    have hQboth := commute_groupAlgebraRep_of_eq_mul φQ φE φQE hprod hcomm
        (IrrepLabel.centralIdem_mem_center p.1.1) (IrrepLabel.centralIdem p.2)
    have hEboth := commute_groupAlgebraRep_of_eq_mul φE φQ φQE
        (fun g => by rw [hprod, (hcomm g g).eq])
        (fun g h => (hcomm h g).symm) (IrrepLabel.centralIdem_mem_center p.1.2)
        (IrrepLabel.centralIdem p.2)
    have hHerm := ((isHermitian_labelProj φQ p.1.1).commute_iff
      (isHermitian_labelProj φE p.1.2)).mp hQE
    exact (hHerm.commute_iff (isHermitian_labelProj φQE p.2)).mp
      (hQboth.mul_left hEboth)
  · have hdim := dim_le_mul_dim_of_compatible hcomm hprod hp
    have hx : (0 : ℝ) < p.1.1.dim := by exact_mod_cast p.1.1.dim_pos
    have hy : (0 : ℝ) < p.1.2.dim := by exact_mod_cast p.1.2.dim_pos
    have hz : (0 : ℝ) < p.2.dim := by exact_mod_cast p.2.dim_pos
    have hlog : Real.log (p.2.dim : ℝ) ≤ Real.log ((p.1.1.dim : ℝ) * p.1.2.dim) := by
      apply Real.log_le_log hz
      exact_mod_cast hdim
    rw [Real.log_mul hx.ne' hy.ne'] at hlog
    linarith
end PermutationRepresentation
