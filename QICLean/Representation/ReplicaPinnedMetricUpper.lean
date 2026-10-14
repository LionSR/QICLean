/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSimilarity

/-!
# An exponential upper bound for a pinned replica metric

For disjoint regions U and Y, the label projections of U, U ∪ Y, and Y
commute. The logarithmic comparison for the common replica weights bounds
(W_U⁻¹ W_{U ∪ Y}⁻¹ W_Y)² by its signed label exponential, multiplied by a
polynomial in the number of copies. The polynomial exponent depends on the
fixed original local spaces and t, and is uniform in both regions.

All three metrics retain the original full-system weights. The comparison
holds on the whole copy space, including zero copies and empty regions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, `comparator:pinned-metric`,
lines 299–308, and the sharp upper proof, lines 405–415;
`05-replicas.tex`, Lemma 6.2, `replicas:W-comparison`, lines 305–316.
Source revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)]

/-- The squared metric factor on the Bell-restricted regions is bounded by
its signed label exponential, up to a polynomial in the copy number. The
same original full-system family defines all three replica weights. The
polynomial exponent is independent of the copy number and both regions.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, `comparator:pinned-metric`,
lines 299–308, and the sharp upper proof, lines 405–415; the labelwise
comparison is `05-replicas.tex`, Lemma 6.2, `replicas:W-comparison`,
lines 305–316. Source revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the whole-space comparison for the displayed regional product;
its identification with the Bell restriction is proved separately. -/
theorem exists_replicaPinnedFactor_le_exp {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (U Y : Finset F),
      Disjoint U Y →
      let W := replicaMetric ι t k
      let L := fun Q : Finset F ↦ labelEntropy (subsystemPerm k ι Q)
      ((W U)⁻¹ * (W (U ∪ Y))⁻¹ * W Y) ^ 2 ≤
        ((((k : ℝ) + 2) ^ C : ℝ) : ℂ) •
          NormedSpace.exp (((2 * t : ℝ) : ℂ) • (L U + L (U ∪ Y) - L Y)) := by
  classical
  obtain ⟨C₀, hC₀, hweight⟩ := exists_abs_log_replicaLabelWeight_add_le ι ht
  refine ⟨6 * C₀, by positivity, ?_⟩
  intro k U Y hUY W L
  let R := ((isOrthogonalResolution_labelProj (subsystemPerm k ι U)).prod
    (isOrthogonalResolution_labelProj (subsystemPerm k ι (U ∪ Y)))
    (fun α β ↦ commute_labelProj_subsystemPerm_of_subset ι k
      Finset.subset_union_left α β)).prod
    (isOrthogonalResolution_labelProj (subsystemPerm k ι Y))
    (fun ab γ ↦
      (commute_labelProj_subsystemPerm_of_disjoint ι k hUY ab.1 γ).mul_left
        (commute_labelProj_subsystemPerm_of_subset ι k
          Finset.subset_union_right γ ab.2).symm)
  have hRU (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p ↦ f p.1.1) =
        (isOrthogonalResolution_labelProj (subsystemPerm k ι U)).hom f := by
    let hU := isOrthogonalResolution_labelProj (subsystemPerm k ι U)
    let hV := isOrthogonalResolution_labelProj (subsystemPerm k ι (U ∪ Y))
    let hY := isOrthogonalResolution_labelProj (subsystemPerm k ι Y)
    let hUV := hU.prod hV (fun α β ↦
      commute_labelProj_subsystemPerm_of_subset ι k Finset.subset_union_left α β)
    exact (hUV.prod_hom_fst hY R _).trans (hU.prod_hom_fst hV hUV f)
  have hRV (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p ↦ f p.1.2) =
        (isOrthogonalResolution_labelProj (subsystemPerm k ι (U ∪ Y))).hom f := by
    let hU := isOrthogonalResolution_labelProj (subsystemPerm k ι U)
    let hV := isOrthogonalResolution_labelProj (subsystemPerm k ι (U ∪ Y))
    let hY := isOrthogonalResolution_labelProj (subsystemPerm k ι Y)
    let hUV := hU.prod hV (fun α β ↦
      commute_labelProj_subsystemPerm_of_subset ι k Finset.subset_union_left α β)
    exact (hUV.prod_hom_fst hY R _).trans (hU.prod_hom_snd hV hUV f)
  have hRY (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p ↦ f p.2) =
        (isOrthogonalResolution_labelProj (subsystemPerm k ι Y)).hom f := by
    let hU := isOrthogonalResolution_labelProj (subsystemPerm k ι U)
    let hV := isOrthogonalResolution_labelProj (subsystemPerm k ι (U ∪ Y))
    let hY := isOrthogonalResolution_labelProj (subsystemPerm k ι Y)
    let hUV := hU.prod hV (fun α β ↦
      commute_labelProj_subsystemPerm_of_subset ι k Finset.subset_union_left α β)
    exact hUV.prod_hom_snd hY R f
  let w := replicaLabelWeight ι t (k := k)
  have hw (l : IrrepLabel (Equiv.Perm (Fin k))) : 0 < w l :=
    replicaLabelWeight_pos ι ht.le l
  have hWU : (replicaMetric ι t k U)⁻¹ =
      R.hom (fun p ↦ (((w p.1.1)⁻¹ : ℝ) : ℂ)) := by
    rw [replicaMetric, labelObservable_inv _ (fun l ↦ (hw l).ne')]
    simpa only [labelObservable_eq_hom] using
      (hRU (fun l ↦ (((w l)⁻¹ : ℝ) : ℂ))).symm
  have hWV : (replicaMetric ι t k (U ∪ Y))⁻¹ =
      R.hom (fun p ↦ (((w p.1.2)⁻¹ : ℝ) : ℂ)) := by
    rw [replicaMetric, labelObservable_inv _ (fun l ↦ (hw l).ne')]
    simpa only [labelObservable_eq_hom] using
      (hRV (fun l ↦ (((w l)⁻¹ : ℝ) : ℂ))).symm
  have hWY : replicaMetric ι t k Y = R.hom (fun p ↦ (w p.2 : ℂ)) := by
    simpa only [replicaMetric, labelObservable_eq_hom] using
      (hRY (fun l ↦ (w l : ℂ))).symm
  let q : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p ↦ ((w p.1.1)⁻¹ * (w p.1.2)⁻¹ * w p.2) ^ 2
  have hProduct : ((replicaMetric ι t k U)⁻¹ *
      (replicaMetric ι t k (U ∪ Y))⁻¹ * replicaMetric ι t k Y) ^ 2 =
      R.hom (fun p ↦ (q p : ℂ)) := by
    simp only [hWU, hWV, hWY, ← map_mul, ← map_pow, q,
      Complex.ofReal_pow, Complex.ofReal_mul]
    exact congrArg R.hom (funext fun p ↦ by simp only [Pi.pow_apply, Pi.mul_apply])
  let g : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p ↦ Real.log p.1.1.dim + Real.log p.1.2.dim - Real.log p.2.dim
  have hG : labelEntropy (subsystemPerm k ι U) +
      labelEntropy (subsystemPerm k ι (U ∪ Y)) - labelEntropy (subsystemPerm k ι Y) =
      R.hom (fun p ↦ (g p : ℂ)) := by
    simp only [labelEntropy, labelObservable_eq_hom, ← hRU, ← hRV, ← hRY,
      ← map_add, ← map_sub, g, Complex.ofReal_sub, Complex.ofReal_add]
    exact congrArg R.hom (funext fun p ↦ by simp only [Pi.add_apply, Pi.sub_apply])
  have hExp : NormedSpace.exp (((2 * t : ℝ) : ℂ) •
      (labelEntropy (subsystemPerm k ι U) + labelEntropy (subsystemPerm k ι (U ∪ Y)) -
        labelEntropy (subsystemPerm k ι Y))) =
      R.hom (fun p ↦ (Real.exp (2 * t * g p) : ℂ)) := by
    simp only [hG, ← map_smul, R.exp_hom, Pi.smul_apply, smul_eq_mul,
      ← Complex.ofReal_mul, Complex.ofReal_exp]
  have hHerm (p : (IrrepLabel (Equiv.Perm (Fin k)) ×
      IrrepLabel (Equiv.Perm (Fin k))) × IrrepLabel (Equiv.Perm (Fin k))) :
      (labelProj (subsystemPerm k ι U) p.1.1 * labelProj (subsystemPerm k ι (U ∪ Y)) p.1.2 *
        labelProj (subsystemPerm k ι Y) p.2).IsHermitian := by
    exact ((((isHermitian_labelProj _ p.1.1).commute_iff
      (isHermitian_labelProj _ p.1.2)).mp
        (commute_labelProj_subsystemPerm_of_subset ι k Finset.subset_union_left
          p.1.1 p.1.2)).commute_iff (isHermitian_labelProj _ p.2)).mp
            ((commute_labelProj_subsystemPerm_of_disjoint ι k hUY p.1.1 p.2).mul_left
              (commute_labelProj_subsystemPerm_of_subset ι k Finset.subset_union_right
                p.2 p.1.2).symm)
  have hcoef (p : (IrrepLabel (Equiv.Perm (Fin k)) ×
      IrrepLabel (Equiv.Perm (Fin k))) × IrrepLabel (Equiv.Perm (Fin k)))
      (hp : labelProj (subsystemPerm k ι U) p.1.1 *
        labelProj (subsystemPerm k ι (U ∪ Y)) p.1.2 * labelProj (subsystemPerm k ι Y) p.2 ≠ 0) :
      q p ≤ ((k : ℝ) + 2) ^ (6 * C₀) * Real.exp (2 * t * g p) := by
    have hlog : Real.log (q p) ≤ 6 * C₀ * Real.log ((k : ℝ) + 2) +
        2 * t * g p := by
      simp only [q, g, Real.log_pow,
        Real.log_mul (mul_pos (inv_pos.mpr (hw p.1.1)) (inv_pos.mpr (hw p.1.2))).ne'
          (hw p.2).ne',
        Real.log_mul (inv_pos.mpr (hw p.1.1)).ne' (inv_pos.mpr (hw p.1.2)).ne',
        Real.log_inv, Nat.cast_ofNat, w]
      linarith only [
        (abs_le.mp (hweight k U p.1.1
          (left_ne_zero_of_mul (left_ne_zero_of_mul hp)))).1,
        (abs_le.mp (hweight k (U ∪ Y) p.1.2
          (right_ne_zero_of_mul (left_ne_zero_of_mul hp)))).1,
        (abs_le.mp (hweight k Y p.2 (right_ne_zero_of_mul hp))).2]
    simpa only [Real.rpow_def_of_pos (by positivity : 0 < (k : ℝ) + 2),
      Real.exp_add, mul_comm (Real.log ((k : ℝ) + 2)) (6 * C₀)] using
        Real.le_exp_of_log_le hlog
  have hpos := R.posSemidef_hom_of_ne_zero hHerm
    (f := fun p ↦ ((k : ℝ) + 2) ^ (6 * C₀) * Real.exp (2 * t * g p) - q p)
    (fun p hp ↦ sub_nonneg.mpr (hcoef p hp))
  have hcoeffeq : (fun p ↦ ((((k : ℝ) + 2) ^ (6 * C₀) *
      Real.exp (2 * t * g p) - q p : ℝ) : ℂ)) =
      (((((k : ℝ) + 2) ^ (6 * C₀) : ℝ) : ℂ) •
        (fun p ↦ (Real.exp (2 * t * g p) : ℂ))) -
        (fun p ↦ (q p : ℂ)) :=
    funext fun p ↦ by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_sub, Complex.ofReal_mul]
  simpa only [hcoeffeq, map_sub, map_smul, sub_nonneg, ← hProduct, ← hExp] using
    hpos.nonneg

end TensorPower
