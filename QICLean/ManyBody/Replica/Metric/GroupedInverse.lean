/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Exponential.ExpConjugation
import QICLean.Representation.YoungSubgroup.GroupedLabelEntropy
import QICLean.ManyBody.Replica.Metric.Similarity

/-!
# The inverse replica metric after splitting the copies

For three disjoint subsystems, the whole-copy label expression is bounded
below by the sum of its good- and bad-copy expressions, less the single
binomial correction. The relevant whole and subgroup label observables
commute. Exponentiating therefore costs exactly `choose(k,r)^a`, where
`a=2t` for the inverse squared replica metric.

The same full-system replica weights are used before and after this
comparison. No positivity of the signed label expression or symmetry of
a vector is assumed. The later removal of the bad-copy exponential is a
separate support argument.

It also contains the following results.

* `TensorPower.exists_replicaMetric_inv_square_le_exp`: whole-space comparison for the inverse
  replica metric.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 454--476,
  `comparator:restriction-dimensions` and `comparator:whole-inverse`,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

section WholeInverse

/-!
## Whole-space comparison for the inverse replica metric

For a fixed finite family of nonzero local Hilbert spaces and fixed `t > 0`,
the replica metrics of pairwise disjoint subsystems `P`, `Y`, and `F` have a common
orthogonal resolution by products of their central label projections. This file bounds
`((W_P⁻¹ W_F⁻¹ W_Y)²)⁻¹` by a polynomial in the number of copies times
`exp(-2t(F_P + F_F - F_Y))`. The polynomial constant is uniform over all copy numbers
and all three subsystems. The proof applies on the whole tensor-product space, including
zero copies and empty subsystems; it does not require a symmetric-subspace restriction.

### References

The manuscript is dated September 24, 2026; the source passages below refer to revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

* OpenAI, *A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
  equation `replicas:w-definition` and Lemma `replicas:metric`, equation `replicas:W-comparison`,
  lines 287–316: the common replica weights and their comparison with label dimensions.
* The same paper, `07-comparators.tex`, lines 454–476: the inverse-metric comparison used
  before separating the good and bad copies.

This is the preceding whole-label comparison only. It does not establish the subgroup
decomposition with its binomial loss or an excitation-component comparison; these are
separate assertions.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
  (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
  [∀ v, Nonempty (ι v)]

/-- A uniform whole-space upper bound for the inverse of the actual squared replica-metric
product (`05-replicas.tex`, Lemma `replicas:metric`, equation `replicas:W-comparison`,
lines 305–316;
`07-comparators.tex`, lines 454–476). The three subsystems need only be pairwise disjoint.
For fixed local spaces and `t`, the constant is independent of the copy number
and the subsystem choices. -/
theorem exists_replicaMetric_inv_square_le_exp {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (P Y F : Finset V),
      Disjoint P Y → Disjoint P F → Disjoint Y F →
      let W := replicaMetric ι t k
      let L := fun S => labelEntropy (subsystemPerm k ι S)
      (((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2)⁻¹ ≤
        (((((k : ℝ) + 2) ^ C : ℝ) : ℂ)) •
          NormedSpace.exp (((-(2 * t) : ℝ) : ℂ) • (L P + L F - L Y)) := by
  classical
  obtain ⟨C₀, hC₀, hweight⟩ := exists_abs_log_replicaLabelWeight_add_le ι ht
  refine ⟨6 * C₀, by positivity, ?_⟩
  intro k P Y F hPY hdisPF hYF
  dsimp only
  let hP := isOrthogonalResolution_labelProj (subsystemPerm k ι P)
  let hF := isOrthogonalResolution_labelProj (subsystemPerm k ι F)
  let hY := isOrthogonalResolution_labelProj (subsystemPerm k ι Y)
  let hPF := hP.prod hF (fun α β =>
    commute_labelProj_subsystemPerm_of_disjoint ι k hdisPF α β)
  let R := hPF.prod hY (fun ab γ =>
    (commute_labelProj_subsystemPerm_of_disjoint ι k hPY ab.1 γ).mul_left
      (commute_labelProj_subsystemPerm_of_disjoint ι k hYF.symm ab.2 γ))
  have hRP (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.1.1) = hP.hom f := by
    exact (hPF.prod_hom_fst hY R _).trans (hP.prod_hom_fst hF hPF f)
  have hRF (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.1.2) = hF.hom f := by
    exact (hPF.prod_hom_fst hY R _).trans (hP.prod_hom_snd hF hPF f)
  have hRY (f : IrrepLabel (Equiv.Perm (Fin k)) → ℂ) :
      R.hom (fun p => f p.2) = hY.hom f := by
    exact hPF.prod_hom_snd hY R f
  let w := replicaLabelWeight ι t (k := k)
  have hw (l : IrrepLabel (Equiv.Perm (Fin k))) : 0 < w l :=
    replicaLabelWeight_pos ι ht.le l
  have hWP : (replicaMetric ι t k P)⁻¹ =
      R.hom (fun p => (((w p.1.1)⁻¹ : ℝ) : ℂ)) := by
    rw [replicaMetric, labelObservable_inv _ (fun l => (hw l).ne')]
    simpa only [labelObservable_eq_hom] using
      (hRP (fun l => (((w l)⁻¹ : ℝ) : ℂ))).symm
  have hWF : (replicaMetric ι t k F)⁻¹ =
      R.hom (fun p => (((w p.1.2)⁻¹ : ℝ) : ℂ)) := by
    rw [replicaMetric, labelObservable_inv _ (fun l => (hw l).ne')]
    simpa only [labelObservable_eq_hom] using
      (hRF (fun l => (((w l)⁻¹ : ℝ) : ℂ))).symm
  have hWY : replicaMetric ι t k Y = R.hom (fun p => (w p.2 : ℂ)) := by
    simpa only [replicaMetric, labelObservable_eq_hom] using
      (hRY (fun l => (w l : ℂ))).symm
  let q : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p => (w p.1.1 * w p.1.2 / w p.2) ^ 2
  have hInv : (((replicaMetric ι t k P)⁻¹ * (replicaMetric ι t k F)⁻¹ *
      replicaMetric ι t k Y) ^ 2)⁻¹ = R.hom (fun p => (q p : ℂ)) := by
    apply Matrix.inv_eq_left_inv
    rw [hWP, hWF, hWY, ← map_mul, ← map_mul, ← map_pow, ← map_mul,
      ← map_one R.hom]
    congr 1
    ext p
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.one_apply]
    norm_cast
    dsimp only [q]
    field_simp [(hw p.1.1).ne', (hw p.1.2).ne', (hw p.2).ne']
  let g : (IrrepLabel (Equiv.Perm (Fin k)) × IrrepLabel (Equiv.Perm (Fin k))) ×
      IrrepLabel (Equiv.Perm (Fin k)) → ℝ :=
    fun p => Real.log p.1.1.dim + Real.log p.1.2.dim - Real.log p.2.dim
  have hG : labelEntropy (subsystemPerm k ι P) + labelEntropy (subsystemPerm k ι F) -
      labelEntropy (subsystemPerm k ι Y) = R.hom (fun p => (g p : ℂ)) := by
    simp only [labelEntropy, labelObservable_eq_hom]
    rw [← hRP, ← hRF, ← hRY, ← map_add, ← map_sub]
    congr 1
    ext p
    simp only [g, Pi.add_apply, Pi.sub_apply, Complex.ofReal_sub, Complex.ofReal_add]
  have hExp : NormedSpace.exp (((-(2 * t) : ℝ) : ℂ) •
      (labelEntropy (subsystemPerm k ι P) + labelEntropy (subsystemPerm k ι F) -
        labelEntropy (subsystemPerm k ι Y))) =
      R.hom (fun p => (Real.exp (-(2 * t) * g p) : ℂ)) := by
    rw [hG, ← map_smul, R.exp_hom]
    simp only [Pi.smul_apply, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_exp]
  have hHerm (p : (IrrepLabel (Equiv.Perm (Fin k)) ×
      IrrepLabel (Equiv.Perm (Fin k))) × IrrepLabel (Equiv.Perm (Fin k))) :
      (labelProj (subsystemPerm k ι P) p.1.1 * labelProj (subsystemPerm k ι F) p.1.2 *
        labelProj (subsystemPerm k ι Y) p.2).IsHermitian := by
    exact ((((isHermitian_labelProj _ p.1.1).commute_iff
      (isHermitian_labelProj _ p.1.2)).mp
        (commute_labelProj_subsystemPerm_of_disjoint ι k hdisPF p.1.1 p.1.2)).commute_iff
          (isHermitian_labelProj _ p.2)).mp
            ((commute_labelProj_subsystemPerm_of_disjoint ι k hPY p.1.1 p.2).mul_left
              (commute_labelProj_subsystemPerm_of_disjoint ι k hYF.symm p.1.2 p.2))
  have hcoef (p : (IrrepLabel (Equiv.Perm (Fin k)) ×
      IrrepLabel (Equiv.Perm (Fin k))) × IrrepLabel (Equiv.Perm (Fin k)))
      (hp : labelProj (subsystemPerm k ι P) p.1.1 *
        labelProj (subsystemPerm k ι F) p.1.2 * labelProj (subsystemPerm k ι Y) p.2 ≠ 0) :
      q p ≤ ((k : ℝ) + 2) ^ (6 * C₀) * Real.exp (-(2 * t) * g p) := by
    have hPn : labelProj (subsystemPerm k ι P) p.1.1 ≠ 0 := fun hz =>
      hp (by simp only [hz, zero_mul])
    have hFn : labelProj (subsystemPerm k ι F) p.1.2 ≠ 0 := fun hz =>
      hp (by simp only [hz, mul_zero, zero_mul])
    have hYn : labelProj (subsystemPerm k ι Y) p.2 ≠ 0 := fun hz =>
      hp (by simp only [hz, mul_zero])
    have heP := (abs_le.mp (hweight k P p.1.1 hPn)).2
    have heF := (abs_le.mp (hweight k F p.1.2 hFn)).2
    have heY := (abs_le.mp (hweight k Y p.2 hYn)).1
    have hqpos : 0 < q p :=
      pow_pos (div_pos (mul_pos (hw p.1.1) (hw p.1.2)) (hw p.2)) 2
    have hlog : Real.log (q p) ≤ 6 * C₀ * Real.log ((k : ℝ) + 2) -
        (2 * t) * g p := by
      simp only [q, g, Real.log_pow,
        Real.log_div (mul_pos (hw p.1.1) (hw p.1.2)).ne' (hw p.2).ne',
        Real.log_mul (hw p.1.1).ne' (hw p.1.2).ne']
      dsimp only [w]
      norm_num only
      linarith only [heP, heF, heY]
    calc
      q p = Real.exp (Real.log (q p)) := (Real.exp_log hqpos).symm
      _ ≤ Real.exp (6 * C₀ * Real.log ((k : ℝ) + 2) - (2 * t) * g p) :=
        Real.exp_le_exp.mpr hlog
      _ = ((k : ℝ) + 2) ^ (6 * C₀) * Real.exp (-(2 * t) * g p) := by
        rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
        congr 1
        ring
  have hpos := R.posSemidef_hom_of_ne_zero hHerm
    (f := fun p => ((k : ℝ) + 2) ^ (6 * C₀) * Real.exp (-(2 * t) * g p) - q p)
    (fun p hp => sub_nonneg.mpr (hcoef p hp))
  have hnonneg := hpos.nonneg
  rw [hInv, hExp]
  apply sub_nonneg.mp
  rw [← map_smul, ← map_sub]
  have hcoeffeq : (fun p => ((((k : ℝ) + 2) ^ (6 * C₀) *
      Real.exp (-(2 * t) * g p) - q p : ℝ) : ℂ)) =
      (((((k : ℝ) + 2) ^ (6 * C₀) : ℝ) : ℂ) •
        (fun p => (Real.exp (-(2 * t) * g p) : ℂ))) -
        (fun p => (q p : ℂ)) := by
    ext p
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub,
      Complex.ofReal_mul]
  rw [← hcoeffeq]
  exact hnonneg
end TensorPower

end WholeInverse

section GroupedInverse

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace PermutationRepresentation

private theorem commute_labelObservable_comp_whole
    {G H X : Type*} [Group G] [Fintype G] [Group H] [Fintype H]
    [Fintype X] [DecidableEq X]
    (φ : G →* Equiv.Perm X) (θ : H →* G)
    (f : IrrepLabel H → ℝ) (g : IrrepLabel G → ℝ) :
    Commute (labelObservable (φ.comp θ) f) (labelObservable φ g) := by
  unfold labelObservable
  apply Commute.sum_left
  intro ell _
  apply Commute.sum_right
  intro ell' _
  exact ((commute_labelProj_comp φ θ ell ell').smul_left _).smul_right _

end PermutationRepresentation

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]

local instance replicaGroupedInverse_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

private theorem commute_whole_subgroup_labelEntropy
    {H : Type*} [Group H] [Fintype H] (k : ℕ)
    (θ : H →* Equiv.Perm (Fin k)) (S T : Finset V)
    (hST : S = T ∨ Disjoint S T) :
    Commute (labelEntropy (subsystemPerm k ι S))
      (labelEntropy ((subsystemPerm k ι T).comp θ)) := by
  rcases hST with hST | hST
  · subst S
    exact (commute_labelObservable_comp_whole (subsystemPerm k ι T) θ _ _).symm
  · exact commute_labelObservable_of_commute _ _
      (fun σ τ => commute_subsystemPerm_of_disjoint k ι hST σ (θ τ)) _ _

/-- The whole signed label exponential is bounded by the actual grouped
exponential with the exact binomial loss. All commutations are derived
from the subgroup inclusions and the disjoint subsystems.
Source: `07-comparators.tex`, lines 454--476,
`comparator:restriction-dimensions` and `comparator:whole-inverse`. -/
theorem exp_neg_whole_labelEntropy_le_exp_grouped
    {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    (P Y F : Finset V) (hPY : Disjoint P Y) (hPF : Disjoint P F)
    (hYF : Disjoint Y F) {a : ℝ} (ha : 0 ≤ a) :
    let L := fun S => labelEntropy (subsystemPerm k ι S)
    let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
    let Lb := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₂ e))
    NormedSpace.exp ((-a) • (L P + L F - L Y)) ≤
      (k.choose r : ℝ) ^ a • NormedSpace.exp
        ((-a) • ((Lg P + Lg F - Lg Y) + (Lb P + Lb F - Lb Y))) := by
  intro L Lg Lb
  let D := fun S => Lg S + Lb S
  let Gw := L P + L F - L Y
  let Gs := D P + D F - D Y
  let q := Real.log (k.choose r : ℝ)
  have horder : Gs - q • (1 : Matrix (Config k ι) (Config k ι) ℂ) ≤ Gw := by
    have hP := (groupedCopies_labelEntropy_bounds e (subsystemPerm k ι P)).1
    have hF := (groupedCopies_labelEntropy_bounds e (subsystemPerm k ι F)).1
    have hY := (groupedCopies_labelEntropy_bounds e (subsystemPerm k ι Y)).2
    have h := sub_le_sub (add_le_add hP hF) hY
    simpa only [Gs, Gw, D, L, Lg, Lb, q, Complex.coe_smul, sub_add_eq_sub_sub] using h
  have hc (S T : Finset V) (hST : S = T ∨ Disjoint S T) : Commute (L S) (D T) :=
    (commute_whole_subgroup_labelEntropy ι k (groupHom₁ e) S T hST).add_right
      (commute_whole_subgroup_labelEntropy ι k (groupHom₂ e) S T hST)
  have hrow (S : Finset V) (hSP : S = P ∨ Disjoint S P)
      (hSF : S = F ∨ Disjoint S F) (hSY : S = Y ∨ Disjoint S Y) :
      Commute (L S) Gs :=
    ((hc S P hSP).add_right (hc S F hSF)).sub_right (hc S Y hSY)
  have hcomm : Commute Gw Gs :=
    ((hrow P (Or.inl rfl) (Or.inr hPF) (Or.inr hPY)).add_left
      (hrow F (Or.inr hPF.symm) (Or.inl rfl) (Or.inr hYF.symm))).sub_left
        (hrow Y (Or.inr hPY.symm) (Or.inr hYF) (Or.inl rfl))
  have hL (S : Finset V) : (L S).IsHermitian := isHermitian_labelObservable _ _
  have hD (S : Finset V) : (D S).IsHermitian :=
    (isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)
  have hGw : Gw.IsHermitian := ((hL P).add (hL F)).sub (hL Y)
  have hGs : Gs.IsHermitian := ((hD P).add (hD F)).sub (hD Y)
  have hscaled : (-a) • Gw ≤ (a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ) +
      (-a) • Gs := by
    have h := neg_le_neg (smul_le_smul_of_nonneg_left horder ha)
    simpa only [sub_eq_add_neg, smul_add, smul_neg, smul_smul,
      neg_add_rev, neg_neg, neg_smul] using h
  have hleft : ((-a) • Gw).IsHermitian := hGw.smul (by simp [IsSelfAdjoint])
  have hright : ((a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ) +
      (-a) • Gs).IsHermitian :=
    (isHermitian_one.smul (by simp [IsSelfAdjoint])).add
      (hGs.smul (by simp [IsSelfAdjoint]))
  have hscaledcomm : Commute ((-a) • Gw)
      ((a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ) + (-a) • Gs) :=
    ((Commute.one_right _).smul_right _).add_right
      ((hcomm.smul_left _).smul_right _)
  have hexp := hleft.exp_le_exp_of_commute hright hscaledcomm hscaled
  have hscalar : NormedSpace.exp ((a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ)) =
      Real.exp (a * q) • (1 : Matrix (Config k ι) (Config k ι) ℂ) := by
    simpa only [Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ)
        (𝔸 := Matrix (Config k ι) (Config k ι) ℂ) (a * q)).symm
  have hchoose : (0 : ℝ) < k.choose r := by
    have hk : m + r = k := by simpa using Fintype.card_congr e
    exact_mod_cast Nat.choose_pos (show r ≤ k by omega)
  have hscalar' : Real.exp (a * q) = (k.choose r : ℝ) ^ a := by
    rw [Real.rpow_def_of_pos hchoose]
    congr 1
    exact mul_comm _ _
  rw [Matrix.exp_add_of_commute _ _
    ((Commute.one_left ((-a) • Gs)).smul_left (a * q)),
    hscalar, hscalar', smul_mul_assoc, one_mul] at hexp
  have hGs' : Gs = (Lg P + Lg F - Lg Y) + (Lb P + Lb F - Lb Y) := by
    dsimp only [Gs, D]
    abel
  simpa only [Gw, hGs'] using hexp

variable [∀ v, Nonempty (ι v)]

/-- The actual whole-space inverse replica metric admits the grouped-copy
bound, with the same full-system weights and exactly the binomial power `2t`.
The polynomial constant is selected before the copy number, the split, and
the three disjoint subsystems. Source: `07-comparators.tex`,
`comparator:whole-inverse`, lines 454--476. -/
theorem exists_replicaMetric_inv_square_le_grouped_exp {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m r k : ℕ) (e : Fin m ⊕ Fin r ≃ Fin k)
      (P Y F : Finset V), Disjoint P Y → Disjoint P F → Disjoint Y F →
      let W := replicaMetric ι t k
      let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
      let Lb := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₂ e))
      (((W P)⁻¹ * (W F)⁻¹ * W Y) ^ 2)⁻¹ ≤
        (((k : ℝ) + 2) ^ C * (k.choose r : ℝ) ^ (2 * t)) •
          NormedSpace.exp ((-(2 * t)) •
            ((Lg P + Lg F - Lg Y) + (Lb P + Lb F - Lb Y))) := by
  obtain ⟨C, hC, hwhole⟩ := exists_replicaMetric_inv_square_le_exp ι ht
  refine ⟨C, hC, ?_⟩
  intro m r k e P Y F hPY hPF hYF
  dsimp only
  have hgroup := exp_neg_whole_labelEntropy_le_exp_grouped ι e P Y F hPY hPF hYF
    (show 0 ≤ 2 * t by positivity)
  have h := smul_le_smul_of_nonneg_left hgroup
    (Real.rpow_nonneg (by positivity : 0 ≤ (k : ℝ) + 2) C)
  have hwhole' := hwhole k P Y F hPY hPF hYF
  simp only [Complex.coe_smul] at hwhole'
  exact hwhole'.trans (by simpa only [smul_smul] using h)

end TensorPower

end

end GroupedInverse
