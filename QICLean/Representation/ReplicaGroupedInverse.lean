/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CommutingExponentialOrder
import QICLean.Representation.GroupedLabelEntropy
import QICLean.Representation.ReplicaWholeInverse

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

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 454--476,
  `comparator:restriction-dimensions` and `comparator:whole-inverse`,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

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
    simpa only [Complex.coe_smul, sub_add_eq_sub_sub] using h
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
    simpa only [smul_sub, smul_smul, neg_sub, neg_smul, sub_eq_add_neg] using h
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
