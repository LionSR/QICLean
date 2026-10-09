/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InvariantExponentialComparison
import QICLean.Analysis.ProjectionCfcUpperBound
import QICLean.Analysis.ReplicaGoodAuxiliaryLabelBound
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Representation.GroupedLabelSymmetricSupport

/-!
# Removing the bad-copy exponential on an actual excitation component

The literal component associated with an excited subset inherits simultaneous
symmetry under permutations of that subset. In the five-factor coordinates
Q, Y, V, C, R, its bad-copy signed label operator is therefore nonnegative
on the component's simultaneous symmetric subspace. Every good-copy label
observable preserves this subspace. The bad exponential may consequently
be removed from the expectation of the grouped exponential.

The only symmetry assumption concerns the original vector. Neither positivity
of the signed label operator on the full space nor commutation of the
excitation projection with the metric is assumed. No normalization is needed,
and zero components and zero copies are included. The good/bad enumeration is
the same literal enumeration used for the actual good auxiliary marginal.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 441--480,
`comparator:defect-mass` and `comparator:whole-inverse`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace TensorPower

section Grouped

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]

local instance replicaBadCopyExponential_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- Bad simultaneous symmetry removes the bad signed exponential from the
actual grouped label expectation. The good signed operator preserves the
required support by disjointness of the copy groups, even though the same
physical regions occur in both groups. Source: `07-comparators.tex`,
lines 454--480. -/
theorem re_dotProduct_exp_grouped_signedLabelEntropy_le
    {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    (P Y F : Finset V) (hPY : Disjoint P Y) (hPF : Disjoint P F)
    (hYF : Disjoint Y F) (hcover : Y ∪ (P ∪ F) = Finset.univ)
    {a : ℝ} (ha : 0 ≤ a) {v : Config k ι → ℂ}
    (hv : v ∈ invariantSubspace ((subsystemPerm k ι Finset.univ).comp (groupHom₂ e))) :
    let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
    let Lb := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₂ e))
    let Gg := Lg P + Lg F - Lg Y
    let Gb := Lb P + Lb F - Lb Y
    (star v ⬝ᵥ (NormedSpace.exp ((-a) • (Gg + Gb)) *ᵥ v)).re ≤
      (star v ⬝ᵥ (NormedSpace.exp ((-a) • Gg) *ᵥ v)).re := by
  intro Lg Lb Gg Gb
  let Q := symProj ((subsystemPerm k ι Finset.univ).comp (groupHom₂ e))
  have hQ : IsStarProjection Q :=
    (exists_labelProj_eq_symProj (G := Equiv.Perm (Fin r))
      (X := Config k ι)).elim (fun ell h =>
        Eq.mp (congrArg IsStarProjection
          (h ((subsystemPerm k ι Finset.univ).comp (groupHom₂ e))))
          (show IsStarProjection
            (labelProj ((subsystemPerm k ι Finset.univ).comp (groupHom₂ e)) ell) from
              ⟨labelProj_mul_self _ ell, (isHermitian_labelProj _ ell).isSelfAdjoint⟩))
  have hQv : Q *ᵥ v = v := symProj_mulVec_of_mem _ hv
  have hbad := subgroup_signedLabelEntropy_symProj_nonneg ι (groupHom₂ e)
    P Y F hPY hPF hYF hcover
  have hGb : Gb.IsHermitian :=
    ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)
  have hGg : Gg.IsHermitian :=
    ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)
  have hbound : Q * NormedSpace.exp ((-a) • Gb) * Q ≤ Q := by
    have h := hGb.compression_exp_neg_smul_le_of_lower_bound hQ hbad.1
      (b := 0) (by simpa only [zero_smul] using hbad.2) ha
    simpa only [mul_zero, Real.exp_zero, one_smul] using h
  have hc (S : Finset V) : Commute (Lg S) Q :=
    commute_good_labelObservable_bad_symProj ι e S (fun ell => Real.log ell.dim)
  have hGgQ : Commute Gg Q := ((hc P).add_left (hc F)).sub_left (hc Y)
  have hc' (S T : Finset V) : Commute (Lg S) (Lb T) :=
    commute_grouped_labelObservables ι e S T _ _
  have hrow (S : Finset V) : Commute (Lg S) Gb :=
    ((hc' S P).add_right (hc' S F)).sub_right (hc' S Y)
  have hGgGb : Commute Gg Gb := ((hrow P).add_left (hrow F)).sub_left (hrow Y)
  simpa only [smul_add] using
    Matrix.IsHermitian.re_dotProduct_exp_add_le_of_compressed_exp_le
      (hGg.smul (show IsSelfAdjoint (-a) by simp [isSelfAdjoint_iff]))
      hQ.isSelfAdjoint.isHermitian (hGgQ.smul_left (-a))
      ((hGgGb.smul_left (-a)).smul_right (-a)) hbound hQv

end Grouped

section FiveFactors

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

local instance replicaBadCopyExponential_fiveFactorDecidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The existing five-factor coordinate equivalence transports simultaneous
copy permutation to the three literal physical and auxiliary actions.
Source: `07-comparators.tex`, lines 427--456. -/
theorem fiveFactorCopiesEquiv_simultaneous_permOp (k : ℕ)
    (σ : Equiv.Perm (Fin k)) :
    (permOp (copyPerm ((f : Fin 5) → ι f) k) σ).submatrix
      (fiveFactorCopiesEquiv ι k).symm (fiveFactorCopiesEquiv ι k).symm =
      permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ) := by
  have he (x : Config k ι) :
      fiveFactorCopiesEquiv ι k (copyPerm ((f : Fin 5) → ι f) k σ x) =
        (copyPerm (ι 0 × (ι 1 × ι 2)) k σ ((fiveFactorCopiesEquiv ι k x).1),
          (copyPerm (ι 3) k σ ((fiveFactorCopiesEquiv ι k x).2.1),
            copyPerm (ι 4) k σ ((fiveFactorCopiesEquiv ι k x).2.2))) := by
    rfl
  have hcondition (x y : (Fin k → ι 0 × (ι 1 × ι 2)) ×
      ((Fin k → ι 3) × (Fin k → ι 4))) :
      copyPerm ((f : Fin 5) → ι f) k σ ((fiveFactorCopiesEquiv ι k).symm y) =
          (fiveFactorCopiesEquiv ι k).symm x ↔
        copyPerm (ι 0 × (ι 1 × ι 2)) k σ y.1 = x.1 ∧
          copyPerm (ι 3) k σ y.2.1 = x.2.1 ∧
            copyPerm (ι 4) k σ y.2.2 = x.2.2 := by
    rw [← (fiveFactorCopiesEquiv ι k).injective.eq_iff, he]
    simp only [Equiv.apply_symm_apply, Prod.ext_iff]
  ext x y
  simp only [Matrix.submatrix_apply, permOp_apply_apply, hcondition, kroneckerMap_apply]
  simp only [ite_zero_mul_ite_zero, one_mul]

end FiveFactors

end TensorPower

namespace Matrix

open TensorPower

/-- The actual bad subgroup preserves the actual excited subset.
Source: `07-comparators.tex`, lines 441--456. -/
theorem replicaGoodBadSplit_bad_image {k : ℕ} (B : Finset (Fin k))
    (τ : Equiv.Perm (Fin B.card)) :
    B.image (groupHom₂ (replicaGoodBadSplit B) τ) = B := by
  have hmaps : ∀ i ∈ B, groupHom₂ (replicaGoodBadSplit B) τ i ∈ B := by
    intro i hi
    obtain ⟨j, hj⟩ := B.equivFin.symm.surjective ⟨i, hi⟩
    have hie : i = replicaGoodBadSplit B (Sum.inr j) := by
      change i = (B.equivFin.symm j).val
      exact (congrArg Subtype.val hj).symm
    rw [hie]
    have haction : groupHom₂ (replicaGoodBadSplit B) τ
        (replicaGoodBadSplit B (Sum.inr j)) =
        replicaGoodBadSplit B (Sum.inr (τ j)) := by
      simp [groupHom₂, youngHom, Equiv.permCongrHom, Equiv.permCongr_def]
    rw [haction]
    exact (B.equivFin.symm (τ j)).property
  apply Finset.eq_of_subset_of_card_le (Finset.image_subset_iff.mpr hmaps)
  rw [Finset.card_image_of_injective _ (groupHom₂ (replicaGoodBadSplit B) τ).injective]

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

local instance replicaBadCopyExponential_componentDecidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The actual excitation component is symmetric under simultaneous
permutation of its bad copies. The component support follows from the
symmetry of the original vector. Source: `07-comparators.tex`, lines 441--456. -/
theorem replicaExcitationComponent_mem_bad_invariantSubspace
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    w ∘ fiveFactorCopiesEquiv ι k ∈
      invariantSubspace ((subsystemPerm k ι Finset.univ).comp
        (groupHom₂ (replicaGoodBadSplit B))) := by
  intro w τ
  let σ := groupHom₂ (replicaGoodBadSplit B) τ
  have hw := replicaExcitationProjection_kronecker_mulVec_preserves_fixed Ω k B σ
    (replicaGoodBadSplit_bad_image B τ)
    (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ) u (hu σ)
  change (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
    (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ)) *ᵥ w = w at hw
  rw [← fiveFactorCopiesEquiv_simultaneous_permOp ι k σ, submatrix_mulVec_equiv] at hw
  rw [subsystemPerm_univ]
  change permOp (copyPerm ((f : Fin 5) → ι f) k) σ *ᵥ
    (w ∘ fiveFactorCopiesEquiv ι k) = w ∘ fiveFactorCopiesEquiv ι k
  funext x
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm] using
    congrFun hw (fiveFactorCopiesEquiv ι k x)

/-- The bad signed exponential may be removed from the grouped metric
expectation of the literal excitation component. The physical regions are
`P=Q∪C`, `Y=Y`, and `F=V∪R`, with the original five factors retained.
Source: `07-comparators.tex`, lines 454--480. -/
theorem replicaExcitationComponent_exp_grouped_le_good
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    {a : ℝ} (ha : 0 ≤ a) :
    let e := replicaGoodBadSplit B
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let f := w ∘ fiveFactorCopiesEquiv ι k
    let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
    let Lb := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₂ e))
    let Gg := Lg {0, 3} + Lg {2, 4} - Lg {1}
    let Gb := Lb {0, 3} + Lb {2, 4} - Lb {1}
    (star f ⬝ᵥ (NormedSpace.exp ((-a) • (Gg + Gb)) *ᵥ f)).re ≤
      (star f ⬝ᵥ (NormedSpace.exp ((-a) • Gg) *ᵥ f)).re := by
  intro e w f Lg Lb Gg Gb
  exact re_dotProduct_exp_grouped_signedLabelEntropy_le ι e {0, 3} {1} {2, 4}
    (by decide) (by decide) (by decide) (by decide) ha
    (replicaExcitationComponent_mem_bad_invariantSubspace ι Ω k B u hu)

end Matrix
