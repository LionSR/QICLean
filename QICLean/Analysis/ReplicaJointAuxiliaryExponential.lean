/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiveFactorAuxiliaryCoordinates
import QICLean.Analysis.InvariantExponentialComparison
import QICLean.Analysis.ReplicaGoodAuxiliaryLabelBound
import QICLean.Representation.GoodAuxiliaryPairCompression
import QICLean.Representation.ReplicaSimilarity

/-!
# Joint auxiliary removal for the actual good-copy expectation

The original whole-copy auxiliary labels define a common projection range.
On that range the sum of the two good auxiliary entropies has the summed
floor, with both bad-copy and both binomial corrections. Every remaining
good-copy factor preserves the same range by the actual nesting and
disjointness of the five physical factors. One compressed exponential
comparison therefore removes both auxiliary exponentials simultaneously.

The original labels are retained after the literal physical excitation
operation and transported through the existing five-factor equivalence.
No independence, normalization, full-space lower bound, or additional label
selection is assumed. The auxiliary labels may be different.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 481--508,
`comparator:good-auxiliary` and `comparator:merge-decomposition`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Matrix ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace TensorPower

local instance replicaJointAuxiliaryExponential_genericDecidableEqConfig
    {V : Type*} [Fintype V] [DecidableEq V] (ι : V → Type*)
    [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)] (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

private theorem commute_subgroup_labelObservables_of_subset_or_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
    {m k : ℕ} (θ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin k))
    (S T : Finset V) (hST : S ⊆ T ∨ Disjoint S T)
    (f g : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    Commute (labelObservable ((subsystemPerm k ι S).comp θ) f)
      (labelObservable ((subsystemPerm k ι T).comp θ) g) := by
  rcases hST with hST | hST
  · rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep]
    apply commute_groupAlgebraRep_of_eq_mul
      ((subsystemPerm k ι S).comp θ) ((subsystemPerm k ι (T \ S)).comp θ)
      ((subsystemPerm k ι T).comp θ) _ _ (sum_smul_centralIdem_mem_center f)
    · intro σ
      change subsystemPerm k ι T (θ σ) = _
      conv_lhs => rw [← Finset.union_sdiff_of_subset hST]
      exact subsystemPerm_union k ι Finset.disjoint_sdiff (θ σ)
    · exact fun σ τ => commute_subsystemPerm_of_disjoint k ι
        Finset.disjoint_sdiff (θ σ) (θ τ)
  · exact commute_labelObservable_of_commute _ _
      (fun σ τ => commute_subsystemPerm_of_disjoint k ι hST (θ σ) (θ τ)) f g

private theorem commute_whole_labelProj_subgroup_labelObservable
    {V : Type*} [Fintype V] [DecidableEq V]
    (ι : V → Type*) [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]
    {m k : ℕ} (θ : Equiv.Perm (Fin m) →* Equiv.Perm (Fin k))
    (S T : Finset V) (hST : S ⊆ T ∨ Disjoint S T)
    (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (g : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    Commute (labelProj (subsystemPerm k ι S) ell)
      (labelObservable ((subsystemPerm k ι T).comp θ) g) := by
  apply Commute.symm
  apply commute_labelObservable_of_forall_commute
  intro σ
  apply Commute.symm
  rcases hST with hST | hST
  · simpa only [labelProj, groupAlgebraRep_single, permOp_comp, one_smul] using
      commute_groupAlgebraRep_subsystemPerm_of_subset ι k hST
        (IrrepLabel.centralIdem_mem_center ell) (MonoidAlgebra.single (θ σ) (1 : ℂ))
  · simpa only [labelProj, groupAlgebraRep_single, permOp_comp, one_smul] using
      commute_groupAlgebraRep_subsystemPerm_of_disjoint ι k hST
        (IrrepLabel.centralIdem ell) (MonoidAlgebra.single (θ σ) (1 : ℂ))

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- The actual five-factor auxiliary label intersection has the summed
good-copy entropy floor. The projection and entropy are transported from
their literal auxiliary tensor factors, without a supplied coordinate
identity. Source: `07-comparators.tex`, lines 481--493. -/
theorem fiveFactor_groupedGood_auxiliaryPair_floor
    {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) :
    let P := labelProj (subsystemPerm k ι {3}) ellC *
      labelProj (subsystemPerm k ι {4}) ellR
    let L := labelEntropy ((subsystemPerm k ι {3}).comp (groupHom₁ e)) +
      labelEntropy ((subsystemPerm k ι {4}).comp (groupHom₁ e))
    let b := Real.log ellC.dim + Real.log ellR.dim -
      (r : ℝ) * (Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))) -
        2 * Real.log (k.choose r)
    IsStarProjection P ∧ b • P ≤ P * L * P := by
  intro P L b
  let η := fiveFactorCopiesEquiv ι k
  let PC := labelProj (copyPerm (ι 3) k) ellC
  let PR := labelProj (copyPerm (ι 4) k) ellR
  let FC := labelEntropy ((copyPerm (ι 3) k).comp (groupHom₁ e))
  let FR := labelEntropy ((copyPerm (ι 4) k).comp (groupHom₁ e))
  let Pf := (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
    (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ (PC ⊗ₖ PR)
  let Lf := (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
    (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      (FC ⊗ₖ (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ) +
        (1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ FR)
  have hPC : (labelProj (subsystemPerm k ι {3}) ellC).submatrix η.symm η.symm =
      (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (PC ⊗ₖ (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ)) := by
    simpa only [MonoidHom.comp_id, PC, η, labelProj] using
      (fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep ι k
        (MonoidHom.id (Equiv.Perm (Fin k))) (IrrepLabel.centralIdem ellC)).1
  have hPR : (labelProj (subsystemPerm k ι {4}) ellR).submatrix η.symm η.symm =
      (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ PR) := by
    simpa only [MonoidHom.comp_id, PR, η, labelProj] using
      (fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep ι k
        (MonoidHom.id (Equiv.Perm (Fin k))) (IrrepLabel.centralIdem ellR)).2
  have hP : P.submatrix η.symm η.symm = Pf := by
    dsimp only [P]
    rw [← submatrix_mul_equiv, hPC, hPR]
    simp only [Pf, ← mul_kronecker_mul, one_mul, mul_one]
  have hLC := (fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep ι k (groupHom₁ e)
    (∑ ell, (Real.log ell.dim : ℂ) • IrrepLabel.centralIdem ell)).1
  have hLR := (fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep ι k (groupHom₁ e)
    (∑ ell, (Real.log ell.dim : ℂ) • IrrepLabel.centralIdem ell)).2
  have hL : L.submatrix η.symm η.symm = Lf := by
    simpa only [L, Lf, FC, FR, η, labelEntropy, labelObservable_eq_groupAlgebraRep,
      submatrix_add, Pi.add_apply, kronecker_add] using congrArg₂ (fun A B => A + B) hLC hLR
  have hPback : Pf.submatrix η η = P := by
    ext x y
    simpa only [submatrix_apply, Equiv.symm_apply_apply] using
      congrArg (fun M => M (η x) (η y)) hP.symm
  have hLback : Lf.submatrix η η = L := by
    ext x y
    simpa only [submatrix_apply, Equiv.symm_apply_apply] using
      congrArg (fun M => M (η x) (η y)) hL.symm
  have hstar (S : Finset (Fin 5)) (ell : IrrepLabel (Equiv.Perm (Fin k))) :
      IsStarProjection (labelProj (subsystemPerm k ι S) ell) := by
    rw [isStarProjection_iff']
    exact ⟨labelProj_mul_self _ _, (isHermitian_labelProj _ _).isSelfAdjoint⟩
  refine ⟨(hstar {3} ellC).mul (hstar {4} ellR)
    (commute_labelProj_subsystemPerm_of_disjoint ι k (by decide) ellC ellR), ?_⟩
  have hfloor := (copyPerm_groupedGood_auxiliaryPair_labelEntropy_compression
    (A := Fin k → ι 0 × (ι 1 × ι 2)) (C := ι 3) (R := ι 4) e ellC ellR).2.2
  have h := (Matrix.le_iff.mp hfloor).submatrix η
  apply Matrix.le_iff.mpr
  simpa only [submatrix_sub, submatrix_smul, ← submatrix_mul_equiv,
    hPback, hLback] using h

/-- Both auxiliary exponentials can be removed on the intersection of the
original whole-label subspaces while retaining the actual remaining good
factors. Every support-preserving commutation is derived from the specified
subsystems. Source: `07-comparators.tex`, lines 481--508. -/
theorem fiveFactor_groupedGood_exp_le_without_auxiliary
    {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) {a : ℝ} (ha : 0 ≤ a)
    {v : Config k ι → ℂ}
    (hv : (labelProj (subsystemPerm k ι {3}) ellC *
      labelProj (subsystemPerm k ι {4}) ellR) *ᵥ v = v) :
    let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
    let G := Lg {0, 3} + Lg {2, 4} - Lg {1}
    let L := Lg {3} + Lg {4}
    let b := Real.log ellC.dim + Real.log ellR.dim -
      (r : ℝ) * (Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))) -
        2 * Real.log (k.choose r)
    (star v ⬝ᵥ (NormedSpace.exp ((-a) • G) *ᵥ v)).re ≤
      Real.exp (-a * b) *
        (star v ⬝ᵥ (NormedSpace.exp ((-a) • (G - L)) *ᵥ v)).re := by
  intro Lg G L b
  let PC := labelProj (subsystemPerm k ι {3}) ellC
  let PR := labelProj (subsystemPerm k ι {4}) ellR
  let P := PC * PR
  have hw (S T : Finset (Fin 5)) (hST : S ⊆ T ∨ Disjoint S T)
      (ell : IrrepLabel (Equiv.Perm (Fin k))) :
      Commute (labelProj (subsystemPerm k ι S) ell) (Lg T) :=
    commute_whole_labelProj_subgroup_labelObservable ι (groupHom₁ e) S T hST ell _
  have hs (S T : Finset (Fin 5)) (hST : S ⊆ T ∨ Disjoint S T) :
      Commute (Lg S) (Lg T) :=
    commute_subgroup_labelObservables_of_subset_or_disjoint ι (groupHom₁ e) S T hST _ _
  have hPCG : Commute PC G :=
    ((hw {3} {0, 3} (Or.inl (by decide)) ellC).add_right
      (hw {3} {2, 4} (Or.inr (by decide)) ellC)).sub_right
        (hw {3} {1} (Or.inr (by decide)) ellC)
  have hPRG : Commute PR G :=
    ((hw {4} {0, 3} (Or.inr (by decide)) ellR).add_right
      (hw {4} {2, 4} (Or.inl (by decide)) ellR)).sub_right
        (hw {4} {1} (Or.inr (by decide)) ellR)
  have hPCL : Commute PC L :=
    (hw {3} {3} (Or.inl (by decide)) ellC).add_right
      (hw {3} {4} (Or.inr (by decide)) ellC)
  have hPRL : Commute PR L :=
    (hw {4} {3} (Or.inr (by decide)) ellR).add_right
      (hw {4} {4} (Or.inl (by decide)) ellR)
  have hCLG : Commute (Lg {3}) G :=
    ((hs {3} {0, 3} (Or.inl (by decide))).add_right
      (hs {3} {2, 4} (Or.inr (by decide)))).sub_right
        (hs {3} {1} (Or.inr (by decide)))
  have hRLG : Commute (Lg {4}) G :=
    ((hs {4} {0, 3} (Or.inr (by decide))).add_right
      (hs {4} {2, 4} (Or.inl (by decide)))).sub_right
        (hs {4} {1} (Or.inr (by decide)))
  have hGL : Commute G L := (hCLG.add_left hRLG).symm
  have hLP : Commute L P := hPCL.symm.mul_right hPRL.symm
  have hHP : Commute (G - L) P :=
    (hPCG.sub_right hPCL).symm.mul_right (hPRG.sub_right hPRL).symm
  have hHL : Commute (G - L) L := hGL.sub_left (Commute.refl L)
  obtain ⟨hP, hfloor⟩ := fiveFactor_groupedGood_auxiliaryPair_floor ι e ellC ellR
  have hG : G.IsHermitian :=
    ((isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)).sub
      (isHermitian_labelObservable _ _)
  have hL : L.IsHermitian :=
    (isHermitian_labelObservable _ _).add (isHermitian_labelObservable _ _)
  have hbound := hL.compression_exp_neg_smul_le_of_lower_bound hP hLP hfloor ha
  have h := Matrix.IsHermitian.re_dotProduct_exp_add_le_of_compressed_exp_le_smul
    ((hG.sub hL).smul (show IsSelfAdjoint (-a) by simp [isSelfAdjoint_iff]))
    hP.isSelfAdjoint.isHermitian (hHP.smul_left (-a))
    ((hHL.smul_left (-a)).smul_right (-a)) hbound hv
  simpa only [← smul_add, sub_add_cancel] using h

end TensorPower

namespace Matrix

open TensorPower

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

local instance replicaJointAuxiliaryExponential_componentDecidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The same literal excitation component retains both original whole-copy
auxiliary labels, and therefore obeys the joint auxiliary-removal bound.
The original labels may differ; no component support certificate or
normalization is assumed. Source: `07-comparators.tex`, lines 441--456
and 481--508. -/
theorem replicaExcitationComponent_exp_good_le_without_auxiliary
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k)))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (huC : ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      (labelProj (copyPerm (ι 3) k) ellC ⊗ₖ
        (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ))) *ᵥ u = u)
    (huR : ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
      ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
        labelProj (copyPerm (ι 4) k) ellR)) *ᵥ u = u)
    {a : ℝ} (ha : 0 ≤ a) :
    let e := replicaGoodBadSplit B
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let f := w ∘ fiveFactorCopiesEquiv ι k
    let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
    let G := Lg {0, 3} + Lg {2, 4} - Lg {1}
    let L := Lg {3} + Lg {4}
    let b := Real.log ellC.dim + Real.log ellR.dim -
      (B.card : ℝ) * (Real.log (Fintype.card (ι 3)) + Real.log (Fintype.card (ι 4))) -
        2 * Real.log (k.choose B.card)
    (star f ⬝ᵥ (NormedSpace.exp ((-a) • G) *ᵥ f)).re ≤
      Real.exp (-a * b) *
        (star f ⬝ᵥ (NormedSpace.exp ((-a) • (G - L)) *ᵥ f)).re := by
  intro e w f Lg G L b
  let η := fiveFactorCopiesEquiv ι k
  let PC := labelProj (copyPerm (ι 3) k) ellC
  let PR := labelProj (copyPerm (ι 4) k) ellR
  have hu : ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
      (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ (PC ⊗ₖ PR)) *ᵥ u = u := by
    have hproduct :
        ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
          (PC ⊗ₖ (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ))) *
        ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
          ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ PR)) =
        (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
          (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ (PC ⊗ₖ PR) := by
      simp only [← mul_kronecker_mul, one_mul, mul_one]
    rw [← hproduct, ← mulVec_mulVec, huR, huC]
  have hw : ((1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
      (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ (PC ⊗ₖ PR)) *ᵥ w = w := by
    simpa only [map_one] using
      replicaExcitationProjection_kronecker_mulVec_preserves_fixed Ω k B 1 (by simp)
        (PC ⊗ₖ PR) u (by simpa only [map_one] using hu)
  have hC := (fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep ι k
    (MonoidHom.id (Equiv.Perm (Fin k))) (IrrepLabel.centralIdem ellC)).1
  have hR := (fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep ι k
    (MonoidHom.id (Equiv.Perm (Fin k))) (IrrepLabel.centralIdem ellR)).2
  simp only [MonoidHom.comp_id] at hC hR
  have hP : (labelProj (subsystemPerm k ι {3}) ellC *
      labelProj (subsystemPerm k ι {4}) ellR).submatrix η.symm η.symm =
      (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2))
        (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ (PC ⊗ₖ PR) := by
    rw [← submatrix_mul_equiv, hC, hR]
    simp only [PC, PR, ← mul_kronecker_mul, one_mul, mul_one]
  rw [← hP, submatrix_mulVec_equiv] at hw
  have hf : (labelProj (subsystemPerm k ι {3}) ellC *
      labelProj (subsystemPerm k ι {4}) ellR) *ᵥ f = f := by
    funext x
    simpa only [f, η, Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply] using
      congrFun hw (η x)
  exact fiveFactor_groupedGood_exp_le_without_auxiliary ι e ellC ellR ha hf

end Matrix
