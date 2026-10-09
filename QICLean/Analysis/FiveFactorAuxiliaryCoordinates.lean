/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Representation.ReplicaMetric

/-!
# Auxiliary operators in the five-factor coordinates

The existing five-factor equivalence identifies each auxiliary copy action
with its literal tensor-factor action, leaving the physical copies and the
other auxiliary register fixed. The identities extend to every group-algebra
element of every copy subgroup. In particular they apply to the original
whole-copy label projections and to the good-copy label entropies.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 481--493 and 520--549,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped Matrix Kronecker

namespace TensorPower

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

local instance fiveFactorAuxiliaryCoordinates_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- The two auxiliary copy permutations become their literal tensor-factor
actions under the existing five-factor equivalence.
Source: `07-comparators.tex`, lines 481--493 and 520--549. -/
theorem fiveFactorCopiesEquiv_auxiliary_permOp (k : ℕ)
    (σ : Equiv.Perm (Fin k)) :
    (permOp (subsystemPerm k ι {3}) σ).submatrix
        (fiveFactorCopiesEquiv ι k).symm (fiveFactorCopiesEquiv ι k).symm =
      (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2)) (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ
          (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ)) ∧
    (permOp (subsystemPerm k ι {4}) σ).submatrix
        (fiveFactorCopiesEquiv ι k).symm (fiveFactorCopiesEquiv ι k).symm =
      (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2)) (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
          permOp (copyPerm (ι 4) k) σ) := by
  have hC (x : Config k ι) :
      fiveFactorCopiesEquiv ι k (subsystemPerm k ι {3} σ x) =
        ((fiveFactorCopiesEquiv ι k x).1,
          (copyPerm (ι 3) k σ ((fiveFactorCopiesEquiv ι k x).2.1),
            (fiveFactorCopiesEquiv ι k x).2.2)) := by rfl
  have hR (x : Config k ι) :
      fiveFactorCopiesEquiv ι k (subsystemPerm k ι {4} σ x) =
        ((fiveFactorCopiesEquiv ι k x).1,
          ((fiveFactorCopiesEquiv ι k x).2.1,
            copyPerm (ι 4) k σ ((fiveFactorCopiesEquiv ι k x).2.2))) := by rfl
  constructor
  · ext x y
    have hc : subsystemPerm k ι {3} σ ((fiveFactorCopiesEquiv ι k).symm y) =
        (fiveFactorCopiesEquiv ι k).symm x ↔
        y.1 = x.1 ∧ copyPerm (ι 3) k σ y.2.1 = x.2.1 ∧ y.2.2 = x.2.2 := by
      rw [← (fiveFactorCopiesEquiv ι k).injective.eq_iff, hC]
      simp only [Equiv.apply_symm_apply, Prod.ext_iff]
    simp only [submatrix_apply, permOp_apply_apply, hc, kroneckerMap_apply, one_apply]
    split_ifs <;> simp_all [eq_comm]
  · ext x y
    have hr : subsystemPerm k ι {4} σ ((fiveFactorCopiesEquiv ι k).symm y) =
        (fiveFactorCopiesEquiv ι k).symm x ↔
        y.1 = x.1 ∧ y.2.1 = x.2.1 ∧ copyPerm (ι 4) k σ y.2.2 = x.2.2 := by
      rw [← (fiveFactorCopiesEquiv ι k).injective.eq_iff, hR]
      simp only [Equiv.apply_symm_apply, Prod.ext_iff]
    simp only [submatrix_apply, permOp_apply_apply, hr, kroneckerMap_apply, one_apply]
    split_ifs <;> simp_all [eq_comm]

/-- Every subgroup group-algebra operator on an auxiliary factor is
transported by the same literal five-factor equivalence. The subgroup need
not be injectively represented. Source: `07-comparators.tex`, lines 481--493
and 520--549. -/
theorem fiveFactorCopiesEquiv_auxiliary_groupAlgebraRep
    {G : Type*} [Group G] (k : ℕ) (θ : G →* Equiv.Perm (Fin k))
    (a : MonoidAlgebra ℂ G) :
    (groupAlgebraRep ((subsystemPerm k ι {3}).comp θ) a).submatrix
        (fiveFactorCopiesEquiv ι k).symm (fiveFactorCopiesEquiv ι k).symm =
      (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2)) (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        (groupAlgebraRep ((copyPerm (ι 3) k).comp θ) a ⊗ₖ
          (1 : Matrix (Fin k → ι 4) (Fin k → ι 4) ℂ)) ∧
    (groupAlgebraRep ((subsystemPerm k ι {4}).comp θ) a).submatrix
        (fiveFactorCopiesEquiv ι k).symm (fiveFactorCopiesEquiv ι k).symm =
      (1 : Matrix (Fin k → ι 0 × (ι 1 × ι 2)) (Fin k → ι 0 × (ι 1 × ι 2)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin k → ι 3) (Fin k → ι 3) ℂ) ⊗ₖ
          groupAlgebraRep ((copyPerm (ι 4) k).comp θ) a) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => constructor <;> simp
  | add a b ha hb =>
    constructor
    · simp only [map_add, submatrix_add, Pi.add_apply, ha.1, hb.1,
        add_kronecker, kronecker_add]
    · simp only [map_add, submatrix_add, Pi.add_apply, ha.2, hb.2,
        add_kronecker, kronecker_add]
  | single σ c =>
    have h := fiveFactorCopiesEquiv_auxiliary_permOp ι k (θ σ)
    constructor
    · simpa only [groupAlgebraRep_single, permOp_comp, submatrix_smul, Pi.smul_apply,
        smul_kronecker, kronecker_smul] using congrArg (fun M => c • M) h.1
    · simpa only [groupAlgebraRep_single, permOp_comp, submatrix_smul, Pi.smul_apply,
        smul_kronecker, kronecker_smul] using congrArg (fun M => c • M) h.2

end TensorPower
