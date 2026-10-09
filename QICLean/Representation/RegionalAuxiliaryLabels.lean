/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RegionalFiveFactorCoordinates
import QICLean.Representation.SubsystemTransport

/-!
# The original auxiliary labels in fixed physical-copy coordinates

The fixed regrouping of the global configuration identifies the two original
auxiliary-site projections with the corresponding whole-copy label
projections. Both auxiliary registers retain their original order and labels.
No vector, normalization, symmetry, or regional cut is supplied.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, `comparator:defect-mass`, lines 421--443,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section
open Matrix PermutationRepresentation
open scoped Kronecker

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)
variable [∀ x, Fintype (β x)] [∀ x, DecidableEq (β x)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R

local instance regionalAuxiliaryLabels_decidableEqPhysical :
    DecidableEq ((x : V) → β x) := Fintype.decidablePiFintype

local instance regionalAuxiliaryLabels_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

/-- The two original auxiliary-site projections in the fixed physical-copy
coordinates. Source: `07-comparators.tex`, `comparator:defect-mass`,
lines 421--443. -/
theorem labelProj_globalReplicaCopiesEquiv_auxiliary
    (k : ℕ) (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) :
    let e := globalReplicaCopiesEquiv β C R k
    let I := (1 : Matrix (Fin k → (x : V) → β x) (Fin k → (x : V) → β x) ℂ)
    ((I ⊗ₖ (labelProj (copyPerm C k) ellC ⊗ₖ
        (1 : Matrix (Fin k → R) (Fin k → R) ℂ))).submatrix e e =
      labelProj (subsystemPerm k ι₀ {some none}) ellC) ∧
    ((I ⊗ₖ ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ
        labelProj (copyPerm R k) ellR)).submatrix e e =
      labelProj (subsystemPerm k ι₀ {none}) ellR) := by
  intro e I
  let eC := e.trans
    ((Equiv.prodComm (Fin k → (x : V) → β x) ((Fin k → C) × (Fin k → R))).trans
      (Equiv.prodAssoc (Fin k → C) (Fin k → R) (Fin k → (x : V) → β x)))
  have heC (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
      prodLeft ((Fin k → R) × (Fin k → (v : V) → β v)) (copyPerm C k) σ (eC x) =
        eC (subsystemPerm k ι₀ {some none} σ x) := by
    simp [eC, e, globalReplicaCopiesEquiv, prodLeft_apply, copyPerm_apply, subsystemPerm_apply]
    rfl
  have hLC : labelProj (copyPerm C k) ellC ⊗ₖ
      (1 : Matrix ((Fin k → R) × (Fin k → (x : V) → β x))
        ((Fin k → R) × (Fin k → (x : V) → β x)) ℂ) =
      Matrix.reindex eC eC (labelProj (subsystemPerm k ι₀ {some none}) ellC) :=
    (labelProj_prodLeft (Z := (Fin k → R) × (Fin k → (x : V) → β x))
      (copyPerm C k) ellC).symm.trans (labelProj_of_intertwine eC heC ellC)
  have hleft : (I ⊗ₖ (labelProj (copyPerm C k) ellC ⊗ₖ
      (1 : Matrix (Fin k → R) (Fin k → R) ℂ))).submatrix e e =
      labelProj (subsystemPerm k ι₀ {some none}) ellC :=
    Matrix.ext fun x y ↦ by
      simpa [Matrix.reindex_apply, Matrix.submatrix_apply,
        ← Matrix.one_kronecker_one (α := ℂ) (m := Fin k → R)
          (n := Fin k → (v : V) → β v), Matrix.kroneckerMap_apply,
        eC, I, mul_comm, mul_left_comm, mul_assoc] using
        congrArg (fun H ↦ H (eC x) (eC y)) hLC
  done

end TensorPower
