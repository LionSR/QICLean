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
  done

end TensorPower
