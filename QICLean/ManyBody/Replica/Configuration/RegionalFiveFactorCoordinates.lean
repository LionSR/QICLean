/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.RegionMatrix
import QICLean.ManyBody.Replica.Configuration.GoodConfigurationDensity
import QICLean.ManyBody.Replica.AddedSiteSpace

/-!
# Regional five-factor coordinates in one global replica space

A disjoint pair of physical regions determines the three physical factors
consisting of those regions and the complement of their union. The two
auxiliary spaces are unchanged. These coordinates identify the original
global configuration space with the five-factor configuration space used
for the component estimates.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 20--37, 80--110 and 421--456, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section

namespace ManyBody

variable {V : Type u} [Fintype V] [DecidableEq V] (β : V → Type u)

/-- The original physical configuration split into two disjoint regions
and the complement of their union. Source: `07-comparators.tex`, lines 20--37. -/
def regionalPhysicalEquiv (Q Y : Finset V) (hQY : Disjoint Q Y) :
    ((v : V) → β v) ≃ RegionConfig β Q ×
      (RegionConfig β Y × RegionConfig β (Q ∪ Y)ᶜ) :=
  (cutEquiv β Q).trans
    ((Equiv.refl _).prodCongr ((complementUnionEquiv β Q Y hQY).trans
      ((Equiv.refl _).prodCongr (complementEquiv β (Q ∪ Y)))))

end ManyBody

namespace TensorPower

/-- Change only the one-copy physical coordinates, retaining both original
auxiliary copy registers. Source: `07-comparators.tex`, lines 421--456. -/
def replicaPhysicalCoordinateEquiv {A B C R : Type*} (e : A ≃ B) (k : ℕ) :
    (Fin k → A) × ((Fin k → C) × (Fin k → R)) ≃
      (Fin k → B) × ((Fin k → C) × (Fin k → R)) :=
  (Equiv.arrowCongr (Equiv.refl (Fin k)) e).prodCongr (Equiv.refl _)

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)

/-- The three actual physical regions followed by the original auxiliary
spaces, in the order used by the component estimates. Source:
`07-comparators.tex`, lines 20--37 and 80--110. -/
def regionalFiveFactorSpace (Q Y : Finset V) : Fin 5 → Type u :=
  ![ManyBody.RegionConfig β Q, ManyBody.RegionConfig β Y,
    ManyBody.RegionConfig β (Q ∪ Y)ᶜ, C, R]

instance regionalFiveFactorSpaceFintype
    [∀ v, Fintype (β v)] [Fintype C] [Fintype R]
    (Q Y : Finset V) (f : Fin 5) : Fintype (regionalFiveFactorSpace β C R Q Y f) := by
  exact Fin.cases (inferInstanceAs (Fintype (ManyBody.RegionConfig β Q)))
    (Fin.cases (inferInstanceAs (Fintype (ManyBody.RegionConfig β Y)))
      (Fin.cases (inferInstanceAs (Fintype (ManyBody.RegionConfig β (Q ∪ Y)ᶜ)))
        (Fin.cases (inferInstanceAs (Fintype C))
          (Fin.cases (inferInstanceAs (Fintype R)) (fun i => Fin.elim0 i))))) f

instance regionalFiveFactorSpaceDecidableEq
    [∀ v, DecidableEq (β v)]
    [DecidableEq C] [DecidableEq R]
    (Q Y : Finset V) (f : Fin 5) : DecidableEq (regionalFiveFactorSpace β C R Q Y f) := by
  exact Fin.cases (inferInstanceAs (DecidableEq (ManyBody.RegionConfig β Q)))
    (Fin.cases (inferInstanceAs (DecidableEq (ManyBody.RegionConfig β Y)))
      (Fin.cases (inferInstanceAs (DecidableEq (ManyBody.RegionConfig β (Q ∪ Y)ᶜ)))
        (Fin.cases (inferInstanceAs (DecidableEq C))
          (Fin.cases (inferInstanceAs (DecidableEq R)) (fun i => Fin.elim0 i))))) f

instance regionalFiveFactorSpaceNonempty
    [∀ v, Nonempty (β v)] [Nonempty C] [Nonempty R]
    (Q Y : Finset V) (f : Fin 5) : Nonempty (regionalFiveFactorSpace β C R Q Y f) := by
  exact Fin.cases (inferInstanceAs (Nonempty (ManyBody.RegionConfig β Q)))
    (Fin.cases (inferInstanceAs (Nonempty (ManyBody.RegionConfig β Y)))
      (Fin.cases (inferInstanceAs (Nonempty (ManyBody.RegionConfig β (Q ∪ Y)ᶜ)))
        (Fin.cases (inferInstanceAs (Nonempty C))
          (Fin.cases (inferInstanceAs (Nonempty R)) (fun i => Fin.elim0 i))))) f

/-- The same original physical-copy and auxiliary registers for every
regional cut. Source: `07-comparators.tex`, lines 80--110 and 421--456. -/
def globalReplicaCopiesEquiv (k : ℕ) :
    Config k (addedSiteSpace (addedSiteSpace β C) R) ≃
      (Fin k → (v : V) → β v) × ((Fin k → C) × (Fin k → R)) where
  toFun x := (fun j v => x j (some (some v)),
    (fun j => x j (some none), fun j => x j none))
  invFun x j o := match o with
    | none => x.2.2 j
    | some none => x.2.1 j
    | some (some v) => x.1 j v
  left_inv x := by
    funext j o
    cases o with
    | none => rfl
    | some o => cases o <;> rfl
  right_inv x := rfl

/-- The literal globalization equivalence for a regional cut. The
auxiliary registers and their order remain unchanged. Source:
`07-comparators.tex`, lines 20--37, 80--110 and 421--456. -/
def regionalFiveFactorCopyEquiv (Q Y : Finset V) (hQY : Disjoint Q Y) (k : ℕ) :
    Config k (addedSiteSpace (addedSiteSpace β C) R) ≃
      Config k (regionalFiveFactorSpace β C R Q Y) :=
  (globalReplicaCopiesEquiv β C R k).trans
    ((replicaPhysicalCoordinateEquiv (C := C) (R := R)
      (ManyBody.regionalPhysicalEquiv β Q Y hQY) k).trans
      (fiveFactorCopiesEquiv (regionalFiveFactorSpace β C R Q Y) k).symm)

end TensorPower

section RegionalAuxiliaryLabels

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
    simp [eC, e, globalReplicaCopiesEquiv, prodLeft_apply, subsystemPerm_apply]
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
      simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_apply_apply, Equiv.trans_apply, Equiv.prodComm_apply,
        Equiv.prodAssoc_apply, Prod.swap,
        ← Matrix.one_kronecker_one (α := ℂ) (m := Fin k → R)
          (n := Fin k → (v : V) → β v), Matrix.kroneckerMap_apply,
        eC, I, mul_rotate'
          ((1 : Matrix (Fin k → (v : V) → β v) (Fin k → (v : V) → β v) ℂ)
            (e x).1 (e y).1)
          (labelProj (copyPerm C k) ellC (e x).2.1 (e y).2.1)
          ((1 : Matrix (Fin k → R) (Fin k → R) ℂ) (e x).2.2 (e y).2.2)] using
        (congrArg (fun H ↦ H (eC x) (eC y)) hLC).trans
          (congrArg₂ (labelProj (subsystemPerm k ι₀ {some none}) ellC)
            (eC.symm_apply_apply x) (eC.symm_apply_apply y))
  let eR := e.trans
    ((Equiv.prodAssoc (Fin k → (x : V) → β x) (Fin k → C) (Fin k → R)).symm.trans
      (Equiv.prodComm ((Fin k → (x : V) → β x) × (Fin k → C)) (Fin k → R)))
  have heR (σ : Equiv.Perm (Fin k)) (x : Config k ι₀) :
      prodLeft ((Fin k → (v : V) → β v) × (Fin k → C)) (copyPerm R k) σ (eR x) =
        eR (subsystemPerm k ι₀ {none} σ x) := by
    simp [eR, e, globalReplicaCopiesEquiv, prodLeft_apply, subsystemPerm_apply]
    rfl
  have hLR : labelProj (copyPerm R k) ellR ⊗ₖ
      (1 : Matrix ((Fin k → (x : V) → β x) × (Fin k → C))
        ((Fin k → (x : V) → β x) × (Fin k → C)) ℂ) =
      Matrix.reindex eR eR (labelProj (subsystemPerm k ι₀ {none}) ellR) :=
    (labelProj_prodLeft (Z := (Fin k → (x : V) → β x) × (Fin k → C))
      (copyPerm R k) ellR).symm.trans (labelProj_of_intertwine eR heR ellR)
  exact ⟨hleft, Matrix.ext fun x y ↦ by
    simpa only [Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Equiv.trans_apply, Equiv.prodComm_apply,
      Equiv.prodAssoc_symm_apply, Prod.swap,
      ← Matrix.one_kronecker_one (α := ℂ) (m := Fin k → (v : V) → β v)
        (n := Fin k → C), Matrix.kroneckerMap_apply,
      eR, I, mul_rotate'
        (labelProj (copyPerm R k) ellR (e x).2.2 (e y).2.2)
        ((1 : Matrix (Fin k → (v : V) → β v) (Fin k → (v : V) → β v) ℂ)
          (e x).1 (e y).1)
        ((1 : Matrix (Fin k → C) (Fin k → C) ℂ) (e x).2.1 (e y).2.1)] using
      (congrArg (fun H ↦ H (eR x) (eR y)) hLR).trans
        (congrArg₂ (labelProj (subsystemPerm k ι₀ {none}) ellR)
          (eR.symm_apply_apply x) (eR.symm_apply_apply y))⟩

end TensorPower
end

end RegionalAuxiliaryLabels

section RegionalPhysicalVector

/-!
# The physical vector under regional grouping

Restriction to two disjoint regions and the complement of their union
identifies the original product basis with the three grouped factors.
This identification preserves the norm of every physical vector.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 421--456, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/


noncomputable section

namespace ManyBody

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The literal regional regrouping preserves the norm of the original
physical vector. Source: `07-comparators.tex`, lines 421--456. -/
theorem norm_regionalPhysicalVector (β : V → Type u)
    [∀ v, Fintype (β v)] (Ω : ((v : V) → β v) → ℂ)
    (Q Y : Finset V) (hQY : Disjoint Q Y) :
    ‖WithLp.toLp 2 (Ω ∘ (regionalPhysicalEquiv β Q Y hQY).symm)‖ =
      ‖WithLp.toLp 2 Ω‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (regionalPhysicalEquiv β Q Y hQY)).norm_map (WithLp.toLp 2 Ω)


end ManyBody
end

end RegionalPhysicalVector
