/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.RegionalLowDefectProjection
import QICLean.Analysis.ProjectionQuadraticBound
import QICLean.Representation.RegionalAuxiliaryLabels

/-!
# The original physical gap in the common replica coordinates

The original gap controls the mass of the common low-defect projection
on a unit vector with simultaneous copy symmetry and its two original
auxiliary labels. All operators and vectors are transported through the
same fixed physical-copy equivalence. The energy in the estimate is the
actual expectation of the averaged original Hamiltonian.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, `comparator:defect-mass`, lines 421--443, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section
open TensorPower PermutationRepresentation
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (C R : Type u)
variable [∀ x, Fintype (β x)] [∀ x, DecidableEq (β x)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R

local instance globalDefectMass_decidableEqPhysical :
    DecidableEq ((x : V) → β x) := Fintype.decidablePiFintype

local instance globalDefectMass_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

/-- The original replica-averaged physical Hamiltonian, with both auxiliary
identities, in the same global configuration coordinates as the metric.
Source: `07-comparators.tex`, lines 421--438. -/
def globalReplicaMeanHamiltonian (H : Matrix ((x : V) → β x) ((x : V) → β x) ℂ) (k : ℕ) :
    Matrix (Config k ι₀) (Config k ι₀) ℂ :=
  (((k : ℝ)⁻¹ • replicaHamiltonian H k) ⊗ₖ
    (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)).submatrix
      (globalReplicaCopiesEquiv β C R k) (globalReplicaCopiesEquiv β C R k)

private theorem fixed_in_original_coordinates
    {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (H : Matrix B B ℂ) (v : A → ℂ)
    (h : H.submatrix e e *ᵥ v = v) : H *ᵥ (v ∘ e.symm) = v ∘ e.symm := by
  funext x
  simpa only [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_apply, Equiv.apply_symm_apply] using congrFun h (e.symm x)

/-- The original gap bounds the mass of the common global projection on
every unit vector with the two original labels and simultaneous symmetry.
This auxiliary statement retains the exact energy expectation.
Source: `07-comparators.tex`, `comparator:defect-mass`, lines 421--443. -/
theorem globalReplicaLowDefectProjection_gap_mass_ge
    {H : Matrix ((x : V) → β x) ((x : V) → β x) ℂ}
    {Ω : ((x : V) → β x) → ℂ} {E₀ g : ℝ}
    (hgap : (H - (E₀ : ℂ) • 1 -
      (g : ℂ) • (1 - vecMulVec Ω (star Ω))).PosSemidef)
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (hg : 0 < g) {k : ℕ} (hk : 0 < k)
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) {τ : ℝ} (hτ : 0 < τ)
    (v : EuclideanSpace ℂ (Config k ι₀)) (hv : ‖v‖ = 1)
    (hsym : symProj (copyPerm ((x : Option (Option V)) → ι₀ x) k) *ᵥ v = v)
    (hC : labelProj (subsystemPerm k ι₀ {some none}) ellC *ᵥ v = v)
    (hR : labelProj (subsystemPerm k ι₀ {none}) ellR *ᵥ v = v) :
    1 - ((star v ⬝ᵥ (globalReplicaMeanHamiltonian β C R H k *ᵥ v)).re - E₀) / g / τ ≤
      (star v ⬝ᵥ (globalReplicaLowDefectProjection β C R Ω k ellC ellR τ *ᵥ v)).re := by
  let e := globalReplicaCopiesEquiv β C R k
  let v₀ := WithLp.toLp 2 (fun x => v (e.symm x))
  have hv₀ : ‖v₀‖ = 1 :=
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map v).trans hv
  obtain ⟨hLC, hLR⟩ := labelProj_globalReplicaCopiesEquiv_auxiliary β C R k ellC ellR
  have hC₀ := fixed_in_original_coordinates e _ (fun x => v x) (hLC.symm ▸ hC)
  have hR₀ := fixed_in_original_coordinates e _ (fun x => v x) (hLR.symm ▸ hR)
  have hS₀ : symProj (replicaJointCopyPerm ((x : V) → β x) C R k) *ᵥ v₀ = v₀ :=
    fixed_in_original_coordinates e _ (fun x => v x)
      ((symProj_replicaJointCopyPerm_submatrix_globalReplicaCopiesEquiv β C R k).symm ▸ hsym)
  have hperm (σ : Equiv.Perm (Fin k)) :
      (permOp (copyPerm ((x : V) → β x) k) σ ⊗ₖ
        (permOp (copyPerm C k) σ ⊗ₖ permOp (copyPerm R k) σ)) *ᵥ v₀ = v₀ := by
    rw [← permOp_replicaJointCopyPerm]
    simpa only [hS₀] using symProj_mulVec_mem
      (replicaJointCopyPerm ((x : V) → β x) C R k) (fun x => v₀ x) σ
  have hmass := replicaLowDefectProjection_gap_mass_ge hgap hΩ hg hk
    ellC ellR hτ v₀ hv₀ hperm hC₀ hR₀
  have hquad (A : Matrix ((Fin k → (x : V) → β x) × ((Fin k → C) × (Fin k → R)))
      ((Fin k → (x : V) → β x) × ((Fin k → C) × (Fin k → R))) ℂ) :
      star v₀ ⬝ᵥ (A *ᵥ v₀) = star v ⬝ᵥ (A.submatrix e e *ᵥ v) := by
    simpa only [v₀, WithLp.ofLp_toLp, Function.comp_def, Equiv.symm_symm] using
      (star_dotProduct_submatrix_equiv A e.symm (fun x => v x)).symm
  simpa only [hquad, globalReplicaMeanHamiltonian, globalReplicaLowDefectProjection, e] using hmass

end Matrix
