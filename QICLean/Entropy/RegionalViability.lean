/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.SubregionCut
import QICLean.Analysis.ViableSubspaceCoordinates

/-!
# Actual tensor coordinates for regional viable spaces

The finite configuration split, followed by the canonical Euclidean tensor
isometry, places the retained region first and its entire exterior second.
The equivalent construction that first places the exterior first agrees
with this map after exchanging the tensor factors.

These coordinate identities support ALVV, arXiv:1602.08828v2,
Definition `d:vs`, lines 433–440, and tensoring, lines 500–523.
-/

open scoped TensorProduct

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual retained-region/exterior tensor coordinates. Supporting ALVV,
arXiv:1602.08828v2, Definition `d:vs`, lines 433–440. -/
noncomputable def regionTensorCoordinates (q : ℕ) (J : Finset V) :
    EuclideanSpace ℂ (V → Fin q) ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ (J → Fin q) ⊗[ℂ] EuclideanSpace ℂ (↥(Jᶜ) → Fin q)) :=
  (regionConfigurationSplit q J).trans (Submodule.euclideanTensorEquiv _ _)

/-- Regional coordinate extension is viability in the actual tensor split.
Supporting ALVV, arXiv:1602.08828v2, Definition `d:vs`, lines 433–440. -/
lemma isCloseTo_prodExt_region_iff_isViable {q : ℕ} {delta : ℝ}
    (J : Finset V) (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)))
    (G : Submodule ℂ (EuclideanSpace ℂ (V → Fin q))) :
    Submodule.IsCloseTo delta (Submodule.prodExt S (↥(Jᶜ) → Fin q))
      (G.map (regionConfigurationSplit q J).toLinearEquiv.toLinearMap) ↔
    Submodule.IsViable delta S (G.map (regionTensorCoordinates q J).toLinearEquiv.toLinearMap) := by
  rw [Submodule.isCloseTo_prodExt_iff_isViable, ← Submodule.map_comp]
  rfl

/-- The exterior-first construction used by physical improving families is
exactly the retained-region-first canonical tensor split. Supporting ALVV,
arXiv:1602.08828v2, Theorem `t:ais`, lines 1010–1024. -/
lemma regionTensorCoordinates_eq_exteriorFirst (q : ℕ) (J : Finset V) :
    regionTensorCoordinates q J =
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        ((FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) J).trans (Equiv.prodComm _ _))).trans
          (Submodule.euclideanTensorEquiv (↥(Jᶜ) → Fin q) (J → Fin q))).trans
        (TensorProduct.commIsometry ℂ (EuclideanSpace ℂ (↥(Jᶜ) → Fin q))
          (EuclideanSpace ℂ (J → Fin q))) := by
  apply LinearIsometryEquiv.ext
  intro psi
  apply (Submodule.euclideanTensorEquiv (J → Fin q) (↥(Jᶜ) → Fin q)).symm.injective
  change (Submodule.euclideanTensorEquiv _ _).symm
      (Submodule.euclideanTensorEquiv _ _ (regionConfigurationSplit q J psi)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  simp only [LinearIsometryEquiv.trans_apply]
  rw [Submodule.euclideanTensorEquiv_symm_comm]
  ext p
  rfl

end Entropy
