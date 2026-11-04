/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RegionTensorSplitting

/-!
# Merging viable spaces on actual disjoint regions

Both child spaces refer to one arbitrary global target, which may be
entangled across all three factors. Their tensor product is transported
back to the actual union configuration space. This is the regional form
of ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523.
No tree recurrence or selection of sampled viable spaces is assumed.
-/

open scoped TensorProduct

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual merged candidate on the union of disjoint regions. Supporting
ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
noncomputable def regionTensorMerge (q : ℕ) (A B : Finset V) (h : Disjoint A B)
    (S1 : Submodule ℂ (EuclideanSpace ℂ (A → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (B → Fin q))) :
    Submodule ℂ (EuclideanSpace ℂ (↥(A ∪ B) → Fin q)) :=
  (S1.tensorProd S2).map (unionTensorCoordinates q A B h).symm.toLinearEquiv.toLinearMap

/-- Actual regional viable spaces merge for the same global target.
No product structure of the target is required. This is ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523, in configuration coordinates. -/
lemma isViable_regionTensorMerge {q : ℕ} {delta1 delta2 : ℝ}
    (A B : Finset V) (h : Disjoint A B)
    (G : Submodule ℂ (EuclideanSpace ℂ (V → Fin q)))
    (S1 : Submodule ℂ (EuclideanSpace ℂ (A → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (B → Fin q)))
    (h1 : Submodule.IsViable delta1 S1
      (G.map (regionTensorCoordinates q A).toLinearEquiv.toLinearMap))
    (h2 : Submodule.IsViable delta2 S2
      (G.map (regionTensorCoordinates q B).toLinearEquiv.toLinearMap)) :
    Submodule.IsViable (delta1 + delta2) (regionTensorMerge q A B h S1 S2)
      (G.map (regionTensorCoordinates q (A ∪ B)).toLinearEquiv.toLinearMap) := by
  let E := EuclideanSpace ℂ (A → Fin q)
  let F := EuclideanSpace ℂ (B → Fin q)
  let R := EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q)
  let C := threeRegionTensorCoordinates q A B h
  let T := G.map C.toLinearEquiv.toLinearMap
  have hfirst : Submodule.IsViable delta1 S1
      (T.map (TensorProduct.assocIsometry ℂ E F R).toLinearEquiv.toLinearMap) := by
    have hcoords := threeRegionTensorCoordinates_assoc q A B h
    have hmap : T.map (TensorProduct.assocIsometry ℂ E F R).toLinearEquiv.toLinearMap =
        (G.map (regionTensorCoordinates q A).toLinearEquiv.toLinearMap).map
          (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ E)
            (exteriorTensorCoordinates q A B h)).toLinearEquiv.toLinearMap := by
      dsimp only [T]
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      exact congrArg (fun e ↦ G.map e.toLinearEquiv.toLinearMap) hcoords
    rw [hmap]
    simpa only [LinearIsometryEquiv.toLinearEquiv_refl, LinearEquiv.refl_toLinearMap,
      Submodule.map_id] using
      (Submodule.isViable_map_congrIsometry_iff (LinearIsometryEquiv.refl ℂ E)
        (exteriorTensorCoordinates q A B h) S1 _).mpr h1
  have hsecond : Submodule.IsViable delta2 S2
      ((T.map (TensorProduct.congrIsometry (TensorProduct.commIsometry ℂ E F)
        (LinearIsometryEquiv.refl ℂ R)).toLinearEquiv.toLinearMap).map
          (TensorProduct.assocIsometry ℂ F E R).toLinearEquiv.toLinearMap) := by
    have hcoords := threeRegionTensorCoordinates_comm_assoc q A B h
    have hmap :
        (T.map (TensorProduct.congrIsometry (TensorProduct.commIsometry ℂ E F)
          (LinearIsometryEquiv.refl ℂ R)).toLinearEquiv.toLinearMap).map
            (TensorProduct.assocIsometry ℂ F E R).toLinearEquiv.toLinearMap =
        (G.map (regionTensorCoordinates q B).toLinearEquiv.toLinearMap).map
          (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ F)
            (rightExteriorTensorCoordinates q A B h)).toLinearEquiv.toLinearMap := by
      dsimp only [T]
      simp only [← Submodule.map_comp]
      exact congrArg (fun e ↦ G.map e.toLinearEquiv.toLinearMap) hcoords
    rw [hmap]
    simpa only [LinearIsometryEquiv.toLinearEquiv_refl, LinearEquiv.refl_toLinearMap,
      Submodule.map_id] using
      (Submodule.isViable_map_congrIsometry_iff (LinearIsometryEquiv.refl ℂ F)
        (rightExteriorTensorCoordinates q A B h) S2 _).mpr h2
  have hmerged := Submodule.IsViable.tensorProd_of_factor_splits S1 S2 T hfirst hsecond
  let U := unionTensorCoordinates q A B h
  have hlocal : (regionTensorMerge q A B h S1 S2).map U.toLinearEquiv.toLinearMap =
      S1.tensorProd S2 :=
    (Submodule.map_symm_eq_iff U.toLinearEquiv).mp rfl
  have htarget :
      (G.map (regionTensorCoordinates q (A ∪ B)).toLinearEquiv.toLinearMap).map
        (TensorProduct.congrIsometry U (LinearIsometryEquiv.refl ℂ R)).toLinearEquiv.toLinearMap =
      T := by
    rw [← Submodule.map_comp]
    rfl
  apply (Submodule.isViable_map_congrIsometry_iff U (LinearIsometryEquiv.refl ℂ R)
    (regionTensorMerge q A B h S1 S2)
      (G.map (regionTensorCoordinates q (A ∪ B)).toLinearEquiv.toLinearMap)).mp
  rwa [hlocal, htarget]

omit [Fintype V] in
/-- The actual merged candidate has dimension at most the product of the
child dimensions. Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma finrank_regionTensorMerge_le (q : ℕ) (A B : Finset V) (h : Disjoint A B)
    (S1 : Submodule ℂ (EuclideanSpace ℂ (A → Fin q)))
    (S2 : Submodule ℂ (EuclideanSpace ℂ (B → Fin q))) :
    Module.finrank ℂ (regionTensorMerge q A B h S1 S2) ≤
      Module.finrank ℂ S1 * Module.finrank ℂ S2 :=
  (Submodule.finrank_map_le _ _).trans (Submodule.finrank_tensorProd_le S1 S2)

/-- Equal regions identify their actual viable subspaces by the canonical
configuration equivalence. Supporting ALVV, arXiv:1602.08828v2,
Definition `d:vs`, lines 433–440. -/
lemma isViable_region_congr {q : ℕ} {delta : ℝ} {J K : Finset V}
    (hJK : J = K) (G : Submodule ℂ (EuclideanSpace ℂ (V → Fin q)))
    (S : Submodule ℂ (EuclideanSpace ℂ (J → Fin q)))
    (hS : Submodule.IsViable delta S
      (G.map (regionTensorCoordinates q J).toLinearEquiv.toLinearMap)) :
    Submodule.IsViable delta
      (S.map (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (FiniteProduct.configurationCongr (fun _ : V ↦ Fin q) hJK)).toLinearEquiv.toLinearMap)
      (G.map (regionTensorCoordinates q K).toLinearEquiv.toLinearMap) := by
  subst K
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (FiniteProduct.configurationCongr (fun _ : V ↦ Fin q) (rfl : J = J))
  have hid : e.toLinearEquiv.toLinearMap = LinearMap.id := by
    ext x c
    rfl
  rw [hid, Submodule.map_id]
  exact hS

end Entropy
