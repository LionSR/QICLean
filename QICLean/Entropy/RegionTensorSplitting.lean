/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RegionalViability
import QICLean.Analysis.ViableSubspaceTensorTransport

/-!
# Tensor coordinates of two disjoint regions

The union and its exterior, or the first region and its split complement,
give the same three tensor factors. These are the actual configuration
isometries used in ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523.
-/

open scoped TensorProduct

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual tensor coordinates of a disjoint union. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
noncomputable def unionTensorCoordinates (q : ℕ) (A B : Finset V) (h : Disjoint A B) :
    EuclideanSpace ℂ (↥(A ∪ B) → Fin q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (A → Fin q) ⊗[ℂ] EuclideanSpace ℂ (B → Fin q) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (FiniteProduct.unionEquiv (fun _ : V ↦ Fin q) A B h)).trans
      (Submodule.euclideanTensorEquiv _ _)

/-- The actual complement of the first region, split into the second region
and the exterior of their union. Supporting ALVV, arXiv:1602.08828v2,
Lemma `l:t`, lines 500–523. -/
noncomputable def exteriorTensorCoordinates (q : ℕ) (A B : Finset V) (h : Disjoint A B) :
    EuclideanSpace ℂ (↥(Aᶜ) → Fin q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (B → Fin q) ⊗[ℂ] EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (FiniteProduct.complementUnionEquiv (fun _ : V ↦ Fin q) A B h)).trans
      (Submodule.euclideanTensorEquiv _ _)

/-- The exterior of the second region, with the original order of the
union retained. Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
noncomputable def rightExteriorTensorCoordinates (q : ℕ) (A B : Finset V)
    (h : Disjoint A B) :
    EuclideanSpace ℂ (↥(Bᶜ) → Fin q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (A → Fin q) ⊗[ℂ] EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((FiniteProduct.complementUnionEquiv (fun _ : V ↦ Fin q) B A h.symm).trans
      ((Equiv.refl _).prodCongr
        (FiniteProduct.configurationCongr (fun _ : V ↦ Fin q)
          (congrArg (fun C : Finset V ↦ Cᶜ) (Finset.union_comm B A)))))).trans
    (Submodule.euclideanTensorEquiv _ _)

/-- Product coordinates in the exterior of the second region. Supporting
ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma rightExteriorTensorCoordinates_symm_tmul_apply (q : ℕ) (A B : Finset V)
    (h : Disjoint A B) (x : EuclideanSpace ℂ (A → Fin q))
    (z : EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q)) (c : ↥(Bᶜ) → Fin q) :
    let e := (FiniteProduct.complementUnionEquiv (fun _ : V ↦ Fin q) B A h.symm).trans
      ((Equiv.refl _).prodCongr
        (FiniteProduct.configurationCongr (fun _ : V ↦ Fin q)
          (congrArg (fun C : Finset V ↦ Cᶜ) (Finset.union_comm B A))))
    (rightExteriorTensorCoordinates q A B h).symm (x ⊗ₜ[ℂ] z) c =
      x (e c).1 * z (e c).2 :=
  Submodule.euclideanTensorEquiv_reindex_symm_tmul _ x z c

/-- The original vector in the actual region/exterior split is the product
of its two factors in configuration coordinates. Supporting ALVV,
arXiv:1602.08828v2, Definition `d:vs`, lines 433–440. -/
lemma regionTensorCoordinates_symm_tmul_apply (q : ℕ) (A : Finset V)
    (x : EuclideanSpace ℂ (A → Fin q)) (y : EuclideanSpace ℂ (↥(Aᶜ) → Fin q))
    (c : V → Fin q) :
    (regionTensorCoordinates q A).symm (x ⊗ₜ[ℂ] y) c =
      x (fun v ↦ c v) * y (fun v ↦ c v) := by
  exact Submodule.euclideanTensorEquiv_reindex_symm_tmul
    (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) A) x y c

omit [Fintype V] in
/-- Product coordinates in the actual union split. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma unionTensorCoordinates_symm_tmul_apply (q : ℕ) (A B : Finset V)
    (h : Disjoint A B) (x : EuclideanSpace ℂ (A → Fin q))
    (y : EuclideanSpace ℂ (B → Fin q)) (c : ↥(A ∪ B) → Fin q) :
    (unionTensorCoordinates q A B h).symm (x ⊗ₜ[ℂ] y) c =
      x ((FiniteProduct.unionEquiv (fun _ : V ↦ Fin q) A B h) c).1 *
        y ((FiniteProduct.unionEquiv (fun _ : V ↦ Fin q) A B h) c).2 :=
  Submodule.euclideanTensorEquiv_reindex_symm_tmul _ x y c

/-- Product coordinates in the actual split complement. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma exteriorTensorCoordinates_symm_tmul_apply (q : ℕ) (A B : Finset V)
    (h : Disjoint A B) (y : EuclideanSpace ℂ (B → Fin q))
    (z : EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q)) (c : ↥(Aᶜ) → Fin q) :
    (exteriorTensorCoordinates q A B h).symm (y ⊗ₜ[ℂ] z) c =
      y ((FiniteProduct.complementUnionEquiv (fun _ : V ↦ Fin q) A B h) c).1 *
        z ((FiniteProduct.complementUnionEquiv (fun _ : V ↦ Fin q) A B h) c).2 :=
  Submodule.euclideanTensorEquiv_reindex_symm_tmul _ y z c

/-- The union/exterior split with its two regional factors kept separate.
Supporting ALVV, arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
noncomputable def threeRegionTensorCoordinates (q : ℕ) (A B : Finset V)
    (h : Disjoint A B) :
    EuclideanSpace ℂ (V → Fin q) ≃ₗᵢ[ℂ]
      (EuclideanSpace ℂ (A → Fin q) ⊗[ℂ] EuclideanSpace ℂ (B → Fin q)) ⊗[ℂ]
        EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q) :=
  (regionTensorCoordinates q (A ∪ B)).trans
    (TensorProduct.congrIsometry (unionTensorCoordinates q A B h)
      (LinearIsometryEquiv.refl ℂ _))

/-- Splitting the union, or first splitting the first region and then its
complement, gives exactly the same three tensor factors. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma threeRegionTensorCoordinates_assoc (q : ℕ) (A B : Finset V) (h : Disjoint A B) :
    (threeRegionTensorCoordinates q A B h).trans
      (TensorProduct.assocIsometry ℂ (EuclideanSpace ℂ (A → Fin q))
        (EuclideanSpace ℂ (B → Fin q)) (EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q))) =
      (regionTensorCoordinates q A).trans
        (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ _)
          (exteriorTensorCoordinates q A B h)) := by
  let f := (threeRegionTensorCoordinates q A B h).trans
    (TensorProduct.assocIsometry ℂ (EuclideanSpace ℂ (A → Fin q))
      (EuclideanSpace ℂ (B → Fin q)) (EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q)))
  let g := (regionTensorCoordinates q A).trans
    (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ _)
      (exteriorTensorCoordinates q A B h))
  have hsymm : f.symm = g.symm := by
    apply LinearIsometryEquiv.ext
    intro t
    induction t with
    | tmul x yz =>
      induction yz with
      | tmul y z =>
        ext c
        simp [f, g, TensorProduct.congrIsometry_symm, threeRegionTensorCoordinates,
          regionTensorCoordinates_symm_tmul_apply, unionTensorCoordinates_symm_tmul_apply,
          exteriorTensorCoordinates_symm_tmul_apply, FiniteProduct.unionEquiv,
          FiniteProduct.complementUnionEquiv, mul_assoc]
      | add v w hv hw => simp only [TensorProduct.tmul_add, map_add, hv, hw]
    | add v w hv hw => simp only [map_add, hv, hw]
  have hinv := congrArg LinearIsometryEquiv.symm hsymm
  simpa only [LinearIsometryEquiv.symm_symm] using hinv

/-- The second-region split gives the same actual three-factor coordinates,
after exchanging the two retained factors. Supporting ALVV,
arXiv:1602.08828v2, Lemma `l:t`, lines 500–523. -/
lemma threeRegionTensorCoordinates_comm_assoc (q : ℕ) (A B : Finset V)
    (h : Disjoint A B) :
    ((threeRegionTensorCoordinates q A B h).trans
      (TensorProduct.congrIsometry
        (TensorProduct.commIsometry ℂ (EuclideanSpace ℂ (A → Fin q))
          (EuclideanSpace ℂ (B → Fin q))) (LinearIsometryEquiv.refl ℂ _))).trans
      (TensorProduct.assocIsometry ℂ (EuclideanSpace ℂ (B → Fin q))
        (EuclideanSpace ℂ (A → Fin q)) (EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q))) =
      (regionTensorCoordinates q B).trans
        (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ _)
          (rightExteriorTensorCoordinates q A B h)) := by
  let f := ((threeRegionTensorCoordinates q A B h).trans
    (TensorProduct.congrIsometry
      (TensorProduct.commIsometry ℂ (EuclideanSpace ℂ (A → Fin q))
        (EuclideanSpace ℂ (B → Fin q))) (LinearIsometryEquiv.refl ℂ _))).trans
    (TensorProduct.assocIsometry ℂ (EuclideanSpace ℂ (B → Fin q))
      (EuclideanSpace ℂ (A → Fin q)) (EuclideanSpace ℂ (↥((A ∪ B)ᶜ) → Fin q)))
  let g := (regionTensorCoordinates q B).trans
    (TensorProduct.congrIsometry (LinearIsometryEquiv.refl ℂ _)
      (rightExteriorTensorCoordinates q A B h))
  have hsymm : f.symm = g.symm := by
    apply LinearIsometryEquiv.ext
    intro t
    induction t with
    | tmul y xz =>
      induction xz with
      | tmul x z =>
        ext c
        have hconfig :
            FiniteProduct.configurationCongr (fun _ : V ↦ Fin q)
              (congrArg (fun C : Finset V ↦ Cᶜ) (Finset.union_comm B A))
              (fun v : ↥((B ∪ A)ᶜ) ↦ c v) =
                (fun v : ↥((A ∪ B)ᶜ) ↦ c v) := by
          funext v
          simp only [FiniteProduct.configurationCongr_apply]
        simp [f, g, TensorProduct.congrIsometry_symm, threeRegionTensorCoordinates,
          regionTensorCoordinates_symm_tmul_apply, unionTensorCoordinates_symm_tmul_apply,
          rightExteriorTensorCoordinates_symm_tmul_apply, FiniteProduct.unionEquiv,
          FiniteProduct.complementUnionEquiv, hconfig,
          mul_assoc, mul_left_comm]
      | add v w hv hw => simp only [TensorProduct.tmul_add, map_add, hv, hw]
    | add v w hv hw => simp only [map_add, hv, hw]
  have hinv := congrArg LinearIsometryEquiv.symm hsymm
  simpa only [LinearIsometryEquiv.symm_symm] using hinv

end Entropy
