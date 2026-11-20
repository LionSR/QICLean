/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Parallel
import QICLean.ManyBody.Sites.Relabel

/-!
# Layers of permutations of qudits

A permutation `π` of the sites that preserves a region `D` permutes the qudits of `D`, as one
gate with the single Kraus operator of entries `[u ∘ π = u']` (`permGate`), which is unitary
(`isUnitary_permGate`). If `π` preserves each of a family of pairwise disjoint cells and fixes
every other site, the layer of these gates on the cells has the one Kraus operator
`sitePermOp π` (`kraus_ofCells_permGate`).

## Main definitions

* `QuantumCircuit.permGate` — the permutation of the qudits of a region along a permutation of
  the sites.

## Main results

* `QuantumCircuit.isUnitary_permGate` — the permutation gate is unitary.
* `QuantumCircuit.kraus_ofCells_permGate` — a layer of permutation gates is the site
  permutation operator.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {V : Type} [Fintype V] [DecidableEq V] {Γ : Geometry V} {α : Type} [Fintype α]
  [DecidableEq α]

/-- The permutation of the qudits of the region `D` along a permutation `π` of the sites that
preserves `D`, as a gate: the matrix with entries `[u ∘ π = u']`. -/
def permGate (π : Equiv.Perm V) (D : Finset V) (hD : ∀ v ∈ D, π v ∈ D) :
    KrausGate D (fun _ ↦ α) (fun _ ↦ α) :=
  KrausFamily.single (Matrix.of fun u u' ↦
    if (fun v : {v // v ∈ D} ↦ u ⟨π v, hD v v.2⟩) = u' then 1 else 0)

omit [Fintype V] in
/-- The permutation gate is unitary: it is the permutation matrix of the relabelling of the
configurations of `D`. -/
theorem isUnitary_permGate (π : Equiv.Perm V) (D : Finset V)
    (hD : ∀ v ∈ D, π v ∈ D) : (permGate (α := α) π D hD).IsUnitary := by
  have hD' : ∀ v ∈ D, π.symm v ∈ D := by
    intro v hv
    have hmap : D.map π.toEmbedding = D := Finset.map_eq_of_subset fun w hw ↦ by
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
      exact hD u hu
    rw [← hmap] at hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
    simpa using hu
  let e : RegionConfig (fun _ ↦ α) D ≃ RegionConfig (fun _ ↦ α) D :=
    { toFun := fun u v ↦ u ⟨π v, hD v v.2⟩
      invFun := fun u v ↦ u ⟨π.symm v, hD' v v.2⟩
      left_inv := fun u ↦ funext fun v ↦ congrArg u (Subtype.ext (by simp))
      right_inv := fun u ↦ funext fun v ↦ congrArg u (Subtype.ext (by simp)) }
  have h : (Matrix.of fun u u' ↦
      if (fun v : {v // v ∈ D} ↦ u ⟨π v, hD v v.2⟩) = u' then (1 : ℂ) else 0) =
      Equiv.Perm.permMatrix ℂ e := by
    ext u u'
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, e]
  rw [permGate, h]
  exact KrausFamily.isUnitary_single (Equiv.Perm.permMatrix_mem_unitaryGroup e)

/-- **A layer of permutations.** Let `π` permute the sites, preserving each of the pairwise
disjoint cells `C` and fixing every other site. The layer of the permutations of the qudits of
the cells of `C` along `π` has the one Kraus operator `sitePermOp π`. -/
theorem kraus_ofCells_permGate (C : Finset Γ.Cell)
    (hC : (C : Set Γ.Cell).PairwiseDisjoint Γ.cell) (π : Equiv.Perm V)
    (hπ : ∀ b ∈ C, ∀ v ∈ Γ.cell b, π v ∈ Γ.cell b)
    (hfix : ∀ v, v ∉ C.biUnion Γ.cell → π v = v)
    (i : (Layer.ofCells (G := KrausGate) C hC fun b ↦ permGate (α := α) π (Γ.cell b)
      (hπ b b.2)).Index) :
    (Layer.ofCells (G := KrausGate) C hC fun b ↦ permGate (α := α) π (Γ.cell b)
      (hπ b b.2)).kraus KrausGate.ev i = sitePermOp π := by
  ext y x
  rw [Layer.kraus_apply, sitePermOp_apply]
  by_cases h : x = y ∘ π
  · subst h
    have h₁ : ∏ b : C, KrausGate.ev ((Layer.ofCells (G := KrausGate) C hC fun b ↦
        permGate (α := α) π (Γ.cell b) (hπ b b.2)).gate b) (i.1 b) (fun v ↦ y v)
        (fun v ↦ (y ∘ π) v) = 1 :=
      Fintype.prod_eq_one _ fun b ↦ ite_eq_left rfl
    have h₂ : ∏ t : (Layer.ofCells (G := KrausGate) C hC fun b ↦
        permGate (α := α) π (Γ.cell b) (hπ b b.2)).Free, ((Layer.ofCells (G := KrausGate) C hC
        fun b ↦ permGate (α := α) π (Γ.cell b) (hπ b b.2)).onsite t).op (i.2 t) (y t)
        ((y ∘ π) t) = 1 :=
      Fintype.prod_eq_one _ fun t ↦ by
        change (1 : Matrix α α ℂ) (y t) (y (π t)) = 1
        rw [hfix t t.2, one_apply_eq]
    rw [ite_eq_left rfl]
    exact (congrArg₂ (· * ·) h₁ h₂).trans (mul_one 1)
  · rw [ite_eq_right h]
    obtain ⟨v, hv⟩ := Function.ne_iff.mp h
    by_cases hc : v ∈ C.biUnion Γ.cell
    · obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hc
      refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ ⟨b, hb⟩) ?_) _
      change (if _ then (1 : ℂ) else 0) = 0
      exact ite_eq_right fun e ↦ hv (congrFun e ⟨v, hvb⟩).symm
    · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨v, hc⟩) ?_)
      change (1 : Matrix α α ℂ) (y v) (x v) = 0
      refine one_apply_ne fun e ↦ hv ?_
      rw [Function.comp_apply, hfix v hc, e]

end QuantumCircuit
