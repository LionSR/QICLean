/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.Encoding
import QICLean.Circuit.Core.Parallel
import QICLean.Circuit.Geometry.Port
import QICLean.Circuit.Geometry.Ring
import QICLean.ManyBody.Sites.Relabel

/-!
# Compiling ring protocols to physical ports

A protocol on the ring of `N` sites whose bases have at most `d ^ k` elements is simulated on the
ring with physical ports (`Geometry.portRing`), with `1 + k + k` qudits of dimension `d` at every
site: the port, `k` data qudits holding the register of the site, and `k` scratch qudits. A gate
on the registers of the sites `j` and `j + 1` is executed by moving the register of `j`, one
digit per port layer, into the scratch qudits of `j + 1`, acting inside the site `j + 1`, and
moving the register back. Every layer of the ring protocol costs `2k` port layers.

## Main results

* `QuantumCircuit.Layer.kraus_ofCells_permGate` — a layer of permutations of the qudits of its
  cells is the permutation of all qudits.
-/

open Matrix ManyBody

namespace QuantumCircuit

/-! ### Layers of permutations of qudits -/

section Perm

variable {V : Type} [Fintype V] [DecidableEq V] {Γ : Geometry V} {α : Type} [Fintype α]
  [DecidableEq α]

/-- The permutation of the qudits of the region `D` along a permutation `π` of the sites that
preserves `D`, as a gate: the matrix with entries `[u ∘ π = u']`. -/
private def permGate (π : Equiv.Perm V) (D : Finset V) (hD : ∀ v ∈ D, π v ∈ D) :
    KrausGate D (fun _ ↦ α) (fun _ ↦ α) :=
  KrausFamily.single (Matrix.of fun u u' ↦
    if (fun v : {v // v ∈ D} ↦ u ⟨π v, hD v v.2⟩) = u' then 1 else 0)

omit [Fintype V] in
private theorem isUnitary_permGate (π : Equiv.Perm V) (D : Finset V)
    (hD : ∀ v ∈ D, π v ∈ D) (hD' : ∀ v ∈ D, π.symm v ∈ D) :
    (permGate (α := α) π D hD).IsUnitary := by
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
private theorem kraus_ofCells_permGate (C : Finset Γ.Cell)
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

end Perm

end QuantumCircuit
