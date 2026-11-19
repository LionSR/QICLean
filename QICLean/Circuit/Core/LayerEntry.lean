/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.LayerDual

/-!
# A layer cell by cell

The map of a layer is the tensor product of the maps of its gates and onsite families: on a
matrix unit `|x⟩⟨x'|` its entry at `(y, y')` is the product of the entries of the local maps on
the local matrix units (`Layer.map_matrixUnit_apply`). Two layers with the same cells whose local
maps agree therefore have the same map. A sum over the configurations of any system of such a
product is the product of the local sums (`Layer.sum_prod_mul_prod`), since the cells and the
remaining sites partition the sites (`Layer.sum_prod_region`).

## Main results

* `QuantumCircuit.Layer.map_matrixUnit_apply` — the entries of the map of a layer on matrix
  units.
* `QuantumCircuit.Layer.sum_prod_mul_prod` — a sum over the configurations of a product over the
  cells and the free sites factors.
-/

open Matrix ManyBody

namespace QuantumCircuit

namespace Layer

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}
  {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X Y : S → Type}

omit [GateFamily G] in
/-- A sum over the configurations of `F` of a product over the cells and the free sites of
functions of the restrictions is the product of the sums over the local configurations. -/
theorem sum_prod_mul_prod {R : Type*} [CommSemiring R] (L : Layer Γ G X Y) {F : S → Type}
    [∀ s, Fintype (F s)] (Φ : (b : L.cells) → RegionConfig F (Γ.cell b) → R)
    (Ψ : (t : L.Free) → F t → R) :
    ∑ f : Config F, (∏ b, Φ b (fun v ↦ f v)) * ∏ t, Ψ t (f t) =
      (∏ b, ∑ z, Φ b z) * ∏ t, ∑ z, Ψ t z := by
  have h := L.sum_prod_region (R := R) (F := F) fun
    | .inl b => Φ b
    | .inr t => fun z ↦ Ψ t (z ⟨t, Finset.mem_singleton_self _⟩)
  simp only [Fintype.prod_sum_type] at h
  refine h.trans (congrArg _ (Fintype.prod_congr _ _ fun t ↦ ?_))
  let : Unique {v // v ∈ ({t.1} : Finset S)} :=
    ⟨⟨⟨t, Finset.mem_singleton_self _⟩⟩, fun v ↦ Subtype.ext (Finset.mem_singleton.mp v.2)⟩
  exact (Equiv.piUnique fun v : {v // v ∈ ({t.1} : Finset S)} ↦ F v).sum_comp (Ψ t)

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The map of a layer on a matrix unit is the product of the maps of its gates and onsite
families on the local matrix units. -/
theorem map_matrixUnit_apply (ev : Interpretation G) (L : Layer Γ G X Y) (x x' : Config X)
    (y y' : Config Y) :
    (L.krausFamily ev).map (Matrix.single x x' 1) y y' =
      (∏ b : L.cells, (L.gateFamily ev b).map (Matrix.single (fun v ↦ x v) (fun v ↦ x' v) 1)
        (fun v ↦ y v) (fun v ↦ y' v)) *
      ∏ s : L.Free, (L.onsite s).map (Matrix.single (x s) (x' s) 1) (y s) (y' s) := by
  simp only [KrausFamily.map_matrixUnit_apply, Fintype.prod_sum, Finset.sum_mul_sum]
  refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun j _ ↦ ?_)
  simp only [krausFamily, kraus, star_mul', star_prod, gateFamily]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end Layer

end QuantumCircuit
