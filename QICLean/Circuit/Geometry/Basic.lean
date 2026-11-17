/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

/-!
# Geometries of cells

A geometry on a set of sites `S` is a family of cells, each a finite set of sites on which one
gate may act, together with a cost of each cell. The bonds of a ring, the windows of an open
chain, the edges of a graph, the wires of one site (at cost zero) and arbitrary sets of parties
are geometries. A circuit on a geometry acts in each layer on pairwise disjoint cells, and its
depth and gate count are measured by the costs.

## Main definitions

* `QuantumCircuit.Geometry` — cells with costs.
* `QuantumCircuit.Geometry.neighbourhood` — a region together with every cell meeting it.
* `QuantumCircuit.Geometry.neighbourhood_mono`,
  `QuantumCircuit.Geometry.iterate_neighbourhood_mono` — monotonicity of the neighbourhood and
  of its iterates.
* `QuantumCircuit.Geometry.restrict` — the cells inside a region, as a geometry on its sites.
-/

namespace QuantumCircuit

/-- A geometry on the sites `S`: a type of cells, the finite set of sites of each cell, and the
cost of a gate on it. -/
structure Geometry (S : Type) where
  /-- The cells. -/
  Cell : Type
  [decEq : DecidableEq Cell]
  /-- The sites of a cell. -/
  cell : Cell → Finset S
  /-- The cost of a gate on a cell. -/
  cost : Cell → ℕ

attribute [instance] Geometry.decEq

namespace Geometry

variable {S : Type} [DecidableEq S]

/-- The region `R` together with every cell that meets it. -/
def neighbourhood (Γ : Geometry S) [Fintype Γ.Cell] (R : Finset S) : Finset S :=
  R ∪ (Finset.univ.filter fun b ↦ (Γ.cell b ∩ R).Nonempty).biUnion Γ.cell

theorem subset_neighbourhood (Γ : Geometry S) [Fintype Γ.Cell] (R : Finset S) :
    R ⊆ Γ.neighbourhood R :=
  Finset.subset_union_left

theorem neighbourhood_mono (Γ : Geometry S) [Fintype Γ.Cell] {R R' : Finset S} (h : R ⊆ R') :
    Γ.neighbourhood R ⊆ Γ.neighbourhood R' := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.mem_union_left _ (h hv)
  · obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨w, hw⟩ := (Finset.mem_filter.mp hb).2
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨b, ?_, hvb⟩)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, ?_⟩
    rw [Finset.mem_inter] at hw ⊢
    exact ⟨hw.1, h hw.2⟩

theorem iterate_neighbourhood_mono (Γ : Geometry S) [Fintype Γ.Cell] {m n : ℕ} (hmn : m ≤ n)
    {R R' : Finset S} (h : R ⊆ R') :
    Γ.neighbourhood^[m] R ⊆ Γ.neighbourhood^[n] R' := by
  induction n generalizing m with
  | zero => rw [Nat.le_zero.mp hmn]; exact h
  | succ n ih =>
    rcases Nat.of_le_succ hmn with hmn | rfl
    · rw [Function.iterate_succ_apply']
      exact (ih hmn).trans (Γ.subset_neighbourhood _)
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact Γ.neighbourhood_mono (ih le_rfl)

/-- The cells contained in the region `D`, as a geometry on the sites of `D`. -/
def restrict (Γ : Geometry S) (D : Finset S) : Geometry {s // s ∈ D} where
  Cell := {b // Γ.cell b ⊆ D}
  cell b := (Γ.cell b.1).subtype (· ∈ D)
  cost b := Γ.cost b.1

end Geometry

end QuantumCircuit
