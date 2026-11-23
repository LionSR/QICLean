/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset

/-!
# The geometry of all finite sets of sites

Every finite set of sites is a cell, so a gate may act on any set of sites at once, as a gate
among several parties does. A cell of one site is private and costs nothing; every other cell,
the empty cell included, costs `1`. The gate count of a circuit on this geometry is then the
number of its gates that are not private, and the participation of a site is the number of such
gates containing it.

The cells form a finite type when the sites do (`Finset S` is finite), so the neighbourhood of a
region is defined on this geometry.

## Main definitions

* `QuantumCircuit.Geometry.subsets` — every finite set of sites is a cell.

## Main results

* `QuantumCircuit.Geometry.subsets_cost_empty`, `QuantumCircuit.Geometry.subsets_cost_singleton`,
  `QuantumCircuit.Geometry.subsets_cost_of_two_le_card` — the cost on the empty cell, on a cell of
  one site, and on a cell of at least two sites.
* `QuantumCircuit.Geometry.subsets_cost_pos_iff` — a cell has positive cost exactly when it is
  not a single site.
-/

namespace QuantumCircuit.Geometry

/-- The geometry whose cells are all finite sets of sites. A cell of one site costs `0`, every
other cell costs `1`. -/
abbrev subsets (S : Type) [DecidableEq S] : Geometry S where
  Cell := Finset S
  cell := id
  cost D := if D.card = 1 then 0 else 1

variable {S : Type} [DecidableEq S]

@[simp] theorem subsets_cell (D : Finset S) : (subsets S).cell D = D :=
  rfl

theorem subsets_cost (D : Finset S) : (subsets S).cost D = if D.card = 1 then 0 else 1 :=
  rfl

/-- The empty cell costs `1`. -/
@[simp] theorem subsets_cost_empty : (subsets S).cost ∅ = 1 :=
  rfl

/-- A cell of one site costs nothing. -/
@[simp] theorem subsets_cost_singleton (s : S) : (subsets S).cost {s} = 0 := by
  simp

/-- A cell of at least two sites costs `1`. -/
theorem subsets_cost_of_two_le_card {D : Finset S} (h : 2 ≤ D.card) : (subsets S).cost D = 1 :=
  ite_eq_right (by omega)

/-- A cell has positive cost exactly when it is not a single site. -/
theorem subsets_cost_pos_iff (D : Finset S) : 0 < (subsets S).cost D ↔ D.card ≠ 1 := by
  rw [subsets_cost]
  split_ifs with h <;> simp [h]

/-- Every cell costs at most `1`. -/
theorem subsets_cost_le_one (D : Finset S) : (subsets S).cost D ≤ 1 := by
  rw [subsets_cost]
  split_ifs <;> omega

end QuantumCircuit.Geometry
