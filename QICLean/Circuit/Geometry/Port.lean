/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# The ring with physical ports

The ring of `N` sites with `W` wires at every site, wire `0` being the physical port. A gate on
all the wires of one site is a local operation, of cost `0`; a gate between two neighbouring
sites acts on their two ports only, at cost `1`. This is the convention of Piroli, Styliaris and
Cirac, arXiv:2103.13367, Supplement, proof of Proposition 2, p. 8: the intersite gates act only on
physical qudits of fixed dimension, and every site may hold a local memory.

## Main definitions

* `QuantumCircuit.Geometry.portRing` — whole sites at cost `0` and pairs of neighbouring ports
  at cost `1`.
-/

namespace QuantumCircuit

namespace Geometry

/-- The ring of `N` sites with `W` wires per site and the port at wire `0`: the cell `inl i` is
all the wires of the site `i`, at cost `0`, and the cell `inr i` is the pair of ports of the
sites `i` and `i + 1`, at cost `1`.

This geometry is formalization-side: it is the gate convention of arXiv:2103.13367, Supplement,
proof of Proposition 2, p. 8, written as cells with costs. -/
def portRing (N W : ℕ) [NeZero W] : Geometry (Fin N × Fin W) where
  Cell := Fin N ⊕ Fin N
  cell
    | .inl i => {i} ×ˢ Finset.univ
    | .inr i => {(i, 0), (finRotate N i, 0)}
  cost
    | .inl _ => 0
    | .inr _ => 1

variable {N W : ℕ} [NeZero W]

@[simp] theorem portRing_cell_inl (i : Fin N) :
    (portRing N W).cell (.inl i) = {i} ×ˢ Finset.univ :=
  rfl

@[simp] theorem portRing_cell_inr (i : Fin N) :
    (portRing N W).cell (.inr i) = {(i, 0), (finRotate N i, 0)} :=
  rfl

@[simp] theorem portRing_cost_inl (i : Fin N) : (portRing N W).cost (.inl i) = 0 :=
  rfl

@[simp] theorem portRing_cost_inr (i : Fin N) : (portRing N W).cost (.inr i) = 1 :=
  rfl

end Geometry

end QuantumCircuit
