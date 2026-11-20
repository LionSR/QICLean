/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Geometry.Basic

/-!
# Blockings of geometries

A map of sites `f : S → S'` groups the sites of a geometry `Γ` into blocks, the sites of a
geometry `Γ'`. A blocking of `Γ` into `Γ'` along `f` with `r` colours sends every cell of `Γ`
to a cell of `Γ'` containing its image, and colours the cells of `Γ'` with `r` colours so that
distinct cells of one colour are disjoint. A layer on `Γ` is then a sequence of `r` layers on
`Γ'`, one for each colour (`QuantumCircuit.IsProtocol.block`).

A blocking is formalization-side: it is the hypothesis under which a protocol on a geometry is a
protocol on its blocks. The ring of `M * k` sites is blocked into the ring of `M` blocks of `k`
consecutive sites with two colours for `M` even and three for `M` odd
(`QuantumCircuit.Geometry.ringBlocking`).

## Main definitions

* `QuantumCircuit.Geometry.Blocking` — a blocking of one geometry into another.
-/

namespace QuantumCircuit

namespace Geometry

variable {S S' : Type} [DecidableEq S']

/-- A blocking of the geometry `Γ` into the geometry `Γ'` along the map of sites `f`, with `r`
colours: every cell `b` of `Γ` is covered by a cell `cover b` of `Γ'` containing its image, the
cells of `Γ'` are coloured so that distinct cells of one colour are disjoint, and the cells of
`Γ` have positive cost.

The cells of one colour can therefore carry gates in one layer on `Γ'`, and a layer on `Γ` is
realised by one layer on `Γ'` for each colour. Positivity of the costs of `Γ` is what the depth
`r` of these layers is charged against: a layer on `Γ` using a cell has depth one, while a layer
using no cell has depth zero and is realised in depth zero.

This structure is formalization-side; the source blocks a chain into consecutive sites
(arXiv:2103.13367v3, `main.tex`, lines 287–289), which is `Geometry.ringBlocking`. -/
structure Blocking (Γ : Geometry S) (Γ' : Geometry S') (f : S → S') (r : ℕ) where
  /-- The cell of `Γ'` covering a cell of `Γ`. -/
  cover : Γ.Cell → Γ'.Cell
  /-- A cell of `Γ` lies, after `f`, in its covering cell. -/
  image_subset : ∀ b, (Γ.cell b).image f ⊆ Γ'.cell (cover b)
  /-- The colour of a cell of `Γ'`. -/
  colour : Γ'.Cell → Fin r
  /-- Distinct cells of one colour are disjoint. -/
  disjoint : ∀ c₁ c₂, colour c₁ = colour c₂ → c₁ ≠ c₂ → Disjoint (Γ'.cell c₁) (Γ'.cell c₂)
  /-- The cells of `Γ` have positive cost. -/
  cost_pos : ∀ b, 0 < Γ.cost b

end Geometry

end QuantumCircuit
