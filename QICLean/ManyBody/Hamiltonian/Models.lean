/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Sites.Lattice.Line
import QICLean.ManyBody.Sites.Lattice.Plane
import QICLean.ManyBody.Sites.Lattice.Square

/-!
# The lattice models

A lattice model is a choice of sites, local dimension and supports, and its Hamiltonians are the
`ManyBody.Interaction`s for that choice. The abbreviations of this file name these choices:

* the chain of `L` sites with its supports of range `R`;
* a finite set `Λ ⊂ ℤ` with its supports of range `R` in the induced path graph;
* a finite set `Λ ⊂ ℤ × ℤ` with its supports of range `R` in the induced nearest-neighbour
  graph;
* the `width × height` square lattice with one term per vertex and one per edge, and the
  `L × L` square as its special case.

They exist for field notation and readability; they add no structure. Hermiticity of the terms
(or only of their sum), the norm bound `J`, the range and the degree are hypotheses of the
statements that use them, and every `Interaction` lemma applies to these types as it stands.

These replace TNLean's structures `ChainHamiltonian L q R J`, `DomainHamiltonian Λ q R J`,
`Lattice.LocalHamiltonian Λ q R J`, `RectangularHamiltonian width height q J` and
`SquareHamiltonian L q J` (TNLean commit `71c1185e9352a3b5237b37a6840640751da6ca2d`): each is one
of these interactions together with the hypotheses that were its fields.

## Main definitions

* `ManyBody.ChainInteraction`, `ManyBody.DomainInteraction`, `ManyBody.PlaneInteraction`,
  `ManyBody.RectangleInteraction`, `ManyBody.SquareInteraction`.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, Section 1, `eq:ham`, and `part0_preamble.tex`, `eq:ham`.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Theorem 1.1, `eq:hamiltonian`, and `eq:model`.
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `eq:model`.
-/

namespace ManyBody

/-- The finite-range interactions on the chain of `L` sites with local dimension `q`: one term
for each support of range `R`. TNLean note, Section 1, `eq:ham`. -/
abbrev ChainInteraction (L q R : ℕ) :=
  Interaction (fun _ : Fin L ↦ Fin q) (fun X : ChainSupport L R ↦ X.1)

/-- The finite-range interactions on a finite set `Λ ⊂ ℤ` with local dimension `q`: one term
for each support of range `R` in the induced path graph. TNLean note, `part0_preamble.tex`,
`eq:ham`. -/
abbrev DomainInteraction (Λ : Finset ℤ) (q R : ℕ) :=
  Interaction (fun _ : Fin Λ.card ↦ Fin q) (fun X : DomainSupport Λ R ↦ X.1)

/-- The finite-range interactions on a finite set `Λ ⊂ ℤ × ℤ` with local dimension `q`: one term
for each support of range `R` in the induced nearest-neighbour graph. Area law, Theorem 1.1,
`eq:hamiltonian`. -/
abbrev PlaneInteraction (Λ : Finset (ℤ × ℤ)) (q R : ℕ) :=
  Interaction (fun _ : ↥Λ ↦ Fin q) (fun X : AdmissibleSupport Λ R ↦ X.1)

/-- The site-and-edge interactions on the `width × height` square lattice with local dimension
`q`: one term on each vertex and one on the two endpoints of each edge. Area law and
polynomial-PEPS, `eq:model`. -/
abbrev RectangleInteraction (width height q : ℕ) :=
  Interaction (fun _ : SquareLatticeVertex width height ↦ Fin q)
    (squareLatticeSiteOrEdgeSupport (width := width) (height := height))

/-- The site-and-edge interactions on the `L × L` square. Polynomial-PEPS, `eq:model`. -/
abbrev SquareInteraction (L q : ℕ) :=
  RectangleInteraction L L q

end ManyBody
