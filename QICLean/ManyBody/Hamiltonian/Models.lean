/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Dynamics.InteractionOperations
import QICLean.ManyBody.Sites.Lattice.Line
import QICLean.ManyBody.Sites.Lattice.Plane
import QICLean.ManyBody.Sites.Lattice.Rectangle
import QICLean.ManyBody.Sites.Lattice.Ring
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
  `L × L` square as its special case;
* the chain of `L` sites with one term on each bond `{i, i + 1}`.

Two maps relate the models. A bond interaction is the range-one chain interaction whose term
on the bond `{i, i + 1}` is the bond term and whose single-site terms vanish
(`ManyBody.BondInteraction.toChainInteraction`), and a rectangle interaction is the range-one
interaction on the rectangular domain of `ℤ × ℤ` whose term on the image of a vertex or an edge
is the transported term, the other terms vanishing
(`ManyBody.RectangleInteraction.toPlaneInteraction`). Both are extensions along an injection of
indices, `ManyBody.Interaction.extend`. On the ring of `N` sites, the translation-invariant
interaction of one operator on `k ≤ N` consecutive sites has the translates of that operator
as its terms (`ManyBody.Interaction.translationInvariant`).

They exist for field notation and readability; they add no structure. Hermiticity of the terms
(or only of their sum), the norm bound `J`, the range and the degree are hypotheses of the
statements that use them, and every `Interaction` lemma applies to these types as it stands.

These replace TNLean's structures `ChainHamiltonian L q R J`, `DomainHamiltonian Λ q R J`,
`Lattice.LocalHamiltonian Λ q R J`, `RectangularHamiltonian width height q J` and
`SquareHamiltonian L q J` (TNLean commit `71c1185e9352a3b5237b37a6840640751da6ca2d`): each is one
of these interactions together with the hypotheses that were its fields.

## Main definitions

* `ManyBody.ChainInteraction`, `ManyBody.DomainInteraction`, `ManyBody.PlaneInteraction`,
  `ManyBody.RectangleInteraction`, `ManyBody.SquareInteraction`, `ManyBody.BondInteraction`.
* `ManyBody.bondSupport`, `ManyBody.BondInteraction.toChainInteraction`.
* `ManyBody.RectangleInteraction.toPlaneInteraction`.
* `ManyBody.Interaction.translationInvariant`.

## Main results

* `ManyBody.RectangleInteraction.hamiltonian_toPlaneInteraction` — the map to the plane keeps
  the Hamiltonian, transported to the configurations of the domain.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, Section 1, `eq:ham`, and `part0_preamble.tex`, `eq:ham`.
* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Theorem 1.1, `eq:hamiltonian`, and `eq:model`.
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `eq:model`.
* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, lines 209–211 and 283.
* N. Schuch, D. Pérez-García, J. I. Cirac, *Classifying quantum phases using matrix product
  states and projected entangled pair states*, arXiv:1010.3732,
  `sec:phases-definition-no-sym`, lines 407–427.
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

/-! ### Bond interactions on the chain -/

section Bond

variable {L q : ℕ}

/-- The nearest-neighbour interactions on the chain of `L` sites with local dimension `q`: one
term for each bond `{i, i + 1}`, `i < L - 1`. Landau, Vazirani and Vidick, arXiv:1307.5143v1,
`algo53.tex`, lines 209–211. -/
abbrev BondInteraction (L q : ℕ) :=
  Interaction (fun _ : Fin L ↦ Fin q) (fun i : Fin (L - 1) ↦ interval L i.val (i.val + 2))

/-- The bond `{i, i + 1}` of the chain of `L` sites as a support of range one. -/
def bondSupport (i : Fin (L - 1)) : ChainSupport L 1 :=
  ⟨interval L i.val (i.val + 2), ⟨⟨i.val, by omega⟩, mem_interval.mpr ⟨le_rfl, by simp⟩⟩,
    fun x hx y hy ↦ by
      rw [mem_interval] at hx hy
      omega⟩

/-- Distinct bonds are distinct supports. -/
theorem bondSupport_injective : Function.Injective (bondSupport (L := L)) := by
  intro i j hij
  have hi : (⟨i.val, by omega⟩ : Fin L) ∈ (bondSupport j).1 := by
    rw [← hij]
    exact mem_interval.mpr ⟨le_rfl, by simp⟩
  have hj : (⟨j.val, by omega⟩ : Fin L) ∈ (bondSupport i).1 := by
    rw [hij]
    exact mem_interval.mpr ⟨le_rfl, by simp⟩
  simp only [bondSupport, mem_interval] at hi hj
  exact Fin.ext (by omega)

/-- **A bond interaction as a range-one chain interaction.** The term on the support
`{i, i + 1}` is the bond term with index `i`, and the terms on all other supports of range one,
the single sites among them, vanish. It is the extension of the bond interaction along the
injection `bondSupport`, so the lemmas on `ManyBody.Interaction.extend` give its terms and its
Hamiltonian, which is the Hamiltonian of the bond interaction. Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, lines 209–211 and 283. -/
noncomputable abbrev BondInteraction.toChainInteraction (Φ : BondInteraction L q) :
    ChainInteraction L q 1 :=
  Φ.extend bondSupport bondSupport_injective (fun X ↦ X.1) fun _ ↦ subset_rfl

end Bond

/-! ### Translation-invariant interactions on the ring -/

section Ring

variable {N k : ℕ} [NeZero N] {α : Type*} [Fintype α] [DecidableEq α]

/-- **The translation-invariant interaction on the ring** of `N` sites of one operator `h` on
`k ≤ N` consecutive sites: its term with index `i` is `h` placed on the window of `k`
consecutive sites starting at `i`. For `k = 2` these windows are the bonds `{i, i + 1}`
(`ManyBody.map_ringWindow_two`). Schuch, Pérez-García and Cirac, arXiv:1010.3732,
`sec:phases-definition-no-sym`, lines 407–427. -/
noncomputable abbrev Interaction.translationInvariant (hk : k ≤ N)
    (h : Matrix (Fin k → α) (Fin k → α) ℂ) :
    Interaction (fun _ : Fin N ↦ α) (fun i ↦ Finset.univ.map (ringWindow hk i)) :=
  Interaction.translates (ringWindow hk) h

end Ring

/-! ### Rectangle interactions on the plane -/

namespace RectangleInteraction

variable {width height q : ℕ}

/-- **A rectangle interaction as a range-one interaction on its domain of the plane.** The term
on the image of a vertex or an edge is its term, transported along the identification of the
vertices with the sites of the rectangular domain, and the terms on all other supports of
range one vanish. It is the relabelling of the sites followed by the extension along the
injection `rectangleSupport`. Area law, Corollary 1.2, and polynomial-PEPS, `eq:model`. -/
noncomputable abbrev toPlaneInteraction (Φ : RectangleInteraction width height q) :
    PlaneInteraction (rectangularDomain width height) q 1 :=
  (Φ.relabel (rectangleSiteEquiv width height) (fun _ ↦ Equiv.refl _)
      (fun i ↦ (rectangleSupport i).1) fun i v ↦ (mem_rectangleSupport_iff i v).symm).extend
    rectangleSupport (rectangleSupport_injective width height) (fun X ↦ X.1) fun _ ↦ subset_rfl

/-- The map to the plane keeps the Hamiltonian, transported to the configurations of the
rectangular domain. Area law, Corollary 1.2. -/
theorem hamiltonian_toPlaneInteraction (Φ : RectangleInteraction width height q) :
    Φ.toPlaneInteraction.hamiltonian =
      Matrix.reindex (siteConfigurationEquiv (rectangleSiteEquiv width height)
          fun _ ↦ Equiv.refl (Fin q))
        (siteConfigurationEquiv (rectangleSiteEquiv width height) fun _ ↦ Equiv.refl (Fin q))
        Φ.hamiltonian := by
  rw [Interaction.hamiltonian_extend, Interaction.hamiltonian_relabel]

end RectangleInteraction

end ManyBody
