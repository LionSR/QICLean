/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Plane
import QICLean.ManyBody.Sites.Lattice.Square

/-!
# The rectangle as a finite domain of the plane

The vertices of the `width × height` square lattice embed in `ℤ × ℤ` by their coordinates, and
their image is the rectangular domain. The embedding identifies the vertices with the sites of
the domain and the square-lattice graph with the induced nearest-neighbour graph of the domain.
Each vertex and each edge of the square lattice thereby gives a support of range one in the
domain, and distinct vertices and edges give distinct supports. Either side may be zero.

Moved from TNLean, `TNLean/PEPS/AreaLaw/RectangularDomain.lean` and
`TNLean/PEPS/AreaLaw/RectangularHamiltonian.lean` (`rectangleAreaLawSupport` and its
injectivity) at commit `414a18fb88`. Changes: namespace `ManyBody` in place of
`TNLean.PEPS.AreaLaw`; the support of a vertex or an edge is its image under the site
identification, written with `Finset.map`; `rectangleConfigurationEquiv` is not moved, since the
configurations are transported by `ManyBody.siteConfigurationEquiv`.

## Main definitions

* `ManyBody.rectangularDomain` — the image of the rectangle in `ℤ × ℤ`.
* `ManyBody.rectangleSiteEquiv` — the vertices as the sites of the domain.
* `ManyBody.rectangleSupport` — the range-one support of a vertex or an edge.

## Main results

* `ManyBody.rectangleGraphIso` — the square-lattice graph is the induced graph of the domain.
* `ManyBody.squareLatticeSiteOrEdgeSupport_injective`, `ManyBody.rectangleSupport_injective`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Corollary 1.2.
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Section 1, the open grid `Λ_L`, and `eq:model`.
-/

namespace ManyBody

variable {width height : ℕ}

/-- The integer coordinates of a vertex of the rectangle. Area law, Corollary 1.2. -/
def rectangleEmbedding (v : SquareLatticeVertex width height) : ℤ × ℤ :=
  ((v.1.val : ℤ), (v.2.val : ℤ))

/-- Distinct vertices of the rectangle have distinct integer coordinates. -/
theorem rectangleEmbedding_injective (width height : ℕ) :
    Function.Injective (rectangleEmbedding (width := width) (height := height)) :=
  fun _ _ h ↦ by simpa [rectangleEmbedding, Prod.ext_iff, Fin.ext_iff] using h

/-- The finite domain of the `width × height` rectangle in `ℤ × ℤ`, also when a side is zero.
Area law, Corollary 1.2. -/
def rectangularDomain (width height : ℕ) : Finset (ℤ × ℤ) :=
  Finset.univ.image (rectangleEmbedding (width := width) (height := height))

/-- The vertices of the rectangle as the sites of its domain. -/
noncomputable def rectangleSiteEquiv (width height : ℕ) :
    SquareLatticeVertex width height ≃ ↥(rectangularDomain width height) :=
  (Equiv.ofInjective rectangleEmbedding (rectangleEmbedding_injective width height)).trans
    (Equiv.subtypeEquivRight (by simp [rectangularDomain, Set.mem_range]))

@[simp]
theorem rectangleSiteEquiv_val (width height : ℕ) (v : SquareLatticeVertex width height) :
    (rectangleSiteEquiv width height v).val = rectangleEmbedding v :=
  rfl

/-- The square-lattice graph is the induced nearest-neighbour graph of the rectangular domain.
Area law, Corollary 1.2. -/
noncomputable def rectangleGraphIso (width height : ℕ) :
    squareLatticeGraph width height ≃g planeDomainGraph (rectangularDomain width height) where
  toEquiv := rectangleSiteEquiv width height
  map_rel_iff' := by
    intro v w
    simp only [planeDomainGraph, rectangleSiteEquiv_val, rectangleEmbedding,
      squareLatticeGraph_adj, squareLatticeHorizontalNeighbor, squareLatticeVerticalNeighbor]
    norm_cast
    simp only [Fin.ext_iff]

/-- Distinct vertices and edges of the square lattice have distinct supports: a vertex is the
only label with a one-point support, and an edge is determined by its two endpoints.
Polynomial-PEPS, `eq:model`. -/
theorem squareLatticeSiteOrEdgeSupport_injective (width height : ℕ) :
    Function.Injective (squareLatticeSiteOrEdgeSupport (width := width) (height := height)) := by
  have hcard (e : Edge (squareLatticeGraph width height)) :
      ({e.1.1, e.1.2} : Finset _).card = 2 :=
    Finset.card_pair ((squareLatticeGraph width height).ne_of_adj e.2.2)
  rintro (v | e) (w | f) h <;> simp only [squareLatticeSiteOrEdgeSupport] at h
  · rw [Finset.singleton_inj.mp h]
  · simpa [← h] using hcard f
  · simpa [h] using hcard e
  · have hs : ({e.1.1, e.1.2} : Set _) = {f.1.1, f.1.2} := by
      rw [← Finset.coe_pair, h, Finset.coe_pair]
    exact congrArg Sum.inr
      ((Edge.ofAdj_eq_of_endpoints e.2.2 e (Or.inl ⟨rfl, rfl⟩)).symm.trans
        (Edge.ofAdj_eq_of_endpoints e.2.2 f (Set.pair_eq_pair_iff.mp hs)))

/-- The support of range one in the rectangular domain of a vertex or an edge of the square
lattice: the image of its vertex, or of the two endpoints of its edge. Area law, Corollary 1.2,
and polynomial-PEPS, `eq:model`. -/
noncomputable def rectangleSupport (i : SquareLatticeSiteOrEdge width height) :
    AdmissibleSupport (rectangularDomain width height) 1 :=
  ⟨(squareLatticeSiteOrEdgeSupport i).map (rectangleSiteEquiv width height).toEmbedding, by
    cases i with
    | inl v =>
      simpa [squareLatticeSiteOrEdgeSupport] using
        isAdmissibleSupport_singleton (rectangularDomain width height) 1
          (rectangleSiteEquiv width height v)
    | inr e =>
      simpa [squareLatticeSiteOrEdgeSupport] using isAdmissibleSupport_pair_of_adj
        (x := rectangleSiteEquiv width height e.1.1) (y := rectangleSiteEquiv width height e.1.2)
        ((rectangleGraphIso width height).map_rel_iff.mpr e.2.2)⟩

/-- A site of the domain lies in the support of a vertex or an edge exactly when the
corresponding vertex lies in its region. -/
theorem mem_rectangleSupport_iff (i : SquareLatticeSiteOrEdge width height)
    (v : SquareLatticeVertex width height) :
    rectangleSiteEquiv width height v ∈ (rectangleSupport i).1 ↔
      v ∈ squareLatticeSiteOrEdgeSupport i := by
  simp [rectangleSupport]

/-- Distinct vertices and edges of the square lattice have distinct supports in the domain.
Polynomial-PEPS, `eq:model`. -/
theorem rectangleSupport_injective (width height : ℕ) :
    Function.Injective (rectangleSupport (width := width) (height := height)) := fun _ _ h ↦
  squareLatticeSiteOrEdgeSupport_injective width height
    (Finset.map_injective _ (congrArg Subtype.val h))

end ManyBody
