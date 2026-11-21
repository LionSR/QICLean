/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Diamond
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Int.Interval
import QICLean.ManyBody.Sites.GraphBoundary

/-!
# Finite domains of the square lattice

A domain is a finite subset `Λ` of `ℤ × ℤ`, and its sites are the elements of `Λ`. Two sites
are adjacent in the induced nearest-neighbour graph when they differ by one in one coordinate.
A support of range `R` is a nonempty set of sites any two of which are joined, inside the
domain, by a walk of length at most `R`. Neither connectedness nor the absence of holes is
assumed.

Moved from TNLean, `TNLean/Lattice/FiniteDomain.lean` (`domainGraph`, `IsAdmissibleSupport`,
`AdmissibleSupport` and their lemmas) at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`. Changes:
namespace `ManyBody` in place of `TNLean.Lattice`; `domainGraph` is renamed `planeDomainGraph`, to
distinguish it from the path graph `lineDomainGraph` of a domain of `ℤ`; the sites are written `↥Λ`,
without the abbreviation `Site Λ`.

The ambient dilation `ManyBody.ambientDilation` and the sites `ManyBody.crossingSites` of the
supports crossing a region are moved from TNLean, `TNLean/Lattice/FiniteDomain.lean` and
`TNLean/Lattice/CrossingSupports.lean` at commit `e113e005`, with `ManyBody.crossingTerms` in place
of `Entropy.crossingTerms`. The edge boundary of a region is the edge boundary
`ManyBody.edgeBoundary (planeDomainGraph Λ) A` of `QICLean.ManyBody.Sites.GraphBoundary`, and
`ManyBody.planeDomainGraph_degree_le_four` supplies the degree bound for its counts; the degree
bound is moved from TNLean, `TNLean/PEPS/AreaLaw/BoundaryConventions.lean`
(`domainGraph_degree_le_four`) at commit `414a18fb88`.

`ManyBody.latticeL1Distance_le_one_of_planeDomainGraph_adj`,
`ManyBody.IsAdmissibleSupport.edist_le`, `ManyBody.IsAdmissibleSupport.card_le` and
`ManyBody.IsAdmissibleSupport.reachable` are moved from TNLean,
`TNLean/PEPS/AreaLaw/GraphPropagation.lean` and `TNLean/PEPS/AreaLaw/ZeroBoundary.lean`
on branch `claude/f6-plane-domain-graph` at commit `38fc1aa67a7b1f09af1610cb629d2ad5648b1a24`.
Changes: the first was `latticeL1Distance_le_one_of_domainGraph_adj` in `TNLean.PEPS.AreaLaw`;
`card_le` applies `ManyBody.card_le_diamond_of_walks` directly, in place of TNLean's
`card_support_le_diamond`.

## Main definitions

* `ManyBody.planeDomainGraph` — the induced nearest-neighbour graph.
* `ManyBody.IsAdmissibleSupport`, `ManyBody.AdmissibleSupport` — the supports of range `R`.
* `ManyBody.ambientDilation` — the sup-norm dilation of a finite set of lattice points.
* `ManyBody.crossingSites` — the sites of the supports of range `R` crossing a region.

## Main results

* `ManyBody.IsAdmissibleSupport.edist_le`, `ManyBody.IsAdmissibleSupport.card_le` — a support of
  range `R` has graph diameter at most `R` and at most `1 + 2R(R + 1)` sites.
* `ManyBody.IsAdmissibleSupport.reachable` — a support lies in one connected component.
* `ManyBody.planeDomainGraph_degree_le_four` — every site has at most four neighbours.
* `ManyBody.exists_walks_of_mem_crossingSites` — a site of a crossing support is near both
  sides of the region.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Theorem 1.1, `eq:hamiltonian`, Sections 1 and 2, Definition 9.3.
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `02-information.tex`, lines 416–424 and 498–564.
-/

namespace ManyBody

/-- The nearest-neighbor graph induced on the domain.
Source: area-law Section 1, before `eq:hamiltonian`. -/
def planeDomainGraph (Λ : Finset (ℤ × ℤ)) : SimpleGraph ↥Λ where
  Adj x y :=
    (x.1.2 = y.1.2 ∧ (x.1.1 + 1 = y.1.1 ∨ y.1.1 + 1 = x.1.1)) ∨
    (x.1.1 = y.1.1 ∧ (x.1.2 + 1 = y.1.2 ∨ y.1.2 + 1 = x.1.2))
  symm := ⟨by intros; omega⟩
  loopless := ⟨by intros; omega⟩

instance (Λ : Finset (ℤ × ℤ)) : DecidableRel (planeDomainGraph Λ).Adj := by
  unfold planeDomainGraph
  infer_instance

/-- A support is nonempty and every pair of its sites is joined inside the
induced domain by a walk of length at most `R`.

Source: area-law `eq:hamiltonian`. -/
def IsAdmissibleSupport (Λ : Finset (ℤ × ℤ)) (R : ℕ) (X : Finset ↥Λ) : Prop :=
  X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X, ∃ p : (planeDomainGraph Λ).Walk x y, p.length ≤ R

/-- The finite index of supports in the Hamiltonian sum, with one index per
nonempty support. Source: area-law `eq:hamiltonian`. -/
abbrev AdmissibleSupport (Λ : Finset (ℤ × ℤ)) (R : ℕ) :=
  {X : Finset ↥Λ // IsAdmissibleSupport Λ R X}

noncomputable instance (Λ : Finset (ℤ × ℤ)) (R : ℕ) :
    Fintype (AdmissibleSupport Λ R) := Fintype.ofFinite _

/-- A singleton is an admissible support at every range.
Source: area-law `eq:hamiltonian`, including range zero. -/
theorem isAdmissibleSupport_singleton (Λ : Finset (ℤ × ℤ)) (R : ℕ) (x : ↥Λ) :
    IsAdmissibleSupport Λ R {x} := by
  refine ⟨Finset.singleton_nonempty x, ?_⟩
  simp only [Finset.mem_singleton]
  rintro y rfl z rfl
  exact ⟨.nil, Nat.zero_le R⟩

/-- The walk condition agrees with Mathlib's extended graph metric.
Disconnected pairs have distance infinity, so cannot satisfy a finite range. -/
theorem exists_walk_length_le_iff_edist_le (Λ : Finset (ℤ × ℤ)) (R : ℕ)
    (x y : ↥Λ) :
    (∃ p : (planeDomainGraph Λ).Walk x y, p.length ≤ R) ↔
      (planeDomainGraph Λ).edist x y ≤ R := by
  constructor
  · rintro ⟨p, hp⟩
    exact p.edist_le.trans (by exact_mod_cast hp)
  · intro h
    obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top
      (ne_top_of_le_ne_top (by simp) h)
    exact ⟨p, by exact_mod_cast hp ▸ h⟩

/-- At range zero, admissible supports are exactly the one-site supports.
Source: area-law Section 2, the range-zero Hamiltonian. -/
theorem isAdmissibleSupport_zero_iff (Λ : Finset (ℤ × ℤ)) (X : Finset ↥Λ) :
    IsAdmissibleSupport Λ 0 X ↔ X.card = 1 := by
  simp only [IsAdmissibleSupport]
  simp_rw [exists_walk_length_le_iff_edist_le]
  simp only [Nat.cast_zero, le_zero_iff, SimpleGraph.edist_eq_zero_iff]
  rw [← Finset.card_le_one, ← Finset.card_pos]
  omega

/-- Adjacent sites form an admissible range-one support.
Source: area-law Corollary 1.2, nearest-neighbor interactions. -/
theorem isAdmissibleSupport_pair_of_adj {Λ : Finset (ℤ × ℤ)}
    {x y : ↥Λ} (h : (planeDomainGraph Λ).Adj x y) :
    IsAdmissibleSupport Λ 1 {x, y} := by
  simp only [IsAdmissibleSupport]
  simp_rw [exists_walk_length_le_iff_edist_le]
  simp [SimpleGraph.edist_le_one_iff_adj_or_eq, h, h.symm]

/-- Adjacent sites of the induced domain graph have lattice distance at most one.
Source: area law, `01-preliminaries.tex`, lines 81–84. -/
theorem latticeL1Distance_le_one_of_planeDomainGraph_adj {Λ : Finset (ℤ × ℤ)} {x y : ↥Λ}
    (hxy : (planeDomainGraph Λ).Adj x y) : latticeL1Distance x.1 y.1 ≤ 1 := by
  simp only [planeDomainGraph] at hxy
  unfold latticeL1Distance
  rcases hxy with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;> omega

namespace IsAdmissibleSupport

variable {Λ : Finset (ℤ × ℤ)} {R : ℕ} {X : Finset ↥Λ}

/-- An admissible support has induced-graph diameter at most `R`.
Source: area law, `eq:hamiltonian` and `03-quasilocal.tex`, line 16. -/
theorem edist_le (hX : IsAdmissibleSupport Λ R X) :
    ∀ x ∈ X, ∀ z ∈ X, (planeDomainGraph Λ).edist x z ≤ R := fun x hx z hz =>
  (exists_walk_length_le_iff_edist_le Λ R x z).mp (hX.2 x hx z hz)

/-- An admissible support has at most `v_R = 1 + 2R(R + 1)` sites.
Source: area law, `eq:quasilocal-budget` (`03-quasilocal.tex`, lines 31–39). -/
theorem card_le (hX : IsAdmissibleSupport Λ R X) : X.card ≤ 1 + 2 * R * (R + 1) :=
  let ⟨a, ha⟩ := hX.1
  card_le_diamond_of_walks Subtype.val X Subtype.val_injective
    (fun _ _ => latticeL1Distance_le_one_of_planeDomainGraph_adj) a R (hX.2 a ha)

/-- **Every admissible support lies in one connected component.**
Source: area law, Lemma 2.2 (`lem:zero-boundary`). -/
theorem reachable (hX : IsAdmissibleSupport Λ R X) {x y : ↥Λ} (hx : x ∈ X) (hy : y ∈ X) :
    (planeDomainGraph Λ).Reachable x y :=
  let ⟨w, _⟩ := hX.2 x hx y hy
  ⟨w⟩

end IsAdmissibleSupport

/-! ### Degrees, ambient dilations and crossing supports -/

/-- Every site of the induced nearest-neighbour graph has at most four neighbours, so the
degree counts of `QICLean.ManyBody.Sites.GraphBoundary` apply with `k = 4`.
Source: area law, Corollary 1.2, the degree count in its proof. -/
theorem planeDomainGraph_degree_le_four (Λ : Finset (ℤ × ℤ)) (x : ↥Λ) :
    (planeDomainGraph Λ).degree x ≤ 4 := by
  classical
  have hcard := Finset.card_image_of_injective
    ((planeDomainGraph Λ).neighborFinset x) (Subtype.val_injective (p := (· ∈ Λ)))
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← hcard]
  refine (Finset.card_le_card (t :=
    {(x.1.1 + 1, x.1.2), (x.1.1 - 1, x.1.2),
      (x.1.1, x.1.2 + 1), (x.1.1, x.1.2 - 1)}) ?_).trans Finset.card_le_four
  simp only [Finset.image_subset_iff]
  intro y hy
  have hy := ((planeDomainGraph Λ).mem_neighborFinset x y).mp hy
  simp only [planeDomainGraph] at hy
  grind [Prod.ext_iff]

/-- The integer sup-norm dilation of a finite set of lattice points, independent of walks in a
domain. Source: area-law Definition 9.3 and the sets `T_j`. -/
def ambientDilation (T : Finset (ℤ × ℤ)) (r : ℕ) : Finset (ℤ × ℤ) :=
  T.biUnion fun x ↦
    (Finset.Icc (x.1 - (r : ℤ)) (x.1 + r)).product (Finset.Icc (x.2 - (r : ℤ)) (x.2 + r))

/-- Membership in an ambient dilation, in coordinate inequalities. -/
theorem mem_ambientDilation_iff {S : Finset (ℤ × ℤ)} {r : ℕ} {x : ℤ × ℤ} :
    x ∈ ambientDilation S r ↔ ∃ p ∈ S,
      p.1 - r ≤ x.1 ∧ x.1 ≤ p.1 + r ∧ p.2 - r ≤ x.2 ∧ x.2 ≤ p.2 + r := by
  simp only [ambientDilation, Finset.mem_biUnion, Finset.product_eq_sprod,
    Finset.mem_product, Finset.mem_Icc]
  tauto

/-- Zero dilation changes no lattice points. -/
@[simp] theorem ambientDilation_zero (T : Finset (ℤ × ℤ)) : ambientDilation T 0 = T := by
  simp [ambientDilation]

/-- The sites of the supports of range `R` crossing `A`, that is, of the supports meeting both
`A` and its complement. At range one these are the endpoints of the edges crossing `A`.
Source: polynomial-PEPS `02-information.tex`, lines 416–424 and 513–524, at range `R`. -/
noncomputable def crossingSites (Λ : Finset (ℤ × ℤ)) (R : ℕ) (A : Finset ↥Λ) : Finset ↥Λ := by
  classical
  exact (crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).biUnion fun X ↦ X.1

/-- **Every site of a crossing support is near both sides of `A`.** It is joined by walks of
length at most `R` to a site of `A` and to a site outside `A`. -/
theorem exists_walks_of_mem_crossingSites {Λ : Finset (ℤ × ℤ)} {R : ℕ} {A : Finset ↥Λ}
    {z : ↥Λ} (hz : z ∈ crossingSites Λ R A) :
    ∃ x ∈ A, ∃ y ∉ A, (∃ p : (planeDomainGraph Λ).Walk z x, p.length ≤ R) ∧
      ∃ p : (planeDomainGraph Λ).Walk z y, p.length ≤ R := by
  classical
  simp only [crossingSites, crossingTerms, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and] at hz
  obtain ⟨X, ⟨⟨x, hxX, hxA⟩, y, hyX, hyA⟩, hzX⟩ := hz
  exact ⟨x, hxA, y, hyA, X.2.2 z hzX x hxX, X.2.2 z hzX y hyX⟩

end ManyBody
