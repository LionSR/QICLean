/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.SupportCounting
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import QICLean.ManyBody.Sites.Lattice.SupDistance

/-!
# Finite counts for ambient neighborhoods and cut endpoints

These are auxiliary cardinality bounds for the dyadic-layer construction in
OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, Section 11, source lines 143–210. They do not construct the dyadic layers
or establish their geometric separation. No connectedness of the domain or
its cut is required.

Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently proved from the manuscript; no upstream Lean proof text is reused.
-/

open scoped BigOperators
open ManyBody (ambientDilation edgeBoundary planeDomainGraph)

namespace ManyBody

/-- An ambient integer neighborhood has at most one square of side `2r+1`
per point of its defining set. Source: Section 11, lines 163–185, the count of
cells whose indices are within sup distance `C₀` of an occupied cell index. -/
theorem card_ambientDilation_le (T : Finset (ℤ × ℤ)) (r : ℕ) :
    (ambientDilation T r).card ≤ (2 * r + 1) ^ 2 * T.card := by
  unfold ambientDilation
  refine Finset.card_biUnion_le.trans ?_
  have h (a : ℤ) : (a + (r : ℤ) + 1 - (a - r)).toNat = 2 * r + 1 := by omega
  simp [Finset.product_eq_sprod, h, pow_two, Nat.mul_comm]

/-- The ambient integer endpoints of the unordered crossing edges.
Source: Section 11, Proposition `prop:two-families`, lines 103–109, and
lines 163–185. These are the source set `Z`, not an ambient boundary. -/
noncomputable def boundaryEndpoints (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ) :
    Finset (ℤ × ℤ) := by
  classical
  exact ((edgeBoundary (planeDomainGraph Λ) A).biUnion Sym2.toFinset).image Subtype.val

/-- A physical crossing edge contributes both endpoints to the source set `Z`.
Source: Lemma 9.4, final proof paragraph, and the definition of `Z`. -/
theorem mem_boundaryEndpoints_of_mem_edgeBoundary {Λ : Finset (ℤ × ℤ)}
    {A : Finset ↥Λ} {e : Sym2 ↥Λ} (he : e ∈ edgeBoundary (planeDomainGraph Λ) A)
    {x : ↥Λ} (hx : x ∈ e) : x.1 ∈ boundaryEndpoints Λ A := by
  classical
  exact Finset.mem_image.mpr
    ⟨x, Finset.mem_biUnion.mpr ⟨e, he, by simpa using hx⟩, rfl⟩

/-- There are at most two endpoints per crossing edge, even when the boundary
is empty. Source: Section 11, lines 179–185, `|Z| ≤ 2b`, absorbed into the
numerical constant there. This does not assert the layer-cell bound. -/
theorem card_boundaryEndpoints_le (Λ : Finset (ℤ × ℤ)) (A : Finset ↥Λ) :
    (boundaryEndpoints Λ A).card ≤ 2 * (edgeBoundary (planeDomainGraph Λ) A).card := by
  classical
  unfold boundaryEndpoints
  refine Finset.card_image_le.trans (Finset.card_biUnion_le.trans ?_)
  calc
    ∑ a ∈ edgeBoundary (planeDomainGraph Λ) A, a.toFinset.card ≤
        ∑ _ ∈ edgeBoundary (planeDomainGraph Λ) A, 2 := by
      refine Finset.sum_le_sum fun a _ ↦ ?_
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    _ = 2 * (edgeBoundary (planeDomainGraph Λ) A).card := by simp [Nat.mul_comm]

/-- Integer indices of the four dyadic children of a parent cell.
Source: area-law Section 11, dyadic cells, lines 157–181. -/
def dyadicChildren (P : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  (P ×ˢ (Finset.univ : Finset (Fin 2 × Fin 2))).image
    fun (z, a) ↦ (2 * z.1 + (a.1.val : ℤ), 2 * z.2 + (a.2.val : ℤ))

/-- Distinct dyadic parents have disjoint four-element child families.
Source: area-law Section 11, dyadic cells and layer counting, lines 157–181. -/
theorem card_dyadicChildren (P : Finset (ℤ × ℤ)) :
    (dyadicChildren P).card = 4 * P.card := by
  have hinj : Function.Injective
      (fun (za : (ℤ × ℤ) × (Fin 2 × Fin 2)) ↦
        (2 * za.1.1 + (za.2.1.val : ℤ), 2 * za.1.2 + (za.2.2.val : ℤ))) := by
    rintro ⟨z, a⟩ ⟨w, b⟩ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp at h₁ h₂
    have hz : z = w := Prod.ext (by omega) (by omega)
    have ha : a = b := Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
    exact Prod.ext hz ha
  rw [dyadicChildren, Finset.card_image_of_injective _ hinj, Finset.card_product]
  simp [Nat.mul_comm]

end ManyBody

section GraphNeighborhoodCutClearance

/-!
## Graph neighborhoods separated from physical cuts

A graph neighborhood of the part of an ambient target collar inside a cut
stays inside the cut and the enlarged collar whenever every cut endpoint is
farther from the target than the sum of the two radii. The estimate applies
to arbitrary finite induced domains, including holes and disconnected parts.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`10-geometry.tex`, lines 815–838, at immutable revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proof is independently written from the manuscript; no upstream Lean
proof text is reused. The ordered two-family construction and separation
from the earlier pieces are further geometric inputs.
-/

open ManyBody (planeDomainGraph graphNeighborhood ambientDilation mem_ambientDilation_iff
  exists_edgeBoundary_of_walk abs_ambientDepth_sub_le_walk_length ambientDepth
  ambientDepth_le_iff_mem_ambientDilation supDist supDist_le_one_of_planeDomainGraph_adj
  exists_mem_ambientDepth_eq supDist_comm natCast_supDist)

namespace ManyBody

/-- A graph neighborhood of the part of an ambient target collar inside a cut
remains inside that cut and inside the enlarged ambient collar, provided every
physical cut endpoint is farther from the target than the two radii together.
No connectedness, convexity or target-nonemptiness assumption is required.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`10-geometry.tex`, lines 815–838, immutable revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is the cut-exclusion and ambient-distance implication; the ordered
partition and the earlier-family clearance estimates are separate results. -/
theorem graphNeighborhood_subset_of_cut_clearance
    (Λ T : Finset (ℤ × ℤ)) (A : Finset ↥Λ) (L R : ℕ)
    (hclear : ∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ A,
      ((L + R : ℕ) : ℤ) < (supDist t z : ℤ)) :
    graphNeighborhood (planeDomainGraph Λ) (A.filter fun x ↦ x.val ∈ ambientDilation T L) R ⊆
      A.filter (fun x ↦ x.val ∈ ambientDilation T (L + R)) := by
  classical
  intro x hx
  obtain ⟨y, hy, p, hp⟩ := ManyBody.mem_graphNeighborhood_iff_exists_walk.mp hx
  rcases Finset.mem_filter.mp hy with ⟨hyA, hyDil⟩
  have hT : T.Nonempty :=
    let ⟨t, ht, _⟩ := Finset.mem_biUnion.mp hyDil
    ⟨t, ht⟩
  have hydepth := (ambientDepth_le_iff_mem_ambientDilation T hT y.val L).mpr hyDil
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · by_contra hxA
    obtain ⟨u, w, -, -, hcut, p', hp'⟩ := exists_edgeBoundary_of_walk p hyA hxA
    have hz : u.val ∈ ManyBody.boundaryEndpoints Λ A :=
      ManyBody.mem_boundaryEndpoints_of_mem_edgeBoundary hcut (by simp)
    have hvariation := (abs_ambientDepth_sub_le_walk_length T hT Subtype.val
      (fun _ _ ↦ supDist_le_one_of_planeDomainGraph_adj) p').trans
        (Int.ofNat_le.mpr (hp'.trans hp))
    obtain ⟨t, ht, hmin⟩ := exists_mem_ambientDepth_eq T hT u.val
    have hdeep : ((L + R : ℕ) : ℤ) < ambientDepth T hT u.val := by
      rw [hmin, supDist_comm]
      exact hclear t ht u.val hz
    rw [abs_le] at hvariation
    omega
  · apply (ambientDepth_le_iff_mem_ambientDilation T hT x.val (L + R)).mp
    have hvariation := (abs_ambientDepth_sub_le_walk_length T hT Subtype.val
      (fun _ _ ↦ supDist_le_one_of_planeDomainGraph_adj) p).trans
        (Int.ofNat_le.mpr hp)
    rw [abs_le] at hvariation
    omega

/-- Clearance from physical cut endpoints and from an entire remote set excludes
both the exterior and that remote set from the graph neighborhood of the target
collar inside the region. In the area-law application, the remote set is the
whole union of the earlier actual regions of the same geometric family.

Source: OpenAI, proof of Theorem 1.1, `10-geometry.tex`, lines 825–838,
immutable revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This auxiliary geometric implication assumes the two clearance estimates;
it does not construct the ordered partition or prove its clearance estimates.
The proof is independently written from the manuscript; no upstream Lean
proof text is reused. -/
theorem exterior_union_subset_graphNeighborhood_compl_of_clearance
    (Λ T : Finset (ℤ × ℤ)) (A J : Finset ↥Λ) (L R : ℕ)
    (hcut : ∀ t ∈ T, ∀ z ∈ ManyBody.boundaryEndpoints Λ A,
      ((L + R : ℕ) : ℤ) < (supDist t z : ℤ))
    (hremote : ∀ t ∈ T, ∀ x ∈ J,
      ((L + R : ℕ) : ℤ) < (supDist t x.val : ℤ)) :
    Aᶜ ∪ J ⊆
      (graphNeighborhood (planeDomainGraph Λ)
        (A.filter fun x ↦ x.val ∈ ambientDilation T L) R)ᶜ := by
  have hN := graphNeighborhood_subset_of_cut_clearance Λ T A L R hcut
  simp_all only [Finset.subset_iff, Finset.mem_compl, Finset.mem_union, Finset.mem_filter,
    mem_ambientDilation_iff, natCast_supDist, lt_max_iff, lt_abs]
  grind

end ManyBody

end GraphNeighborhoodCutClearance
