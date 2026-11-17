/-
Copyright (c) 2026 TNLean and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors, QICLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Lattice distance and the diamond count

The lattice distance on `ℤ × ℤ` is the sum of the coordinate displacements. Along a walk in a
graph whose edges have displacement at most one, the displacement is at most the length of the
walk. The closed ball of radius `R` for the lattice distance has exactly `1 + 2R(R + 1)` points,
so a finite set of vertices joined to one vertex by walks of length at most `R` has at most that
many elements, when the vertices embed injectively in `ℤ × ℤ`. Holes and disconnected components
are allowed.

Moved from TNLean, `TNLean/PEPS/AreaLaw/GraphLatticeDistance.lean` and
`TNLean/PEPS/AreaLaw/GraphLatticeDiamond.lean` at commit
`868d2c957aebacdf8807b2fbe78abdc01edb0a85`. Changes: one module, in namespace `ManyBody` in
place of `TNLean.PEPS.AreaLaw`; the statements and proofs are unchanged.

## Main definitions

* `ManyBody.latticeL1Distance` — the lattice distance on `ℤ × ℤ`.
* `ManyBody.latticeDiamond` — the closed ball of radius `R` for the lattice distance.

## Main results

* `ManyBody.latticeL1Distance_le_walk_length` — displacement is at most walk length.
* `ManyBody.card_latticeDiamond` — the ball of radius `R` has `1 + 2R(R + 1)` points.
* `ManyBody.card_le_diamond_of_walks`, `ManyBody.card_le_diamond_of_edist_le` — the count for
  vertices within graph distance `R` of one vertex.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  `01-preliminaries.tex`, lines 81–87 (`eq:ball-count`).
-/

open scoped BigOperators

namespace ManyBody

section Distance

/-- The ambient integer lattice distance, measured by the sum of coordinate displacements.
Source: the ambient displacement comparison preceding `eq:ball-count`. -/
def latticeL1Distance (a b : ℤ × ℤ) : ℕ :=
  (a.1 - b.1).natAbs + (a.2 - b.2).natAbs

/-- Ambient lattice distance vanishes at a site. -/
@[simp]
theorem latticeL1Distance_self (a : ℤ × ℤ) : latticeL1Distance a a = 0 := by
  simp [latticeL1Distance]

/-- Ambient lattice distance satisfies the triangle inequality. -/
theorem latticeL1Distance_triangle (a b c : ℤ × ℤ) :
    latticeL1Distance a c ≤ latticeL1Distance a b + latticeL1Distance b c := by
  have hx : (a.1 - c.1).natAbs ≤ (a.1 - b.1).natAbs + (b.1 - c.1).natAbs := by
    have he : a.1 - c.1 = (a.1 - b.1) + (b.1 - c.1) := by omega
    rw [he]
    exact Int.natAbs_add_le _ _
  have hy : (a.2 - c.2).natAbs ≤ (a.2 - b.2).natAbs + (b.2 - c.2).natAbs := by
    have he : a.2 - c.2 = (a.2 - b.2) + (b.2 - c.2) := by omega
    rw [he]
    exact Int.natAbs_add_le _ _
  dsimp only [latticeL1Distance]
  omega

variable {V : Type*} {G : SimpleGraph V} (coord : V → ℤ × ℤ)

/-- A walk has ambient displacement at most its length when each edge has displacement at most
one. Walks are in the full given graph, without any restriction to an interaction support.
Source: `01-preliminaries.tex`, lines 81–84, preceding `eq:ball-count`. -/
theorem latticeL1Distance_le_walk_length
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    {a b : V} (p : G.Walk a b) : latticeL1Distance (coord a) (coord b) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
      calc
        latticeL1Distance (coord a) (coord c) ≤
            latticeL1Distance (coord a) (coord b) +
              latticeL1Distance (coord b) (coord c) :=
          latticeL1Distance_triangle _ _ _
        _ ≤ 1 + p.length := Nat.add_le_add (hstep hab) ih
        _ = (SimpleGraph.Walk.cons hab p).length := by simp [Nat.add_comm]

/-- A finite upper bound on extended graph distance also bounds ambient displacement.
The extended distance retains the value `⊤` between different graph components.
Source: the displacement comparison preceding `eq:ball-count`. -/
theorem latticeL1Distance_le_of_edist_le
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    {a b : V} {R : ℕ} (hdist : G.edist a b ≤ (R : ℕ∞)) :
    latticeL1Distance (coord a) (coord b) ≤ R := by
  have hfinite : G.edist a b < ⊤ := lt_of_le_of_lt hdist (by simp)
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top (ne_of_lt hfinite)
  have hlength : p.length ≤ R :=
    ENat.natCast_le_natCast.mp (hp.le.trans hdist)
  exact (latticeL1Distance_le_walk_length coord hstep p).trans hlength

end Distance

section Diamond

private def latticeDiamondRows (R : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(R : ℤ)) (R : ℤ)).biUnion fun x ↦
    ({x} : Finset ℤ) ×ˢ Finset.Icc (|x| - (R : ℤ)) ((R : ℤ) - |x|)

private theorem mem_latticeDiamondRows {R : ℕ} {p : ℤ × ℤ} :
    p ∈ latticeDiamondRows R ↔ p.1.natAbs + p.2.natAbs ≤ R := by
  constructor
  · intro hp
    obtain ⟨x, _, hp⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hpx, hpy⟩ := Finset.mem_product.mp hp
    have hpx' : p.1 = x := Finset.mem_singleton.mp hpx
    have hpy' := Finset.mem_Icc.mp hpy
    have habs : |p.2| ≤ (R : ℤ) - |p.1| := by
      rw [abs_le, hpx']
      constructor <;> omega
    have hcast : ((p.1.natAbs + p.2.natAbs : ℕ) : ℤ) ≤ (R : ℤ) := by
      rw [Nat.cast_add, Int.natCast_natAbs, Int.natCast_natAbs]
      omega
    exact Int.ofNat_le.mp hcast
  · intro hp
    have hcast := Int.ofNat_le.mpr hp
    simp only [Nat.cast_add, Int.natCast_natAbs] at hcast
    have hxabs : |p.1| ≤ (R : ℤ) := by
      have := abs_nonneg p.2
      omega
    have hyabs : |p.2| ≤ (R : ℤ) - |p.1| := by omega
    have hx := abs_le.mp hxabs
    have hy := abs_le.mp hyabs
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1, Finset.mem_Icc.mpr hx, Finset.mem_product.mpr ⟨by simp, ?_⟩⟩
    apply Finset.mem_Icc.mpr
    constructor <;> omega

private theorem sum_latticeDiamond_rows (R : ℕ) :
    (∑ x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (2 * ((R : ℤ) - |x|) + 1)) =
      1 + 2 * (R : ℤ) * ((R : ℤ) + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
      have hdisj : Disjoint (Finset.Icc (-(R : ℤ)) (R : ℤ))
          {(-((R : ℤ) + 1)), ((R : ℤ) + 1)} := by
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        have hbounds := Finset.mem_Icc.mp hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
        rcases hx' with hx' | hx' <;> omega
      have hpair : -((R : ℤ) + 1) ≠ (R : ℤ) + 1 := by omega
      have hcard : ((Finset.Icc (-(R : ℤ)) (R : ℤ)).card : ℤ) = 2 * (R : ℤ) + 1 := by
        rw [Int.card_Icc]
        omega
      have hshift :
          (∑ x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (2 * ((R : ℤ) + 1 - |x|) + 1)) =
            (∑ x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (2 * ((R : ℤ) - |x|) + 1)) +
              ((Finset.Icc (-(R : ℤ)) (R : ℤ)).card : ℤ) * 2 := by
        calc
          _ = ∑ x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ),
              ((2 * ((R : ℤ) - |x|) + 1) + 2) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
          _ = _ := by rw [Finset.sum_add_distrib]; simp
      simp only [Nat.cast_succ]
      rw [Finset.Icc_succ_succ, Finset.sum_union hdisj, Finset.sum_pair hpair,
        hshift, ih, hcard]
      simp only [abs_neg, abs_of_nonneg (by omega : 0 ≤ (R : ℤ) + 1)]
      ring

private theorem card_latticeDiamondRows (R : ℕ) :
    (latticeDiamondRows R).card = 1 + 2 * R * (R + 1) := by
  have hdisj : (↑(Finset.Icc (-(R : ℤ)) (R : ℤ)) : Set ℤ).PairwiseDisjoint
      (fun x ↦ ({x} : Finset ℤ) ×ˢ
        Finset.Icc (|x| - (R : ℤ)) ((R : ℤ) - |x|)) := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hx : p.1 = x := Finset.mem_singleton.mp (Finset.mem_product.mp hp).1
    have hy : p.1 = y := Finset.mem_singleton.mp (Finset.mem_product.mp hq).1
    exact hxy (hx.symm.trans hy)
  have hcard : ((latticeDiamondRows R).card : ℤ) =
      ∑ x ∈ Finset.Icc (-(R : ℤ)) (R : ℤ), (2 * ((R : ℤ) - |x|) + 1) := by
    rw [latticeDiamondRows, Finset.card_biUnion hdisj, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hbounds := Finset.mem_Icc.mp hx
    have habs : |x| ≤ (R : ℤ) := abs_le.mpr hbounds
    rw [Finset.card_product, Finset.card_singleton, one_mul, Int.card_Icc]
    omega
  have h := hcard.trans (sum_latticeDiamond_rows R)
  apply Int.ofNat_injective
  change ((latticeDiamondRows R).card : ℤ) = ((1 + 2 * R * (R + 1) : ℕ) : ℤ)
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] using h

/-- The closed ambient integer lattice ball, represented as a native finite set.
Source: `eq:ball-count`. -/
def latticeDiamond (a : ℤ × ℤ) (R : ℕ) : Finset (ℤ × ℤ) :=
  (latticeDiamondRows R).image fun p ↦ (a.1 - p.1, a.2 - p.2)

/-- Membership in the finite lattice diamond is exactly the ambient distance condition.
Source: the ambient lattice ball in `eq:ball-count`. -/
@[simp]
theorem mem_latticeDiamond {a p : ℤ × ℤ} {R : ℕ} :
    p ∈ latticeDiamond a R ↔ latticeL1Distance a p ≤ R := by
  rw [latticeDiamond, Finset.mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa [latticeL1Distance] using mem_latticeDiamondRows.mp hq
  · intro hp
    refine ⟨(a.1 - p.1, a.2 - p.2), ?_, ?_⟩
    · apply mem_latticeDiamondRows.mpr
      exact hp
    · apply Prod.ext <;> dsimp <;> omega

/-- The paper's exact ambient diamond count, including the radius-zero case.
Source: `eq:ball-count`, `v_R = 1 + 2 R (R + 1)`. -/
@[simp]
theorem card_latticeDiamond (a : ℤ × ℤ) (R : ℕ) :
    (latticeDiamond a R).card = 1 + 2 * R * (R + 1) := by
  have hinj : Function.Injective (fun p : ℤ × ℤ ↦ (a.1 - p.1, a.2 - p.2)) := by
    intro p q hpq
    have hx := congrArg Prod.fst hpq
    have hy := congrArg Prod.snd hpq
    apply Prod.ext <;> dsimp at hx hy ⊢ <;> omega
  rw [latticeDiamond, Finset.card_image_of_injective _ hinj, card_latticeDiamondRows]

variable {V : Type*} {G : SimpleGraph V} (coord : V → ℤ × ℤ)

/-- An injectively embedded finite set in an ambient radius-`R` ball obeys the exact diamond
count. Source: `eq:ball-count`. -/
theorem card_le_diamond_of_latticeL1Distance_le (s : Finset V)
    (hcoord : Function.Injective coord) (a : V) (R : ℕ)
    (hs : ∀ x ∈ s, latticeL1Distance (coord a) (coord x) ≤ R) :
    s.card ≤ 1 + 2 * R * (R + 1) := by
  classical
  calc
    s.card ≤ (latticeDiamond (coord a) R).card :=
      Finset.card_le_card_of_injOn coord
        (fun x hx ↦ mem_latticeDiamond.mpr (hs x hx))
        (fun _ _ _ _ h ↦ hcoord h)
    _ = 1 + 2 * R * (R + 1) := card_latticeDiamond _ _

/-- Vertices reached by walks of length at most `R` obey the paper's exact ambient count.
Source: the walk displacement argument for `eq:ball-count`. -/
theorem card_le_diamond_of_walks (s : Finset V) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (a : V) (R : ℕ) (hs : ∀ x ∈ s, ∃ p : G.Walk a x, p.length ≤ R) :
    s.card ≤ 1 + 2 * R * (R + 1) := by
  apply card_le_diamond_of_latticeL1Distance_le coord s hcoord a R
  intro x hx
  obtain ⟨p, hp⟩ := hs x hx
  exact (latticeL1Distance_le_walk_length coord hstep p).trans hp

/-- Every finite set in a closed graph ball obeys the exact ambient diamond count.
A finite extended-distance bound excludes disconnected sites without a global connectivity
hypothesis. Source: `eq:ball-count`. -/
theorem card_le_diamond_of_edist_le (s : Finset V) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (a : V) (R : ℕ) (hs : ∀ x ∈ s, G.edist a x ≤ (R : ℕ∞)) :
    s.card ≤ 1 + 2 * R * (R + 1) := by
  apply card_le_diamond_of_latticeL1Distance_le coord s hcoord a R
  intro x hx
  exact latticeL1Distance_le_of_edist_le coord hstep (hs x hx)

end Diamond

end ManyBody
