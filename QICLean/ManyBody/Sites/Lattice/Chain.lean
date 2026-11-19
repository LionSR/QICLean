/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OverlapGraph
import QICLean.Algebra.PathGraphConnected
import QICLean.ManyBody.Sites.Lattice.PathGraph
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat

/-!
# The chain of `L` sites: intervals and supports of range `R`

The chain of `L` sites is `Fin L`, with consecutive positions adjacent. An interval `[a, b)` is
the set of sites whose position lies in `[a, b)`. A support of range `R` is a nonempty set of
sites of diameter at most `R`; it lies in `R + 1` consecutive sites.

Moved from TNLean at commit `71c1185e9352a3b5237b37a6840640751da6ca2d`:
`TNLean/MPS/AreaLaw/Basic.lean` (the intervals) and `TNLean/MPS/AreaLaw/Hamiltonian.lean`
(`IsChainSupport`, `ChainSupport` and their lemmas). Changes: namespace `ManyBody` in place of
`TNLean.MPS.AreaLaw`; no other change.

Moved from TNLean on branch `refactor/chain-support-manybody` at commit
`83d33eaaede50fb5204da88a7c12b54261da53b6`, with names, statements and proofs unchanged:
`boundaryEdges`, `mem_boundaryEdges`, `boundaryEdges_empty` and `boundaryEdges_univ` from
`TNLean/MPS/AreaLaw/EntropyInequalities.lean`; `IsChainSupport.exists_boundary_window_of_split`
from `TNLean/MPS/AreaLaw/BoundaryCounting.lean`; `IsChainSupport.eq_interval_of_splits_of_range_one`
from `TNLean/MPS/AreaLaw/RangeOneCut.lean`; `ChainSupport.edist_le` from
`TNLean/MPS/AreaLaw/LiebRobinson.lean`. Changes: namespace `ManyBody` in place of
`TNLean.MPS.AreaLaw`.

Moved from TNLean (`e113e005`): the bonds, their overlap graph and the size of their union from
`TNLean/Lattice/ClusterExpansion/NearestNeighborPath.lean` and `NearestNeighborIntervalRank.lean`.
Changes: `nearestNeighbor` is `ManyBody.chainBond`, and the lemmas are renamed after it.

## Main definitions

* `ManyBody.interval` — the sites of position at least `a` and less than `b`.
* `ManyBody.IsChainSupport`, `ManyBody.ChainSupport` — the supports of range `R`.
* `ManyBody.boundaryEdges` — the edges of the chain leaving a region.
* `ManyBody.chainBond` — the nearest-neighbour bonds `{i, i + 1}`.

## Main results

* `ManyBody.IsChainSupport.exists_boundary_window_of_split` — a support split by a region lies
  in a window of `2R` sites about one of its boundary edges.
* `ManyBody.IsChainSupport.eq_interval_of_splits_of_range_one` — a range-one support split by
  a cut is the adjacent pair at that cut.
* `ManyBody.ChainSupport.edist_le` — a support of range `R` has path-graph diameter at most `R`.
* `ManyBody.overlapGraph_chainBond_eq_pathGraph` — the overlap graph of the bonds is the path.
* `ManyBody.card_biUnion_chainBond_le` — the bonds of `s` consecutive labels cover `s + 1` sites.

## References

* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, Section 1, `eq:ham`, and Section 2, the setting.
-/

namespace ManyBody

variable {L R : ℕ}

/-- The interval `[a, b)` of the chain of `L` sites: the sites of position at least `a`
and less than `b`. -/
def interval (L a b : ℕ) : Finset (Fin L) := Finset.univ.filter fun i ↦ a ≤ i.val ∧ i.val < b

/-- Membership in an interval. -/
@[simp]
theorem mem_interval {a b : ℕ} {i : Fin L} : i ∈ interval L a b ↔ a ≤ i.val ∧ i.val < b := by
  simp [interval]

/-- Two adjacent intervals `[a, b)` and `[b, c)` are disjoint. -/
theorem disjoint_interval_interval (a b c : ℕ) :
    Disjoint (interval L a b) (interval L b c) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.disjoint_left.mp (Finset.Ico_disjoint_Ico_consecutive a b c))
    (Finset.mem_Ico.mpr (mem_interval.mp hx))
    (Finset.mem_Ico.mpr (mem_interval.mp hy))

/-- Intervals are monotone in their ends. -/
theorem interval_mono {a a' b b' : ℕ} (ha : a' ≤ a) (hb : b ≤ b') :
    interval L a b ⊆ interval L a' b' := by
  intro i hi
  rw [mem_interval] at hi ⊢
  omega

/-- An interval with `b ≤ a` has no sites. -/
theorem interval_eq_empty {a b : ℕ} (h : b ≤ a) : interval L a b = ∅ := by
  ext i
  simp only [mem_interval, Finset.notMem_empty, iff_false]
  omega

/-- The interval `[0, b)` with `b ≥ L` is the whole chain. -/
theorem interval_zero_eq_univ {b : ℕ} (hb : L ≤ b) : interval L 0 b = Finset.univ := by
  ext i
  simp only [mem_interval, Finset.mem_univ, iff_true]
  exact ⟨Nat.zero_le _, lt_of_lt_of_le i.2 hb⟩

/-- An interval `[a, b)` has at most `b - a` sites. -/
theorem card_interval_le (a b : ℕ) : (interval L a b).card ≤ b - a := by
  have h := Finset.card_le_card_of_injOn (fun i : Fin L ↦ i.val)
    (s := interval L a b) (t := Finset.Ico a b)
    (fun i hi ↦ Finset.mem_Ico.mpr (mem_interval.mp hi)) Fin.val_injective.injOn
  rwa [Nat.card_Ico] at h


/-- A support of range `R`: a nonempty set of sites of diameter at most `R`. -/
def IsChainSupport (L R : ℕ) (X : Finset (Fin L)) : Prop :=
  X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X, y.val ≤ x.val + R

instance (L R : ℕ) : DecidablePred (IsChainSupport L R) := fun X ↦
  inferInstanceAs (Decidable (X.Nonempty ∧ ∀ x ∈ X, ∀ y ∈ X, y.val ≤ x.val + R))

/-- The supports of range `R` of the chain of `L` sites. -/
abbrev ChainSupport (L R : ℕ) := {X : Finset (Fin L) // IsChainSupport L R X}

/-- A support of range `R` has at most `R + 1` sites. -/
theorem IsChainSupport.card_le {X : Finset (Fin L)} (hX : IsChainSupport L R X) :
    X.card ≤ R + 1 := by
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image X (fun x ↦ x.val) hX.1
  have hsub : X.image (fun x : Fin L ↦ x.val) ⊆ Finset.Icc x₀.val (x₀.val + R) := by
    intro p hp
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_Icc.mpr ⟨hmin y hy, hX.2 x₀ hx₀ y hy⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Icc] at this
  omega

/-- A chain support of maximal cardinality is a full contained window.
Source: the one-dimensional note, part1_arealaw.tex, rem:sharper, lines 706–748. -/
theorem IsChainSupport.exists_eq_interval_of_card_eq
    {L R : ℕ} {X : Finset (Fin L)} (hX : IsChainSupport L R X)
    (hcard : X.card = R + 1) :
    ∃ a : ℕ, a + R + 1 ≤ L ∧ X = interval L a (a + R + 1) := by
  obtain ⟨x₀, hx₀, hmin⟩ := Finset.exists_min_image X (fun x ↦ x.val) hX.1
  have hsub : X.image (fun x : Fin L ↦ x.val) ⊆ Finset.Icc x₀.val (x₀.val + R) :=
    fun p hp ↦ let ⟨y, hy, hyp⟩ := Finset.mem_image.mp hp
      hyp ▸ Finset.mem_Icc.mpr ⟨hmin y hy, hX.2 x₀ hx₀ y hy⟩
  have himage : X.image (fun x : Fin L ↦ x.val) = Finset.Icc x₀.val (x₀.val + R) :=
    Finset.eq_of_subset_of_card_le hsub (by
      simp [Finset.card_image_of_injective _ Fin.val_injective, hcard, Nat.card_Icc,
        Nat.add_assoc])
  obtain ⟨y, hy, hyval⟩ := Finset.mem_image.mp
    (show x₀.val + R ∈ X.image (fun x : Fin L ↦ x.val) from
      himage.symm ▸ Finset.mem_Icc.mpr ⟨Nat.le_add_right _ _, le_rfl⟩)
  refine ⟨x₀.val, Nat.succ_le_of_lt (hyval ▸ y.isLt), ?_⟩
  ext i
  simpa [interval, Finset.mem_image, Fin.val_inj, Nat.lt_succ_iff] using
    (Iff.of_eq (congrArg (fun T : Finset ℕ ↦ i.val ∈ T) himage))

/-- A support of range `R` split by the interval `[a, b)`, meeting both it and its
complement, lies in the window `[a - R, a + R)` or in the window `[b - R, b + R)`. -/
theorem IsChainSupport.subset_window_of_splits {X : Finset (Fin L)}
    (hX : IsChainSupport L R X) {a b : ℕ}
    (hsplit : (∃ v ∈ X, v ∈ interval L a b) ∧ ∃ v ∈ X, v ∉ interval L a b) :
    X ⊆ interval L (a - R) (a + R) ∨ X ⊆ interval L (b - R) (b + R) := by
  obtain ⟨⟨v, hvX, hv⟩, ⟨w, hwX, hw⟩⟩ := hsplit
  rw [mem_interval] at hv hw
  have hvw := hX.2 v hvX w hwX
  have hwv := hX.2 w hwX v hvX
  by_cases hwa : w.val < a
  · left
    intro x hx
    have h1 := hX.2 x hx v hvX
    have h2 := hX.2 w hwX x hx
    rw [mem_interval]
    omega
  · right
    intro x hx
    have h1 := hX.2 v hvX x hx
    have h2 := hX.2 x hx w hwX
    rw [mem_interval]
    omega

/-- A support of range one split by the cut after the first `k` sites is the adjacent pair at
that cut. Source: Landau, Vazirani and Vidick, arXiv:1307.5143v1, `algo53.tex`, the
nearest-neighbour assumption at line 283 and the cut decomposition at lines 409–410. -/
theorem IsChainSupport.eq_interval_of_splits_of_range_one {L k : ℕ} {X : Finset (Fin L)}
    (hX : IsChainSupport L 1 X)
    (hsplit : (∃ x ∈ X, x.val < k) ∧ ∃ y ∈ X, k ≤ y.val) :
    X = interval L (k - 1) (k + 1) := by
  obtain ⟨⟨x, hx, hxk⟩, y, hy, hky⟩ := hsplit
  have htwo : X.card = 2 := by
    have hcard := hX.card_le
    have hlt : 1 < X.card := Finset.one_lt_card.mpr
      ⟨x, hx, y, hy, by rintro rfl; omega⟩
    omega
  obtain ⟨a, -, hXa⟩ := hX.exists_eq_interval_of_card_eq htwo
  have hak : k = a + 1 := by
    have hax := mem_interval.mp ((Finset.ext_iff.mp hXa x).mp hx)
    have hay := mem_interval.mp ((Finset.ext_iff.mp hXa y).mp hy)
    omega
  rw [hXa]
  congr 1 <;> omega

/-- The path distance between two sites of a range-`R` support is at most `R`.
Hastings, arXiv:0705.2024v4, finite-range condition, lines 90–94. -/
theorem ChainSupport.edist_le {L R : ℕ} (X : ChainSupport L R)
    (x : Fin L) (hx : x ∈ X.1) (z : Fin L) (hz : z ∈ X.1) :
    (SimpleGraph.pathGraph L).edist x z ≤ (R : ℕ∞) := by
  rw [SimpleGraph.pathGraph_edist]
  have hxz := X.2.2 x hx z hz
  have hzx := X.2.2 z hz x hx
  exact_mod_cast (show Nat.dist x.val z.val ≤ R by
    simp only [Nat.dist]
    omega)

/-! ### Boundary edges of a region -/

/-- The boundary edges of a region `A` of the chain of `L` sites: the positions `p` with
`p + 1 < L` such that exactly one of the sites at positions `p` and `p + 1` lies in `A`, that
is, the edges `{p, p + 1}` of the chain leaving `A`. -/
def boundaryEdges (L : ℕ) (A : Finset (Fin L)) : Finset ℕ :=
  (Finset.range (L - 1)).filter fun p ↦ ¬ ((∃ i ∈ A, i.val = p) ↔ ∃ i ∈ A, i.val = p + 1)

/-- Membership in the boundary edges of a region, in terms of positions. -/
theorem mem_boundaryEdges {A : Finset (Fin L)} {p : ℕ} :
    p ∈ boundaryEdges L A ↔
      p + 1 < L ∧ ¬ ((∃ i ∈ A, i.val = p) ↔ ∃ i ∈ A, i.val = p + 1) := by
  rw [boundaryEdges, Finset.mem_filter, Finset.mem_range, Nat.lt_sub_iff_add_lt]

/-- The empty region has no boundary edges. -/
theorem boundaryEdges_empty : boundaryEdges L ∅ = ∅ := by
  ext p
  simp [mem_boundaryEdges]

/-- The whole chain has no boundary edges. -/
theorem boundaryEdges_univ : boundaryEdges L Finset.univ = ∅ := by
  ext p
  simp only [mem_boundaryEdges, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_and, not_not]
  intro hp
  exact ⟨fun _ ↦ ⟨⟨p + 1, hp⟩, rfl⟩, fun _ ↦ ⟨⟨p, by omega⟩, rfl⟩⟩

/-- A support split by a region lies in a window about one of its
boundary edges. Source: TNLean note, `eq:count`, and
`part2a_mps_information.tex`, lines 359–363. -/
lemma IsChainSupport.exists_boundary_window_of_split
    {L R : ℕ} {X D : Finset (Fin L)} (hX : IsChainSupport L R X)
    (hsplit : (∃ u ∈ X, u ∈ D) ∧ ∃ v ∈ X, v ∉ D) :
    ∃ p ∈ boundaryEdges L D,
      X ⊆ interval L (p + 1 - R) (p + 1 + R) := by
  classical
  let P (m : ℕ) := ∃ i ∈ D, i.val = m
  have hordered (u v : Fin L) (hu : u ∈ X) (hv : v ∈ X) (huv : u.val < v.val)
      (hmem : ¬ (P u.val ↔ P v.val)) :
      ∃ p ∈ boundaryEdges L D, X ⊆ interval L (p + 1 - R) (p + 1 + R) := by
    let Q (n : ℕ) := u.val + n ≤ v.val ∧ (P (u.val + n) ↔ P v.val)
    have hQ0 : ¬ Q 0 := by simpa only [Q, Nat.add_zero, huv.le, true_and] using hmem
    have hQex : ∃ n, Q n := ⟨v.val - u.val, by
      simp only [Q, Nat.add_sub_of_le huv.le, le_refl, iff_self, and_self]⟩
    obtain ⟨n, hn, hn1⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists hQ0 hQex
    simp only [Q] at hn hn1
    refine ⟨u.val + n, mem_boundaryEdges.mpr ⟨by have := v.isLt; omega, ?_⟩, ?_⟩
    · change ¬ (P (u.val + n) ↔ P (u.val + n + 1))
      intro he
      exact hn ⟨by omega, he.trans (by simpa only [Nat.add_assoc] using hn1.2)⟩
    · intro z hz
      rw [mem_interval]
      have huz := hX.2 u hu z hz
      have hzv := hX.2 z hz v hv
      omega
  obtain ⟨⟨u, hu, huD⟩, v, hv, hvD⟩ := hsplit
  have hPu : P u.val := ⟨u, huD, rfl⟩
  have hPv : ¬ P v.val := by
    rintro ⟨i, hi, hiv⟩
    exact hvD (Fin.ext hiv ▸ hi)
  rcases lt_trichotomy u.val v.val with huv | huv | hvu
  · exact hordered u v hu hv huv (fun he ↦ hPv (he.mp hPu))
  · exact (hPv (huv ▸ hPu)).elim
  · exact hordered v u hv hu hvu (fun he ↦ hPv (he.mpr hPu))

/-! ### The nearest-neighbour bonds -/

section ChainBond

open Finset SimpleGraph

variable {N : ℕ}

/-- The bond `{i, i + 1}` of the chain of `N + 1` sites, for a label `i : Fin N`: the support
of a nearest-neighbour term. ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
def chainBond (N : ℕ) (i : Fin N) : Finset (Fin (N + 1)) := {i.castSucc, i.succ}

/-- The overlap graph of the bonds is the label path. Supporting ALVV, arXiv:1602.08828v2,
`eq:rho-expansion`, lines 1971–2013. -/
theorem overlapGraph_chainBond_eq_pathGraph (N : ℕ) :
    overlapGraph (chainBond N) = pathGraph N := by
  ext i j
  change (i ≠ j ∧ (({i.castSucc, i.succ} : Finset (Fin (N + 1))) ∩
    {j.castSucc, j.succ}).Nonempty) ↔ _
  rw [pathGraph_adj]
  simp only [Finset.Nonempty, mem_inter, mem_insert, mem_singleton]
  simp only [or_and_right, exists_or, exists_eq_left]
  simp only [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  omega

/-- The bonds of a connected label interval cover at most one more site than labels. Supporting
ALVV, arXiv:1602.08828v2, `eq:rho-expansion`, lines 1971–2013. -/
theorem card_biUnion_chainBond_le {C : Finset (Fin N)}
    (hC : ((pathGraph N).induce (C : Set (Fin N))).Connected) :
    (C.biUnion (chainBond N)).card ≤ C.card + 1 := by
  have hord := ordConnected_of_pathGraph_connected hC
  have hne : C.Nonempty := by
    obtain ⟨p⟩ := hC.nonempty
    exact ⟨p, p.property⟩
  have hsub : C.biUnion (chainBond N) ⊆ Icc (C.min' hne).castSucc (C.max' hne).succ := by
    intro v hv
    obtain ⟨i, hi, hvi⟩ := mem_biUnion.mp hv
    have hmin : (C.min' hne).val ≤ i.val := C.min'_le i hi
    have hmax : i.val ≤ (C.max' hne).val := C.le_max' i hi
    rw [mem_Icc]
    simp only [chainBond, mem_insert, mem_singleton] at hvi
    rcases hvi with rfl | rfl <;> simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ] <;> omega
  have hlen : C.card = (C.max' hne).val + 1 - (C.min' hne).val :=
    (congrArg Finset.card (eq_Icc_of_ordConnected hord hne)).trans (Fin.card_Icc _ _)
  have hle : (C.min' hne).val ≤ (C.max' hne).val := C.min'_le _ (C.max'_mem hne)
  have hcard : (Icc (C.min' hne).castSucc (C.max' hne).succ).card = C.card + 1 := by
    rw [Fin.card_Icc]
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  exact (Finset.card_le_card hsub).trans_eq hcard

end ChainBond

end ManyBody
