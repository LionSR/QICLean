/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.RectangleColumns
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Rev

/-!
# The snake order of a rectangle

The sites of the rectangle `[0, L) × [0, w)` are listed column by column: the columns
`{c} × [0, w)` follow each other for `c = 0, …, L - 1`, the columns with even `c` are run through
with the second coordinate increasing, and those with odd `c` with it decreasing. The site
`(c, r)` therefore has position `w c + r` when `c` is even and `w c + (w - 1 - r)` when `c` is
odd. Consecutive sites of this order are nearest neighbours.

The prefix of the first `k` sites contains the columns `0, …, k / w - 1`, lies in the columns
`0, …, k / w`, and differs from the former by at most `w` sites. Its edge boundary in the
nearest-neighbour graph of the rectangle has at most `w + 1` edges: an edge between two columns
is determined by its second coordinate, and at most one edge inside a column joins the prefix to
its complement, since the two ends of such an edge are consecutive in the order.

All statements hold for empty rectangles, for one site, and for `k` beyond the number of sites.

## Main definitions

* `ManyBody.snakeFlip` — the permutation of `Fin L × Fin w` reversing the odd columns.
* `ManyBody.snakeEquiv` — the snake order `Fin (L * w) ≃ ↥(rectangularDomain L w)`.
* `ManyBody.snakeIndex` — the position of a vertex of the rectangle in the snake order.
* `ManyBody.snakePrefix` — the first `k` sites of the snake order.

## Main results

* `ManyBody.snakeIndex_val` — the position in coordinates.
* `ManyBody.stripColumn_snakeEquiv` — the site of position `i` lies in the column `i / w`.
* `ManyBody.stripInterval_subset_snakePrefix`, `ManyBody.snakePrefix_subset_stripInterval`,
  `ManyBody.card_snakePrefix_sdiff_le` — comparison of a prefix with whole columns.
* `ManyBody.card_edgeBoundary_snakePrefix_le` — the edge boundary of a prefix has at most `w + 1`
  edges.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Section 1, the comparison of the square grid with a chain.
-/

namespace ManyBody

/-! ### The order -/

/-- The permutation of the vertices of the rectangle that reverses the second coordinate in the
columns of odd first coordinate. It is an involution. -/
def snakeFlip (L w : ℕ) : Equiv.Perm (Fin L × Fin w) where
  toFun x := (x.1, if x.1.val % 2 = 0 then x.2 else x.2.rev)
  invFun x := (x.1, if x.1.val % 2 = 0 then x.2 else x.2.rev)
  left_inv x := by by_cases hx : x.1.val % 2 = 0 <;> simp [hx]
  right_inv x := by by_cases hx : x.1.val % 2 = 0 <;> simp [hx]

/-- The value of the column-reversing permutation. -/
theorem snakeFlip_apply (L w : ℕ) (x : Fin L × Fin w) :
    snakeFlip L w x = (x.1, if x.1.val % 2 = 0 then x.2 else x.2.rev) :=
  rfl

/-- The column-reversing permutation is its own inverse. -/
theorem snakeFlip_symm (L w : ℕ) : (snakeFlip L w).symm = snakeFlip L w :=
  rfl

/-- The snake order of the sites of the rectangle `[0, L) × [0, w)`: the position `i` is the
site of first coordinate `i / w` and second coordinate `i % w`, reversed to `w - 1 - i % w` when
`i / w` is odd. Source: the square-grid comparison, Section 1. -/
noncomputable def snakeEquiv (L w : ℕ) : Fin (L * w) ≃ ↥(rectangularDomain L w) :=
  finProdFinEquiv.symm.trans ((snakeFlip L w).trans (rectangleSiteEquiv L w))

/-- The position of a vertex of the rectangle in the snake order. -/
def snakeIndex (L w : ℕ) (p : Fin L × Fin w) : Fin (L * w) :=
  finProdFinEquiv ((snakeFlip L w).symm p)

/-- The snake order sends the position of a vertex to the site of that vertex. -/
@[simp] theorem snakeEquiv_snakeIndex (L w : ℕ) (p : Fin L × Fin w) :
    snakeEquiv L w (snakeIndex L w p) = rectangleSiteEquiv L w p := by
  simp only [snakeEquiv, snakeIndex, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.apply_symm_apply]

/-- The position of the site of a vertex in the snake order. -/
@[simp] theorem snakeEquiv_symm_rectangleSiteEquiv (L w : ℕ) (p : Fin L × Fin w) :
    (snakeEquiv L w).symm (rectangleSiteEquiv L w p) = snakeIndex L w p := by
  rw [Equiv.symm_apply_eq, snakeEquiv_snakeIndex]

/-- The position of the vertex `(c, r)` is `w c + r` for even `c` and `w c + (w - 1 - r)` for
odd `c`. -/
theorem snakeIndex_val (L w : ℕ) (p : Fin L × Fin w) :
    (snakeIndex L w p).val = (if p.1.val % 2 = 0 then p.2.val else w - 1 - p.2.val) +
      w * p.1.val := by
  simp only [snakeIndex, snakeFlip_symm, snakeFlip_apply, finProdFinEquiv_apply_val]
  split_ifs <;> simp [Fin.rev, Nat.sub_sub, Nat.add_comm]

/-- The site of position `i` lies in the column `i / w`, also in the reversed columns. -/
theorem stripColumn_snakeEquiv {L w : ℕ} (i : Fin (L * w)) :
    stripColumn (snakeEquiv L w i) = i.val / w := by
  change ((i.val / w : ℕ) : ℤ).toNat = i.val / w
  simp only [Int.toNat_natCast]

/-! ### Prefixes -/

/-- The first `k` sites of the snake order of the rectangle. -/
noncomputable def snakePrefix (L w k : ℕ) : Finset ↥(rectangularDomain L w) :=
  (Finset.univ.filter fun i : Fin (L * w) ↦ i.val < k).map (snakeEquiv L w).toEmbedding

/-- A site lies in the prefix of length `k` exactly when its position is less than `k`. -/
@[simp] theorem mem_snakePrefix {L w k : ℕ} {v : ↥(rectangularDomain L w)} :
    v ∈ snakePrefix L w k ↔ ((snakeEquiv L w).symm v).val < k := by
  simp only [snakePrefix, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The site of position `i` lies in the prefix of length `k` exactly when `i < k`. -/
theorem snakeEquiv_mem_snakePrefix {L w k : ℕ} {i : Fin (L * w)} :
    snakeEquiv L w i ∈ snakePrefix L w k ↔ i.val < k := by
  simp

/-- A prefix of the snake order contains every column before the one it ends in. -/
theorem stripInterval_subset_snakePrefix {L w k : ℕ} (_hw : 1 ≤ w) :
    stripInterval L w 0 (k / w) ⊆ snakePrefix L w k := by
  intro x hx
  let i := (snakeEquiv L w).symm x
  have hi : stripColumn x = i.val / w := by
    simpa only [i, Equiv.apply_symm_apply] using stripColumn_snakeEquiv i
  have hx' := (mem_stripInterval.mp hx).2
  rw [hi] at hx'
  rw [mem_snakePrefix]
  change i.val < k
  by_contra hik
  exact absurd (Nat.div_le_div_right (c := w) (not_lt.mp hik)) (by omega)

/-- A prefix of the snake order meets no column after the one it ends in. -/
theorem snakePrefix_subset_stripInterval {L w k : ℕ} (_hw : 1 ≤ w) :
    snakePrefix L w k ⊆ stripInterval L w 0 (k / w + 1) := by
  intro x hx
  have hik := mem_snakePrefix.mp hx
  rw [mem_stripInterval]
  have hcol := stripColumn_snakeEquiv ((snakeEquiv L w).symm x)
  rw [Equiv.apply_symm_apply] at hcol
  rw [hcol]
  exact ⟨Nat.zero_le _, Nat.lt_succ_of_le (Nat.div_le_div_right hik.le)⟩

/-- A prefix of the snake order differs from the columns before the one it ends in by at most
`w` sites. -/
theorem card_snakePrefix_sdiff_le {L w k : ℕ} (hw : 1 ≤ w) :
    (snakePrefix L w k \ stripInterval L w 0 (k / w)).card ≤ w := by
  classical
  have hsub : snakePrefix L w k \ stripInterval L w 0 (k / w) ⊆
      stripInterval L w (k / w) (k / w + 1) := by
    intro x hx
    have hcol := mem_stripInterval.mp (snakePrefix_subset_stripInterval hw
      (Finset.mem_sdiff.mp hx).1)
    have hn := (Finset.mem_sdiff.mp hx).2
    simp only [mem_stripInterval] at hn ⊢
    omega
  exact (Finset.card_le_card hsub).trans (by
    simpa using card_stripInterval_le L w (k / w) (k / w + 1))

/-! ### The edge boundary of a prefix -/

private theorem snakeIndex_row_lt {L w : ℕ} {p p' : Fin L × Fin w} (h : p.1.val < p'.1.val) :
    (snakeIndex L w p).val < (snakeIndex L w p').val := by
  have hoff (p : Fin L × Fin w) :
      (if p.1.val % 2 = 0 then p.2.val else w - 1 - p.2.val) < w := by
    split_ifs <;> omega
  rw [snakeIndex_val, snakeIndex_val]
  have hmul : w * (p.1.val + 1) ≤ w * p'.1.val := Nat.mul_le_mul_left _ h
  have := hoff p
  rw [Nat.mul_add, Nat.mul_one] at hmul
  omega

private theorem snakeIndex_adj_same_row {L w : ℕ} {p p' : Fin L × Fin w}
    (hrow : p.1 = p'.1) (hadj : (squareLatticeGraph L w).Adj p p') :
    (snakeIndex L w p).val + 1 = (snakeIndex L w p').val ∨
      (snakeIndex L w p').val + 1 = (snakeIndex L w p).val := by
  rcases hadj with ⟨_, h | h⟩ | ⟨_, h | h⟩
  · have := congrArg Fin.val hrow
    omega
  · have := congrArg Fin.val hrow
    omega
  all_goals
    rw [snakeIndex_val, snakeIndex_val, hrow]
    split_ifs <;> omega

/-- The ordered pairs of adjacent vertices with the first in the prefix of length `k` and the
second outside it. -/
private noncomputable def snakeBoundaryPairs (L w k : ℕ) :
    Finset ((Fin L × Fin w) × (Fin L × Fin w)) := by
  classical
  exact Finset.univ.filter fun p ↦ (squareLatticeGraph L w).Adj p.1 p.2 ∧
    (snakeIndex L w p.1).val < k ∧ k ≤ (snakeIndex L w p.2).val

private theorem boundaryPair_row_lt {L w k : ℕ} {p : (Fin L × Fin w) × (Fin L × Fin w)}
    (hp : p ∈ snakeBoundaryPairs L w k) (hrow : p.1.1 ≠ p.2.1) :
    p.1.1.val < p.2.1.val := by
  classical
  obtain ⟨_, hadj, hlt, hge⟩ := Finset.mem_filter.mp hp
  by_contra h
  have heq : p.1.1.val ≠ p.2.1.val := fun heq ↦ hrow (Fin.ext heq)
  have hrev := snakeIndex_row_lt (p := p.2) (p' := p.1) (by omega)
  omega

private theorem boundaryPair_same_row_index {L w k : ℕ}
    {p : (Fin L × Fin w) × (Fin L × Fin w)}
    (hp : p ∈ snakeBoundaryPairs L w k) (hrow : p.1.1 = p.2.1) :
    (snakeIndex L w p.1).val + 1 = k ∧ (snakeIndex L w p.2).val = k := by
  classical
  obtain ⟨_, hadj, hlt, hge⟩ := Finset.mem_filter.mp hp
  have h := snakeIndex_adj_same_row hrow hadj
  omega

private theorem boundaryPair_diff_row_column {L w k : ℕ}
    {p : (Fin L × Fin w) × (Fin L × Fin w)}
    (hp : p ∈ snakeBoundaryPairs L w k) (hrow : p.1.1 ≠ p.2.1) :
    p.1.2 = p.2.2 ∧ p.1.1.val + 1 = p.2.1.val := by
  classical
  obtain ⟨_, hadj, hlt, hge⟩ := Finset.mem_filter.mp hp
  rcases hadj with ⟨hcol, hadj⟩ | ⟨hrow', _⟩
  · have h := boundaryPair_row_lt hp hrow
    exact ⟨hcol, by omega⟩
  · exact (hrow hrow').elim

private theorem boundaryPairs_diff_row_inj {L w k : ℕ}
    {p p' : (Fin L × Fin w) × (Fin L × Fin w)}
    (hp : p ∈ snakeBoundaryPairs L w k) (hp' : p' ∈ snakeBoundaryPairs L w k)
    (hrow : p.1.1 ≠ p.2.1) (hrow' : p'.1.1 ≠ p'.2.1)
    (hcol : p.1.2 = p'.1.2) : p = p' := by
  classical
  obtain ⟨hc, hr⟩ := boundaryPair_diff_row_column hp hrow
  obtain ⟨hc', hr'⟩ := boundaryPair_diff_row_column hp' hrow'
  obtain ⟨_, _, hlt, hge⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, _, hlt', hge'⟩ := Finset.mem_filter.mp hp'
  have hrows : p.1.1 = p'.1.1 := by
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hle : (snakeIndex L w p.2).val ≤ (snakeIndex L w p'.1).val := by
        rcases lt_or_eq_of_le (show p.2.1.val ≤ p'.1.1.val by omega) with hlt | heq
        · exact (snakeIndex_row_lt hlt).le
        · have he : p.2 = p'.1 := Prod.ext (Fin.ext heq) (hc.symm.trans hcol)
          rw [he]
      omega
    · have hle : (snakeIndex L w p'.2).val ≤ (snakeIndex L w p.1).val := by
        rcases lt_or_eq_of_le (show p'.2.1.val ≤ p.1.1.val by omega) with hlt | heq
        · exact (snakeIndex_row_lt hlt).le
        · have he : p'.2 = p.1 := Prod.ext (Fin.ext heq) (hc'.symm.trans hcol.symm)
          rw [he]
      omega
  exact Prod.ext (Prod.ext hrows hcol)
    (Prod.ext (Fin.ext (by have := congrArg Fin.val hrows; omega)) (hc.symm.trans (hcol.trans hc')))

private theorem card_snakeBoundaryPairs_le (L w k : ℕ) :
    (snakeBoundaryPairs L w k).card ≤ w + 1 := by
  classical
  let f : ((Fin L × Fin w) × (Fin L × Fin w)) → Fin (w + 1) := fun p ↦
    if p.1.1 = p.2.1 then ⟨w, by omega⟩ else ⟨p.1.2.val, by omega⟩
  have hf : Set.InjOn f (snakeBoundaryPairs L w k : Set _) := by
    intro p hp p' hp' heq
    by_cases hrow : p.1.1 = p.2.1 <;> by_cases hrow' : p'.1.1 = p'.2.1
    · obtain ⟨hu, hv⟩ := boundaryPair_same_row_index hp hrow
      obtain ⟨hu', hv'⟩ := boundaryPair_same_row_index hp' hrow'
      have hinj : Function.Injective (snakeIndex L w) :=
        finProdFinEquiv.injective.comp (snakeFlip L w).symm.injective
      exact Prod.ext (hinj (Fin.ext (by omega))) (hinj (Fin.ext (by omega)))
    · have hval := congrArg Fin.val heq
      simp only [f, hrow, hrow', ↓reduceIte] at hval
      omega
    · have hval := congrArg Fin.val heq
      simp only [f, hrow, hrow', ↓reduceIte] at hval
      omega
    · exact boundaryPairs_diff_row_inj hp hp' hrow hrow' (by
        have hval := congrArg Fin.val heq
        simp only [f, hrow, hrow', ↓reduceIte] at hval
        exact Fin.ext hval)
  simpa using Finset.card_le_card_of_injOn f (t := Finset.univ) (by simp [Set.MapsTo]) hf

/-- The edge boundary of a prefix of the snake order of the rectangle `[0, L) × [0, w)` has at
most `w + 1` edges. An edge between two columns is charged to its second coordinate, at most
once for each of the `w` values; the remaining edges join consecutive positions of one column,
so at most one of them leaves the prefix. Source: the square-grid cutwidth comparison in
*Polynomial PEPS approximation of gapped square-grid ground states*, Section 1. -/
theorem card_edgeBoundary_snakePrefix_le (L w k : ℕ) :
    (edgeBoundary (planeDomainGraph (rectangularDomain L w)) (snakePrefix L w k)).card ≤
      w + 1 := by
  classical
  let f : ((Fin L × Fin w) × (Fin L × Fin w)) →
      Sym2 ↥(rectangularDomain L w) := fun p ↦
    s(rectangleSiteEquiv L w p.1, rectangleSiteEquiv L w p.2)
  have hcover : edgeBoundary (planeDomainGraph (rectangularDomain L w)) (snakePrefix L w k) ⊆
      (snakeBoundaryPairs L w k).image f := by
    intro e he
    obtain ⟨he, x, hx, y, hy, rfl⟩ := mem_edgeBoundary.mp he
    obtain ⟨a, rfl⟩ := (rectangleSiteEquiv L w).surjective x
    obtain ⟨b, rfl⟩ := (rectangleSiteEquiv L w).surjective y
    have hadj : (planeDomainGraph (rectangularDomain L w)).Adj
        (rectangleSiteEquiv L w a) (rectangleSiteEquiv L w b) := by
      simpa only [SimpleGraph.mem_edgeSet] using he
    have ha : (snakeIndex L w a).val < k := by
      simpa only [mem_snakePrefix, snakeEquiv_symm_rectangleSiteEquiv] using hx
    have hb : k ≤ (snakeIndex L w b).val := by
      have : ¬ (snakeIndex L w b).val < k := by
        simpa only [mem_snakePrefix, snakeEquiv_symm_rectangleSiteEquiv] using hy
      omega
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (rectangleGraphIso L w).map_rel_iff.mp hadj, ha, hb⟩, rfl⟩
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_image_le).trans (card_snakeBoundaryPairs_le L w k))

end ManyBody
