/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Rectangle
import QICLean.ManyBody.Sites.Lattice.IntegerRectangle

/-!
# Column intervals of a rectangle

The rectangular domain `[0, L) × [0, w)` of `ℤ × ℤ` is cut into its `L` columns of `w` sites.
A column interval `[a, b)` is the set of sites whose column lies in `[a, b)`; it has at most
`(b - a) w` sites. The supports are the supports of range `R` of the induced lattice graph of
the domain, and columns are never grouped into larger sites.

A support of range `R` split by a column interval meets one of the two bands of `R` columns on
the inside of the cuts. Since at most `2^{2R(R+1)}` supports of range `R` contain a given site,
at most `2R 2^{2R(R+1)} w` supports cross any column interval, linearly many in the width `w`.
The shells `[a - (i + 1) R, b + (i + 1) R)` of a column interval are split by disjoint sets of
supports. A support of range `R` has at most `1 + 2R(R + 1)` sites, not `R + 1` as on the
chain: a cross of diameter two has five sites.

## Main definitions

* `ManyBody.stripColumn`, `ManyBody.stripRow` — the coordinates of a site of the rectangle.
* `ManyBody.stripInterval` — the sites of the columns `a, …, b - 1`.
* `ManyBody.stripCrossConst` — the coefficient `2R 2^{2R(R+1)}` of the crossing count.

## Main results

* `ManyBody.mem_rectangularDomain` — the sites of the rectangle by their coordinates.
* `ManyBody.card_stripInterval_le`, `ManyBody.card_stripInterval_enlargement_sdiff_le` — the
  number of sites of a column interval and of its enlargement.
* `ManyBody.card_crossingTerms_stripInterval_le` — at most `2R 2^{2R(R+1)} w` supports cross a
  column interval.
* `ManyBody.strip_single_splitting` — a support splits at most one of the shells.
* `ManyBody.card_crossingTerms_stripPrefix_le` — a region between two consecutive prefixes of
  columns is crossed by at most `(R + 1) 2^{2R(R+1)} w` supports.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Section 2, the supports of the
  lattice Hamiltonian and their count.
-/

namespace ManyBody

variable {L w R : ℕ}

/-- The sites of the rectangular domain are the points with coordinates in `[0, L) × [0, w)`. -/
theorem mem_rectangularDomain {p : ℤ × ℤ} :
    p ∈ rectangularDomain L w ↔ 0 ≤ p.1 ∧ p.1 < L ∧ 0 ≤ p.2 ∧ p.2 < w := by
  constructor
  · intro hp
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hp
    have h1 := v.1.isLt
    have h2 := v.2.isLt
    simp only [rectangleEmbedding]
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    refine Finset.mem_image.mpr
      ⟨(⟨p.1.toNat, by omega⟩, ⟨p.2.toNat, by omega⟩), Finset.mem_univ _, ?_⟩
    simp only [rectangleEmbedding]
    ext <;> simp <;> omega

/-- The column coordinate of a site of the rectangle. -/
def stripColumn (x : ↥(rectangularDomain L w)) : ℕ := x.1.1.toNat

/-- The row coordinate of a site of the rectangle. -/
def stripRow (x : ↥(rectangularDomain L w)) : ℕ := x.1.2.toNat

/-- The sites of the columns `a, …, b - 1` of the rectangle. -/
def stripInterval (L w a b : ℕ) : Finset ↥(rectangularDomain L w) :=
  Finset.univ.filter fun x ↦ a ≤ stripColumn x ∧ stripColumn x < b

/-- Membership in a column interval is determined by the column. -/
@[simp] theorem mem_stripInterval {a b : ℕ} {x : ↥(rectangularDomain L w)} :
    x ∈ stripInterval L w a b ↔ a ≤ stripColumn x ∧ stripColumn x < b := by
  simp [stripInterval]

/-- At most `w` sites occur in each column of an interval. -/
theorem card_stripInterval_le (L w a b : ℕ) :
    (stripInterval L w a b).card ≤ (b - a) * w := by
  classical
  have hinj : Function.Injective (fun x : ↥(rectangularDomain L w) ↦
      (stripColumn x, stripRow x)) := by
    intro x y h
    have hx := mem_rectangularDomain.mp x.2
    have hy := mem_rectangularDomain.mp y.2
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    apply Subtype.ext
    simp only [stripColumn, stripRow] at h₁ h₂
    ext <;> omega
  calc (stripInterval L w a b).card ≤
      ((Finset.Ico a b) ×ˢ Finset.range w).card := by
        apply Finset.card_le_card_of_injOn
          (fun x ↦ (stripColumn x, stripRow x)) ?_ hinj.injOn
        intro x hx
        have hx' := mem_stripInterval.mp hx
        have hrow : stripRow x < w := by
          have := mem_rectangularDomain.mp x.2
          simp only [stripRow]
          omega
        exact Finset.mem_product.mpr
          ⟨Finset.mem_Ico.mpr hx', Finset.mem_range.mpr hrow⟩
    _ = (b - a) * w := by simp

/-- Enlarging a column interval by `d` columns on each side adds at most `2dw` sites, including
clipped and empty intervals. -/
theorem card_stripInterval_enlargement_sdiff_le (L w a b d : ℕ) :
    (stripInterval L w (a - d) (b + d) \ stripInterval L w a b).card ≤ 2 * d * w := by
  classical
  have hcover : stripInterval L w (a - d) (b + d) \ stripInterval L w a b ⊆
      stripInterval L w (a - d) a ∪ stripInterval L w b (b + d) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union, mem_stripInterval] at hx ⊢
    omega
  calc _ ≤ _ := Finset.card_le_card hcover
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ (a - (a - d)) * w + ((b + d) - b) * w :=
      Nat.add_le_add (card_stripInterval_le _ _ _ _) (card_stripInterval_le _ _ _ _)
    _ ≤ 2 * d * w := by
      have : a - (a - d) ≤ d := by omega
      simp only [Nat.add_sub_cancel_left]
      nlinarith [Nat.mul_le_mul_right w this]

/-- Two sites of a support of range `R` lie at most `R` columns apart. -/
theorem stripColumn_le_add_range (X : AdmissibleSupport (rectangularDomain L w) R)
    {x y : ↥(rectangularDomain L w)} (hx : x ∈ X.1) (hy : y ∈ X.1) :
    stripColumn y ≤ stripColumn x + R := by
  obtain ⟨p, hp⟩ := X.2.2 x hx y hy
  have hd := supDist_le_of_walk p hp
  have hx' := mem_rectangularDomain.mp x.2
  have hy' := mem_rectangularDomain.mp y.2
  simp only [supDist] at hd
  simp only [stripColumn]
  omega

/-- A support split by a column interval meets one of the two bands of `R` columns on the
inside of the cuts. -/
theorem crossingSupport_meets_stripBand {a b : ℕ}
    (X : AdmissibleSupport (rectangularDomain L w) R)
    (hX : X ∈ crossingTerms (fun Y : AdmissibleSupport (rectangularDomain L w) R ↦ Y.1)
      (stripInterval L w a b)) :
    ∃ x ∈ stripInterval L w a (a + R) ∪ stripInterval L w (b - R) b, x ∈ X.1 := by
  classical
  simp only [crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
  obtain ⟨⟨x, hx, hxA⟩, y, hy, hyA⟩ := hX
  have hxy := stripColumn_le_add_range X hx hy
  have hyx := stripColumn_le_add_range X hy hx
  refine ⟨x, ?_, hx⟩
  simp only [Finset.mem_union, mem_stripInterval] at hxA hyA ⊢
  omega

/-- The coefficient `2R 2^{2R(R+1)}`, independent of the width, of the number of supports
crossing a column interval. -/
def stripCrossConst (R : ℕ) : ℕ := 2 * R * 2 ^ (2 * R * (R + 1))

/-- At most `2R 2^{2R(R+1)} w` supports of range `R` cross any column interval. -/
theorem card_crossingTerms_stripInterval_le (L w R a b : ℕ) :
    (crossingTerms (fun X : AdmissibleSupport (rectangularDomain L w) R ↦ X.1)
      (stripInterval L w a b)).card ≤ stripCrossConst R * w := by
  classical
  let band := stripInterval L w a (a + R) ∪ stripInterval L w (b - R) b
  have hband : band.card ≤ 2 * R * w := by
    calc _ ≤ _ := Finset.card_union_le _ _
      _ ≤ ((a + R) - a) * w + (b - (b - R)) * w :=
        Nat.add_le_add (card_stripInterval_le _ _ _ _) (card_stripInterval_le _ _ _ _)
      _ ≤ 2 * R * w := by
        have : b - (b - R) ≤ R := by omega
        simp only [Nat.add_sub_cancel_left]
        nlinarith [Nat.mul_le_mul_right w this]
  calc _ ≤ band.card * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      card_le_card_mul_of_forall_exists_mem fun X hX ↦
        crossingSupport_meets_stripBand X hX
    _ ≤ (2 * R * w) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      Nat.mul_le_mul_right _ hband
    _ = stripCrossConst R * w := by
      simp only [stripCrossConst, Nat.add_sub_cancel_left]
      ring

/-- Column intervals grow when either endpoint moves outwards. -/
theorem stripInterval_mono {a b c d : ℕ} (hca : c ≤ a) (hbd : b ≤ d) :
    stripInterval L w a b ⊆ stripInterval L w c d := by
  intro x hx
  simp only [mem_stripInterval] at hx ⊢
  omega

/-- A support of range `R` splits at most one of the column shells
`[a - (i + 1) R, b + (i + 1) R)`. -/
theorem strip_single_splitting {a b : ℕ}
    (X : AdmissibleSupport (rectangularDomain L w) R) {i j : ℕ}
    (hi : (∃ x ∈ X.1, x ∈ stripInterval L w (a - (i + 1) * R) (b + (i + 1) * R)) ∧
      ∃ x ∈ X.1, x ∉ stripInterval L w (a - (i + 1) * R) (b + (i + 1) * R))
    (hj : (∃ x ∈ X.1, x ∈ stripInterval L w (a - (j + 1) * R) (b + (j + 1) * R)) ∧
      ∃ x ∈ X.1, x ∉ stripInterval L w (a - (j + 1) * R) (b + (j + 1) * R)) : i = j := by
  have hnot {k l : ℕ} (hkl : k < l)
      (hk : ∃ x ∈ X.1,
        x ∈ stripInterval L w (a - (k + 1) * R) (b + (k + 1) * R))
      (hl : ∃ x ∈ X.1,
        x ∉ stripInterval L w (a - (l + 1) * R) (b + (l + 1) * R)) : False := by
    obtain ⟨x, hxX, hx⟩ := hk
    obtain ⟨y, hyX, hy⟩ := hl
    have hxy := stripColumn_le_add_range X hxX hyX
    have hyx := stripColumn_le_add_range X hyX hxX
    have hstep : (k + 1) * R + R ≤ (l + 1) * R := by
      simpa only [Nat.succ_mul] using
        Nat.mul_le_mul_right R (Nat.succ_le_succ (Nat.succ_le_of_lt hkl))
    simp only [mem_stripInterval] at hx hy
    omega
  rcases lt_trichotomy i j with h | h | h
  · exact (hnot h hi.1 hj.2).elim
  · exact h
  · exact (hnot h hj.1 hi.2).elim

/-- A region between the prefixes of `c` and of `c + 1` columns is crossed by at most
`(R + 1) 2^{2R(R+1)} w` supports of range `R`, whatever part of the last column it contains. -/
theorem card_crossingTerms_stripPrefix_le {c : ℕ}
    (A : Finset ↥(rectangularDomain L w))
    (hleft : stripInterval L w 0 c ⊆ A)
    (hright : A ⊆ stripInterval L w 0 (c + 1)) :
    (crossingTerms (fun X : AdmissibleSupport (rectangularDomain L w) R ↦ X.1) A).card ≤
      ((R + 1) * 2 ^ (2 * R * (R + 1))) * w := by
  classical
  let band := stripInterval L w (c - R) (c + 1)
  have hmeet (X : AdmissibleSupport (rectangularDomain L w) R)
      (hX : X ∈ crossingTerms (fun X : AdmissibleSupport (rectangularDomain L w) R ↦ X.1) A) :
      ∃ x ∈ band, x ∈ X.1 := by
    simp only [crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and] at hX
    obtain ⟨⟨x, hx, hxA⟩, y, hy, hyA⟩ := hX
    have hxcol := mem_stripInterval.mp (hright hxA)
    have hycol : c ≤ stripColumn y := by
      by_contra hn
      exact hyA (hleft (mem_stripInterval.mpr ⟨Nat.zero_le _, by omega⟩))
    have hdist := stripColumn_le_add_range X hx hy
    exact ⟨x, by simp only [band, mem_stripInterval]; omega, hx⟩
  have hband : band.card ≤ (R + 1) * w := by
    refine (card_stripInterval_le L w (c - R) (c + 1)).trans ?_
    exact Nat.mul_le_mul_right w (by omega)
  calc _ ≤ band.card * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      card_le_card_mul_of_forall_exists_mem hmeet
    _ ≤ ((R + 1) * w) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) :=
      Nat.mul_le_mul_right _ hband
    _ = _ := by simp only [Nat.add_sub_cancel_left]; ring

end ManyBody
