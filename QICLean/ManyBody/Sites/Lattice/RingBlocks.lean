/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Nat.Dist
import Mathlib.Tactic.Linarith

/-!
# Blocks of consecutive sites of the ring

For a radius `ℓ`, the ring of `M` sites is divided into consecutive blocks of `2ℓ` sites, the
remainder going to the last block: site `v` lies in block `min (v / (2ℓ)) (N - 1)` of `N` blocks.
With `N = max 1 (M / (2ℓ))` the remainder is smaller than one further block, so each block has
fewer than `4ℓ` sites, and a ring shorter than `2ℓ` is one block. Every site `i` is assigned to
the boundary `⌊(i + ℓ) / (2ℓ)⌋` between two blocks (to boundary `0` past the last block). The
ball of radius `ℓ` about `i` in the cyclic distance `min (|i - v|, M - |i - v|)` meets only the
two blocks adjacent to its boundary; the blocks need not have equal sizes.

## Main definitions

* `ManyBody.roundedPeriodicBlock` — the block of a site.
* `ManyBody.roundedPeriodicEdge` — the boundary assigned to a site.
* `ManyBody.roundedPeriodicDistance` — the cyclic distance on `Fin M`.
* `ManyBody.roundedPeriodicBlockCount` — the number `max 1 (M / (2ℓ))` of blocks.

## Main results

* `ManyBody.roundedPeriodicEdge_support_of_cover`, `ManyBody.roundedPeriodicEdge_zero_support` —
  a ball of radius `ℓ` meets only the two blocks adjacent to the boundary of its center.
* `ManyBody.roundedPeriodicBlockCount_cover`, `ManyBody.roundedPeriodicBlockCount_upper` — the
  blocks have at least `2ℓ` and fewer than `4ℓ` sites, unless there is one block.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, Section II,
  lines 609–628, where the rounding of the blocks is suppressed.
-/

namespace ManyBody


/-- The block `min (v / (2ℓ)) (N - 1)` of a site: blocks of `2ℓ` consecutive sites, the
remainder included in the last of the `N` blocks. -/
def roundedPeriodicBlock {M : ℕ} (N ℓ : ℕ) (v : Fin M) : ℕ :=
  min ((v : ℕ) / (2 * ℓ)) (N - 1)

/-- The boundary `⌊(i + ℓ) / (2ℓ)⌋` assigned to a site, or `0` past the last block. -/
def roundedPeriodicEdge {M N ℓ : ℕ} (hN : 0 < N) (i : Fin M) : Fin N :=
  if hq : ((i : ℕ) + ℓ) / (2 * ℓ) < N then
    ⟨((i : ℕ) + ℓ) / (2 * ℓ), hq⟩ else ⟨0, hN⟩

/-- The cyclic distance `min (|i - v|, M - |i - v|)` on the ring of `M` sites. -/
def roundedPeriodicDistance {M : ℕ} (i v : Fin M) : ℕ :=
  min (Nat.dist (i : ℕ) (v : ℕ)) (M - Nat.dist (i : ℕ) (v : ℕ))

/-- The block of every site is one of the `N` blocks. -/
theorem roundedPeriodicBlock_lt {M N ℓ : ℕ} (hN : 0 < N) (v : Fin M) :
    roundedPeriodicBlock N ℓ v < N :=
  (Nat.min_le_right _ _).trans_lt (Nat.sub_lt hN (by omega))

/-- A site assigned to a boundary `j > 0` lies within `ℓ` of the position `2ℓ j` of that
boundary. -/
theorem roundedPeriodicEdge_internal_centre {M N ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N)
    (i : Fin M) {j : Fin N} (hj : 0 < (j : ℕ))
    (he : roundedPeriodicEdge (ℓ := ℓ) hN i = j) :
    (j : ℕ) * (2 * ℓ) ≤ (i : ℕ) + ℓ ∧
      (i : ℕ) < (j : ℕ) * (2 * ℓ) + ℓ := by
  unfold roundedPeriodicEdge at he
  split_ifs at he with hq
  · have hval : ((i : ℕ) + ℓ) / (2 * ℓ) = (j : ℕ) := congrArg Fin.val he
    have hlo := Nat.div_mul_le_self ((i : ℕ) + ℓ) (2 * ℓ)
    have hhi := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * ℓ)).mp
      (show ((i : ℕ) + ℓ) / (2 * ℓ) < (j : ℕ) + 1 by omega)
    rw [hval] at hlo
    constructor
    · exact hlo
    · nlinarith
  · have hval : (0 : ℕ) = (j : ℕ) := congrArg Fin.val he
    omega

/-- The ball of radius `ℓ` about a site assigned to a boundary `j > 0` meets only the two blocks
adjacent to it, when the `N` blocks have at least `2ℓ` sites. -/
theorem roundedPeriodicEdge_support {M N ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N)
    (hNM : N * (2 * ℓ) ≤ M) (i v : Fin M) {j : Fin N} (hj : 0 < (j : ℕ))
    (he : roundedPeriodicEdge (ℓ := ℓ) hN i = j)
    (hv : roundedPeriodicDistance i v ≤ ℓ) :
    roundedPeriodicBlock N ℓ v + 1 = (j : ℕ) ∨
      roundedPeriodicBlock N ℓ v = (j : ℕ) := by
  obtain ⟨hlo, hhi⟩ := roundedPeriodicEdge_internal_centre hℓ hN i hj he
  have hzlo : ℓ ≤ (i : ℕ) := by
    have hm := Nat.mul_le_mul_right (2 * ℓ) (show 1 ≤ (j : ℕ) by omega)
    nlinarith
  have hzhi : (i : ℕ) + ℓ < M := by
    have hm := Nat.mul_le_mul_right (2 * ℓ) (show (j : ℕ) + 1 ≤ N by omega)
    nlinarith
  have hd : Nat.dist (i : ℕ) (v : ℕ) ≤ ℓ := by
    unfold roundedPeriodicDistance at hv
    rw [min_le_iff] at hv
    rcases hv with hv | hv
    · exact hv
    · unfold Nat.dist at hv ⊢
      have hi := i.isLt
      have hx := v.isLt
      omega
  have hjw : (j : ℕ) * (2 * ℓ) = ((j : ℕ) - 1) * (2 * ℓ) + 2 * ℓ := by
    have : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
    nlinarith
  have hxlo : ((j : ℕ) - 1) * (2 * ℓ) ≤ (v : ℕ) := by
    have hd' := Nat.dist_tri_right' (i : ℕ) (v : ℕ)
    nlinarith
  have hxhi : (v : ℕ) < ((j : ℕ) + 1) * (2 * ℓ) := by
    have hd' := Nat.dist_tri_right (i : ℕ) (v : ℕ)
    nlinarith
  have hqlo := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * ℓ)).mpr hxlo
  have hqhi := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * ℓ)).mpr hxhi
  have hqN : (v : ℕ) / (2 * ℓ) ≤ N - 1 := by have := j.isLt; omega
  simp only [roundedPeriodicBlock, min_eq_left hqN]
  omega

/-- The number `max 1 (M / (2ℓ))` of blocks of the ring of `M` sites. -/
def roundedPeriodicBlockCount (M ℓ : ℕ) : ℕ := max 1 (M / (2 * ℓ))

/-- There is at least one block. -/
theorem roundedPeriodicBlockCount_pos (M ℓ : ℕ) :
    0 < roundedPeriodicBlockCount M ℓ := by
  unfold roundedPeriodicBlockCount
  omega

/-- Either `N` blocks of `2ℓ` sites fit in the ring, or there is one block. -/
theorem roundedPeriodicBlockCount_cover (M ℓ : ℕ) :
    roundedPeriodicBlockCount M ℓ * (2 * ℓ) ≤ M ∨
      roundedPeriodicBlockCount M ℓ = 1 := by
  by_cases hq : 1 ≤ M / (2 * ℓ)
  · left
    simpa only [roundedPeriodicBlockCount, max_eq_right hq] using
      Nat.div_mul_le_self M (2 * ℓ)
  · right
    unfold roundedPeriodicBlockCount
    omega

/-- The remainder is smaller than one further block of `2ℓ` sites. -/
theorem roundedPeriodicBlockCount_upper {M ℓ : ℕ} (hℓ : 0 < ℓ) :
    M < (roundedPeriodicBlockCount M ℓ + 1) * (2 * ℓ) := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * ℓ)).mp
  have : M / (2 * ℓ) ≤ roundedPeriodicBlockCount M ℓ := le_max_right _ _
  omega

/-- A nonempty ring has at most as many blocks as sites. -/
theorem roundedPeriodicBlockCount_le {M ℓ : ℕ} (hM : 0 < M) :
    roundedPeriodicBlockCount M ℓ ≤ M :=
  max_le (by omega) (Nat.div_le_self _ _)

/-- The ball of radius `ℓ` about a site assigned to a boundary `j > 0` meets only the two blocks
adjacent to it, also when the ring is one block. -/
theorem roundedPeriodicEdge_support_of_cover {M N ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N)
    (hcover : N * (2 * ℓ) ≤ M ∨ N = 1) (i v : Fin M) {j : Fin N}
    (hj : 0 < (j : ℕ)) (he : roundedPeriodicEdge (ℓ := ℓ) hN i = j)
    (hv : roundedPeriodicDistance i v ≤ ℓ) :
    roundedPeriodicBlock N ℓ v + 1 = (j : ℕ) ∨
      roundedPeriodicBlock N ℓ v = (j : ℕ) := by
  rcases hcover with hNM | hN1
  · exact roundedPeriodicEdge_support hℓ hN hNM i v hj he hv
  · have := j.isLt
    omega

private theorem cyclic_end_block_support {M ℓ c x z : ℕ}
    (hcM : c + 2 * ℓ ≤ M) (hx : x < M) (hz : z < M)
    (hc : z < ℓ ∨ c + ℓ ≤ z)
    (hd : min (Nat.dist z x) (M - Nat.dist z x) ≤ ℓ) :
    x < 2 * ℓ ∨ c ≤ x := by
  unfold Nat.dist at hd
  omega

private theorem roundedPeriodicEdge_zero_centre {M N ℓ : ℕ}
    (hℓ : 0 < ℓ) (hN : 0 < N) (i : Fin M) {j : Fin N}
    (hj : (j : ℕ) = 0) (he : roundedPeriodicEdge (ℓ := ℓ) hN i = j) :
    (i : ℕ) < ℓ ∨ (N - 1) * (2 * ℓ) + ℓ ≤ (i : ℕ) := by
  unfold roundedPeriodicEdge at he
  split_ifs at he with hq
  · have hval : ((i : ℕ) + ℓ) / (2 * ℓ) = 0 := (congrArg Fin.val he).trans hj
    left
    have hbound := (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * ℓ)).mp
      (show ((i : ℕ) + ℓ) / (2 * ℓ) < 1 by omega)
    omega
  · right
    have hbound := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * ℓ)).mp (Nat.le_of_not_gt hq)
    have hstep : N - 1 + 1 = N := by omega
    nlinarith

/-- The ball of radius `ℓ` about a site assigned to the boundary `0` meets only the first and the
last block. -/
theorem roundedPeriodicEdge_zero_support {M N ℓ : ℕ} (hℓ : 0 < ℓ) (hN : 0 < N)
    (hcover : N * (2 * ℓ) ≤ M ∨ N = 1) (i v : Fin M) {j : Fin N}
    (hj : (j : ℕ) = 0) (he : roundedPeriodicEdge (ℓ := ℓ) hN i = j)
    (hv : roundedPeriodicDistance i v ≤ ℓ) :
    roundedPeriodicBlock N ℓ v = 0 ∨ roundedPeriodicBlock N ℓ v + 1 = N := by
  rcases hcover with hNM | hN1
  · have hc := roundedPeriodicEdge_zero_centre hℓ hN i hj he
    have hstep : N - 1 + 1 = N := by omega
    have hcM : (N - 1) * (2 * ℓ) + 2 * ℓ ≤ M := by nlinarith
    have hx := cyclic_end_block_support hcM v.isLt i.isLt hc hv
    rcases hx with hx | hx
    · left
      simp only [roundedPeriodicBlock, Nat.div_eq_of_lt hx, zero_min]
    · right
      have hq := (Nat.le_div_iff_mul_le (by omega : 0 < 2 * ℓ)).mpr hx
      simpa only [roundedPeriodicBlock, min_eq_right hq] using hstep
  · left
    simp only [roundedPeriodicBlock, hN1, Nat.sub_self, min_zero]

end ManyBody
