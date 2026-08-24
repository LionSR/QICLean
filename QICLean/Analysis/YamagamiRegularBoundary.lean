/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CyclicReciprocal
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Yamagami's regular-boundary recurrence

This file formalizes the dimension-reduction step on p. 525 of
S. Yamagami, *Cyclic inequalities*, Proc. Amer. Math. Soc. 118 (1993),
521--527.  For the stride-one functional, delete a zero final coordinate.
The remaining cyclic order is represented by the map

`ZMod (N - 1) → ZMod N,  i ↦ i.val`.

The reduced forward window skips the deleted coordinate.  Before that
coordinate is reached, the original denominator has one additional
nonnegative term; after it is reached, the two windows agree because the
skipped term is zero.  Consequently the comparison is non-strict.  The
statement uses Lean's total division, so it remains valid when the reduced
vector has a singular denominator.
-/

open scoped BigOperators

namespace Yamagami

/-- Delete the final coordinate from a cyclic vector while preserving the
linear order `0, ..., N - 2` used in Yamagami's p. 525 reduction. -/
def deleteLastCoordinate (N : ℕ) (x : ZMod N → ℝ) : ZMod (N - 1) → ℝ :=
  fun i ↦ x (i.val : ZMod N)

/-- Embed a step in the reduced forward window into the original window.
After the path crosses the deleted final coordinate, its step is increased
by one. -/
private def reducedStepEmbedding (N m : ℕ) (i : ZMod (N - 1))
    (hm : 1 ≤ m) (q : Fin (m - 1)) : Fin m :=
  if i.val + q.val + 1 < N - 1 then
    ⟨q.val, by omega⟩
  else
    ⟨q.val + 1, by omega⟩

private theorem reducedStepEmbedding_injective
    (N m : ℕ) (hm : 1 ≤ m) (i : ZMod (N - 1)) :
    Function.Injective (reducedStepEmbedding N m i hm) := by
  intro q r hqr
  apply Fin.ext
  have hval := congrArg Fin.val hqr
  by_cases hq : i.val + q.val + 1 < N - 1 <;>
    by_cases hr : i.val + r.val + 1 < N - 1 <;>
      simp [reducedStepEmbedding, hq, hr] at hval <;> omega

private theorem deleteLastCoordinate_forwardStep
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : 1 ≤ m)
    (hmN : m ≤ N - 2) (x : ZMod N → ℝ) (i : ZMod (N - 1))
    (q : Fin (m - 1)) :
    deleteLastCoordinate N x
        (i + ((q.val + 1 : ℕ) : ZMod (N - 1))) =
      x ((i.val : ZMod N) +
        (((reducedStepEmbedding N m i hm q).val + 1 : ℕ) : ZMod N)) := by
  let _ : NeZero (N - 1) := ⟨by omega⟩
  unfold deleteLastCoordinate
  congr 1
  apply ZMod.val_injective N
  have hreducedVal :
      (i + ((q.val + 1 : ℕ) : ZMod (N - 1))).val < N - 1 :=
    ZMod.val_lt _
  rw [ZMod.val_natCast_of_lt (by omega :
    (i + ((q.val + 1 : ℕ) : ZMod (N - 1))).val < N)]
  have hqReduced : q.val + 1 < N - 1 := by omega
  have hqReducedVal :
      (((q.val + 1 : ℕ) : ZMod (N - 1))).val = q.val + 1 :=
    ZMod.val_natCast_of_lt hqReduced
  by_cases hcross : i.val + q.val + 1 < N - 1
  · have hleft :
        i.val + (((q.val + 1 : ℕ) : ZMod (N - 1))).val < N - 1 := by
      omega
    rw [ZMod.val_add_of_lt hleft]
    rw [hqReducedVal]
    simp only [reducedStepEmbedding, hcross, ite_true, Fin.val_mk]
    have hiN : i.val < N := by
      have hi := ZMod.val_lt i
      omega
    have hstepN : q.val + 1 < N := by omega
    have hright :
        ((i.val : ZMod N).val +
          (((q.val + 1 : ℕ) : ZMod N)).val < N) := by
      rw [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hstepN]
      omega
    rw [ZMod.val_add_of_lt hright, ZMod.val_natCast_of_lt hiN,
      ZMod.val_natCast_of_lt hstepN]
  · have hleft :
        N - 1 ≤ i.val + (((q.val + 1 : ℕ) : ZMod (N - 1))).val := by
      omega
    rw [ZMod.val_add_of_le hleft, hqReducedVal]
    simp only [reducedStepEmbedding, hcross, ite_false, Fin.val_mk]
    have hiN : i.val < N := by
      have hi := ZMod.val_lt i
      omega
    have hstepN : q.val + 1 + 1 < N := by omega
    have hright :
        N ≤ (i.val : ZMod N).val +
          (((q.val + 1 + 1 : ℕ) : ZMod N)).val := by
      rw [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hstepN]
      omega
    rw [ZMod.val_add_of_le hright, ZMod.val_natCast_of_lt hiN,
      ZMod.val_natCast_of_lt hstepN]
    omega

private theorem reduced_forward_sum_le
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : 1 ≤ m)
    (hmN : m ≤ N - 2) (x : ZMod N → ℝ) (hx : ∀ j, 0 ≤ x j)
    (i : ZMod (N - 1)) :
    (∑ q : Fin (m - 1),
        deleteLastCoordinate N x
          (i + ((q.val + 1 : ℕ) : ZMod (N - 1)))) ≤
      ∑ k : Fin m,
        x ((i.val : ZMod N) + ((k.val + 1 : ℕ) : ZMod N)) := by
  let e : Fin (m - 1) → Fin m := reducedStepEmbedding N m i hm
  have he : Function.Injective e := reducedStepEmbedding_injective N m hm i
  calc
    (∑ q : Fin (m - 1),
        deleteLastCoordinate N x
          (i + ((q.val + 1 : ℕ) : ZMod (N - 1)))) =
        ∑ q : Fin (m - 1),
          x ((i.val : ZMod N) + ((e q).val + 1 : ℕ)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact deleteLastCoordinate_forwardStep N m hN hm hmN x i q
    _ = ∑ k ∈ Finset.univ.image e,
        x ((i.val : ZMod N) + ((k.val + 1 : ℕ) : ZMod N)) := by
      symm
      rw [Finset.sum_image he.injOn]
    _ ≤ ∑ k : Fin m,
        x ((i.val : ZMod N) + ((k.val + 1 : ℕ) : ZMod N)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun k _ _ ↦ hx _)

private theorem sum_erase_lastCoordinate
    (N : ℕ) [NeZero N] [NeZero (N - 1)] (hN : 2 ≤ N)
    (f : ZMod N → ℝ) :
    (∑ j ∈ (Finset.univ : Finset (ZMod N)).erase
        ((N - 1 : ℕ) : ZMod N), f j) =
      ∑ i : ZMod (N - 1), f (i.val : ZMod N) := by
  symm
  apply Finset.sum_bij (fun i _ ↦ (i.val : ZMod N))
  · intro i _
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro heq
    have hval := congrArg ZMod.val heq
    rw [ZMod.val_natCast_of_lt (by
      have hi := ZMod.val_lt i
      omega : i.val < N)] at hval
    rw [ZMod.val_natCast_of_lt (by omega : N - 1 < N)] at hval
    have hi := ZMod.val_lt i
    omega
  · intro a _ b _ hab
    apply ZMod.val_injective (N - 1)
    have hval := congrArg ZMod.val hab
    rw [ZMod.val_natCast_of_lt (by
      have ha := ZMod.val_lt a
      omega : a.val < N)] at hval
    rw [ZMod.val_natCast_of_lt (by
      have hb := ZMod.val_lt b
      omega : b.val < N)] at hval
    exact hval
  · intro b hb
    have hbne : b ≠ ((N - 1 : ℕ) : ZMod N) := (Finset.mem_erase.mp hb).1
    have hbvalne : b.val ≠ N - 1 := by
      intro hval
      apply hbne
      apply ZMod.val_injective N
      rw [ZMod.val_natCast_of_lt (by omega : N - 1 < N)]
      exact hval
    have hbsmall : b.val < N - 1 := by
      have hbval := ZMod.val_lt b
      omega
    refine ⟨(b.val : ZMod (N - 1)), Finset.mem_univ _, ?_⟩
    rw [ZMod.val_natCast_of_lt hbsmall, ZMod.natCast_zmod_val]
  · intro i _
    rfl

private theorem retained_summand_le_reduced
    (N m : ℕ) [NeZero N] [NeZero (N - 1)] (hN : 3 ≤ N)
    (hm : 1 ≤ m) (hmN : m ≤ N - 2) (s : ℝ) (hs : (N : ℝ) ≤ s)
    (x : ZMod N → ℝ) (hx : ∀ j, 0 ≤ x j) (i : ZMod (N - 1)) :
    x (i.val : ZMod N) /
        forwardDenominator N m s x (i.val : ZMod N) ≤
      deleteLastCoordinate N x i /
        forwardDenominator (N - 1) (m - 1) (s - 1)
          (deleteLastCoordinate N x) i := by
  have hcoeff :
      (s - 1) - ((m - 1 : ℕ) : ℝ) = s - (m : ℝ) := by
    rw [Nat.cast_sub hm]
    norm_num
  have hsum := reduced_forward_sum_le N m hN hm hmN x hx i
  have hdenominator :
      forwardDenominator (N - 1) (m - 1) (s - 1)
          (deleteLastCoordinate N x) i ≤
        forwardDenominator N m s x (i.val : ZMod N) := by
    unfold forwardDenominator
    rw [hcoeff]
    change
      (s - (m : ℝ)) * x (i.val : ZMod N) +
          ∑ q : Fin (m - 1), deleteLastCoordinate N x
            (i + ((q.val + 1 : ℕ) : ZMod (N - 1))) ≤
        (s - (m : ℝ)) * x (i.val : ZMod N) +
          ∑ k : Fin m,
            x ((i.val : ZMod N) + ((k.val + 1 : ℕ) : ZMod N))
    exact add_le_add_right hsum _
  change
    x (i.val : ZMod N) / forwardDenominator N m s x (i.val : ZMod N) ≤
      x (i.val : ZMod N) /
        forwardDenominator (N - 1) (m - 1) (s - 1)
          (deleteLastCoordinate N x) i
  by_cases hxi : x (i.val : ZMod N) = 0
  · have hxiCast : x (ZMod.cast i : ZMod N) = 0 := by
      rw [ZMod.cast_eq_val]
      exact hxi
    simp [hxiCast]
  · have hxipos : 0 < x (i.val : ZMod N) :=
      lt_of_le_of_ne (hx _) (Ne.symm hxi)
    have hmNlt : m < N := by omega
    have hms : (m : ℝ) < s := by
      have hmNR : (m : ℝ) < (N : ℝ) := by exact_mod_cast hmNlt
      exact hmNR.trans_le hs
    have hsumNonneg :
        0 ≤ ∑ q : Fin (m - 1), deleteLastCoordinate N x
          (i + ((q.val + 1 : ℕ) : ZMod (N - 1))) :=
      Finset.sum_nonneg fun q _ ↦ hx _
    have hdenominatorPos :
        0 < forwardDenominator (N - 1) (m - 1) (s - 1)
          (deleteLastCoordinate N x) i := by
      unfold forwardDenominator
      rw [hcoeff]
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr hms) hxipos) hsumNonneg
    exact div_le_div_of_nonneg_left (hx _) hdenominatorPos hdenominator

/-- Yamagami's p. 525 regular-boundary recurrence, with the zero placed in
the final coordinate.  The hypotheses are the exact stride-one source range
used before the `m = 1` base case.  No regularity condition is needed after
adopting Lean's totalized convention `0 / 0 = 0`; in particular, the reduced
vector is allowed to be singular. -/
theorem functional_le_deleteLastCoordinate
    (N m : ℕ) [NeZero N] (hN : 3 ≤ N) (hm : 2 ≤ m)
    (hmN : m ≤ N - 2) (s : ℝ) (hs : (N : ℝ) ≤ s)
    (x : ZMod N → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hlast : x ((N - 1 : ℕ) : ZMod N) = 0) :
    functional N m s x ≤
      @functional (N - 1) (m - 1) ⟨by omega⟩
        (s - 1) (deleteLastCoordinate N x) := by
  let _ : NeZero (N - 1) := ⟨by omega⟩
  unfold functional
  rw [← Finset.sum_erase_add (Finset.univ : Finset (ZMod N))
    (fun i ↦ x i / forwardDenominator N m s x i)
    (Finset.mem_univ ((N - 1 : ℕ) : ZMod N))]
  rw [hlast, zero_div, add_zero]
  rw [sum_erase_lastCoordinate N (by omega)
    (fun i ↦ x i / forwardDenominator N m s x i)]
  exact Finset.sum_le_sum fun i _ ↦
    retained_summand_le_reduced N m hN (by omega) hmN s hs x hx i

end Yamagami
