/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Data.List.Rotate

/-!
# Induction on finite cyclic indices and on natural-number intervals

This file records an induction principle for a nonempty finite cyclic index, the reindexing of
statements about cyclically adjacent pairs, the action of one-step rotation on nonterminal
indices and on values modulo the length, and the constancy on a finite natural-number interval
of a function whose values agree at every pair of successive indices.

Moved from TNLean, `TNLean/Algebra/FinCyclicInduction.lean` and `TNLean/Algebra/NatInterval.lean`
at commit `49b78ed821` (Apache-2.0). Changes: the two files are merged.

## Main results

* `Fin.cyclic_induction`: a predicate holding at `0` and closed under `· + 1` holds everywhere.
* `Fin.forall_sub_one_iff`, `Fin.finRotate_succ_castSucc`, `coe_finRotate_mod`.
* `eq_of_forall_succ_eq_of_mem_Icc`: equality of any two values in the interval.

Moved from TNLean, `TNLean/MPS/Operator/DensityOperator/AreaLaw.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

/-- `finRotate` advances the value by one modulo `N`. -/
theorem coe_finRotate_mod {N : ℕ} (i : Fin N) :
    ((finRotate N) i : ℕ) = (i.val + 1) % N := by
  simp [Fin.add_def, finRotate_apply]

namespace Fin

/-- A predicate that holds at `0` and is closed under `· + 1` holds at every
index, because `+1` generates the cyclic group from `0`. Proved by induction on
`i.val`: the predecessor of a nonzero `i` is `⟨i.val - 1, _⟩`, whose successor
is `i`. -/
theorem cyclic_induction {m : ℕ} [NeZero m] {P : Fin m → Prop}
    (h0 : P 0) (hstep : ∀ i : Fin m, P i → P (i + 1)) (i : Fin m) : P i := by
  induction hi : i.val generalizing i with
  | zero => obtain rfl : i = 0 := Fin.ext (by simpa using hi); exact h0
  | succ k ih =>
    have hk : k < m := by have := i.isLt; omega
    have e : (⟨k, hk⟩ : Fin m) + 1 = i := by
      apply Fin.ext
      have hmod_one : 1 < m := by omega
      have hone : (1 : Fin m).val = 1 := by
        have : (1 : Fin m).val = 1 % m := Fin.val_one' m
        rw [this]; exact Nat.mod_eq_of_lt hmod_one
      rw [Fin.val_add, Fin.val_mk, hone, hi]
      exact Nat.mod_eq_of_lt (by have := i.isLt; omega)
    rw [← e]
    exact hstep _ (ih ⟨k, hk⟩ rfl)

/-- A statement about every pair `(j, j - 1)` of cyclically adjacent indices is the same
as the statement about every pair `(j + 1, j)`. -/
theorem forall_sub_one_iff {m : ℕ} [NeZero m] {P : Fin m → Fin m → Prop} :
    (∀ j, P j (j - 1)) ↔ ∀ j, P (j + 1) j :=
  ⟨fun h j => by simpa using h (j + 1), fun h j => by simpa using h (j - 1)⟩

/-- One-step rotation on `Fin (N + 1)` sends the nonterminal embedding of
`i : Fin N` to its ordinary successor. -/
lemma finRotate_succ_castSucc {N : ℕ} (i : Fin N) :
    finRotate (N + 1) i.castSucc = i.succ := by
  have h := finRotate_of_lt (n := N) i.isLt
  have e1 : (⟨(i : ℕ), i.isLt.trans_le N.le_succ⟩ : Fin (N + 1)) = i.castSucc := Fin.ext rfl
  have e2 : (⟨(i : ℕ) + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (N + 1)) = i.succ := Fin.ext rfl
  rw [e1, e2] at h
  exact h

end Fin

/-- A function on a finite interval is constant when it agrees at each pair of
successive indices. -/
theorem eq_of_forall_succ_eq_of_mem_Icc {α : Sort*} {a n i j : ℕ}
    (f : (m : ℕ) → m ≤ n → α)
    (hstep : ∀ m, a ≤ m → (hm : m < n) → f m hm.le = f (m + 1) hm)
    (hai : a ≤ i) (hin : i ≤ n) (haj : a ≤ j) (hjn : j ≤ n) :
    f i hin = f j hjn := by
  have climb : ∀ k m, a ≤ m → ∀ h : m + k ≤ n,
      f m (Nat.le_add_right m k |>.trans h) = f (m + k) h := by
    intro k
    induction k with
    | zero => intro m _ _; rfl
    | succ k ih =>
        intro m ham h
        have hmk : m + k < n := by
          apply Nat.lt_of_succ_le
          simpa [Nat.add_assoc] using h
        exact (ih m ham hmk.le).trans
          (hstep (m + k) (ham.trans (Nat.le_add_right m k)) hmk)
  rcases le_total i j with hij | hji
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact climb k i hai hjn
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hji
    exact (climb k j haj hin).symm

section

open scoped Matrix ComplexOrder BigOperators

open Matrix Finset

/-- `List.ofFn` precomposed with `finRotate` is the one-step list rotation. A
general fact about `List.ofFn`, `finRotate`, and `List.rotate`. -/
theorem ofFn_comp_finRotate {α : Type*} {n : ℕ} (σ : Fin (n + 1) → α) :
    List.ofFn (σ ∘ finRotate (n + 1)) = (List.ofFn σ).rotate 1 := by
  apply List.ext_getElem
  · simp
  · intro i h1 _
    simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_rotate,
      List.length_ofFn]
    congr 1
    have : finRotate (n + 1) ⟨i, by simpa using h1⟩
        = ⟨(i + 1) % (n + 1), Nat.mod_lt _ (Nat.succ_pos n)⟩ := by
      rw [finRotate_apply]; ext; simp [Fin.add_def]
    rw [this]

/-- The value of the `p`-fold cyclic shift is `(i + p) mod N`. -/
theorem coe_finRotate_pow {N : ℕ} (p : ℕ) (i : Fin N) :
    (((finRotate N : Fin N → Fin N)^[p]) i : ℕ) = (i.val + p) % N := by
  induction p with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', coe_finRotate_mod, ih, Nat.mod_add_mod, Nat.add_assoc]

end
