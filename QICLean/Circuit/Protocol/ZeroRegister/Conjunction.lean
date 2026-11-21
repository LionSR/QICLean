/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Permutation
import QICLean.Algebra.FinCastAddNatAdd
import QICLean.ManyBody.Sites.Support

/-!
# Reversible conjunction of zero tests

A register of `a` data sites of dimension `d` is followed by `a` scratch sites. At step `j`
a controlled increment adds `1` to the scratch site `j` when the data site `j` is `0` and,
except at the first step, the preceding scratch site is `1`. The increment does not read the
site it changes, so each step is a permutation of all configurations of the `a + a` sites, it
changes and reads at most three sites, and its inverse is defined on every input. Starting
with the scratch register at `0`, after `k ≤ a` steps the data are unchanged, the scratch site
`j < k` holds `1` exactly when the data sites `0, …, j` are all `0`, and the remaining
scratch sites are still `0`. This is the reversible conjunction of the initialized-register
reflection.

The declarations restate the algebra of `TNLean/Circuit/ZeroRegisterConjunction.lean`
(Apache-2.0). The changes: the controlled increment is defined directly as a permutation of
configurations instead of through a general shift of one site; the locality of a step is the
membership of its permutation matrix in the operators supported on its three sites instead of
a predicate on permutations; the clean action is stated for one length `k ≤ a`. The gate
counts of the steps and of the whole network are not restated here.

## Main definitions

* `QuantumCircuit.zeroPrefixTest`, `QuantumCircuit.zeroPrefixBit` — the test that the first
  `k` data sites are `0`, and its value in the levels `0`, `1`.
* `QuantumCircuit.zeroConjunctionIncrement` — the increment read by step `j`.
* `QuantumCircuit.zeroConjunctionStep` — the controlled increment of step `j`.
* `QuantumCircuit.zeroConjunctionPerm` — the composite of the first `k` steps.
* `QuantumCircuit.zeroConjunctionState` — the configuration after `k` steps on clean scratch.
* `QuantumCircuit.zeroConjunctionStepSites` — the sites read and changed by step `j`.

## Main results

* `QuantumCircuit.zeroPrefixBit_eq_one` — the encoded test is `1` exactly when it holds.
* `QuantumCircuit.zeroConjunctionStep_state` — one step advances the invariant.
* `QuantumCircuit.zeroConjunctionPerm_apply_clean` — the first `k` steps on clean scratch.
* `QuantumCircuit.zeroConjunctionPerm_apply_clean_last_eq_one_iff` — after all steps the last
  scratch site is `1` exactly when the data are `0`.
* `QuantumCircuit.permMatrix_zeroConjunctionStep_mem_supportedOperators`,
  `QuantumCircuit.card_zeroConjunctionStepSites_le` — a step acts on at most three sites.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {d a : ℕ}

/-- All data sites before the cutoff `k` are `0`. -/
def zeroPrefixTest [NeZero d] (x : Fin a → Fin d) (k : ℕ) : Prop :=
  ∀ i : Fin a, i.val < k → x i = 0

/-- The value of the prefix zero test, encoded in the levels `0` and `1`. -/
noncomputable def zeroPrefixBit [NeZero d] (x : Fin a → Fin d) (k : ℕ) : Fin d := by
  classical
  exact if zeroPrefixTest x k then 1 else 0

/-- The preceding scratch site; at the first step it is the site itself and is not read. -/
def zeroConjunctionPrev (j : Fin a) : Fin a :=
  ⟨j.val - 1, (Nat.sub_le _ _).trans_lt j.isLt⟩

variable [NeZero d]

/-- The increment of step `j`: `1` when the data site `j` is `0` and either `j = 0` or the
preceding scratch site is `1`, and `0` otherwise. -/
def zeroConjunctionIncrement (j : Fin a) (z : Fin (a + a) → Fin d) : Fin d :=
  if z (Fin.castAdd a j) = 0 ∧ (j.val = 0 ∨ z (Fin.natAdd a (zeroConjunctionPrev j)) = 1)
  then 1 else 0

/-- The increment of step `j` does not read the scratch site `j` it changes. -/
theorem zeroConjunctionIncrement_update (j : Fin a) (z : Fin (a + a) → Fin d) (c : Fin d) :
    zeroConjunctionIncrement j (Function.update z (Fin.natAdd a j) c) =
      zeroConjunctionIncrement j z := by
  by_cases hj : j.val = 0
  · simp only [zeroConjunctionIncrement, Function.update_of_ne (Fin.castAdd_ne_natAdd j j), hj,
      true_or, and_true]
  · have hprev : Fin.natAdd a (zeroConjunctionPrev j) ≠ Fin.natAdd a j :=
      (Fin.natAdd_injective a a).ne fun h ↦ by
        have hval := congrArg Fin.val h
        simp only [zeroConjunctionPrev] at hval
        omega
    simp only [zeroConjunctionIncrement, Function.update_of_ne (Fin.castAdd_ne_natAdd j j),
      Function.update_of_ne hprev]

/-- The controlled increment of step `j`: the increment is added to the scratch site `j`. It
is a permutation of all configurations, inverted by subtracting the increment. -/
def zeroConjunctionStep (j : Fin a) : Equiv.Perm (Fin (a + a) → Fin d) where
  toFun z := Function.update z (Fin.natAdd a j) (z (Fin.natAdd a j) + zeroConjunctionIncrement j z)
  invFun z :=
    Function.update z (Fin.natAdd a j) (z (Fin.natAdd a j) - zeroConjunctionIncrement j z)
  left_inv z := by
    simp only [zeroConjunctionIncrement_update, Function.update_idem, Function.update_self,
      add_sub_cancel_right, Function.update_eq_self]
  right_inv z := by
    simp only [zeroConjunctionIncrement_update, Function.update_idem, Function.update_self,
      sub_add_cancel, Function.update_eq_self]

theorem zeroConjunctionStep_apply (j : Fin a) (z : Fin (a + a) → Fin d) :
    zeroConjunctionStep j z =
      Function.update z (Fin.natAdd a j) (z (Fin.natAdd a j) + zeroConjunctionIncrement j z) :=
  rfl

/-- The composite of the first `k` controlled increments, applied in the order of the steps;
steps beyond the register are absent. -/
def zeroConjunctionPerm : ℕ → Equiv.Perm (Fin (a + a) → Fin d)
  | 0 => 1
  | k + 1 => if h : k < a then zeroConjunctionStep ⟨k, h⟩ * zeroConjunctionPerm k
      else zeroConjunctionPerm k

/-- The configuration after the first `k` steps on clean scratch: the data `x` are kept, the
scratch site `j < k` holds the test of the data sites `0, …, j`, and the other scratch sites
are `0`. -/
noncomputable def zeroConjunctionState (x : Fin a → Fin d) (k : ℕ) : Fin (a + a) → Fin d :=
  Fin.append x fun j ↦ if j.val < k then zeroPrefixBit x (j.val + 1) else 0

private theorem zeroPrefixTest_succ (x : Fin a → Fin d) (j : Fin a) :
    zeroPrefixTest x (j.val + 1) ↔ zeroPrefixTest x j.val ∧ x j = 0 := by
  constructor
  · intro h
    exact ⟨fun i hi ↦ h i (by omega), h j (by omega)⟩
  · rintro ⟨h, hj⟩ i hi
    by_cases hij : i = j
    · simpa [hij] using hj
    · exact h i (by have := Fin.val_injective.ne hij; omega)

/-- For `d ≥ 2` the encoded prefix test is `1` exactly when the test holds. -/
theorem zeroPrefixBit_eq_one (hd : 2 ≤ d) (x : Fin a → Fin d) (k : ℕ) :
    zeroPrefixBit x k = 1 ↔ zeroPrefixTest x k := by
  have hone : (1 : Fin d) ≠ 0 := by
    rw [Ne, Fin.one_eq_zero_iff]
    omega
  classical
  by_cases h : zeroPrefixTest x k <;> simp [zeroPrefixBit, h, hone.symm]

private theorem zeroConjunctionIncrement_state (hd : 2 ≤ d) (x : Fin a → Fin d) (j : Fin a) :
    zeroConjunctionIncrement j (zeroConjunctionState x j.val) = zeroPrefixBit x (j.val + 1) := by
  classical
  have hcond : (j.val = 0 ∨
      (if (zeroConjunctionPrev j).val < j.val then
        zeroPrefixBit x ((zeroConjunctionPrev j).val + 1) else 0) = 1) ↔
      zeroPrefixTest x j.val := by
    by_cases hj : j.val = 0
    · simp [hj, zeroPrefixTest]
    · have hlt : (zeroConjunctionPrev j).val < j.val := by
        dsimp [zeroConjunctionPrev]
        omega
      have hsucc : (zeroConjunctionPrev j).val + 1 = j.val := by
        dsimp [zeroConjunctionPrev]
        omega
      simp [hj, hlt, hsucc, zeroPrefixBit_eq_one hd]
  simp only [zeroConjunctionIncrement, zeroConjunctionState, Fin.append_left, Fin.append_right]
  have hiff : (x j = 0 ∧ (j.val = 0 ∨
      (if (zeroConjunctionPrev j).val < j.val then
        zeroPrefixBit x ((zeroConjunctionPrev j).val + 1) else 0) = 1)) ↔
      zeroPrefixTest x (j.val + 1) := by
    rw [hcond, zeroPrefixTest_succ]
    exact and_comm
  rw [zeroPrefixBit]
  exact if_congr hiff rfl rfl

/-- Each controlled increment advances the conjunction invariant by one step. -/
theorem zeroConjunctionStep_state (hd : 2 ≤ d) (x : Fin a → Fin d) (j : Fin a) :
    zeroConjunctionStep j (zeroConjunctionState x j.val) =
      zeroConjunctionState x (j.val + 1) := by
  funext p
  rw [zeroConjunctionStep_apply, zeroConjunctionIncrement_state hd]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) p
  · rw [Function.update_of_ne (Fin.castAdd_ne_natAdd i j)]
    simp only [zeroConjunctionState, Fin.append_left]
  · by_cases hij : i = j
    · subst i
      rw [Function.update_self]
      simp only [zeroConjunctionState, Fin.append_right, lt_self_iff_false,
        Nat.lt_succ_self, ite_false, ite_true, zero_add]
    · have hsites : Fin.natAdd a i ≠ Fin.natAdd a j := (Fin.natAdd_injective a a).ne hij
      have hcut : i.val < j.val ↔ i.val < j.val + 1 := by
        have := Fin.val_injective.ne hij
        omega
      rw [Function.update_of_ne hsites]
      simp only [zeroConjunctionState, Fin.append_right, hcut]

/-- On every data configuration with clean scratch, the first `k ≤ a` controlled increments
compute the prefix tests of lengths `1, …, k`. -/
theorem zeroConjunctionPerm_apply_clean (hd : 2 ≤ d) (x : Fin a → Fin d) {k : ℕ}
    (hk : k ≤ a) : zeroConjunctionPerm k (Fin.append x 0) = zeroConjunctionState x k := by
  induction k with
  | zero =>
    simp only [zeroConjunctionPerm, Equiv.Perm.coe_one, id_eq, zeroConjunctionState,
      Nat.not_lt_zero, ite_false]
    rfl
  | succ k ih =>
    have hka : k < a := by omega
    simp only [zeroConjunctionPerm, hka, dite_true, Equiv.Perm.coe_mul, Function.comp_apply,
      ih (by omega)]
    exact zeroConjunctionStep_state hd x ⟨k, hka⟩

/-- On clean scratch, after all `a` steps the last scratch site is `1` exactly when every data
site is `0`. -/
theorem zeroConjunctionPerm_apply_clean_last_eq_one_iff (hd : 2 ≤ d) (ha : 0 < a)
    (x : Fin a → Fin d) :
    zeroConjunctionPerm a (Fin.append x 0) (Fin.natAdd a ⟨a - 1, by omega⟩) = 1 ↔
      ∀ i, x i = 0 := by
  have hsucc : a - 1 + 1 = a := by omega
  rw [zeroConjunctionPerm_apply_clean hd x le_rfl]
  simp only [zeroConjunctionState, Fin.append_right, Fin.isLt, ite_true, hsucc,
    zeroPrefixBit_eq_one hd, zeroPrefixTest, true_implies]

/-- The sites read and changed by step `j`: the data site `j`, the preceding scratch site and
the scratch site `j`. -/
def zeroConjunctionStepSites (j : Fin a) : Finset (Fin (a + a)) :=
  {Fin.castAdd a j, Fin.natAdd a (zeroConjunctionPrev j), Fin.natAdd a j}

omit [NeZero d] in
/-- Step `j` acts on at most three sites. -/
theorem card_zeroConjunctionStepSites_le (j : Fin a) : (zeroConjunctionStepSites j).card ≤ 3 :=
  Finset.card_le_three

omit [NeZero d] in
/-- The permutation matrix of a permutation of configurations that changes only the sites of
`S`, by a rule reading only the sites of `S`, is supported on `S`. -/
private theorem permMatrix_mem_supportedOperators_of_local {m : ℕ} {S : Finset (Fin m)}
    (σ : Equiv.Perm (Fin m → Fin d)) (h₁ : ∀ x, ∀ i ∉ S, σ x i = x i)
    (h₂ : ∀ x y, (∀ j ∈ S, x j = y j) → ∀ i ∈ S, σ x i = σ y i) :
    σ.permMatrix ℂ ∈ supportedOperators (Qudits (Fin m) d) S := by
  have hone := one_mem (supportedOperators (Qudits (Fin m) d) S)
  have happly : ∀ x y : Fin m → Fin d, σ.permMatrix ℂ x y = (1 : Matrix _ _ ℂ) (σ x) y :=
    fun x y ↦ by
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, one_apply]
  refine ⟨fun x y ⟨v, hv, hne⟩ ↦ ?_, fun x y x' y' hx hy hxy hxy' ↦ ?_⟩
  · rw [happly, apply_eq_zero_of_mem_supportedOperators hone hv (by rwa [h₁ x v hv])]
  · rw [happly, happly]
    exact (mem_supportedOperators_iff.mp hone).2 _ _ _ _ (h₂ x x' hx) hy
      (fun i hi ↦ by rw [h₁ x i hi, hxy i hi]) fun i hi ↦ by rw [h₁ x' i hi, hxy' i hi]

/-- The permutation matrix of step `j` is supported on the sites of the step. -/
theorem permMatrix_zeroConjunctionStep_mem_supportedOperators (j : Fin a) :
    (zeroConjunctionStep (d := d) j).permMatrix ℂ ∈
      supportedOperators (Qudits (Fin (a + a)) d) (zeroConjunctionStepSites j) := by
  have ht : Fin.natAdd a j ∈ zeroConjunctionStepSites j := by simp [zeroConjunctionStepSites]
  refine permMatrix_mem_supportedOperators_of_local _ (fun x i hi ↦ ?_) fun x y hxy i hi ↦ ?_
  · rw [zeroConjunctionStep_apply, Function.update_of_ne (by rintro rfl; exact hi ht)]
  · have hinc : zeroConjunctionIncrement j x = zeroConjunctionIncrement j y := by
      simp only [zeroConjunctionIncrement,
        hxy (Fin.castAdd a j) (by simp [zeroConjunctionStepSites]),
        hxy (Fin.natAdd a (zeroConjunctionPrev j)) (by simp [zeroConjunctionStepSites])]
    rw [zeroConjunctionStep_apply, zeroConjunctionStep_apply]
    by_cases hit : i = Fin.natAdd a j
    · subst hit
      simp only [Function.update_self, hxy _ ht, hinc]
    · rw [Function.update_of_ne hit, Function.update_of_ne hit, hxy i hi]

end QuantumCircuit
