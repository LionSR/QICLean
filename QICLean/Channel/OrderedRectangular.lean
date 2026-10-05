/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausCPTP

/-!
# Ordered intervals of rectangular channels

An interval composes the actual maps between its successive matrix spaces. Its endpoints
are natural numbers, so adjoining intervals compose without identifying different matrix
spaces. The empty interval is the identity on its actual endpoint space.

## References

* Wolf, *Quantum Channels & Operations*, Chapter 2, composition of quantum channels.
-/

namespace Matrix

variable {D : ℕ → ℕ}

/-- Composition of the maps from the right endpoint of `[a,b)` to its left endpoint. -/
noncomputable def channelInterval
    (E : ∀ i, Matrix (Fin (D (i + 1))) (Fin (D (i + 1))) ℂ →ₗ[ℂ]
      Matrix (Fin (D i)) (Fin (D i)) ℂ)
    (a b : ℕ) (h : a ≤ b) :
    Matrix (Fin (D b)) (Fin (D b)) ℂ →ₗ[ℂ] Matrix (Fin (D a)) (Fin (D a)) ℂ :=
  Nat.leRecOn (C := fun i => Matrix (Fin (D i)) (Fin (D i)) ℂ →ₗ[ℂ]
    Matrix (Fin (D a)) (Fin (D a)) ℂ) h
      (fun {i} T => T.comp (E i)) LinearMap.id

variable (E : ∀ i, Matrix (Fin (D (i + 1))) (Fin (D (i + 1))) ℂ →ₗ[ℂ]
  Matrix (Fin (D i)) (Fin (D i)) ℂ)

@[simp] theorem channelInterval_self (a : ℕ) :
    channelInterval E a a le_rfl = LinearMap.id :=
  Nat.leRecOn_self _

/-- Appending the rightmost site appends its transfer on the right of the composition. -/
theorem channelInterval_succ {a b : ℕ} (h : a ≤ b) :
    channelInterval E a (b + 1) (Nat.le_succ_of_le h) =
      (channelInterval E a b h).comp (E b) :=
  Nat.leRecOn_succ h _

/-- Adjacent actual intervals compose in their original order. -/
theorem channelInterval_comp {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (channelInterval E a b hab).comp (channelInterval E b c hbc) =
      channelInterval E a c (hab.trans hbc) := by
  induction hbc with
  | refl => simp
  | @step c hbc ih =>
    rw [channelInterval_succ E hbc, ← LinearMap.comp_assoc, ih,
      channelInterval_succ E (hab.trans hbc)]

@[simp] theorem channelInterval_single (a : ℕ) :
    channelInterval E a (a + 1) (Nat.le_succ a) = E a := by
  rw [channelInterval_succ E le_rfl, channelInterval_self, LinearMap.id_comp]

/-- Peeling the leftmost site preserves the order of the actual interval. -/
theorem channelInterval_succ_left {a b : ℕ} (h : a + 1 ≤ b) :
    (E a).comp (channelInterval E (a + 1) b h) =
      channelInterval E a b ((Nat.le_succ a).trans h) := by
  simpa only [channelInterval_single] using channelInterval_comp E (Nat.le_succ a) h

/-- Shifting every site and cut by the same offset shifts the selected interval. -/
theorem channelInterval_shift (k : ℕ) {a b : ℕ} (h : a ≤ b) :
    channelInterval (D := fun i => D (k + i)) (fun i => E (k + i)) a b h =
      channelInterval E (k + a) (k + b) (Nat.add_le_add_left h k) := by
  induction h with
  | refl => simp
  | @step b h ih =>
    rw [channelInterval_succ (D := fun i => D (k + i)) (fun i => E (k + i)) h, ih]
    exact (channelInterval_succ E (Nat.add_le_add_left h k)).symm

/-- Complete positivity is preserved through an interval of changing matrix spaces. -/
theorem channelInterval_isKrausCP {a b : ℕ} (h : a ≤ b)
    (hE : ∀ i, a ≤ i → i < b → IsKrausCP (E i)) :
    IsKrausCP (channelInterval E a b h) := by
  revert hE
  induction h with
  | refl =>
    intro _
    simpa using (isKrausCPTP_id (α := Fin (D a))).isKrausCP
  | @step b h ih =>
    intro hE
    rw [channelInterval_succ E h]
    exact isKrausCP_comp (hE b h (Nat.lt_succ_self b))
      (ih fun i hai hib => hE i hai (Nat.lt_succ_of_lt hib))

/-- Trace preservation and complete positivity hold on every actual interval. -/
theorem channelInterval_isKrausCPTP {a b : ℕ} (h : a ≤ b)
    (hE : ∀ i, a ≤ i → i < b → IsKrausCPTP (E i)) :
    IsKrausCPTP (channelInterval E a b h) := by
  revert hE
  induction h with
  | refl =>
    intro _
    simpa using (isKrausCPTP_id (α := Fin (D a)))
  | @step b h ih =>
    intro hE
    rw [channelInterval_succ E h]
    exact isKrausCPTP_comp (hE b h (Nat.lt_succ_self b))
      (ih fun i hai hib => hE i hai (Nat.lt_succ_of_lt hib))

end Matrix
