/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.LowFrequencySelection

/-! # Axiom audit and boundary cases for local low-frequency choices -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped BigOperators

/-- info:
'Finset.exists_two_window_low_frequency_selectors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Finset.exists_two_window_low_frequency_selectors

-- Zero total frequency, with the same selectors for every global function.
example {ι : Type*} [Fintype ι] (L R : Finset ι)
    (hL : L.Nonempty) (hR : R.Nonempty) :
    ∃ pL : (↥L → ℕ) → ↥L, ∃ pR : (↥R → ℕ) → ↥R,
      ∀ f : ι → ℕ, (∑ a, f a) ≤ 0 →
        f (pL (fun a : ↥L ↦ f a)) = 0 ∧
        f (pR (fun a : ↥R ↦ f a)) = 0 := by
  obtain ⟨pL, pR, h⟩ := Finset.exists_two_window_low_frequency_selectors L R hL hR
  exact ⟨pL, pR, fun f hf ↦ by simpa using h f 0 hf⟩

-- Distinct singleton windows, and a nonzero frequency function of total seven.
example :
    let f : Fin 2 → ℕ := fun a ↦ if a = 0 then 3 else 4
    ∃ u : ↥({0} : Finset (Fin 2)), ∃ v : ↥({1} : Finset (Fin 2)),
      f u ≤ 7 ∧ f v ≤ 7 := by
  obtain ⟨pL, pR, h⟩ := Finset.exists_two_window_low_frequency_selectors
    ({0} : Finset (Fin 2)) {1} (by decide) (by decide)
  exact ⟨pL (fun a ↦ if a.val = 0 then 3 else 4),
    pR (fun a ↦ if a.val = 0 then 3 else 4),
    by simpa using h (fun a ↦ if a = 0 then 3 else 4) 7 (by decide)⟩

-- The two windows coincide. The nonzero total is six and each bound is three.
example :
    let f : Fin 2 → ℕ := fun a ↦ if a = 0 then 6 else 0
    ∃ u : ↥(Finset.univ : Finset (Fin 2)),
      ∃ v : ↥(Finset.univ : Finset (Fin 2)), f u ≤ 3 ∧ f v ≤ 3 := by
  obtain ⟨pL, pR, h⟩ := Finset.exists_two_window_low_frequency_selectors
    (Finset.univ : Finset (Fin 2)) Finset.univ (by decide) (by decide)
  exact ⟨pL (fun a ↦ if a.val = 0 then 6 else 0),
    pR (fun a ↦ if a.val = 0 then 6 else 0),
    by simpa using h (fun a ↦ if a = 0 then 6 else 0) 6 (by decide)⟩
