/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.LowFrequencyWordPartition

/-! # Axiom guard and boundary applications for the common word partition -/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Fintype.exists_two_window_word_coefficient_partition_of_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.exists_two_window_word_coefficient_partition_of_le

/-- info:
'Fintype.exists_two_window_word_coefficient_partition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Fintype.exists_two_window_word_coefficient_partition

open scoped BigOperators

-- The actual word coefficient family at zero power, for overlapping windows.
open Classical in
example {ι 𝓡 : Type*} [Fintype ι] [Semiring 𝓡]
    (W : Finset ι) (hW : W.Nonempty) (H : ι → 𝓡) :
    ∃ pickL : (↥W → ℕ) → ↥W, ∃ pickR : (↥W → ℕ) → ↥W,
      let k := 0
      let E := Finset.piAntidiag (Finset.univ : Finset ι) k
      let B := (W.product (Finset.range (k / W.card + 1))).product
        (W.product (Finset.range (k / W.card + 1)))
      let left : (ι → ℕ) → ↥W := fun a ↦ pickL (fun u : ↥W ↦ a u)
      let right : (ι → ℕ) → ↥W := fun a ↦ pickR (fun v : ↥W ↦ a v)
      let label : (ι → ℕ) → (ι × ℕ) × (ι × ℕ) := fun a ↦
        (((left a : ι), a (left a)), ((right a : ι), a (right a)))
      let coefficient : (ι → ℕ) → 𝓡 := fun a ↦
        ∑ w ∈ (Finset.univ : Finset (Fin k → ι)).filter
            (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a),
          (List.ofFn (fun p ↦ H (w p))).prod
      1 = ∑ t ∈ B, ∑ a ∈ E with label a = t, coefficient a := by
  obtain ⟨pickL, pickR, _, h⟩ :=
    Fintype.exists_two_window_word_coefficient_partition (𝓡 := 𝓡) W W hW hW
  exact ⟨pickL, pickR, by simpa only [pow_zero] using h H 0⟩

-- Identical windows and degree two, retaining both ordered products H(a)H(b).
open Classical in
example {ι 𝓡 : Type*} [Fintype ι] [Semiring 𝓡]
    (W : Finset ι) (hW : W.Nonempty) (H : ι → 𝓡) :
    ∃ pickL : (↥W → ℕ) → ↥W, ∃ pickR : (↥W → ℕ) → ↥W,
      let k := 2
      let E := Finset.piAntidiag (Finset.univ : Finset ι) k
      let B := (W.product (Finset.range (k / W.card + 1))).product
        (W.product (Finset.range (k / W.card + 1)))
      let left : (ι → ℕ) → ↥W := fun a ↦ pickL (fun u : ↥W ↦ a u)
      let right : (ι → ℕ) → ↥W := fun a ↦ pickR (fun v : ↥W ↦ a v)
      let label : (ι → ℕ) → (ι × ℕ) × (ι × ℕ) := fun a ↦
        (((left a : ι), a (left a)), ((right a : ι), a (right a)))
      let coefficient : (ι → ℕ) → 𝓡 := fun a ↦
        ∑ w ∈ (Finset.univ : Finset (Fin k → ι)).filter
            (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a),
          (List.ofFn (fun p ↦ H (w p))).prod
      (∑ b, ∑ a, H a * H b) = ∑ t ∈ B, ∑ a ∈ E with label a = t, coefficient a := by
  obtain ⟨pickL, pickR, _, h⟩ :=
    Fintype.exists_two_window_word_coefficient_partition (𝓡 := 𝓡) W W hW hW
  exact ⟨pickL, pickR, by simpa only [pow_two, Finset.sum_mul, Finset.mul_sum] using h H 2⟩
