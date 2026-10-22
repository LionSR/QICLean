/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.TwoMarkerWordCoefficients

/-! # Axiom guard and boundary cases for two distinguished word frequencies -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped BigOperators

/-- info:
'Polynomial.coeff_coeff_pow_two_markers_eq_sum_full_counts'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.coeff_coeff_pow_two_markers_eq_sum_full_counts

/- Boundary applications of the full-frequency coefficient identity. -/

open Classical in
example {ι 𝓡 : Type*} [Fintype ι] [Semiring 𝓡] [Algebra ℂ 𝓡]
    (H : ι → 𝓡) (u v : ι) (huv : u ≠ v) (z : ι → ℂ) (i j : ℕ) :
    let O := ((Finset.univ : Finset ι).erase u).erase v
    let E := Finset.piAntidiag (Finset.univ : Finset ι) 0
    let coefficient : (ι → ℕ) → 𝓡 := fun a ↦
      ∑ w ∈ (Finset.univ : Finset (Fin 0 → ι)).filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a),
        (List.ofFn (fun p ↦ H (w p))).prod
    (∑ a ∈ E with a u = i ∧ a v = j,
      (∏ b ∈ O, z b ^ a b) • coefficient a) =
        if i = 0 ∧ j = 0 then 1 else 0 := by
  classical
  have h := Polynomial.coeff_coeff_pow_two_markers_eq_sum_full_counts H u v huv z 0 i j
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simpa [pow_zero, Polynomial.coeff_one, hi, hj] using h.symm

-- Only the two distinguished labels remain; both orders survive.
open Classical in
example {ι 𝓡 : Type*} [Fintype ι] [Semiring 𝓡] [Algebra ℂ 𝓡]
    (H : ι → 𝓡) (u v : ι) (huv : u ≠ v)
    (hO : ((Finset.univ : Finset ι).erase u).erase v = ∅) :
    let E := Finset.piAntidiag (Finset.univ : Finset ι) 2
    (∑ a ∈ E with a u = 1 ∧ a v = 1,
      ∑ w ∈ (Finset.univ : Finset (Fin 2 → ι)).filter
          (fun w ↦ (WordMultiplicity.countsFinsupp w : ι → ℕ) = a),
        (List.ofFn (fun p ↦ H (w p))).prod) = H u * H v + H v * H u := by
  classical
  have h := Polynomial.coeff_coeff_pow_two_markers_eq_sum_full_counts
    H u v huv (fun _ ↦ 1) 2 1 1
  have hs :
      (((Polynomial.C (Polynomial.C (0 : 𝓡) + Polynomial.C (H v) * Polynomial.X) +
          Polynomial.C (Polynomial.C (H u)) * Polynomial.X) ^ 2).coeff 1).coeff 1 =
        H u * H v + H v * H u := by
    simp [pow_two, Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero, add_comm]
  exact Eq.trans (by
    simpa only [hO, Finset.sum_empty, Finset.prod_empty, one_smul] using h.symm) hs

-- Impossible distinguished frequencies give zero without a new premise on the main theorem.
open Classical in
example {ι 𝓡 : Type*} [Fintype ι] [Semiring 𝓡] [Algebra ℂ 𝓡]
    (H : ι → 𝓡) (u v : ι) (huv : u ≠ v)
    (z : ι → ℂ) (k i j : ℕ) (hbad : k < i + j) :
    let O := ((Finset.univ : Finset ι).erase u).erase v
    let D := ∑ a ∈ O, z a • H a
    let F : Polynomial (Polynomial 𝓡) :=
      Polynomial.C (Polynomial.C D + Polynomial.C (H v) * Polynomial.X) +
        Polynomial.C (Polynomial.C (H u)) * Polynomial.X
    ((F ^ k).coeff i).coeff j = 0 := by
  classical
  dsimp only
  rw [Polynomial.coeff_coeff_pow_two_markers_eq_sum_full_counts H u v huv z k i j]
  apply Finset.sum_eq_zero
  intro a ha
  rcases Finset.mem_filter.mp ha with ⟨haE, hai, haj⟩
  have hsum : (∑ b, a b) = k := (Finset.mem_piAntidiag.mp haE).1
  have htwo : a u + a v ≤ ∑ b, a b :=
    Finset.add_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ u)
      (Finset.mem_univ v) huv
  have hle : i + j ≤ k := by simpa only [hai, haj, hsum] using htwo
  exact ((Nat.not_le_of_gt hbad) hle).elim
