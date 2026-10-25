/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.WordCoefficientExpansion

/-! # Axiom check and empty-alphabet and zero-power applications -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped BigOperators

/-- info:
'Polynomial.coeff_pow_sum_smul_add_C_mul_X_eq_sum_counts'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.coeff_pow_sum_smul_add_C_mul_X_eq_sum_counts

-- With no ordinary letters and a positive ordinary degree, the frequency family is empty.
example : ((Polynomial.C (3 : ℂ) * Polynomial.X) ^ 2).coeff 1 = 0 := by
  simpa using Polynomial.coeff_pow_sum_smul_add_C_mul_X_eq_sum_counts
    (ι := Empty) (fun e ↦ nomatch e) (3 : ℂ) (fun e ↦ nomatch e) 1 1

-- The zero-power coefficient family sums to the identity in an arbitrary complex algebra.
open Classical in
example {ι R : Type*} [Fintype ι] [Semiring R] [Algebra ℂ R]
    (H : ι → R) (T : R) (z : ι → ℂ) :
    let E := Finset.piAntidiag (Finset.univ : Finset ι) 0
    (∑ a : E, (∏ j, z j ^ a.val j) •
      ∑ w ∈ (Finset.univ : Finset (Fin 0 → Option ι)).filter
          (fun w ↦ WordMultiplicity.countsFinsupp w none = 0 ∧
            ∀ j : ι, WordMultiplicity.countsFinsupp w (some j) = a.val j),
        (List.ofFn (fun p ↦ match w p with
          | none => T
          | some j => H j)).prod) = 1 := by
  simpa only [Nat.zero_add, pow_zero, Polynomial.coeff_one, ite_true,
    List.ofFn_zero, List.prod_nil] using
    (Polynomial.coeff_pow_sum_smul_add_C_mul_X_eq_sum_counts H T z 0 0).symm
