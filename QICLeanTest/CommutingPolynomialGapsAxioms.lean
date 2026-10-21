/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.CommutingPolynomialGaps
import QICLean.Algebra.OrderedPolynomialGaps
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! # Axiom checks and boundary applications for commuting-gap spans -/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped BigOperators

/-- info:
'Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps

/-- info:
'Finset.card_piAntidiag_univ_fin_prod_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Finset.card_piAntidiag_univ_fin_prod_bool

private def boundaryGapSpan {𝕜 R : Type*} [Semiring 𝕜] [Semiring R] [Module 𝕜 R]
    (A B T : R) (m k : ℕ) : Submodule 𝕜 R :=
  let E := Finset.piAntidiag
    (Finset.univ : Finset (Fin (k + 1) × Bool)) m
  Submodule.span 𝕜 (Set.range (fun d : E ↦
    (List.ofFn (fun j : Fin k ↦
      A ^ d.val (j.castSucc, false) * B ^ d.val (j.castSucc, true) * T)).prod *
      (A ^ d.val (Fin.last k, false) * B ^ d.val (Fin.last k, true))))

-- No distinguished letters: the original arbitrary power lies in the binomial span.
example {𝕜 R : Type*} [Semiring 𝕜] [Semiring R] [Module 𝕜 R]
    (A B T : R) (hAB : Commute A B) (m : ℕ) :
    (A + B) ^ m ∈ boundaryGapSpan (𝕜 := 𝕜) A B T m 0 := by
  simpa [boundaryGapSpan, Polynomial.coeff_zero_eq_eval_zero] using
    Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps (𝕜 := 𝕜) A B T hAB m 0

-- No ordinary letters: the unique all-zero gap tuple represents T^k, including k=0.
example {𝕜 R : Type*} [Semiring 𝕜] [Semiring R] [Module 𝕜 R]
    (A B T : R) (hAB : Commute A B) (k : ℕ) :
    T ^ k ∈ boundaryGapSpan (𝕜 := 𝕜) A B T 0 k := by
  have coeffTop :
      ((Polynomial.C (A + B) + Polynomial.C T * Polynomial.X) ^ k).coeff k = T ^ k := by
    simpa [Finset.Nat.antidiagonalTuple_zero_right] using
      Polynomial.coeff_pow_C_add_C_mul_X_eq_sum_gaps (A + B) T 0 k
  simpa only [boundaryGapSpan, Nat.zero_add, coeffTop] using
    Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps (𝕜 := 𝕜) A B T hAB 0 k

-- Two ordinary letters retain both contributions to AB.
example {𝕜 R : Type*} [Semiring 𝕜] [Semiring R] [Module 𝕜 R]
    (A B T : R) (hAB : Commute A B) :
    A ^ 2 + 2 * A * B + B ^ 2 ∈ boundaryGapSpan (𝕜 := 𝕜) A B T 2 0 := by
  simpa [boundaryGapSpan, Polynomial.coeff_zero_eq_eval_zero, hAB.add_sq] using
    Polynomial.coeff_pow_C_add_C_mul_X_mem_span_commuting_gaps (𝕜 := 𝕜) A B T hAB 2 0

-- All-zero gap exponents give exactly one tuple.
example (k : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin (k + 1) × Bool)) 0).card = 1 := by
  exact (Finset.card_piAntidiag_univ_fin_prod_bool 0 k).trans (by simp)

-- With no separator there are m+1 exponent pairs.
example (m : ℕ) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin 1 × Bool)) m).card = m + 1 := by
  simpa using Finset.card_piAntidiag_univ_fin_prod_bool m 0
