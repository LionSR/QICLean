/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Rank-one matrix sandwiches

This file records the trace formula for sandwiching a matrix between two copies
of a rank-one matrix.
-/

open scoped Matrix BigOperators
open Matrix

namespace Matrix

/-- Closing a rank-one insertion between two matrices factorizes the boundary
contraction into the two single-matrix contractions. -/
theorem sandwich_mul_rankOne_mul {n : Type*} [Fintype n]
    (a b : n → ℂ) (A X : Matrix n n ℂ) :
    a ⬝ᵥ ((A * vecMulVec b a * X) *ᵥ b) =
      (a ⬝ᵥ (A *ᵥ b)) * (a ⬝ᵥ (X *ᵥ b)) := by
  simp only [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_mulVec, dotProduct_smul, Matrix.dotProduct_mulVec]
  simp [dotProduct, Finset.mul_sum, Finset.sum_mul]

/-- When adjacent factors of a nonempty list admit the rank-one insertion
`vecMulVec b a`, the boundary contraction of the list product is the product of
the individual boundary contractions. -/
theorem sandwich_listProd {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (P : Matrix n n ℂ → Prop)
    (hpair : ∀ A B, P A → P B → A * B = A * vecMulVec b a * B) :
    ∀ l : List (Matrix n n ℂ), l ≠ [] → (∀ A ∈ l, P A) →
      a ⬝ᵥ (l.prod *ᵥ b) =
        (l.map fun A ↦ a ⬝ᵥ (A *ᵥ b)).prod := by
  intro l hl hP
  induction l with
  | nil => exact (hl rfl).elim
  | cons A l ih =>
      cases l with
      | nil => simp
      | cons B l =>
          have hA : P A := hP A (by simp)
          have hB : P B := hP B (by simp)
          have htail : ∀ X ∈ B :: l, P X := by
            intro X hX
            exact hP X (by simp [hX])
          rw [List.prod_cons, List.prod_cons, ← Matrix.mul_assoc,
            hpair A B hA hB, Matrix.mul_assoc,
            sandwich_mul_rankOne_mul]
          change (a ⬝ᵥ (A *ᵥ b)) * (a ⬝ᵥ ((B :: l).prod *ᵥ b)) = _
          rw [ih (by simp) htail]
          simp

/-- The trace of a rank-one insertion between two matrices is the boundary
contraction of their cyclically rotated product. -/
theorem trace_mul_rankOne_mul {n : Type*} [Fintype n]
    (a b : n → ℂ) (A X : Matrix n n ℂ) :
    Matrix.trace (A * vecMulVec b a * X) = a ⬝ᵥ ((X * A) *ᵥ b) := by
  rw [Matrix.trace_mul_comm (A * vecMulVec b a) X, ← Matrix.mul_assoc,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, ← Matrix.mulVec_mulVec]
  simp [dotProduct, mul_comm]

/-- When adjacent factors of a list of length at least two admit the rank-one
insertion `vecMulVec b a`, the trace of the list product is the product of the
individual boundary contractions. -/
theorem trace_listProd {n : Type*} [Fintype n] [DecidableEq n]
    (a b : n → ℂ) (P : Matrix n n ℂ → Prop)
    (hpair : ∀ A B, P A → P B → A * B = A * vecMulVec b a * B)
    (l : List (Matrix n n ℂ)) (hl : 1 < l.length) (hP : ∀ A ∈ l, P A) :
    Matrix.trace l.prod = (l.map fun A ↦ a ⬝ᵥ (A *ᵥ b)).prod := by
  rcases l with _ | ⟨A, l⟩
  · simp at hl
  cases l with
  | nil => simp at hl
  | cons B l =>
      have hA : P A := hP A (by simp)
      have hB : P B := hP B (by simp)
      have hrot : ∀ X ∈ (B :: l) ++ [A], P X := by
        intro X hX
        apply hP X
        simp only [List.mem_append, List.mem_cons] at hX ⊢
        tauto
      rw [List.prod_cons, List.prod_cons, ← Matrix.mul_assoc,
        hpair A B hA hB, Matrix.mul_assoc, trace_mul_rankOne_mul]
      have hprod : ((B :: l) ++ [A]).prod = B * l.prod * A := by
        simp [Matrix.mul_assoc]
      rw [← hprod, sandwich_listProd a b P hpair _ (by simp) hrot]
      simp [mul_comm, mul_left_comm]

/-- Rank-one sandwiching is scalar multiplication by the corresponding trace. -/
theorem vecMulVec_mul_mul_vecMulVec_eq_trace_smul
    {n : Type*} [Fintype n] (ρ Φ : n → ℂ) (P : Matrix n n ℂ) :
    vecMulVec ρ Φ * P * vecMulVec ρ Φ =
      trace (P * vecMulVec ρ Φ) • vecMulVec ρ Φ := by
  classical
  have hscalar : (Φ ᵥ* P) ⬝ᵥ ρ = trace (P * vecMulVec ρ Φ) := by
    simp only [vecMul, dotProduct, trace, diag, mul_apply, vecMulVec_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, hscalar, vecMulVec_smul]

/-- A vanishing trace through a rank-one matrix gives a zero sandwich. -/
theorem vecMulVec_mul_mul_vecMulVec_eq_zero_of_trace
    {n : Type*} [Fintype n] (ρ Φ : n → ℂ) (P : Matrix n n ℂ)
    (hP : trace (P * vecMulVec ρ Φ) = 0) :
    vecMulVec ρ Φ * P * vecMulVec ρ Φ = 0 := by
  rw [vecMulVec_mul_mul_vecMulVec_eq_trace_smul, hP, zero_smul]

/-- A rank-one matrix sandwiches a matrix to zero when their mixed trace vanishes. -/
theorem rankOne_sandwich_eq_zero_of_trace
    {n : Type*} [Fintype n] (E P : Matrix n n ℂ) (ρ Φ : n → ℂ)
    (hE : E = vecMulVec ρ Φ) (htrace : trace (P * E) = 0) :
    E * P * E = 0 := by
  subst E
  exact vecMulVec_mul_mul_vecMulVec_eq_zero_of_trace ρ Φ P htrace

end Matrix
