/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SourceContraction

/-! Boundary regressions for finite source contraction: no positions, an empty
source endpoint, two complex phases, and one corrected position. -/

open scoped BigOperators

-- No source positions leave the fixed coefficient matrix unchanged.
example (K : Matrix (Fin 2) (Fin 3) ℂ)
    (X : (p : Fin 0) → Matrix (Fin 1) (Fin 2) ℂ) :
    Matrix.sourceContraction (fun _ : (p : Fin 0) → Fin 1 × Fin 2 => K) X = K := by
  rw [Matrix.sourceContraction_apply]
  simp

-- An empty endpoint makes the actual coefficient contraction zero.
example (coeff : ((p : Fin 1) → Fin 0 × Fin 3) → Matrix (Fin 2) (Fin 1) ℂ)
    (X : (p : Fin 1) → Matrix (Fin 0) (Fin 3) ℂ) :
    Matrix.sourceContraction coeff X = 0 := by
  let : IsEmpty ((p : Fin 1) → Fin 0 × Fin 3) :=
    ⟨fun x => Fin.elim0 (x 0).1⟩
  rw [Matrix.sourceContraction_apply]
  simp

-- Ordinary source phases are multiplied, with no hidden bra conjugation.
example :
    Matrix.sourceContraction
      (fun _ : (p : Fin 2) → Fin 1 × Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (fun p => Matrix.of fun _ _ => if p = 0 then Complex.I else -Complex.I) 0 0 = 1 := by
  rw [Matrix.sourceContraction_apply_apply]
  simp [Fin.prod_univ_two, Complex.I_mul_I]

-- A correction at just the first position changes the result by -i.
example :
    (Matrix.sourceContraction
      (fun _ : (p : Fin 2) → Fin 1 × Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (fun p => Matrix.of fun _ _ => if p = 0 then Complex.I + 1 else -Complex.I) -
    Matrix.sourceContraction
      (fun _ : (p : Fin 2) → Fin 1 × Fin 1 => (1 : Matrix (Fin 1) (Fin 1) ℂ))
      (fun p => Matrix.of fun _ _ => if p = 0 then Complex.I else -Complex.I))
      0 0 = -Complex.I := by
  simp only [Matrix.sub_apply, Matrix.sourceContraction_apply_apply]
  simp [Fin.prod_univ_two, add_mul, Complex.I_mul_I]
