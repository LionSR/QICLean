/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ChoiJamiolkowski
import QICLean.Channel.KrausIterateChoi
import QICLean.Kraus.Injectivity
import Mathlib.Analysis.Matrix.Order

/-!
# Choi matrices of trace-factorized maps

For `T X = trace (L * X) • R`, the normalized Choi matrix is
`D⁻¹ • (R ⊗ₖ Lᵀ)`. If both factors are positive definite, this matrix is
positive definite. Consequently, any Kraus family representing `T` spans the
full matrix algebra.

The last implication supplies the full-support step in the proof of
Cirac–Pérez-García–Schuch–Verstraete, arXiv:1703.09188, Proposition IV.5,
lines 775–783. It requires neither trace preservation nor idempotence.
-/

open scoped Matrix Kronecker ComplexOrder

namespace ChoiJamiolkowski

/-- The normalized Choi matrix of a trace-factorized map is the tensor product
of its output matrix and the transpose of its input matrix, divided by the
matrix dimension. No positivity hypothesis is needed. -/
theorem choiMatrix_eq_kronecker_of_eq_trace_smul {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (L R : Matrix (Fin D) (Fin D) ℂ)
    (hT : ∀ X, T X = Matrix.trace (L * X) • R) :
    choiMatrix T = (D : ℂ)⁻¹ • (R ⊗ₖ Lᵀ) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [choiMatrix_apply, omegaSlice_eq_single, omegaCoeff_eq_inv (NeZero.pos D), hT]
  simp [Matrix.trace_mul_single, Matrix.kroneckerMap_apply, mul_comm, mul_left_comm,
    mul_assoc]

/-- Positive-definite trace factors give a positive-definite Choi matrix. -/
theorem choiMatrix_posDef_of_eq_trace_smul {D : ℕ} [NeZero D]
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (L R : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef) (hR : R.PosDef)
    (hT : ∀ X, T X = Matrix.trace (L * X) • R) :
    (choiMatrix T).PosDef := by
  rw [choiMatrix_eq_kronecker_of_eq_trace_smul T L R hT]
  exact (hR.kronecker hL.transpose).smul (by
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
      (Complex.zero_lt_real.mpr
        (inv_pos.mpr (Nat.cast_pos.mpr (NeZero.pos D)) : 0 < (D : ℝ)⁻¹)))

end ChoiJamiolkowski

namespace Kraus

/-- A Kraus family whose map has positive-definite trace factors spans the full
matrix algebra. This is the algebraic implication used in the full-support
step of CPSV17, arXiv:1703.09188, Proposition IV.5, lines 775–783. -/
theorem isInjective_of_mapLM_eq_trace_smul {d D : ℕ} [NeZero D]
    (A : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (L R : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef) (hR : R.PosDef)
    (hA : ∀ X, mapLM A X = Matrix.trace (L * X) • R) :
    IsInjective A := by
  simpa only [wordSpan_one, IsInjective] using
    (choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top A 1).mp
      (by simpa only [pow_one] using
            (ChoiJamiolkowski.choiMatrix_posDef_of_eq_trace_smul (mapLM A) L R hL hR hA))

end Kraus
