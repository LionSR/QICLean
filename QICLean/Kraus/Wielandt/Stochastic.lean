/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Kraus.Stochastic
import QICLean.Channel.KrausIterateChoi
import QICLean.Channel.ChoiJamiolkowski
import QICLean.Kraus.Wielandt.Primitivity.VectorSpreadPositivity

/-!
# The classical positive-power criterion for stochastic Kraus words

For the matrix-unit embedding of a nonnegative classical matrix, the normalized
Choi matrix of every positive iterate is diagonal. Its entries are the entries
of the corresponding classical power divided by the state-space dimension.
Consequently, a positive length has full Kraus-word span precisely when the
classical power is strictly positive. The same criterion characterizes full
vector spreading at every nonzero input.

This proves the equality of the positive-length admissible sets behind
Proposition 2 of Sanz, Pérez-García, Wolf and Cirac, arXiv:0909.5347, lines
478–494. No primitivity, irreducibility or word-span witness is added as a
hypothesis to the fixed-length criteria.

## Main definitions

* `Matrix.positivePowerIndex`: the least positive length with a strictly positive
  matrix power, or zero if there is no such length.

## Main results

* `Kraus.stochasticFamily_choiMatrix_pow_succ`: the exact diagonal Choi matrix.
* `Kraus.stochasticFamily_wordSpan_succ_eq_top_iff`: the full-word-span criterion.
* `Kraus.stochasticFamily_vectorSpreadSpan_succ_iff`: the vector-spreading criterion.

## References

* Sanz, Pérez-García, Wolf and Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347, Proposition 2, source `main.tex`, lines 478–494.
-/

noncomputable section

open scoped Matrix BigOperators ComplexOrder

/-- The classical index `p(a)` from arXiv:0909.5347, Proposition 2, source lines
475–494. As with the quantum word indices, the empty admissible set has index zero. -/
def Matrix.positivePowerIndex {D : ℕ} (a : Matrix (Fin D) (Fin D) ℝ) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ∀ i j : Fin D, 0 < (a ^ n) i j}

namespace Kraus

variable {D : ℕ} [NeZero D]

/-- The normalized Choi matrix of a positive iterate of the stochastic embedding
is diagonal, with entry `(a^(n+1))ᵢⱼ/D` at output-input pair `(i,j)`.
Source: arXiv:0909.5347, Proposition 2, lines 478–494. -/
theorem stochasticFamily_choiMatrix_pow_succ (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (n : ℕ) :
    ChoiJamiolkowski.choiMatrix ((mapLM (stochasticFamily a)) ^ (n + 1)) =
      Matrix.diagonal (fun p : Fin D × Fin D ↦ ((a ^ (n + 1)) p.1 p.2 : ℂ) / D) := by
  ext p q
  rcases p with ⟨i, j⟩
  rcases q with ⟨k, l⟩
  rw [ChoiJamiolkowski.choiMatrix_apply, ChoiJamiolkowski.omegaSlice_eq_single,
    ChoiJamiolkowski.omegaCoeff_eq_inv (NeZero.pos D),
    stochasticFamily_mapLM_pow_succ a ha]
  by_cases hik : i = k <;> by_cases hjl : j = l <;>
    simp [Matrix.diagonal_apply, Matrix.single_apply, ite_and, hik, hjl,
      Prod.mk.injEq, div_eq_mul_inv, mul_comm]

/-- At every positive length, full exact-word span is equivalent to strict
positivity of the corresponding classical matrix power. Source:
arXiv:0909.5347, Proposition 2, lines 478–494. -/
theorem stochasticFamily_wordSpan_succ_eq_top_iff (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (n : ℕ) :
    wordSpan (stochasticFamily a) (n + 1) = ⊤ ↔
      ∀ i j : Fin D, 0 < (a ^ (n + 1)) i j := by
  rw [← choiMatrix_mapLM_pow_posDef_iff_wordSpan_eq_top,
    stochasticFamily_choiMatrix_pow_succ a ha, Matrix.posDef_diagonal_iff]
  have hD : (0 : ℝ) < D := by exact_mod_cast NeZero.pos D
  constructor
  · intro h i j
    have hquot : 0 < (a ^ (n + 1)) i j / (D : ℝ) := by
      exact_mod_cast h (i, j)
    have hmul := mul_pos hquot hD
    simpa only [div_mul_cancel₀ _ (ne_of_gt hD)] using hmul
  · intro h p
    exact_mod_cast div_pos (h p.1 p.2) hD

/-- At every positive length, spreading every nonzero vector is equivalent to
strict positivity of the classical power. Necessity tests the actual rank-one
coordinate states; sufficiency uses the full-word-span criterion.
Source: arXiv:0909.5347, Proposition 2, lines 478–494. -/
theorem stochasticFamily_vectorSpreadSpan_succ_iff (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (n : ℕ) :
    (∀ φ : Fin D → ℂ, φ ≠ 0 → vectorSpreadSpan (stochasticFamily a) φ (n + 1) = ⊤) ↔
      ∀ i j : Fin D, 0 < (a ^ (n + 1)) i j := by
  constructor
  · intro h i j
    let φ : Fin D → ℂ := Pi.single j 1
    have hφ : φ ≠ 0 := by
      intro hz
      have := congrFun hz j
      simp [φ] at this
    have hpd := mapLM_pow_rankOne_posDef_of_vectorSpreadSpan_eq_top
      (stochasticFamily a) h φ hφ
    rw [stochasticFamily_mapLM_pow_succ a ha] at hpd
    have hentry : (0 : ℂ) < ((a ^ (n + 1)) i j : ℂ) := by
      simpa [φ, Matrix.vecMulVec_apply, Pi.single_apply, ite_and] using
        hpd.diag_pos (i := i)
    exact_mod_cast hentry
  · intro h φ hφ
    exact vectorSpreadSpan_eq_top_of_wordSpan_eq_top (stochasticFamily a)
      ((stochasticFamily_wordSpan_succ_eq_top_iff a ha n).mpr h) φ hφ

end Kraus
