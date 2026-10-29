/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausMap
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Kraus embedding of a classical stochastic matrix

A nonnegative matrix `a` gives the matrix-unit Kraus letters
`Kᵢⱼ = √(aᵢⱼ) |i⟩⟨j|`. Their map erases off-diagonal entries and applies
`a` to the remaining diagonal. Column-stochasticity gives trace preservation.
Every positive iterate acts on a classical diagonal by the same power of `a`.

The letters are indexed by all ordered pairs, including letters with zero
coefficient. The number of these labels is not the linearly independent
Kraus count used in the quantitative Wielandt bound.

## Main definitions

* `Kraus.stochasticLetter`: one weighted matrix unit.
* `Kraus.stochasticFamily`: the pair-indexed family, reindexed by `Fin (D * D)`.

## Main results

* `Kraus.stochasticFamily_isTP`: column-stochasticity gives normalization.
* `Kraus.stochasticFamily_isChannel`: the actual family defines a quantum channel.
* `Kraus.stochasticFamily_mapLM`: the map on an arbitrary matrix.
* `Kraus.stochasticFamily_mapLM_diagonal`: the classical action on a real diagonal.
* `Kraus.stochasticFamily_mapLM_pow_succ_diagonal`: the classical action of positive iterates.

## References

* Sanz, Pérez-García, Wolf and Cirac, *A quantum version of Wielandt's inequality*,
  arXiv:0909.5347, Proposition 2 and its stochastic embedding, lines 460–494
  of the source `main.tex`.
-/

noncomputable section

open scoped Matrix BigOperators

namespace Kraus

variable {D : ℕ}

/-- The weighted matrix unit `√(aᵢⱼ)|i⟩⟨j|` in the classical embedding of
arXiv:0909.5347, Proposition 2, source lines 463–470. -/
def stochasticLetter (a : Matrix (Fin D) (Fin D) ℝ) (i j : Fin D) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.single i j (↑(Real.sqrt (a i j)) : ℂ)

/-- All matrix-unit Kraus letters of the stochastic embedding, including zero
letters, reindexed by a single finite alphabet. Source: arXiv:0909.5347,
Proposition 2, lines 463–470. -/
def stochasticFamily (a : Matrix (Fin D) (Fin D) ℝ) :
    Fin (D * D) → Matrix (Fin D) (Fin D) ℂ := fun k ↦
  stochasticLetter a (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

@[simp] theorem stochasticFamily_apply_pair (a : Matrix (Fin D) (Fin D) ℝ)
    (i j : Fin D) : stochasticFamily a (finProdFinEquiv (i, j)) = stochasticLetter a i j := by
  simp [stochasticFamily]

private theorem stochasticLetter_adj_mul (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (i j : Fin D) :
    (stochasticLetter a i j)ᴴ * stochasticLetter a i j =
      Matrix.single j j (a i j : ℂ) := by
  rw [stochasticLetter, Matrix.conjTranspose_single, Complex.star_def, Complex.conj_ofReal,
    Matrix.single_mul_single_same]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (ha i j)]

private theorem stochasticLetter_sandwich (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (X : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    stochasticLetter a i j * X * (stochasticLetter a i j)ᴴ =
      Matrix.single i i ((a i j : ℂ) * X j j) := by
  rw [stochasticLetter, Matrix.conjTranspose_single, Complex.star_def, Complex.conj_ofReal,
    Matrix.single_mul_mul_single]
  congr 1
  rw [mul_right_comm, ← Complex.ofReal_mul, Real.mul_self_sqrt (ha i j)]

/-- Column-stochastic matrices give the trace-preserving Kraus normalization.
The column convention agrees with `p' = a p` in arXiv:0909.5347, lines 463–470. -/
theorem stochasticFamily_isTP (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : a ∈ Matrix.colStochastic ℝ (Fin D)) : IsTP (stochasticFamily a) := by
  unfold IsTP
  rw [← finProdFinEquiv.sum_comp (fun k : Fin (D * D) ↦
    (stochasticFamily a k)ᴴ * stochasticFamily a k)]
  simp only [stochasticFamily_apply_pair, Fintype.sum_prod_type]
  simp_rw [stochasticLetter_adj_mul a (fun i j ↦ Matrix.nonneg_of_mem_colStochastic ha)]
  rw [Finset.sum_comm]
  calc
    ∑ j : Fin D, ∑ i : Fin D, Matrix.single j j (a i j : ℂ) =
        ∑ j : Fin D, Matrix.single j j (∑ i : Fin D, (a i j : ℂ)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact ((Matrix.singleAddMonoidHom j j).map_sum _ _).symm
    _ = ∑ j : Fin D, Matrix.single j j (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      exact_mod_cast Matrix.sum_col_of_mem_colStochastic ha j
    _ = 1 := Matrix.sum_single_one

/-- The normalized stochastic Kraus embedding is a quantum channel.
Source: arXiv:0909.5347, Proposition 2, lines 478–482. -/
theorem stochasticFamily_isChannel (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : a ∈ Matrix.colStochastic ℝ (Fin D)) : IsChannel (mapLM (stochasticFamily a)) :=
  isChannel_mapLM _ (stochasticFamily_isTP a ha)

/-- The embedded channel discards off-diagonal entries and applies the
classical matrix to the diagonal. Source: arXiv:0909.5347, lines 463–470. -/
theorem stochasticFamily_mapLM (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (X : Matrix (Fin D) (Fin D) ℂ) :
    mapLM (stochasticFamily a) X =
      Matrix.diagonal (fun i ↦ ∑ j : Fin D, (a i j : ℂ) * X j j) := by
  rw [mapLM_apply, map_apply, ← finProdFinEquiv.sum_comp (fun k : Fin (D * D) ↦
    stochasticFamily a k * X * (stochasticFamily a k)ᴴ)]
  simp only [stochasticFamily_apply_pair, Fintype.sum_prod_type]
  simp_rw [stochasticLetter_sandwich a ha]
  rw [← Matrix.sum_single_eq_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  exact ((Matrix.singleAddMonoidHom i i).map_sum _ _).symm

/-- Classical probability vectors evolve by `p ↦ a p` inside the actual
quantum channel. The identity holds for every real vector, without requiring
positivity of that vector. Source: arXiv:0909.5347, lines 463–470. -/
theorem stochasticFamily_mapLM_diagonal (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (p : Fin D → ℝ) :
    mapLM (stochasticFamily a) (Matrix.diagonal fun j ↦ (p j : ℂ)) =
      Matrix.diagonal (fun i ↦ ((a *ᵥ p) i : ℂ)) := by
  rw [stochasticFamily_mapLM a ha]
  congr 1
  funext i
  simp [Matrix.mulVec, Matrix.dotProduct]

/-- Every positive channel iterate acts on a classical diagonal by the same
classical matrix power. This is the iterate identity underlying Proposition 2
of arXiv:0909.5347, source lines 478–494. -/
theorem stochasticFamily_mapLM_pow_succ_diagonal (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (p : Fin D → ℝ) (n : ℕ) :
    ((mapLM (stochasticFamily a)) ^ (n + 1))
        (Matrix.diagonal fun j ↦ (p j : ℂ)) =
      Matrix.diagonal (fun i ↦ (((a ^ (n + 1)) *ᵥ p) i : ℂ)) := by
  induction n with
  | zero => simpa using stochasticFamily_mapLM_diagonal a ha p
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, stochasticFamily_mapLM_diagonal a ha]
      simp only [Matrix.mulVec_mulVec, ← pow_succ']

/-- On an arbitrary input matrix, every positive iterate discards its
off-diagonal entries and applies the corresponding classical power to the
diagonal. Source: arXiv:0909.5347, Proposition 2, lines 478–494. -/
theorem stochasticFamily_mapLM_pow_succ (a : Matrix (Fin D) (Fin D) ℝ)
    (ha : ∀ i j, 0 ≤ a i j) (X : Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    ((mapLM (stochasticFamily a)) ^ (n + 1)) X =
      Matrix.diagonal (fun i ↦ ∑ j : Fin D, ((a ^ (n + 1)) i j : ℂ) * X j j) := by
  induction n with
  | zero => simpa using stochasticFamily_mapLM a ha X
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, stochasticFamily_mapLM a ha]
      congr 1
      funext i
      simp only [Matrix.diagonal_apply_eq]
      rw [pow_succ' a (n + 1)]
      simp only [Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]

end Kraus
