/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixGramUnitary
import QICLean.Channel.KrausCPTP

/-!
# Fixed pure-environment embeddings

A system is inserted into a designated basis coordinate of a finite environment.
The insertion is isometric, is natural under system operators, and every isometry
with the same domain extends to a joint unitary on this initialized subspace.

These generic operations are shared by open-system and Markov dilations. The public
`Matrix.fixedEnvEmbedding` name is retained from the Markov-dilation construction.
Source: Wolf, Quantum Channels and Operations, Theorem 2.5; Hayden–Jozsa–Petz–Winter,
arXiv:quant-ph/0304007, Appendix A, Theorem 10.
-/

open scoped Kronecker

namespace Matrix

/-- Insert a finite system into one fixed environment coordinate. -/
def fixedEnvEmbedding
    {S E : Type*} [DecidableEq S] [DecidableEq E] (e₀ : E) :
    Matrix (S × E) S ℂ :=
  fun se s => if se.2 = e₀ then (1 : Matrix S S ℂ) se.1 s else 0

/-- The fixed-environment insertion is an isometry. -/
theorem fixedEnvEmbedding_conjTranspose_mul_self
    {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
    (e₀ : E) :
    (fixedEnvEmbedding (S := S) e₀)ᴴ * fixedEnvEmbedding (S := S) e₀ = 1 := by
  ext s t
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  by_cases hst : s = t
  · subst t
    simp [fixedEnvEmbedding, Matrix.one_apply]
  · have hts : t ≠ s := fun h => hst h.symm
    simp [fixedEnvEmbedding, Matrix.one_apply, hst, hts]

theorem mul_fixedEnvEmbedding_apply
    {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E]
    (U : Matrix (S × E) (S × E) ℂ) (e₀ : E)
    (se : S × E) (s : S) :
    (U * fixedEnvEmbedding (S := S) e₀) se s = U se (s, e₀) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (s, e₀)]
  · simp [fixedEnvEmbedding]
  · rintro ⟨s', e'⟩ _ hne
    by_cases h : e' = e₀
    · subst e'
      have hs : s' ≠ s := by
        intro hs
        exact hne (Prod.ext hs rfl)
      simp [fixedEnvEmbedding, hs]
    · simp [fixedEnvEmbedding, h]
  · simp

/-- Fixed-environment insertion is natural for a system matrix. -/
theorem fixedEnvEmbedding_mul
    {S E : Type*} [Fintype S] [DecidableEq S]
    [Fintype E] [DecidableEq E]
    (e₀ : E) (A : Matrix S S ℂ) :
    fixedEnvEmbedding (S := S) e₀ * A =
      (A ⊗ₖ (1 : Matrix E E ℂ)) *
        fixedEnvEmbedding (S := S) e₀ := by
  ext se s
  rcases se with ⟨s', e⟩
  rw [mul_fixedEnvEmbedding_apply]
  by_cases he : e = e₀
  · subst e
    simp [fixedEnvEmbedding, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
  · simp [fixedEnvEmbedding, Matrix.mul_apply,
      Matrix.kroneckerMap_apply, he]

/-- Extend an isometry from a fixed pure environment input to a unitary on
the system and environment. -/
theorem exists_unitary_mul_fixedEnvEmbedding_eq
    {S E : Type*} [Fintype S] [DecidableEq S] [Fintype E] [DecidableEq E]
    (e₀ : E) (V : Matrix (S × E) S ℂ) (hV : Vᴴ * V = 1) :
    ∃ U : Matrix.unitaryGroup (S × E) ℂ,
      V = (U : Matrix (S × E) (S × E) ℂ) *
        fixedEnvEmbedding (S := S) e₀ := by
  apply Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
  rw [hV, fixedEnvEmbedding_conjTranspose_mul_self]

end Matrix
