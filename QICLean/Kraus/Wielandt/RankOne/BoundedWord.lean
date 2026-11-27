/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Kraus.WordSpan
import QICLean.Spectral.Eigenvalue.NonzeroTraceEigenvalue
import QICLean.Kraus.Wielandt.SpanGrowth.NonzeroTraceProduct

/-!
# Bounded two-sided word spans

This file introduces the two-sided span

`biRectSpan P Q K n = span{ P * M * Q : M ∈ wordSpan K n }`

for a finite family of square matrices. If the exact word span is full, this
space is the full range of the map $X \mapsto PXQ$. If `P` and `Q` belong to
bounded word spans, every element of the two-sided span belongs to a bounded
word span.

## Main results

* `Kraus.exists_word_eigenvector`: eigenvectors from finite-family word products.
-/

open scoped Matrix

namespace Kraus

section BoundedWord

variable {d D : ℕ}

/-- The image of `wordSpan K n` under the map $X \mapsto PXQ$. -/
noncomputable def biRectSpan
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (n : ℕ) :
    Submodule ℂ (Matrix (Fin D) (Fin D) ℂ) :=
  Submodule.map ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q))
    (wordSpan K n)

/-- If the exact word span is full, the two-sided span is the full range of
$X \mapsto PXQ$. -/
theorem biRectSpan_eq_range_of_wordSpan_eq_top
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    (htop : wordSpan K n = ⊤) :
    biRectSpan P Q K n =
      LinearMap.range ((LinearMap.mulLeft ℂ P).comp (LinearMap.mulRight ℂ Q)) := by
  rw [biRectSpan, htop, Submodule.map_top]

private theorem mem_biRectSpan_iff
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {n : ℕ}
    {M : Matrix (Fin D) (Fin D) ℂ} :
    M ∈ biRectSpan P Q K n ↔
      ∃ X, X ∈ wordSpan K n ∧ P * X * Q = M := by
  constructor
  · intro hM
    rcases Submodule.mem_map.mp hM with ⟨X, hX, rfl⟩
    exact ⟨X, hX, by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Matrix.mul_assoc]⟩
  · rintro ⟨X, hX, hM⟩
    rw [← hM]
    exact Submodule.mem_map.mpr ⟨X, hX, by
      simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
        Matrix.mul_assoc]⟩

/-- If `P` and `Q` belong to word spans of lengths `m₁` and `m₂`, respectively,
then the two-sided span generated from words of length `n` lies in the word
span of length `m₁ + n + m₂`. -/
theorem biRectSpan_le_wordSpan
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {m₁ m₂ n : ℕ}
    (P Q : Matrix (Fin D) (Fin D) ℂ)
    (hP : P ∈ wordSpan K m₁) (hQ : Q ∈ wordSpan K m₂) :
    biRectSpan P Q K n ≤ wordSpan K (m₁ + n + m₂) := by
  intro M hM
  rcases (mem_biRectSpan_iff P Q K).mp hM with ⟨Y, hY, rfl⟩
  have hPY : P * Y ∈ wordSpan K (m₁ + n) := by
    rw [wordSpan_add]
    exact Submodule.mul_mem_mul hP hY
  rw [wordSpan_add]
  exact Submodule.mul_mem_mul hPY hQ

end BoundedWord

section Products

/-!
## Eigenvectors from finite-family word products

A full exact word span supplies a bounded word product with nonzero trace. Such a product has a
nonzero eigenvalue and a corresponding nonzero eigenvector.
-/

variable {d D : ℕ}

/-- If an exact word span is full, some word of length at most `D ^ 2` evaluates to a matrix with
a nonzero eigenvalue and a corresponding nonzero eigenvector.

The coarse length bound and exact-span hypothesis are inherited from
`exists_nonzero_trace_word`, where their relation to the paper is documented.

Paper: arXiv:0909.5347, Theorem 1 proof, first paragraph. -/
theorem exists_word_eigenvector [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) {N : ℕ}
    (hN : wordSpan K N = ⊤) :
    ∃ (w₀ : List (Fin d)) (μ : ℂ) (φ : Fin D → ℂ),
      w₀.length ≤ D ^ 2 ∧
      μ ≠ 0 ∧
      φ ≠ 0 ∧
      Kraus.evalWord K w₀ *ᵥ φ = μ • φ := by
  obtain ⟨w₀, hw₀_len, hw₀_tr⟩ := exists_nonzero_trace_word K hN
  obtain ⟨μ, φ, hμ, hφ, heig⟩ := exists_eigenvector_of_trace_ne_zero _ hw₀_tr
  exact ⟨w₀, μ, φ, hw₀_len, hμ, hφ, heig⟩

end Products

end Kraus
