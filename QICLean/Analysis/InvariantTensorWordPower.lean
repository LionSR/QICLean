/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.InvariantOperatorBounds
import QICLean.Analysis.TensorOperatorPower

/-!
# Actual operator words from invariant-subspace bounds

A fixed tensor decomposition and target/complement bounds imply every
ordered-word error-reduction estimate for the same operator and target.
No common spectral eigenbasis, positivity or scalar action on the target
is required. This supports ALVV, arXiv:1602.08828v2,
Lemma l:er, lines 597–622, under a change of regional coordinates.
-/

open scoped BigOperators TensorProduct

namespace Submodule
variable {𝕜 M R ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]

/-- The actual ordered words of one tensor decomposition improve viability
for every power and every viable input. The same operator supplies all
bounds; no spectral-projector or polynomial premise is added.
Supporting ALVV, arXiv:1602.08828v2, Lemma l:er, lines 597–622. -/
theorem IsViable.word_power_of_tensor_decomposition
    {T : Submodule 𝕜 (M ⊗[𝕜] R)} {Delta : ℝ}
    (K : M ⊗[𝕜] R →L[𝕜] M ⊗[𝕜] R)
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (hdec : K = ∑ i, TensorProduct.mapL (A i) (B i))
    (hDelta : 0 ≤ Delta)
    (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ z ∈ Tᗮ, K z ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ z ∈ Tᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2)
    (r : ℕ) (S : Submodule 𝕜 M) (delta : ℝ)
    (hS : IsViable delta S T) (hdelta : delta < 1) :
    let grow := ⨆ w : Fin r → ι,
      S.map ((List.ofFn (fun j ↦ A (w j))).prod : M →ₗ[𝕜] M)
    Module.finrank 𝕜 grow ≤ Fintype.card ι ^ r * Module.finrank 𝕜 S ∧
      IsViable (Delta ^ r / (1 - delta) ^ 2) grow T := by
  have hpower : K ^ r = ∑ w : Fin r → ι,
      TensorProduct.mapL (List.ofFn (fun j ↦ A (w j))).prod
        (List.ofFn (fun j ↦ B (w j))).prod := by
    rw [hdec, TensorProduct.pow_sum_mapL_eq_sum_words]
  obtain ⟨hT, hTo, hL, hH⟩ :=
    K.invariant_subspace_bounds_pow T Delta hDelta hKT hKTo hlow hhigh r
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    hS.map_of_tensor_decomposition
      (fun w : Fin r → ι ↦ (List.ofFn (fun j ↦ A (w j))).prod)
      (fun w : Fin r → ι ↦ (List.ofFn (fun j ↦ B (w j))).prod)
      hpower hdelta (pow_nonneg hDelta r) hT hTo hL hH

end Submodule
