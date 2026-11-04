/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.FiniteSumPowers
import QICLean.Analysis.SpectralProjectorPower

/-!
# Actual operator words in powers of a tensor decomposition

A finite decomposition of an improving operator gives its actual powered
family by taking ordered products of the retained factors. The same order
is used in the environment factors. No commutativity of the summands is
required. The low spectral target is fixed before the power and the viable
input space. This supports ALVV, arXiv:1602.08828v2, `def:spectral-AGSP`,
lines 570–581, and `l:er`, lines 597–622.
-/

open scoped BigOperators TensorProduct

namespace TensorProduct

variable {𝕜 M R : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R]

/-- Ordered simultaneous products of the two factors give the actual
product of tensor operators. Supporting ALVV, arXiv:1602.08828v2,
`def:spectral-AGSP`, lines 570–581. -/
lemma prod_mapL_ofFn {ι : Type*} (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (r : ℕ) (w : Fin r → ι) :
    (List.ofFn (fun j ↦ mapL (A (w j)) (B (w j)))).prod =
      mapL (List.ofFn (fun j ↦ A (w j))).prod (List.ofFn (fun j ↦ B (w j))).prod := by
  induction r with
  | zero => simp [← ContinuousLinearMap.coe_inj]
  | succ r ih =>
    simp only [List.ofFn_succ, List.prod_cons, ih, mapL_mul]

/-- The actual power of a finite tensor sum is decomposed by its ordered
operator words. Empty alphabets and exponent zero are included. Supporting
ALVV, arXiv:1602.08828v2, `def:spectral-AGSP`, lines 570–581,
and `l:er`, lines 597–622. -/
lemma pow_sum_mapL_eq_sum_words {ι : Type*} [Fintype ι]
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R) (r : ℕ) :
    (∑ i, mapL (A i) (B i)) ^ r =
      ∑ w : Fin r → ι,
        mapL (List.ofFn (fun j ↦ A (w j))).prod (List.ofFn (fun j ↦ B (w j))).prod := by
  rw [Fintype.sum_pow_eq_sum_ordered_words]
  exact Finset.sum_congr rfl fun w _ ↦ prod_mapL_ofFn A B r w

end TensorProduct

namespace Submodule

variable {𝕜 M R ι n : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]
  [Fintype ι] [Fintype n]

/-- The actual finite operator-word family improves viability for the same
fixed low spectral target, with cardinality raised to the power and squared
suppression `Delta ^ r`. Supporting ALVV, arXiv:1602.08828v2,
`def:spectral-AGSP`, lines 570–581, and `l:er`, lines 597–622. -/
lemma IsSpectralProjector.viability_word_power
    {K H : M ⊗[𝕜] R →L[𝕜] M ⊗[𝕜] R}
    {b : OrthonormalBasis n 𝕜 (M ⊗[𝕜] R)} {h k : n → ℝ}
    {eta0 eta1 Delta : ℝ}
    (hK : IsSpectralProjector K H b h k eta0 eta1 Delta)
    (hgap : ∀ j, h j ≤ eta0 ∨ eta1 ≤ h j) (hDelta : 0 ≤ Delta)
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (hdec : K = ∑ i, TensorProduct.mapL (A i) (B i)) (r : ℕ) :
    let T := span 𝕜 (b '' {j | h j ≤ eta0})
    ∀ (S : Submodule 𝕜 M) (delta : ℝ), IsViable delta S T → delta < 1 →
      let grow := ⨆ w : Fin r → ι,
        S.map ((List.ofFn (fun j ↦ A (w j))).prod : M →ₗ[𝕜] M)
      Module.finrank 𝕜 grow ≤ Fintype.card ι ^ r * Module.finrank 𝕜 S ∧
        IsViable (Delta ^ r / (1 - delta) ^ 2) grow T := by
  intro T S delta hS hdelta grow
  have hpower : K ^ r = ∑ w : Fin r → ι,
      TensorProduct.mapL (List.ofFn (fun j ↦ A (w j))).prod
        (List.ofFn (fun j ↦ B (w j))).prod := by
    rw [hdec, TensorProduct.pow_sum_mapL_eq_sum_words]
  obtain ⟨hKT, hKTo, hlow, hhigh⟩ := (hK.pow r).contract hgap
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    hS.map_of_tensor_decomposition
      (fun w : Fin r → ι ↦ (List.ofFn (fun j ↦ A (w j))).prod)
      (fun w : Fin r → ι ↦ (List.ofFn (fun j ↦ B (w j))).prod)
      hpower hdelta (pow_nonneg hDelta r) hKT hKTo hlow hhigh

end Submodule
