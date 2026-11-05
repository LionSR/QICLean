/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TensorOperatorPower
import QICLean.Analysis.ViableSubspaceOrder
import QICLean.Analysis.QuantitativeFilterIteration

/-!
# Untrimmed powers of an actual tensor-factor family

The energy-estimation space in ALVV is a separate powered family image,
without the intervening collective trims used for the retained viable set.
Uniform contraction and minimum target gain give geometrically decreasing
viability error for these literal images. This supports ALVV,
arXiv:1602.08828v2, Figure `fig:algo1`, line 1631, and the energy-estimation
argument at line 1807. Identification of the generated local soft operator
and the source's printed power count are separate conclusions.
-/

namespace Real

/-- A logarithmic power makes the existing untrimmed operator-word error
smaller than the requested accuracy. Auxiliary to ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and its energy-estimation argument at line 1807.
This is an explicit sufficient count, not an identification of the printed count. -/
theorem word_filter_error_ceil_log_le {delta Delta eta : ℝ}
    (hdelta : delta ≤ 1 / 2) (hDelta0 : 0 ≤ Delta) (hDelta : Delta ≤ 1 / 4)
    (heta0 : 0 < eta) :
    let n := ⌈4 * Real.log (4 / eta)⌉₊ + 1
    Delta ^ n / (1 - delta) ^ 2 ≤ eta := by
  intro n
  have hn : 4 * Real.log (4 / eta) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by dsimp only [n]; push_cast; linarith)
  have hlog : Real.log (eta / 4) = -Real.log (4 / eta) := by
    rw [Real.log_div (ne_of_gt heta0) (by norm_num),
      Real.log_div (by norm_num) (ne_of_gt heta0)]
    ring
  have hexp : Real.exp (-(1 / 4 : ℝ) * n) ≤ eta / 4 := by
    rw [← Real.exp_log (by positivity : 0 < eta / 4), Real.exp_le_exp, hlog]
    linarith only [hn]
  have hpow : Delta ^ n ≤ eta / 4 := by
    calc
      Delta ^ n ≤ (1 - (1 : ℝ) / 4) ^ n :=
        pow_le_pow_left₀ hDelta0 (by linarith only [hDelta]) n
      _ ≤ Real.exp (-(1 / 4 : ℝ) * n) :=
        filter_trim_contraction_pow_le_exp le_rfl n
      _ ≤ eta / 4 := hexp
  have hs : (1 / 4 : ℝ) ≤ (1 - delta) ^ 2 := by
    nlinarith only [hdelta, sq_nonneg (1 / 2 - delta)]
  apply (div_le_iff₀ (by linarith only [hs] : 0 < (1 - delta) ^ 2)).mpr
  nlinarith only [hpow, mul_le_mul_of_nonneg_left hs heta0.le]

end Real

open scoped TensorProduct InnerProductSpace

namespace Submodule

variable {𝕜 M R ι n : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]
  [Fintype ι] [Fintype n]

/-- The actual ordered-word image reaches arbitrary accuracy at an explicit
logarithmic power, with its actual dimension bound retained. The target and
factor family remain fixed. Supporting ALVV, arXiv:1602.08828v2,
Figure `fig:algo1`, line 1631, and the energy-estimation argument at line 1807.
The generated soft Hamiltonian and the printed power count are not identified here. -/
theorem IsSpectralProjector.viability_word_power_ceil_log
    {K H : M ⊗[𝕜] R →L[𝕜] M ⊗[𝕜] R}
    {b : OrthonormalBasis n 𝕜 (M ⊗[𝕜] R)} {h k : n → ℝ}
    {eta0 eta1 Delta : ℝ}
    (hK : IsSpectralProjector K H b h k eta0 eta1 Delta)
    (hgap : ∀ j, h j ≤ eta0 ∨ eta1 ≤ h j)
    (hDelta0 : 0 ≤ Delta) (hDelta : Delta ≤ 1 / 4)
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (hdec : K = ∑ i, TensorProduct.mapL (A i) (B i)) :
    let T := span 𝕜 (b '' {j | h j ≤ eta0})
    ∀ (S : Submodule 𝕜 M) (delta : ℝ), IsViable delta S T → delta ≤ 1 / 2 →
    ∀ eta : ℝ, 0 < eta →
    let power := ⌈4 * Real.log (4 / eta)⌉₊ + 1
    let grow := ⨆ w : Fin power → ι,
      S.map ((List.ofFn (fun j ↦ A (w j))).prod : M →ₗ[𝕜] M)
    Module.finrank 𝕜 grow ≤ Fintype.card ι ^ power * Module.finrank 𝕜 S ∧
      IsViable eta grow T := by
  intro T S delta hS hdelta eta heta power grow
  obtain ⟨hdim, hviable⟩ := hK.viability_word_power hgap hDelta0 A B hdec power
    S delta hS (by linarith only [hdelta])
  exact ⟨hdim, IsCloseTo.of_le hviable
    (Real.word_filter_error_ceil_log_le hdelta hDelta0 hDelta heta)⟩

end Submodule
