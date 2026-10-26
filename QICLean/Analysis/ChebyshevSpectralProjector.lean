/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ChebyshevFilter
import QICLean.Analysis.ViableSubspaceSpectralProjector

/-!
# The Chebyshev filter as a spectral projector

Arad, Landau, Vazirani and Vidick (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition
`def:Cheby-AGSP` and Theorem `thm:Cheby-AGSP`, items 1–3, lines 789–853) apply the normalized
Chebyshev polynomial `p` of degree `n` to the Hamiltonian. For a self-adjoint `H` with spectrum
below `u`, the operator `K = p(H)` has the eigenvectors of `H`, eigenvalues of `H` at most `a`
give eigenvalues of `K` at least `1`, and eigenvalues of `H` in `[b, u]` give eigenvalues of `K`
of modulus at most `2 exp (-2 n √((b - a)/(u - a)))`. In the language of
`Submodule.IsSpectralProjector`, `K` is a spectral projector for `(H, a, b)` with parameter
`Δ = (2 exp (-2 n √((b - a)/(u - a))))²`, relative to the eigenbasis of `H`.

This is the input that Lemma `l:er` (`Submodule.IsViable.spectralProjector`) needs from the
Chebyshev construction; the tensor decomposition of `K` is a separate statement. Positivity of
`K` is not claimed: the unsquared normalized filter need not be positive semidefinite (see
`docs/paper-gaps/alvv16_chebyshev_filter_positivity.tex`), and `IsSpectralProjector` does not
require it.

## Main statements

* `ContinuousLinearMap.aeval_map_apply_of_apply_eq_smul`: a real polynomial in `H` acts on an
  eigenvector of `H` with real eigenvalue `μ` by `p(μ)`.
* `Submodule.isSpectralProjector_aeval`: a real polynomial with the scalar filter properties
  gives a spectral projector.
* `Submodule.exists_isSpectralProjector_chebyshev`: the Chebyshev filter of degree `n`.
-/

open Polynomial Module
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

namespace ContinuousLinearMap

omit [FiniteDimensional 𝕜 E] in
/-- A real polynomial in `H` acts on an eigenvector with real eigenvalue `μ` by `p(μ)`. The
polynomial is applied through its image in `𝕜[X]`. -/
theorem aeval_map_apply_of_apply_eq_smul (H : E →L[𝕜] E) {μ : ℝ} {v : E}
    (hv : H v = (μ : 𝕜) • v) (p : ℝ[X]) :
    aeval H (p.map (algebraMap ℝ 𝕜)) v = ((p.eval μ : ℝ) : 𝕜) • v := by
  have hpow : ∀ m : ℕ, (H ^ m) v = ((μ : 𝕜) ^ m) • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ']
      change H ((H ^ m) v) = _
      rw [ih, map_smul, hv, smul_smul, pow_succ, mul_comm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.map_add, map_add, add_apply, hp, hq, eval_add, RCLike.ofReal_add, add_smul]
  | monomial m a =>
    rw [Polynomial.map_monomial, aeval_monomial]
    change (algebraMap 𝕜 (E →L[𝕜] E) (algebraMap ℝ 𝕜 a)) ((H ^ m) v) = _
    rw [hpow, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self, smul_smul,
      eval_monomial, RCLike.ofReal_mul, RCLike.ofReal_pow, RCLike.algebraMap_eq_ofReal]

end ContinuousLinearMap

namespace Submodule

/-- **A real polynomial as a spectral projector.** Let `H` be self-adjoint with eigenbasis `b`
and eigenvalues `h`. If a real polynomial satisfies `1 ≤ p(t)` for `t ≤ η₀` and `p(t) ^ 2 ≤ Δ`
for the eigenvalues `t ≥ η₁`, then `p(H)` is a spectral projector for `(H, η₀, η₁)` with
parameter `Δ`, with eigenvalues `p (h j)`. -/
theorem isSpectralProjector_aeval {m : ℕ} (H : E →L[𝕜] E)
    (hH : (H : E →ₗ[𝕜] E).IsSymmetric) (hn : finrank 𝕜 E = m) (p : ℝ[X]) {η₀ η₁ Δ : ℝ}
    (hlow : ∀ t : ℝ, t ≤ η₀ → 1 ≤ p.eval t)
    (hhigh : ∀ j, η₁ ≤ hH.eigenvalues hn j → (p.eval (hH.eigenvalues hn j)) ^ 2 ≤ Δ) :
    IsSpectralProjector (aeval H (p.map (algebraMap ℝ 𝕜))) H (hH.eigenvectorBasis hn)
      (hH.eigenvalues hn) (fun j => p.eval (hH.eigenvalues hn j)) η₀ η₁ Δ where
  apply_H j := hH.apply_eigenvectorBasis hn j
  apply_K j := H.aeval_map_apply_of_apply_eq_smul (hH.apply_eigenvectorBasis hn j) p
  one_le _ hj := hlow _ hj
  sq_le j hj := hhigh j hj

/-- **The Chebyshev filter as a spectral projector** (arXiv:1602.08828v2, Theorem
`thm:Cheby-AGSP`, items 1–3, lines 789–853). Let `H` be self-adjoint with all eigenvalues at most
`u`, and let `a < b ≤ u`. For every degree `n` there is a real polynomial `p` of degree `n` with
`p(a) = 1` such that `p(H)` is a spectral projector for `(H, a, b)` with parameter
`(2 exp (-2 n √((b - a)/(u - a))))²`. -/
theorem exists_isSpectralProjector_chebyshev {m : ℕ} (H : E →L[𝕜] E)
    (hH : (H : E →ₗ[𝕜] E).IsSymmetric) (hn : finrank 𝕜 E = m) (n : ℕ) {a b u : ℝ}
    (hab : a < b) (hbu : b ≤ u) (hupper : ∀ j, hH.eigenvalues hn j ≤ u) :
    ∃ p : ℝ[X], p.natDegree = n ∧ p.eval a = 1 ∧
      IsSpectralProjector (aeval H (p.map (algebraMap ℝ 𝕜))) H (hH.eigenvectorBasis hn)
        (hH.eigenvalues hn) (fun j => p.eval (hH.eigenvalues hn j)) a b
        ((2 * Real.exp (-2 * (n : ℝ) * Real.sqrt ((b - a) / (u - a)))) ^ 2) := by
  obtain ⟨p, hdeg, hpa, hleft, hbound⟩ :=
    Polynomial.Chebyshev.exists_interval_shrinking_polynomial n hab hbu
  refine ⟨p, hdeg, hpa, isSpectralProjector_aeval H hH hn p hleft fun j hj => ?_⟩
  have h := hbound _ ⟨hj, hupper j⟩
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

end Submodule
