/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.DominantEigenvector
import QICLean.Analysis.IsometricDomainExtension
import QICLean.Channel.BoundaryGluing

/-!
# The leading eigenvector of a near-optimal left state

Fix a cut `(A ⊗ S) ⊗ R` and an isometry `W : ℂ^B → R`, and let
`H = H_L ⊗ 1 + 1 ⊗ K` with `H_L` on `A ⊗ S` and `K` on `S ⊗ R`. Let `H` have a ground vector
`Γ` with energy `E₀` and gap `Δ`. Let `w = (1 ⊗ W) x` have energy at most `E₀ + e`, and let
`σ` be a density matrix on `(A ⊗ S) ⊗ ℂ^B` whose left energy `tr(σ (H_L ⊗ 1))` is at most that
of the left state `x`, and whose boundary contraction is within trace distance `τ` of that of
`x`. If `4 (e + ‖K‖ τ) < Δ`, then `σ` has an eigenvalue larger than `1/2` whose unit
eigenvector `u` extends to `u' = (1 ⊗ W) u` with energy at most `E₀ + 2 (e + ‖K‖ τ)` and
overlap `|⟨Γ, u'⟩| ≥ 1 - 2 (e + ‖K‖ τ)/Δ`.

This is Lemma `l:leading` of Landau, Vazirani and Vidick. There, `x = ls(w)` is feasible for
the size-trimming program, so its minimizer `σ` has left energy at most that of `x`; the net
point is within `c_ε/(2n)` of `cont(w)` and the constraint keeps `σ` within `c_ε/(2n)` of it,
so `τ = c_ε/n`; with `‖K‖ ≤ n` and `e = 6√c_ε`, the energy bound is
`E₀ + 2(6√c_ε + c_ε) ≤ E₀ + 14√c_ε`.

## Main results

* `Matrix.trace_gluing_mul_kronecker_one`: `tr((1 ⊗ W) X (1 ⊗ W)* (H_L ⊗ 1)) = tr(X (H_L ⊗ 1))`.
* `Matrix.exists_leading_eigenvector_of_gluing`: the leading eigenvector.

## References

* Z. Landau, U. Vazirani, T. Vidick, *A polynomial-time algorithm for the ground state of
  1D gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`,
  lines 493–505.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace Matrix

variable {a s r b : Type*} [Fintype a] [Fintype s] [Fintype r] [Fintype b]
  [DecidableEq a] [DecidableEq s] [DecidableEq r] [DecidableEq b]

/-- Gluing does not change the energy of an operator acting on the left of the cut. -/
theorem trace_gluing_mul_kronecker_one (W : Matrix r b ℂ) (hW : Wᴴ * W = 1)
    (X : Matrix ((a × s) × b) ((a × s) × b) ℂ) (HL : Matrix (a × s) (a × s) ℂ) :
    (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) * X * ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W)ᴴ *
        (HL ⊗ₖ (1 : Matrix r r ℂ))).trace = (X * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace := by
  set J := (1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W
  have h : Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ)) * J = HL ⊗ₖ (1 : Matrix b b ℂ) := by
    simp only [J, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, hW]
  calc (J * X * Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ))).trace
      = (J * (X * (Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ))))).trace := by simp only [Matrix.mul_assoc]
    _ = (X * (Jᴴ * (HL ⊗ₖ (1 : Matrix r r ℂ))) * J).trace := Matrix.trace_mul_comm _ _
    _ = (X * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace := by rw [← h]; simp only [Matrix.mul_assoc]

/-- **The leading eigenvector of a near-optimal left state** (Lemma `l:leading` of
arXiv:1307.5143v1, `algo53.tex`, lines 493–505). Let `W` be an isometry, `w = (1 ⊗ W) x`,
`H = H_L ⊗ 1 + 1 ⊗ K`, and let `H - E₀ ≥ Δ (1 - |Γ⟩⟨Γ|)` with `‖Γ‖ = 1` and `Δ > 0`. Suppose
`⟨w, H w⟩ ≤ E₀ + e`, and that the density matrix `σ` satisfies
`tr(σ (H_L ⊗ 1)) ≤ tr(|x⟩⟨x| (H_L ⊗ 1))` and `‖tr_A σ - tr_A |x⟩⟨x|‖₁ ≤ τ`. If
`4 (e + ‖K‖ τ) < Δ`, then `σ` has a unit eigenvector `u` with eigenvalue larger than `1/2`
such that `u' = (1 ⊗ W) u` has energy at most `E₀ + 2 (e + ‖K‖ τ)` and
`|⟨Γ, u'⟩| ≥ 1 - 2 (e + ‖K‖ τ)/Δ`. -/
theorem exists_leading_eigenvector_of_gluing (W : Matrix r b ℂ) (hW : Wᴴ * W = 1)
    (HL : Matrix (a × s) (a × s) ℂ) (K : Matrix (s × r) (s × r) ℂ)
    {E₀ Δ e τ : ℝ} {Γ : EuclideanSpace ℂ ((a × s) × r)}
    (hgap : (HL ⊗ₖ (1 : Matrix r r ℂ) +
        reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
          ((1 : Matrix a a ℂ) ⊗ₖ K) - (E₀ : ℂ) • 1 -
      (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Γ) (star (WithLp.ofLp Γ)))).PosSemidef)
    (hΓ : ‖Γ‖ = 1) (hΔ : 0 < Δ)
    {σ : Matrix ((a × s) × b) ((a × s) × b) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (x : (a × s) × b → ℂ)
    (hopt : (σ * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re ≤
      (vecMulVec x (star x) * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace.re)
    (hτ : rectangularTraceNorm
      (partialTraceFirst σ - partialTraceFirst (vecMulVec x (star x))) ≤ τ)
    (hw : (vecMulVec (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)
        (star (((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) *ᵥ x)) *
      (HL ⊗ₖ (1 : Matrix r r ℂ) +
        reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
          ((1 : Matrix a a ℂ) ⊗ₖ K))).trace.re ≤ E₀ + e)
    (h4 : 4 * (e + ‖K‖ * τ) < Δ) :
    ∃ (u : EuclideanSpace ℂ ((a × s) × b)) (μ : ℝ), ‖u‖ = 1 ∧
      σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u ∧ 1 / 2 < μ ∧
      (⟪toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u,
          toEuclideanLin (HL ⊗ₖ (1 : Matrix r r ℂ) +
            reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
              ((1 : Matrix a a ℂ) ⊗ₖ K))
            (toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u)⟫_ℂ).re ≤
        E₀ + 2 * (e + ‖K‖ * τ) ∧
      1 - 2 * (e + ‖K‖ * τ) / Δ ≤
        ‖⟪Γ, toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u⟫_ℂ‖ := by
  classical
  set J := (1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W with hJdef
  set Hf := HL ⊗ₖ (1 : Matrix r r ℂ) +
    reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
      ((1 : Matrix a a ℂ) ⊗ₖ K) with hHf
  set e' := e + ‖K‖ * τ
  have hJJ : Jᴴ * J = 1 := by
    rw [hJdef, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
      hW, one_kronecker_one]
  set σ' := J * σ * Jᴴ
  have hσ' : σ'.PosSemidef := hσ.mul_mul_conjTranspose_same J
  have htr' : σ'.trace = 1 := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, htr]
  -- The energy of the glued state.
  have hglue := re_trace_gluing_le W hW σ x HL K
  have hK0 : 0 ≤ ‖K‖ := norm_nonneg K
  have hxv : (vecMulVec x (star x) * (HL ⊗ₖ (1 : Matrix b b ℂ))).trace =
      (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) * (HL ⊗ₖ (1 : Matrix r r ℂ))).trace := by
    have hv : vecMulVec (J *ᵥ x) (star (J *ᵥ x)) = J * vecMulVec x (star x) * Jᴴ := by
      rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_conjTranspose, star_star]
    rw [hv, trace_gluing_mul_kronecker_one W hW]
  have henergy : (σ' * Hf).trace.re ≤ E₀ + e' := by
    have hsplit : (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) * Hf).trace.re =
        (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) * (HL ⊗ₖ (1 : Matrix r r ℂ))).trace.re +
          (vecMulVec (J *ᵥ x) (star (J *ᵥ x)) *
            reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
              ((1 : Matrix a a ℂ) ⊗ₖ K)).trace.re := by
      rw [hHf, Matrix.mul_add, trace_add, Complex.add_re]
    rw [← hxv] at hsplit
    have := mul_le_mul_of_nonneg_left hτ hK0
    simp only [σ', e'] at hglue ⊢
    linarith
  obtain ⟨v', μ, hv'1, hv'eig, hμ, hv'E, hv'ov⟩ :=
    hσ'.exists_eigenvector_of_re_trace_mul_le htr' hgap hΓ hΔ henergy h4
  -- The eigenvector lies in the range of `J`, and `u = Jᴴ v'` is an eigenvector of `σ`.
  have hμ0 : (μ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : μ ≠ 0)
  have heig : σ' *ᵥ WithLp.ofLp v' = (μ : ℂ) • WithLp.ofLp v' := by
    have h := congrArg WithLp.ofLp hv'eig
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, WithLp.ofLp_smul] using h
  set y := WithLp.ofLp v'
  have hrange : J *ᵥ (Jᴴ *ᵥ y) = y := by
    have hy : y = J *ᵥ ((μ : ℂ)⁻¹ • (σ *ᵥ (Jᴴ *ᵥ y))) := by
      rw [mulVec_smul, mulVec_mulVec, mulVec_mulVec]
      change y = (μ : ℂ)⁻¹ • (σ' *ᵥ y)
      rw [heig, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    conv_rhs => rw [hy]
    conv_lhs => rw [hy]
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  set u : EuclideanSpace ℂ ((a × s) × b) := WithLp.toLp 2 (Jᴴ *ᵥ y)
  have hJu : toEuclideanLin J u = v' := by
    rw [← (WithLp.ofLp_injective 2).eq_iff]
    simp only [toLpLin_apply, WithLp.ofLp_toLp, u]
    exact hrange
  have hnorm : ‖toEuclideanLin J u‖ = ‖u‖ := by
    simpa only [toLpLin_apply] using norm_toLp_mulVec_of_isometry J hJJ u
  refine ⟨u, μ, ?_, ?_, hμ, ?_, ?_⟩
  · rw [← hnorm, hJu, hv'1]
  · have h : Jᴴ *ᵥ (σ' *ᵥ y) = σ *ᵥ (Jᴴ *ᵥ y) := by
      rw [mulVec_mulVec, mulVec_mulVec, show σ' = J * σ * Jᴴ from rfl, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    simp only [u]
    rw [← h, heig, mulVec_smul]
  · rwa [hJu]
  · rwa [hJu]

end Matrix
