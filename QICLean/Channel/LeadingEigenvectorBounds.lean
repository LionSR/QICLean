/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.LeadingEigenvector
import QICLean.Analysis.DominantEigenvectorUniqueness

/-!
# Bounds for every dominant eigenvector of a glued state

The energy and overlap bounds for a near-optimal left density matrix hold for every supplied
unit eigenvector whose eigenvalue exceeds one half. The existing existence theorem gives one
such vector, and phase uniqueness transfers its bounds to any other choice.

This is an auxiliary choice-independent form of Landau, Vazirani and Vidick,
arXiv:1307.5143v1, `algo53.tex`, Lemma `l:leading`, lines 493–505.
-/

open scoped Matrix Kronecker Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace Matrix

variable {a s r b : Type*} [Fintype a] [Fintype s] [Fintype r] [Fintype b]
  [DecidableEq a] [DecidableEq s] [DecidableEq r] [DecidableEq b]

/-- Every unit eigenvector of the left density matrix with eigenvalue larger than one half
satisfies the gluing energy and overlap bounds. Auxiliary choice-independent form of LVV13,
`algo53.tex`, Lemma `l:leading`, lines 493–505. -/
theorem leading_eigenvector_bounds_of_gluing (W : Matrix r b ℂ) (hW : Wᴴ * W = 1)
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
    (h4 : 4 * (e + ‖K‖ * τ) < Δ)
    (u : EuclideanSpace ℂ ((a × s) × b)) (μ : ℝ) (hu : ‖u‖ = 1)
    (huσ : σ *ᵥ WithLp.ofLp u = (μ : ℂ) • WithLp.ofLp u) (hμ : 1 / 2 < μ) :
    (⟪toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u,
        toEuclideanLin (HL ⊗ₖ (1 : Matrix r r ℂ) +
          reindex (Equiv.prodAssoc a s r).symm (Equiv.prodAssoc a s r).symm
            ((1 : Matrix a a ℂ) ⊗ₖ K))
          (toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u)⟫_ℂ).re ≤
      E₀ + 2 * (e + ‖K‖ * τ) ∧
    1 - 2 * (e + ‖K‖ * τ) / Δ ≤
      ‖⟪Γ, toEuclideanLin ((1 : Matrix (a × s) (a × s) ℂ) ⊗ₖ W) u⟫_ℂ‖ := by
  classical
  obtain ⟨v, ν, hv, hvσ, hν, hvE, hvov⟩ :=
    exists_leading_eigenvector_of_gluing W hW HL K hgap hΓ hΔ hσ htr x hopt hτ hw h4
  obtain ⟨-, z, hz, huz⟩ :=
    hσ.eigenvalue_eq_and_exists_unit_smul_of_gt_half htr hv hu hvσ huσ hν hμ
  have hphase : z * (starRingEnd ℂ) z = (1 : ℂ) := by
    simpa only [hz, one_pow, Complex.ofReal_one] using Complex.mul_conj' z
  constructor
  · simpa only [huz, map_smul, inner_smul_left, inner_smul_right, ← mul_assoc,
      hphase, one_mul] using hvE
  · simpa only [huz, map_smul, inner_smul_right, norm_mul, hz, one_mul] using hvov

end Matrix
