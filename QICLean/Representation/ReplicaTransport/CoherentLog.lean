/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Setup

/-!
# The logarithmic passage from a rank-one pin to every symmetric state

Let `X` be positive definite, commuting with copy permutations, with
`X ≥ e^{φ(θ)} P_{θ,k}` for every unit `θ`. Then for every density matrix `ρ` on `𝒮_k`,
`∫ φ dμ_ρ - log D_k ≤ Tr(ρ log X)`.

The source argument (area-law paper, proof of Proposition 7.4, `06-transport.tex`
lines 520--575): integrating the pin against Haar measure gives
`X ≥ D_k^{-1} 𝒬_k(e^φ)` on `𝒮_k`, where `𝒬_k(f) = D_k ∫ f(θ) P_{θ,k} dθ` is unital
(coherent-state resolution, `TensorPower.unitaryTwirl_coherentProj`); the block-matrix
inequality `𝒬_k(f)^{-1} ≤ 𝒬_k(f^{-1})` and the resolvent formula for `log` give the
operator Jensen inequality `log 𝒬_k(f) ≥ 𝒬_k(log f)` (display `transport:log-jensen`);
operator monotonicity of `log` concludes. Everything takes place on `𝒮_k`, where
`𝒬_k(1)` is the identity.

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory PermutationRepresentation

noncomputable section

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The coherent-state vector `U e_a` is continuous in `U`. -/
theorem continuous_coherentVec (a : Ω) :
    Continuous fun U : unitaryGroup Ω ℂ => (U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1 := by
  refine continuous_pi fun x => ?_
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun y _ => (continuous_unitary_apply Ω _ _).mul continuous_const

omit [Fintype Ω] [DecidableEq Ω] in
/-- The coherent projector `P_{θ,k}` depends continuously on `θ`. -/
theorem continuous_coherentProj {X : Type*} [TopologicalSpace X] (k : ℕ) {θ : X → Ω → ℂ}
    (hθ : Continuous θ) : Continuous fun x => coherentProj k (θ x) := by
  refine continuous_pi fun y => continuous_pi fun z => ?_
  simp only [coherentProj, vecMulVec_apply, tensorVec, Pi.star_apply, star_prod]
  fun_prop

/-- The integrand of a coherent average is Haar integrable. -/
theorem integrable_coherentIntegrand (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    Integrable (fun U : unitaryGroup Ω ℂ => (f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) : ℂ) •
      coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)) (unitaryHaar Ω) :=
  ((Complex.continuous_ofReal.comp (hf.comp (continuous_coherentVec a))).smul
    (continuous_coherentProj k (continuous_coherentVec a))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The coherent average `𝒬_k(f) = D_k ∫ f(θ) P_{θ,k} dθ` (`06-transport.tex` line 523). -/
def coherentAverage (k : ℕ) (a : Ω) (f : (Ω → ℂ) → ℝ) : Matrix (Fin k → Ω) (Fin k → Ω) ℂ :=
  (symDim Ω k : ℂ) • ∫ U, (f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) : ℂ) •
    coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) ∂(unitaryHaar Ω)

/-- Tracing a coherent average against `ρ` gives the coherent integral. -/
theorem trace_mul_coherentAverage (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) :
    (ρ * coherentAverage k a f).trace.re = coherentIntegral k a ρ f := by
  have hF := integrable_coherentIntegrand k a hf
  let L : Matrix (Fin k → Ω) (Fin k → Ω) ℂ →L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap ((Matrix.traceLinearMap _ ℂ ℂ) ∘ₗ LinearMap.mulLeft ℂ ρ)
  have hL : ∀ M, L M = (ρ * M).trace := fun M => rfl
  have hint : Integrable (fun U : unitaryGroup Ω ℂ => L ((f ((U : Matrix Ω Ω ℂ) *ᵥ
      Pi.single a 1) : ℂ) • coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)))
      (unitaryHaar Ω) := L.integrable_comp hF
  rw [coherentIntegral, coherentAverage, mul_smul_comm, trace_smul, ← hL,
    ← L.integral_comp_comm hF, smul_eq_mul, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
  congr 1
  rw [← RCLike.re_to_complex, ← integral_re hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [hL, mul_smul_comm, trace_smul, smul_eq_mul, RCLike.re_to_complex,
    Complex.re_ofReal_mul]

/-- **Operator Jensen inequality for the logarithm** (`06-transport.tex`, display
`transport:log-jensen`, lines 526--546), compressed to `𝒮_k`: for continuous `f > 0`,
`Π 𝒬_k(log f) Π ≤ Π log(𝒬_k(f) + (1 - Π)) Π`. -/
theorem coherentAverage_log_le (k : ℕ) (a : Ω) {f : (Ω → ℂ) → ℝ} (hf : Continuous f)
    (hpos : ∀ θ, 0 < f θ) :
    coherentAverage k a (fun θ => Real.log (f θ)) ≤
      symProj (copyPerm Ω k) *
        CFC.log (coherentAverage k a f + (1 - symProj (copyPerm Ω k))) *
          symProj (copyPerm Ω k) := by
  sorry

/-- **Logarithmic passage** (`06-transport.tex` lines 520--575): a rank-one pin
`X ≥ e^{φ(θ)} P_{θ,k}` for all unit `θ`, with `X` positive definite and commuting with copy
permutations, gives `∫ φ dμ_ρ - log D_k ≤ Tr(ρ log X)` for every density matrix `ρ`
on `𝒮_k`. -/
theorem coherentIntegral_sub_log_le_re_trace_mul_log {k : ℕ} (a : Ω)
    {X : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hX : X.PosDef)
    (hXc : ∀ s, Commute (permOp (copyPerm Ω k) s) X) {φ : (Ω → ℂ) → ℝ} (hφ : Continuous φ)
    (hpin : ∀ θ : Ω → ℂ, star θ ⬝ᵥ θ = 1 → Real.exp (φ θ) • coherentProj k θ ≤ X)
    {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hsym : symProj (copyPerm Ω k) * ρ = ρ) :
    coherentIntegral k a ρ φ - Real.log (symDim Ω k) ≤ (ρ * CFC.log X).trace.re := by
  sorry

/-- `D_k` is polynomial in `k`: `log D_k = O(log (k + 1))`. -/
theorem log_symDim_isBigO :
    (fun k : ℕ => Real.log (symDim Ω k)) =O[Filter.atTop] fun k : ℕ => Real.log (k + 1) := by
  sorry

end TensorPower
