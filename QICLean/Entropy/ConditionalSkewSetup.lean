/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcComplex
import QICLean.Channel.PartialTrace
import QICLean.Entropy.MarginalPhaseSetup

/-!
# The scalar function of the conditional skew estimate

Let `θ` be a vector on `P = P₀ P₁` and `W = (x U) F`, with marginals `ρ_P`, `ρ_W` and
`ρ_Y` (`Y = x U`), and let `h` be an operator on `P₀ x`.  The function of the conditional
skew estimate is
$$f(z)=\langle\theta,\rho_P^{[z]}\rho_Y^{[-z]}h\rho_P^{[-z]}\rho_Y^{[z]}\theta\rangle,$$
with powers vanishing on the kernels and every operator tensored with the identity on
the remaining factors.  This file sets up the lifts, the powers, the function, and the
facts that the support projections fix `θ`.

## Main definitions

* `Entropy.ConditionalSkew.margP`, `margW`, `margY`.
* `Entropy.ConditionalSkew.liftP`, `liftY`, `liftH`.
* `Entropy.ConditionalSkew.skewFun`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Lemma 5.3 (`lem:skew`),
  `04-conditional.tex`, lines 487–507.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.ConditionalSkew

open _root_.Matrix

variable {P₀ P₁ X U F : Type*} [Fintype P₀] [DecidableEq P₀] [Fintype P₁] [DecidableEq P₁]
  [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U] [Fintype F] [DecidableEq F]

/-- The power function `t ↦ t^z` vanishing at zero. -/
def suppPowFun (z : ℂ) (t : ℝ) : ℂ := if t = 0 then 0 else ((t : ℝ) : ℂ) ^ z

/-- The marginal `ρ_P` on `P = P₀ P₁`. -/
def margP (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix (P₀ × P₁) (P₀ × P₁) ℂ :=
  partialTraceRight (vecMulVec θ (star θ))

/-- The marginal `ρ_W` on `W = (x U) F`. -/
def margW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix ((X × U) × F) ((X × U) × F) ℂ :=
  partialTraceLeft (vecMulVec θ (star θ))

/-- The marginal `ρ_Y` on `Y = x U`. -/
def margY (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : Matrix (X × U) (X × U) ℂ :=
  partialTraceRight (margW θ)

theorem posSemidef_margP (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : (margP θ).PosSemidef :=
  (posSemidef_vecMulVec_self_star θ).partialTraceRight

theorem posSemidef_margW (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : (margW θ).PosSemidef :=
  (posSemidef_vecMulVec_self_star θ).partialTraceLeft

theorem posSemidef_margY (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) : (margY θ).PosSemidef :=
  (posSemidef_margW θ).partialTraceRight

/-- An operator on `P`, tensored with the identity on `W`. -/
def liftP (A : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  A ⊗ₖ (1 : Matrix ((X × U) × F) ((X × U) × F) ℂ)

/-- An operator on `Y = x U`, tensored with the identity on `P` and `F`. -/
def liftY (B : Matrix (X × U) (X × U) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  (1 : Matrix (P₀ × P₁) (P₀ × P₁) ℂ) ⊗ₖ (B ⊗ₖ (1 : Matrix F F ℂ))

/-- The regrouping `(P₀ P₁)((x U) F) → (P₀ x)(P₁ (U F))`. -/
def regroup (q : (P₀ × P₁) × ((X × U) × F)) : (P₀ × X) × (P₁ × (U × F)) :=
  ((q.1.1, q.2.1.1), (q.1.2, (q.2.1.2, q.2.2)))

/-- An operator on `P₀ x`, tensored with the identity on `P₁ U F`. -/
def liftH (h : Matrix (P₀ × X) (P₀ × X) ℂ) :
    Matrix ((P₀ × P₁) × ((X × U) × F)) ((P₀ × P₁) × ((X × U) × F)) ℂ :=
  (h ⊗ₖ (1 : Matrix (P₁ × (U × F)) (P₁ × (U × F)) ℂ)).submatrix regroup regroup

/-- The function `f(z) = ⟨θ, ρ_P^{[z]} ρ_Y^{[-z]} h ρ_P^{[-z]} ρ_Y^{[z]} θ⟩` of the
conditional skew estimate.  Area-law manuscript, `04-conditional.tex`, lines 495–500. -/
def skewFun (θ : (P₀ × P₁) × ((X × U) × F) → ℂ) (h : Matrix (P₀ × X) (P₀ × X) ℂ) (z : ℂ) : ℂ :=
  star θ ⬝ᵥ ((liftP (cfcC (margP θ) (suppPowFun z)) * liftY (cfcC (margY θ) (suppPowFun (-z))) *
    liftH h * liftP (cfcC (margP θ) (suppPowFun (-z))) *
    liftY (cfcC (margY θ) (suppPowFun z))) *ᵥ θ)

end Entropy.ConditionalSkew

end
