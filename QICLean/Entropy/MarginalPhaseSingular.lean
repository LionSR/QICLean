/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MarginalPhaseLimit
import QICLean.Entropy.ConditionalEntropy

/-!
# The marginal-phase comparison for arbitrary states

Let `ρ` be a density matrix on `x (U F)`, possibly singular, with `d = dim x` and
`η = I(x:F|U)_ρ`.  With kernel-completed phases,
$$\bigl\lVert\bigl((\hat\rho_U^{-iu}\hat\rho_{xU}^{iu})\otimes I_F
   -\hat\rho_{UF}^{-iu}\hat\rho_{xUF}^{iu}\bigr)\sqrt\rho\bigr\rVert_2
 \le2\,|\sinh\pi u|\,\mathcal R_\eta .$$
The proof applies the faithful case to `ρ_ε = (1 - ε) ρ + (ε / N) I` and lets `ε → 0`.
In the eigenbases of `ρ` and of its marginals all phases of `ρ_ε` and of its marginals
are explicit; off the kernels they converge, on the kernels they are common unimodular
scalars, and the support inclusions make the kernel parts vanish in the limit.

## Main results

* `Entropy.MarginalPhase.norm_phaseDifference_le`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Lemma 5.2
  (`lem:conditional-phases`), `04-conditional.tex`, lines 321–339; singular case of the
  proof, lines 456–478.
-/

open Filter Topology
open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.MarginalPhase

open _root_.Matrix

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- Tensoring with `I_x` on the left, as a linear map. -/
def oneKron : Matrix U U ℂ →ₗ[ℂ] Matrix (X × U) (X × U) ℂ where
  toFun M := (1 : Matrix X X ℂ) ⊗ₖ M
  map_add' A B := kronecker_add _ _ _
  map_smul' c A := by rw [kronecker_smul]; rfl

/-- The embedding `W ↦ W ⊗ I_F`, as a linear map. -/
def embedFLin : Matrix (X × U) (X × U) ℂ →ₗ[ℂ] Matrix (X × (U × F)) (X × (U × F)) ℂ where
  toFun := embedF
  map_add' := embedF_add
  map_smul' := embedF_smul

/-- The kernel-completed phase difference
`(ρ̂_U^{-iu} ρ̂_{xU}^{iu}) ⊗ I_F - ρ̂_{UF}^{-iu} ρ̂^{iu}`.  Area-law manuscript,
`04-conditional.tex`, line 332. -/
def phaseDifference {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} (hρ : ρ.PosSemidef) (u : ℝ) :
    Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  embedF (((1 : Matrix X X ℂ) ⊗ₖ hatPhase (posSemidef_marginalU hρ).1 (-u)) *
      hatPhase (posSemidef_marginalXU hρ).1 u) -
    ((1 : Matrix X X ℂ) ⊗ₖ hatPhase (posSemidef_marginalUF hρ).1 (-u)) * hatPhase hρ.1 u

/-- The affine functions of the approximation on `ρ`, `ρ_{xU}`, `ρ_U`, `ρ_{UF}`. -/
def affF (X U F : Type*) [Fintype X] [Fintype U] [Fintype F] (c : ℝ) (ε t : ℝ) : ℝ :=
  (1 - ε) * t + ε / Fintype.card (X × (U × F)) * c

/-- The phase family `t ↦ (affF c ε t) ^ z` in a fixed eigenbasis. -/
def phaseFam {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ} (hM : M.IsHermitian)
    (g : ℝ → ℝ) (z : ℂ) : Matrix n n ℂ :=
  spectralFun hM.eigenvectorUnitary (fun k => ((g (hM.eigenvalues k) : ℝ) : ℂ) ^ z)

section Bound

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ} (hρ : ρ.PosSemidef)

/-- The faithful bound at `ρ_ε`, written in the eigenbases of `ρ` and of its marginals. -/
theorem norm_approx_le [Nonempty X] [Nonempty U] [Nonempty F] (htr : ρ.trace = 1) (u : ℝ)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ‖(WithLp.toLp 2 (vec
        ((embedF (((1 : Matrix X X ℂ) ⊗ₖ phaseFam (posSemidef_marginalU hρ).1
              (affF X U F (Fintype.card F * Fintype.card X) ε) (-(u * Complex.I))) *
            phaseFam (posSemidef_marginalXU hρ).1 (affF X U F (Fintype.card F) ε)
              (u * Complex.I)) -
          ((1 : Matrix X X ℂ) ⊗ₖ phaseFam (posSemidef_marginalUF hρ).1
              (affF X U F (Fintype.card X) ε) (-(u * Complex.I))) *
            phaseFam hρ.1 (affF X U F 1 ε) (u * Complex.I)) *
          spectralFun hρ.1.eigenvectorUnitary
            (fun k => ((affF X U F 1 ε (hρ.1.eigenvalues k) ^ (1 / 2 : ℝ) : ℝ) : ℂ)))) :
        EuclideanSpace ℂ ((X × (U × F)) × (X × (U × F))))‖ ≤
      2 * |Real.sinh (Real.pi * u)| * phaseRate (Fintype.card X)
        (condMutualInfo (approx ρ ε) (posDef_approx hρ h0 h1).posSemidef) := by
  have hpd := posDef_approx hρ h0 h1
  have h := norm_phaseDifference_le_of_posDef hpd (trace_approx htr ε) u
  rw [cpowSpec_of_eq_cfc (posDef_marginalU (F := F) hpd) (posSemidef_marginalU hρ).1 _
      (marginalU_approx hρ ε),
    cpowSpec_of_eq_cfc (posDef_marginalXU (F := F) hpd) (posSemidef_marginalXU hρ).1 _
      (marginalXU_approx hρ ε),
    cpowSpec_of_eq_cfc (posDef_marginalUF hpd) (posSemidef_marginalUF hρ).1 _
      (marginalUF_approx hρ ε),
    cpowSpec_of_eq_cfc hpd hρ.1 _ (approx_eq_cfc hρ.1 ε),
    rpowSpec_of_eq_cfc hpd hρ.1 _ (approx_eq_cfc hρ.1 ε)] at h
  convert h using 8 <;> simp [phaseFam, affF, approxW, mul_assoc]

end Bound

end Entropy.MarginalPhase

end
