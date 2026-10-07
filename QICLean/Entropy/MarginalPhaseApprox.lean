/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.MarginalPhaseSupport

/-!
# Faithful approximation of a state on three systems

For a density matrix `ρ` on `x (U F)` with `N = dim (x U F)` and `0 < ε ≤ 1`, the
approximation `ρ_ε = (1 - ε) ρ + (ε / N) I` is positive definite of trace one, and each
of its marginals is an affine function of the corresponding marginal of `ρ`.  Hence the
complex powers of `ρ_ε` and of its marginals are spectral functions in the eigenbases of
`ρ` and of its marginals, and so are their entropies.

## Main definitions

* `Entropy.MarginalPhase.approx`.

## Main results

* `Entropy.MarginalPhase.posDef_approx`, `trace_approx`.
* `Entropy.MarginalPhase.marginalXU_approx`, `marginalU_approx`, `marginalUF_approx`.
* `Entropy.MarginalPhase.cpowSpec_of_eq_cfc`, `rpowSpec_of_eq_cfc`,
  `vonNeumannEntropy_of_eq_cfc`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 456–459.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder

noncomputable section

namespace Entropy.MarginalPhase

open Matrix

section Conversion

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem cpowSpec_of_eq_cfc {A M : Matrix n n ℂ} (hA : A.PosDef) (hM : M.IsHermitian)
    (h : ℝ → ℝ) (heq : A = cfc h M) (z : ℂ) :
    cpowSpec hA z = spectralFun hM.eigenvectorUnitary
      (fun k => ((h (hM.eigenvalues k) : ℝ) : ℂ) ^ z) := by
  subst heq
  exact hM.spectralFun_cfc_comp h hA.1 (fun t => (t : ℂ) ^ z)

theorem rpowSpec_of_eq_cfc {A M : Matrix n n ℂ} (hA : A.PosDef) (hM : M.IsHermitian)
    (h : ℝ → ℝ) (heq : A = cfc h M) (s : ℝ) :
    rpowSpec hA s = spectralFun hM.eigenvectorUnitary
      (fun k => ((h (hM.eigenvalues k) ^ s : ℝ) : ℂ)) := by
  subst heq
  exact hM.spectralFun_cfc_comp h hA.1 (fun t => ((t ^ s : ℝ) : ℂ))

theorem vonNeumannEntropy_of_eq_cfc {A M : Matrix n n ℂ} (hA : A.IsHermitian)
    (hM : M.IsHermitian) (h : ℝ → ℝ) (heq : A = cfc h M) :
    vonNeumannEntropy A hA = ∑ k, Real.negMulLog (h (hM.eigenvalues k)) := by
  subst heq
  have key := hM.spectralFun_cfc_comp h hA (fun t => ((Real.negMulLog t : ℝ) : ℂ))
  have h1 := congrArg (fun T => (Matrix.trace T).re) key
  simp only [trace_spectralFun, Complex.re_sum, Complex.ofReal_re] at h1
  rw [vonNeumannEntropy]
  exact h1

end Conversion

variable {X U F : Type*} [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
  [Fintype F] [DecidableEq F]

/-- The faithful approximation `ρ_ε = (1 - ε) ρ + (ε / N) I` with `N = dim (x U F)`.
Area-law manuscript, `04-conditional.tex`, line 457. -/
def approx (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) (ε : ℝ) :
    Matrix (X × (U × F)) (X × (U × F)) ℂ :=
  (1 - ε) • ρ + (ε / Fintype.card (X × (U × F))) • (1 : Matrix (X × (U × F)) (X × (U × F)) ℂ)

omit [Fintype X] [Fintype U] in
theorem marginalXU_affine (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) (a b : ℝ) :
    marginalXU (a • ρ + b • (1 : Matrix (X × (U × F)) (X × (U × F)) ℂ)) =
      a • marginalXU ρ + (b * Fintype.card F) • (1 : Matrix (X × U) (X × U) ℂ) := by
  ext i j
  simp only [marginalXU, partialTraceRight_apply, submatrix_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Finset.sum_add_distrib, EmbeddingLike.apply_eq_iff_eq,
    Prod.mk.injEq, Complex.real_smul, ← Finset.mul_sum]
  by_cases h : i = j
  · subst h; simp [Finset.card_univ]
  · simp [h]

omit [Fintype U] [Fintype F] in
theorem marginalUF_affine (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) (a b : ℝ) :
    marginalUF (a • ρ + b • (1 : Matrix (X × (U × F)) (X × (U × F)) ℂ)) =
      a • marginalUF ρ + (b * Fintype.card X) • (1 : Matrix (U × F) (U × F) ℂ) := by
  ext i j
  simp only [marginalUF, partialTraceLeft_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Finset.sum_add_distrib, Prod.mk.injEq, Complex.real_smul, ← Finset.mul_sum]
  by_cases h : i = j
  · subst h; simp [Finset.card_univ]
  · simp [h]

omit [Fintype U] in
theorem marginalU_affine (ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ) (a b : ℝ) :
    marginalU (a • ρ + b • (1 : Matrix (X × (U × F)) (X × (U × F)) ℂ)) =
      a • marginalU ρ + (b * Fintype.card F * Fintype.card X) • (1 : Matrix U U ℂ) := by
  rw [marginalU, marginalXU_affine, marginalU]
  ext i j
  simp only [partialTraceLeft_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Finset.sum_add_distrib, Prod.mk.injEq, Complex.real_smul, ← Finset.mul_sum]
  by_cases h : i = j
  · subst h; simp [Finset.card_univ]
  · simp [h]

section Approx

variable {ρ : Matrix (X × (U × F)) (X × (U × F)) ℂ}

/-- The approximating weight `ε / N`. -/
abbrev approxW (ε : ℝ) : ℝ := ε / Fintype.card (X × (U × F))

theorem posDef_approx [Nonempty X] [Nonempty U] [Nonempty F] (hρ : ρ.PosSemidef) {ε : ℝ}
    (h0 : 0 < ε) (h1 : ε ≤ 1) : (approx ρ ε).PosDef := by
  have hN : (0 : ℝ) < Fintype.card (X × (U × F)) := Nat.cast_pos.2 Fintype.card_pos
  exact PosDef.posSemidef_add (hρ.smul (sub_nonneg.2 h1)) (PosDef.one.smul (div_pos h0 hN))

theorem trace_approx [Nonempty X] [Nonempty U] [Nonempty F] (htr : ρ.trace = 1) (ε : ℝ) :
    (approx ρ ε).trace = 1 := by
  have hN : (Fintype.card (X × (U × F)) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [approx, trace_add, trace_smul, trace_smul, htr, trace_one, Complex.real_smul,
    Complex.real_smul]
  push_cast
  field_simp
  ring

theorem approx_eq_cfc (hρ : ρ.IsHermitian) (ε : ℝ) :
    approx ρ ε = cfc (fun t : ℝ => (1 - ε) * t + approxW (X := X) (U := U) (F := F) ε) ρ :=
  (hρ.cfc_affine _ _).symm

theorem marginalXU_approx (hρ : ρ.PosSemidef) (ε : ℝ) :
    marginalXU (approx ρ ε) = cfc (fun t : ℝ => (1 - ε) * t +
      approxW (X := X) (U := U) (F := F) ε * Fintype.card F) (marginalXU ρ) := by
  rw [approx, marginalXU_affine, (posSemidef_marginalXU hρ).1.cfc_affine]

theorem marginalUF_approx (hρ : ρ.PosSemidef) (ε : ℝ) :
    marginalUF (approx ρ ε) = cfc (fun t : ℝ => (1 - ε) * t +
      approxW (X := X) (U := U) (F := F) ε * Fintype.card X) (marginalUF ρ) := by
  rw [approx, marginalUF_affine, (posSemidef_marginalUF hρ).1.cfc_affine]

theorem marginalU_approx (hρ : ρ.PosSemidef) (ε : ℝ) :
    marginalU (approx ρ ε) = cfc (fun t : ℝ => (1 - ε) * t +
      approxW (X := X) (U := U) (F := F) ε * Fintype.card F * Fintype.card X) (marginalU ρ) := by
  rw [approx, marginalU_affine, (posSemidef_marginalU hρ).1.cfc_affine]

end Approx

end Entropy.MarginalPhase

end
