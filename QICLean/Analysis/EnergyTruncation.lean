/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityTruncation

/-!
# Truncating the high spectrum of a Hermitian matrix

For a Hermitian matrix `A` and an energy `τ`, the truncation replaces every eigenvalue above `τ`
by `τ` and keeps the others:
`Ã = A P_{(-∞, τ)} + τ P_{[τ, ∞)}`, where `P_{[τ, ∞)}` is the spectral projection of `A` onto
eigenvalues at least `τ`. In the functional calculus, `Ã = min (A, τ)`.

This is the truncation of a local term in Arad, Kuwahara and Landau, *Connecting global and
local energy distributions in quantum spin models on a lattice* (arXiv:1406.3898,
`low70.tex`, Definition `def:Ht`, lines 684–697), and the hard truncation of Arad, Landau,
Vazirani and Vidick (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Definition
`def:hard-trunc`, lines 873–886), where `A = H_J` and `τ = ε_J + t`.

The truncation is Hermitian, commutes with `A`, lies below `A` and below `τ`, and lies above
every lower bound of the spectrum of `A` that is at most `τ`.

## Main statements

* `Matrix.energyTruncation`: the truncation `min (A, τ)`.
* `Matrix.IsHermitian.energyTruncation_eq`: the form `A (1 - P_{[τ, ∞)}) + τ P_{[τ, ∞)}`.
* `Matrix.IsHermitian.energyTruncation_le`, `energyTruncation_le_smul_one`,
  `smul_one_le_energyTruncation`: the order bounds.
-/

open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The truncation of `A` at the energy `τ`: every eigenvalue above `τ` is replaced by `τ`.
Arad, Kuwahara and Landau, arXiv:1406.3898, Definition `def:Ht`; Arad, Landau, Vazirani and
Vidick, arXiv:1602.08828v2, Definition `def:hard-trunc`. -/
def energyTruncation (A : Matrix n n ℂ) (τ : ℝ) : Matrix n n ℂ :=
  cfc (fun t : ℝ ↦ min t τ) A

/-- The truncation in the form of the sources: `A P_{(-∞, τ)} + τ P_{[τ, ∞)}`. -/
theorem IsHermitian.energyTruncation_eq (hA : A.IsHermitian) (τ : ℝ) :
    energyTruncation A τ =
      A * (1 - spectralProjectionGE A τ) + (τ : ℂ) • spectralProjectionGE A τ := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  have hP : spectralProjectionGE A τ = cfc (fun t : ℝ ↦ if τ ≤ t then 1 else 0) A := rfl
  have h1 : (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ (1 : ℝ)) A := by
    rw [cfc_const (1 : ℝ) A hA.isSelfAdjoint, map_one]
  have hid : A = cfc (fun t : ℝ ↦ t) A := (cfc_id' ℝ A hA.isSelfAdjoint).symm
  have hτ : (τ : ℂ) • spectralProjectionGE A τ =
      cfc (fun t : ℝ ↦ τ * if τ ≤ t then 1 else 0) A := by
    rw [cfc_const_mul τ _ A (hc _), hP, ← Complex.coe_smul]
  rw [hτ, hP, h1]
  conv_rhs => lhs; lhs; rw [hid]
  rw [← cfc_sub (fun _ : ℝ ↦ (1 : ℝ)) _ A (hc _) (hc _), ← _root_.cfc_mul _ _ A (hc _) (hc _),
    ← _root_.cfc_add (a := A) (fun t : ℝ ↦ t * (1 - if τ ≤ t then 1 else 0))
      (fun t : ℝ ↦ τ * if τ ≤ t then 1 else 0) (hc _) (hc _), energyTruncation]
  congr 1
  funext t
  split_ifs with h
  · simp [min_eq_right h]
  · push Not at h
    simp [min_eq_left h.le]

/-- The truncation is Hermitian. -/
theorem isHermitian_energyTruncation (A : Matrix n n ℂ) (τ : ℝ) :
    (energyTruncation A τ).IsHermitian :=
  (cfc_predicate _ A : IsSelfAdjoint (energyTruncation A τ))

/-- The truncation commutes with `A`. -/
theorem IsHermitian.commute_energyTruncation (hA : A.IsHermitian) (τ : ℝ) :
    Commute A (energyTruncation A τ) := by
  change A * energyTruncation A τ = energyTruncation A τ * A
  conv_lhs => lhs; rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  conv_rhs => rhs; rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  rw [energyTruncation, ← _root_.cfc_mul (fun t : ℝ ↦ t) (fun t ↦ min t τ) A,
    ← _root_.cfc_mul (fun t ↦ min t τ) (fun t : ℝ ↦ t) A]
  congr 1
  funext t
  exact mul_comm _ _

/-- The truncation lies below `A`. -/
theorem IsHermitian.energyTruncation_le (hA : A.IsHermitian) (τ : ℝ) :
    energyTruncation A τ ≤ A := by
  conv_rhs => rw [← cfc_id' ℝ A hA.isSelfAdjoint]
  exact cfc_mono fun t _ => min_le_left t τ

/-- The truncation lies below `τ`. -/
theorem IsHermitian.energyTruncation_le_smul_one (hA : A.IsHermitian) (τ : ℝ) :
    energyTruncation A τ ≤ (τ : ℂ) • 1 := by
  have h : (τ : ℂ) • (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ τ) A := by
    rw [cfc_const τ A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [h]
  exact cfc_mono fun t _ => min_le_right t τ

/-- If every eigenvalue of `A` is at least `ε` and `ε ≤ τ`, the truncation lies above `ε`. -/
theorem IsHermitian.smul_one_le_energyTruncation (hA : A.IsHermitian) {ε τ : ℝ} (hετ : ε ≤ τ)
    (hspec : ∀ t ∈ spectrum ℝ A, ε ≤ t) :
    (ε : ℂ) • 1 ≤ energyTruncation A τ := by
  have h : (ε : ℂ) • (1 : Matrix n n ℂ) = cfc (fun _ : ℝ ↦ ε) A := by
    rw [cfc_const ε A hA.isSelfAdjoint, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]
  rw [h]
  exact cfc_mono fun t ht => le_min (hspec t ht) hετ

end Matrix
