/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Kronecker.PartialTranspose
import QICLean.Algebra.Matrix.MatrixAux
import QICLean.Analysis.TraceNorm.RectangularTraceNormAlgebra

/-!
# Maximally entangled overlap, PPT upper bound, and trace-norm stability

For a bipartite operator `σ` on `ℂ^d ⊗ ℂ^d`, its **maximally entangled overlap**
(or singlet fraction when `σ` is a state) is the real trace pairing

  `maxEntangledOverlap d σ = Re tr(|Ω_d⟩⟨Ω_d| σ)`,

where `|Ω_d⟩ = d⁻¹/² ∑_j |j,j⟩` is the canonical maximally entangled unit vector
and `omegaProj d = |Ω_d⟩⟨Ω_d|`.

For a density matrix `σ`, this quantity is the squared pure-target fidelity
`⟨Ω_d|σ|Ω_d⟩`; it is intentionally kept distinct from `Matrix.rootFidelity`
and from half the trace norm `Matrix.traceDistance`.

## Main definitions

* `Matrix.maxEntangledOverlap`: the real trace pairing `Re tr(|Ω_d⟩⟨Ω_d| σ)`.

## Main results

* `Matrix.isStarProjection_omegaProj`, `Matrix.omegaProj_posSemidef`,
  `Matrix.l2_opNorm_omegaProj_le_one`: projector, positivity, and contraction
  properties of `|Ω_d⟩⟨Ω_d|`.
* `Matrix.maxEntangledOverlap_eq_swap_partialTransposeLeft`: rewriting the
  overlap via partial transpose as `Re tr(F_d σ^{T₁}) / d`.
* `Matrix.maxEntangledOverlap_le_trace_re_div_of_isPPT`: every PPT matrix `σ`
  with `d > 0` satisfies `maxEntangledOverlap d σ ≤ Re tr(σ) / d`.
* `Matrix.maxEntangledOverlap_le_one_div_of_isPPT`: every normalized PPT
  matrix (`tr σ = 1`, `d > 0`) satisfies `maxEntangledOverlap d σ ≤ 1 / d`.
* `Matrix.maxEntangledOverlap_sum_le_sum_trace_re_div_of_isPPT`: unnormalized
  finite-sum cap for PPT families.
* `Matrix.abs_maxEntangledOverlap_sub_le`:
  `|maxEntangledOverlap d σ - maxEntangledOverlap d τ| ≤ rectangularTraceNorm (σ - τ)`.
* `Matrix.abs_one_sub_maxEntangledOverlap_le`:
  `|1 - maxEntangledOverlap d σ| ≤ rectangularTraceNorm (σ - omegaProj d)` for `d > 0`.
* `Matrix.one_sub_one_div_le_rectangularTraceNorm_sub_omegaProj_of_isPPT`:
  `1 - 1 / d ≤ rectangularTraceNorm (σ - omegaProj d)` for any normalized PPT
  matrix and `d > 0`.
* `Matrix.continuous_maxEntangledOverlap`: continuity of the overlap functional.
-/

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder Kronecker BigOperators

noncomputable section

namespace Matrix

/-! ## Projector and contraction properties of `omegaProj` -/

/-- The maximally entangled projector `|Ω_d⟩⟨Ω_d|` is an orthogonal (star) projection
for every `d : ℕ` (for `d = 0` it is the unique empty matrix). -/
theorem isStarProjection_omegaProj (d : ℕ) : IsStarProjection (omegaProj d) := by
  rw [isStarProjection_iff']
  exact ⟨omegaProj_mul_self, by simpa only [star_eq_conjTranspose] using omegaProj_conjTranspose⟩

/-- The maximally entangled projector `|Ω_d⟩⟨Ω_d|` is positive semidefinite. -/
theorem omegaProj_posSemidef (d : ℕ) : (omegaProj d).PosSemidef := by
  have h : (omegaProj d)ᴴ * omegaProj d = omegaProj d := by
    rw [omegaProj_conjTranspose, omegaProj_mul_self]
  rw [← h]
  exact posSemidef_conjTranspose_mul_self (omegaProj d)

/-- The complementary projector `1 - |Ω_d⟩⟨Ω_d|` is positive semidefinite. -/
theorem one_sub_omegaProj_posSemidef (d : ℕ) :
    ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - omegaProj d).PosSemidef := by
  have hproj := (isStarProjection_omegaProj d).one_sub
  have h : ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - omegaProj d)ᴴ *
      (1 - omegaProj d) = 1 - omegaProj d := by
    rw [← star_eq_conjTranspose, hproj.isSelfAdjoint.star_eq, hproj.isIdempotentElem.eq]
  rw [← h]
  exact posSemidef_conjTranspose_mul_self _

/-- The maximally entangled projector is an `ℓ²`-operator contraction: `‖|Ω_d⟩⟨Ω_d|‖ ≤ 1`. -/
theorem l2_opNorm_omegaProj_le_one (d : ℕ) : ‖omegaProj d‖ ≤ 1 :=
  (isStarProjection_omegaProj d).norm_le

/-! ## Definition and basic algebraic properties -/

/-- The overlap of a bipartite matrix `σ` on `ℂ^d ⊗ ℂ^d` with the maximally entangled
projector `|Ω_d⟩⟨Ω_d|`, defined as `Re tr(|Ω_d⟩⟨Ω_d| σ)`.

For a density matrix `σ`, this is the squared pure-target fidelity `⟨Ω_d|σ|Ω_d⟩`,
distinct from `Matrix.rootFidelity` and half the trace norm `Matrix.traceDistance`. -/
def maxEntangledOverlap (d : ℕ)
    (σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  (omegaProj d * σ).trace.re

theorem maxEntangledOverlap_def (d : ℕ)
    (σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    maxEntangledOverlap d σ = (omegaProj d * σ).trace.re :=
  rfl

@[simp]
theorem maxEntangledOverlap_zero (d : ℕ) :
    maxEntangledOverlap d 0 = 0 := by
  simp [maxEntangledOverlap]

theorem maxEntangledOverlap_add (d : ℕ)
    (σ τ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    maxEntangledOverlap d (σ + τ) = maxEntangledOverlap d σ + maxEntangledOverlap d τ := by
  simp [maxEntangledOverlap, mul_add, trace_add]

theorem maxEntangledOverlap_sub (d : ℕ)
    (σ τ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    maxEntangledOverlap d (σ - τ) = maxEntangledOverlap d σ - maxEntangledOverlap d τ := by
  simp [maxEntangledOverlap, mul_sub, trace_sub]

theorem maxEntangledOverlap_neg (d : ℕ)
    (σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    maxEntangledOverlap d (-σ) = -maxEntangledOverlap d σ := by
  simp [maxEntangledOverlap]

theorem maxEntangledOverlap_smul_real (d : ℕ) (r : ℝ)
    (σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    maxEntangledOverlap d (r • σ) = r * maxEntangledOverlap d σ := by
  simp [maxEntangledOverlap, trace_smul]

theorem maxEntangledOverlap_sum {ι : Type*} (d : ℕ) (s : Finset ι)
    (σ : ι → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    maxEntangledOverlap d (∑ i ∈ s, σ i) = ∑ i ∈ s, maxEntangledOverlap d (σ i) := by
  simp [maxEntangledOverlap, Finset.mul_sum, trace_sum]

/-- The maximally entangled overlap is continuous on the finite-dimensional matrix space. -/
theorem continuous_maxEntangledOverlap (d : ℕ) :
    Continuous (maxEntangledOverlap d) := by
  unfold maxEntangledOverlap
  refine Complex.continuous_re.comp ?_
  have htr : Continuous (Matrix.trace :
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ → ℂ) := by
    change Continuous fun M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ ↦ ∑ p, M p p
    fun_prop
  exact htr.comp (continuous_const.mul continuous_id)

/-! ## Canonical values and positivity bounds -/

/-- For `d > 0`, the maximally entangled state has overlap `1` with itself.
The hypothesis `0 < d` is necessary: for `d = 0`, the empty matrix has trace `0`. -/
theorem maxEntangledOverlap_omegaProj {d : ℕ} (hd : 0 < d) :
    maxEntangledOverlap d (omegaProj d) = 1 := by
  rw [maxEntangledOverlap, omegaProj_mul_self, trace_omegaProj hd, Complex.one_re]

/-- For `d > 0`, the unnormalized identity matrix has maximally entangled overlap `1`. -/
theorem maxEntangledOverlap_one {d : ℕ} (hd : 0 < d) :
    maxEntangledOverlap d 1 = 1 := by
  rw [maxEntangledOverlap, Matrix.mul_one, trace_omegaProj hd, Complex.one_re]

/-- For a positive semidefinite matrix, the maximally entangled overlap is nonnegative. -/
theorem maxEntangledOverlap_nonneg_of_posSemidef {d : ℕ}
    {σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ maxEntangledOverlap d σ :=
  (Complex.nonneg_iff.mp ((omegaProj_posSemidef d).trace_mul_nonneg hσ)).1

/-- For a positive semidefinite matrix, the maximally entangled overlap is at most `Re tr(σ)`. -/
theorem maxEntangledOverlap_le_trace_re_of_posSemidef {d : ℕ}
    {σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hσ : σ.PosSemidef) :
    maxEntangledOverlap d σ ≤ σ.trace.re := by
  have hnonneg : 0 ≤ ((1 - omegaProj d) * σ).trace.re :=
    (Complex.nonneg_iff.mp ((one_sub_omegaProj_posSemidef d).trace_mul_nonneg hσ)).1
  rw [sub_mul, Matrix.one_mul, trace_sub, Complex.sub_re] at hnonneg
  linarith [maxEntangledOverlap_def d σ]

/-- For a positive semidefinite trace-one matrix, the maximally entangled overlap is at most `1`. -/
theorem maxEntangledOverlap_le_one_of_posSemidef {d : ℕ}
    {σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1) :
    maxEntangledOverlap d σ ≤ 1 := by
  have h := maxEntangledOverlap_le_trace_re_of_posSemidef hσ
  simpa [htr] using h

/-! ## Partial-transpose identity and PPT overlap bound -/

/-- Rewriting the maximally entangled overlap via partial transpose:
`maxEntangledOverlap d σ = Re tr(F_d σ^{T₁}) / d`. -/
theorem maxEntangledOverlap_eq_swap_partialTransposeLeft (d : ℕ)
    (σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    maxEntangledOverlap d σ = (swapMatrix d * partialTransposeLeft σ).trace.re / (d : ℝ) := by
  rw [maxEntangledOverlap, ← trace_partialTransposeLeft_mul_partialTransposeLeft,
    partialTransposeLeft_omegaProj, Matrix.smul_mul, trace_smul, smul_eq_mul]
  have hd : ((d : ℂ)⁻¹) = (((d : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hd, Complex.re_ofReal_mul, inv_mul_eq_div]

/-- Maximally entangled overlap on a product operator `A ⊗ B`:
`maxEntangledOverlap d (A ⊗ B) = Re tr(Aᵀ B) / d`. -/
theorem maxEntangledOverlap_kronecker (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    maxEntangledOverlap d (A ⊗ₖ B) = (Aᵀ * B).trace.re / (d : ℝ) := by
  rw [maxEntangledOverlap_eq_swap_partialTransposeLeft, partialTransposeLeft_kronecker,
    trace_swapMatrix_mul_kronecker]

/-- **Unnormalized PPT overlap bound.** Every bipartite matrix `σ` on `ℂ^d ⊗ ℂ^d` with
positive partial transpose and `d > 0` satisfies

  `maxEntangledOverlap d σ ≤ Re tr(σ) / d`.

No positivity or trace normalization of `σ` itself is needed beyond `IsPPT σ`; when `σ` is
additionally positive semidefinite, `0 ≤ maxEntangledOverlap d σ` also holds. -/
theorem maxEntangledOverlap_le_trace_re_div_of_isPPT {d : ℕ} (hd : 0 < d)
    {σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hσ : σ.IsPPT) :
    maxEntangledOverlap d σ ≤ σ.trace.re / (d : ℝ) := by
  rw [maxEntangledOverlap_eq_swap_partialTransposeLeft]
  have hnonneg : 0 ≤ ((1 - swapMatrix d) * partialTransposeLeft σ).trace.re :=
    (Complex.nonneg_iff.mp ((one_sub_swapMatrix_posSemidef d).trace_mul_nonneg hσ)).1
  rw [sub_mul, Matrix.one_mul, trace_sub, trace_partialTransposeLeft, Complex.sub_re] at hnonneg
  have hle : (swapMatrix d * partialTransposeLeft σ).trace.re ≤ σ.trace.re := by linarith
  exact div_le_div_of_nonneg_right hle (Nat.cast_pos.mpr hd).le

/-- **Normalized PPT overlap bound.** Every trace-one PPT matrix on `ℂ^d ⊗ ℂ^d` with `d > 0`
has maximally entangled overlap at most `1 / d`. -/
theorem maxEntangledOverlap_le_one_div_of_isPPT {d : ℕ} (hd : 0 < d)
    {σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hσ : σ.IsPPT) (htr : σ.trace = 1) :
    maxEntangledOverlap d σ ≤ 1 / (d : ℝ) := by
  have h := maxEntangledOverlap_le_trace_re_div_of_isPPT hd hσ
  simpa [htr] using h

/-- **Unnormalized PPT overlap bound for finite sums.** For any finite family of PPT
operators `σ_i` (such as postselection branches), the overlap of the sum is bounded by
`(∑_i Re tr(σ_i)) / d`. -/
theorem maxEntangledOverlap_sum_le_sum_trace_re_div_of_isPPT {ι : Type*} {d : ℕ} (hd : 0 < d)
    (s : Finset ι) (σ : ι → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hσ : ∀ i ∈ s, (σ i).IsPPT) :
    maxEntangledOverlap d (∑ i ∈ s, σ i) ≤ (∑ i ∈ s, (σ i).trace.re) / (d : ℝ) := by
  rw [maxEntangledOverlap_sum, Finset.sum_div]
  exact Finset.sum_le_sum fun i hi ↦ maxEntangledOverlap_le_trace_re_div_of_isPPT hd (hσ i hi)

/-! ## Trace-norm stability and gap from the maximally entangled state -/

/-- **Overlap Lipschitz bound in the full trace norm.** For arbitrary bipartite matrices `σ, τ`,
the difference of their maximally entangled overlaps is bounded by
`rectangularTraceNorm (σ - τ)`. -/
theorem abs_maxEntangledOverlap_sub_le (d : ℕ)
    (σ τ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    |maxEntangledOverlap d σ - maxEntangledOverlap d τ| ≤ rectangularTraceNorm (σ - τ) := by
  rw [← maxEntangledOverlap_sub, maxEntangledOverlap]
  calc
    |((omegaProj d * (σ - τ)).trace).re| ≤ ‖(omegaProj d * (σ - τ)).trace‖ :=
      Complex.abs_re_le_norm _
    _ = ‖((σ - τ) * omegaProj d).trace‖ := by rw [Matrix.trace_mul_comm]
    _ ≤ ‖omegaProj d‖ * rectangularTraceNorm (σ - τ) :=
      norm_trace_mul_le_l2_opNorm_mul_rectangularTraceNorm (σ - τ) (omegaProj d)
    _ ≤ 1 * rectangularTraceNorm (σ - τ) :=
      mul_le_mul_of_nonneg_right (l2_opNorm_omegaProj_le_one d) (rectangularTraceNorm_nonneg _)
    _ = rectangularTraceNorm (σ - τ) := one_mul _

/-- For `d > 0`, the overlap deficit `|1 - maxEntangledOverlap d σ|` is bounded by the full
trace norm `rectangularTraceNorm (σ - omegaProj d)`. -/
theorem abs_one_sub_maxEntangledOverlap_le {d : ℕ} (hd : 0 < d)
    (σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    |1 - maxEntangledOverlap d σ| ≤ rectangularTraceNorm (σ - omegaProj d) := by
  have h := abs_maxEntangledOverlap_sub_le d σ (omegaProj d)
  rw [maxEntangledOverlap_omegaProj hd, abs_sub_comm] at h
  exact h

/-- For `d > 0`, `1 - rectangularTraceNorm (σ - omegaProj d) ≤ maxEntangledOverlap d σ`. -/
theorem one_sub_rectangularTraceNorm_le_maxEntangledOverlap {d : ℕ} (hd : 0 < d)
    (σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    1 - rectangularTraceNorm (σ - omegaProj d) ≤ maxEntangledOverlap d σ := by
  have h := (abs_le.mp (abs_one_sub_maxEntangledOverlap_le hd σ)).2
  linarith

/-- **PPT trace-norm gap from the maximally entangled state.** Any normalized PPT matrix
on `ℂ^d ⊗ ℂ^d` with `d > 0` is separated from `|Ω_d⟩⟨Ω_d|` in full trace norm by at least
`1 - 1 / d`. -/
theorem one_sub_one_div_le_rectangularTraceNorm_sub_omegaProj_of_isPPT {d : ℕ} (hd : 0 < d)
    {σ : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ} (hσ : σ.IsPPT) (htr : σ.trace = 1) :
    1 - 1 / (d : ℝ) ≤ rectangularTraceNorm (σ - omegaProj d) := by
  have h1 := maxEntangledOverlap_le_one_div_of_isPPT hd hσ htr
  have h2 := one_sub_rectangularTraceNorm_le_maxEntangledOverlap hd σ
  linarith

end Matrix
