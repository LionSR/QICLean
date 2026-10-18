/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchurLabelMomentBounds
import QICLean.Analysis.SurprisalMoment
import QICLean.Analysis.CfcFinKronecker
import QICLean.Analysis.ReplicaPermutationCovariance
import QICLean.Analysis.Entropy

/-!
# Centered surprisal moments of tensor powers

The trace weight removes the kernel of a density matrix. Consequently its
surprisal moment factors under tensor powers for every real exponent, including
one. This is the independent-copy step in OpenAI's area-law manuscript,
September 24, 2026, `07-comparators.tex`, lines 75–85 and 227–238. In particular,
the spectral convention at line 83 is retained without a full-rank assumption.
-/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace Matrix

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Spectral calculus evaluates the centered surprisal exponential also on a
singular matrix; the subsequent trace weight will remove its kernel. -/
private theorem exp_centered_neg_log_eq_cfc {σ : Matrix Ω Ω ℂ}
    (hσ : σ.IsHermitian) (s t : ℝ) :
    NormedSpace.exp ((t : ℂ) • (-CFC.log σ - (s : ℂ) • 1)) =
      cfc (fun x : ℝ ↦ Real.exp (t * (-Real.log x - s))) σ := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ σ) :=
    σ.finite_real_spectrum.continuousOn f
  have hc : cfc (fun x : ℝ ↦ t * (-Real.log x - s)) σ =
      (t : ℂ) • (-CFC.log σ - (s : ℂ) • 1) := by
    rw [cfc_const_mul _ _ _ (hcont _), cfc_sub _ _ _ (hcont _) (hcont _),
      cfc_neg, cfc_const (R := ℝ) s σ (show IsSelfAdjoint σ from hσ)]
    simp only [CFC.log, Algebra.algebraMap_eq_smul_one, Complex.coe_smul]
  rw [cfc_comp' Real.exp (fun x : ℝ ↦ t * (-Real.log x - s)) σ
    Real.continuous_exp.continuousOn (hcont _) (show IsSelfAdjoint σ from hσ), hc]
  exact (CFC.real_exp_eq_normedSpace_exp (by
    apply Matrix.IsHermitian.smul
    · exact IsSelfAdjoint.log.neg.sub (Matrix.isHermitian_one.smul (by
        change star (s : ℂ) = (s : ℂ)
        simp))
    · change star (t : ℂ) = (t : ℂ)
      simp)).symm

/-
Provenance-ID: 8753-qic-schur-iid-03
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.re_trace_mul_exp_centered_neg_log_eq_surprisalMoment
Manuscript: September 24, 2026, comparator:mgf-data and signed-label-moments.
-/

/-- The actual centered trace moment equals the existing scalar surprisal
moment of the eigenvalues. This is the positive-eigenvalue convention of
`07-comparators.tex`, lines 75–85, with an arbitrary center. -/
theorem re_trace_mul_exp_centered_neg_log_eq_surprisalMoment
    {σ : Matrix Ω Ω ℂ} (hσ : σ.IsHermitian) (s t : ℝ) :
    (σ * NormedSpace.exp ((t : ℂ) • (-CFC.log σ - (s : ℂ) • 1))).trace.re =
      Real.exp (-t * s) * Entropy.surprisalMoment hσ.eigenvalues t := by
  rw [exp_centered_neg_log_eq_cfc hσ, hσ.cfc_eq, hσ.self_mul_cfc,
    hσ.trace_cfc_eq_sum]
  simp only [Complex.re_sum, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]
  simp only [Entropy.surprisalMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show t * (-Real.log (hσ.eigenvalues i) - s) =
    -t * s + t * -Real.log (hσ.eigenvalues i) by ring, Real.exp_add]
  ring

/-- The zero-weight convention makes the scalar surprisal integrand
multiplicative even at exponent one. -/
private theorem surprisal_integrand_mul (t x y : ℝ) :
    (x * y) * Real.exp (t * -Real.log (x * y)) =
      (x * Real.exp (t * -Real.log x)) * (y * Real.exp (t * -Real.log y)) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.log_mul hx hy, neg_add, mul_add, Real.exp_add]
  ring

omit [DecidableEq Ω] in
/-- The trace of a constant finite tensor power is the corresponding scalar power. -/
private theorem trace_finKronecker_const (H : Matrix Ω Ω ℂ) (k : ℕ) :
    (finKronecker (fun _ : Fin k ↦ H)).trace = H.trace ^ k := by
  simp only [Matrix.trace, Matrix.diag, finKronecker_apply]
  calc
    _ = ∏ _ : Fin k, ∑ i : Ω, H i i :=
      (Fintype.prod_sum (fun (_ : Fin k) (i : Ω) ↦ H i i)).symm
    _ = _ := by simp

/-- The spectral sum is real; this complex trace identity permits tensor powers
without introducing a power of the real part of an arbitrary complex number. -/
private theorem trace_surprisal_cfc {σ : Matrix Ω Ω ℂ} (hσ : σ.IsHermitian) (t : ℝ) :
    (cfc (fun x : ℝ ↦ x * Real.exp (t * -Real.log x)) σ).trace =
      (Entropy.surprisalMoment hσ.eigenvalues t : ℂ) := by
  rw [hσ.cfc_eq, hσ.trace_cfc_eq_sum]
  simp [Entropy.surprisalMoment]

/-
Provenance-ID: 8753-qic-schur-iid-04
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.re_trace_mul_exp_centered_neg_log_finKronecker
Manuscript: September 24, 2026, comparator:mgf-data and signed-label-moments.
-/

/-- The actual centered surprisal moment of a tensor power is the corresponding
power of the one-copy moment, for every real exponent. This proves the
independent-copy step of `07-comparators.tex`, lines 227–238, including singular
states and the zero-copy tensor power. -/
theorem re_trace_mul_exp_centered_neg_log_finKronecker
    {σ : Matrix Ω Ω ℂ} (hσ : σ.PosSemidef) (s t : ℝ) (k : ℕ) :
    let ρ := finKronecker (fun _ : Fin k ↦ σ)
    (ρ * NormedSpace.exp ((t : ℂ) • (-CFC.log ρ - ((k : ℝ) * s : ℂ) • 1))).trace.re =
      ((σ * NormedSpace.exp ((t : ℂ) • (-CFC.log σ - (s : ℂ) • 1))).trace.re) ^ k := by
  dsimp only
  let hρ := finKronecker_posSemidef (fun _ : Fin k ↦ σ) (fun _ ↦ hσ)
  have hm : Entropy.surprisalMoment hρ.isHermitian.eigenvalues t =
      (Entropy.surprisalMoment hσ.isHermitian.eigenvalues t) ^ k := by
    have h := congrArg Matrix.trace (cfc_finKronecker_const hσ
      (fun x : ℝ ↦ x * Real.exp (t * -Real.log x)) (by simp)
      (fun x y _ _ ↦ surprisal_integrand_mul t x y) k)
    rw [trace_finKronecker_const, trace_surprisal_cfc hρ.isHermitian,
      trace_surprisal_cfc hσ.isHermitian] at h
    exact_mod_cast h
  simp only [← Complex.ofReal_mul]
  rw [re_trace_mul_exp_centered_neg_log_eq_surprisalMoment hρ.isHermitian,
    re_trace_mul_exp_centered_neg_log_eq_surprisalMoment hσ.isHermitian, hm, mul_pow]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

end Matrix

namespace TensorPower

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-
Provenance-ID: 8753-qic-schur-iid-05
Original formalization, no upstream Lean proof text reused.
Declaration: TensorPower.log_centered_surprisalMoment_finKronecker_le
Manuscript: September 24, 2026, comparator:mgf-data and signed-label-moments.
-/

/-- The one-copy assumption `comparator:mgf-data` gives the actual centered
`k`-copy logarithmic moment bound. This is the iid step in
`07-comparators.tex`, lines 75–85 and 227–238; no tensor-power moment bound is
assumed. The displayed hypothesis is the one-copy estimate at the chosen `t`. -/
theorem log_centered_surprisalMoment_finKronecker_le
    {σ : Matrix Ω Ω ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (k : ℕ) (C₀ ℬ t : ℝ)
    (hmgf : Real.log (Entropy.surprisalMoment hσ.isHermitian.eigenvalues t) ≤
      t * vonNeumannEntropy σ hσ.isHermitian + C₀ * ℬ * t ^ 2) :
    let ρ := finKronecker (fun _ : Fin k ↦ σ)
    Real.log (ρ * NormedSpace.exp ((t : ℂ) •
      (-CFC.log ρ - ((k : ℝ) * vonNeumannEntropy σ hσ.isHermitian : ℂ) • 1))).trace.re ≤
        C₀ * k * ℬ * t ^ 2 := by
  dsimp only
  rw [Matrix.re_trace_mul_exp_centered_neg_log_finKronecker hσ, Real.log_pow,
    Matrix.re_trace_mul_exp_centered_neg_log_eq_surprisalMoment hσ.isHermitian]
  have hp := Entropy.surprisalMoment_pos hσ.eigenvalues_nonneg
    (posSemidef_trace_one_eigenvalues_sum_one hσ htr) t
  rw [Real.log_mul (Real.exp_pos _).ne' hp.ne', Real.log_exp]
  have h := mul_le_mul_of_nonneg_left hmgf (Nat.cast_nonneg (α := ℝ) k)
  nlinarith

/-
Provenance-ID: 8753-qic-schur-iid-06
Original formalization, no upstream Lean proof text reused.
Declaration: TensorPower.log_centered_labelEntropy_finKronecker_le
Manuscript: September 24, 2026, comparator:mgf-data and signed-label-moments.
-/

/-- For the actual iid state, the one-copy hypothesis gives both signed label
moments with a common small-exponent range and the explicit Schur logarithmic
loss. This is `comparator:signed-label-moments`, `07-comparators.tex`, lines
227–238, conditional only on the one-copy data in lines 75–85. -/
theorem log_centered_labelEntropy_finKronecker_le
    {σ : Matrix Ω Ω ℂ} (hσ : σ.PosSemidef) (htr : σ.trace = 1)
    (k : ℕ) (C₀ c₀ ℬ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) (hℬ : 1 ≤ ℬ)
    (hmgf : ∀ t : ℝ, |t| ≤ c₀ / Real.sqrt ℬ →
      Real.log (Entropy.surprisalMoment hσ.isHermitian.eigenvalues t) ≤
        t * vonNeumannEntropy σ hσ.isHermitian + C₀ * ℬ * t ^ 2) :
    let ρ := finKronecker (fun _ : Fin k ↦ σ)
    0 < min c₀ 1 / 2 ∧
      ∀ t : ℝ, |t| ≤ (min c₀ 1 / 2) / Real.sqrt ℬ →
      Real.log (ρ * NormedSpace.exp ((t : ℂ) •
        (PermutationRepresentation.labelEntropy (copyPerm Ω k) -
          ((k : ℝ) * vonNeumannEntropy σ hσ.isHermitian : ℂ) • 1))).trace.re ≤
        2 * C₀ * k * ℬ * t ^ 2 + ((Fintype.card Ω : ℝ) ^ 2 / 2) * Real.log (k + 1) := by
  let ρ := finKronecker (fun _ : Fin k ↦ σ)
  have hρ : ρ.PosSemidef := finKronecker_posSemidef _ (fun _ ↦ hσ)
  have hρtr : ρ.trace = 1 := by rw [Matrix.trace_finKronecker_const, htr, one_pow]
  have hL (t : ℝ) (ht : |t| ≤ c₀ / Real.sqrt ℬ) :=
    log_centered_surprisalMoment_finKronecker_le hσ htr k C₀ ℬ t (hmgf t ht)
  simpa only [Complex.ofReal_mul] using
    log_centered_labelEntropy_moments_uniform (Ω := Ω) (k := k) (ρ := ρ)
    hρ hρtr (fun π ↦ (Matrix.commute_finKronecker_const_permOp σ k π).symm)
    ((k : ℝ) * vonNeumannEntropy σ hσ.isHermitian) C₀ c₀ ℬ hC hc hℬ
    (fun t ht ↦ by simpa only [Complex.ofReal_mul] using hL t ht)

end TensorPower
