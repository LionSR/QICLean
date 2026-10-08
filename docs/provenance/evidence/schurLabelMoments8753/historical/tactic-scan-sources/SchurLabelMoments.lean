/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchurSurprisal
import QICLean.Analysis.WeightedTraceHolder

/-!
# Centered Schur-label moments from supported surprisal moments

Let `ρ` be a permutation-invariant density matrix, `L = -log ρ` on its
support, and `F` the logarithm of the irreducible dimension. For an arbitrary
real center, the positive exponential moment of `F` is bounded by that of
`L`. The negative moment is bounded by the geometric mean of the negative
`L` moment at twice the parameter and the Schur remainder moment.

The positive comparison uses the joint spectral resolution on the support
of `ρ`. No inequality `F ≤ L` on the entire ambient space is asserted.
The resulting copy-permutation estimate uses the proved polynomial Schur
remainder bound. Bounds on the centered surprisal moments themselves are
separate input to the later concentration argument.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 227–237,
`comparator:signed-label-moments`; the Schur remainder is Lemma 6.1(5).
-/

noncomputable section
open Matrix Module
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  {φ : G →* Equiv.Perm X} {ρ : Matrix X X ℂ}
  (hρ : ρ.PosSemidef) (hinv : ∀ g, Commute (permOp φ g) ρ)

/-- Centering and real scaling act on the scalar values of a spectral resolution. -/
private theorem centered_hom {I : Type*} [Fintype I] [DecidableEq I]
    {P : I → Matrix X X ℂ} (R : IsOrthogonalResolution P) (f : I → ℝ) (s u : ℝ) :
    (u : ℂ) • (R.hom (fun i ↦ (f i : ℂ)) - (s : ℂ) • 1) =
      R.hom (fun i ↦ ((u * (f i - s) : ℝ) : ℂ)) := by
  rw [← map_one R.hom, ← map_smul, ← map_sub, ← map_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one,
    Complex.ofReal_mul, Complex.ofReal_sub]

/-- The state weights the joint exponential by its actual eigenvalue. -/
private theorem mul_exp_joint_hom
    (f : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℝ) :
    ρ * NormedSpace.exp ((isOrthogonalResolution_joint hρ hinv).hom
      (fun p ↦ (f p : ℂ))) =
      (isOrthogonalResolution_joint hρ hinv).hom
        (fun p ↦ (((p.1 : ℝ) * Real.exp (f p) : ℝ) : ℂ)) := by
  let R := isOrthogonalResolution_joint hρ hinv
  have hρR : ρ = R.hom (fun p ↦ ((p.1 : ℝ) : ℂ)) := by
    have h := joint_hom_fst hρ hinv id
    rw [Matrix.IsHermitian.cfc_id] at h
    exact h.symm
  rw [R.exp_hom]
  refine (congrArg (· * _) hρR).trans ?_
  rw [← map_mul]
  congr 1
  funext p
  simp only [Pi.mul_apply, Complex.ofReal_mul, Complex.ofReal_exp]

/-
Provenance-ID: 8753-qic-schur-label-moments-01
Original formalization, no upstream Lean proof text reused.
Declaration: PermutationRepresentation.re_trace_mul_exp_centered_labelEntropy_le
Manuscript: September 24, 2026, comparator:signed-label-moments, lines 227–237.
-/

include hρ hinv in
/-- The positive centered label moment is bounded by the centered surprisal moment.
The comparison is made on the support of the state, as in the area-law manuscript,
`07-comparators.tex`, lines 227–237; the center is arbitrary. -/
theorem re_trace_mul_exp_centered_labelEntropy_le (htr : ρ.trace = 1)
    (s u : ℝ) (hu : 0 ≤ u) :
    (ρ * NormedSpace.exp ((u : ℂ) • (labelEntropy φ - (s : ℂ) • 1))).trace.re ≤
      (ρ * NormedSpace.exp ((u : ℂ) • (-CFC.log ρ - (s : ℂ) • 1))).trace.re := by
  classical
  let R := isOrthogonalResolution_joint hρ hinv
  rw [labelEntropy_eq_joint_hom hρ hinv, neg_log_eq_joint_hom hρ hinv,
    centered_hom, centered_hom, mul_exp_joint_hom hρ hinv, mul_exp_joint_hom hρ hinv]
  apply sub_nonneg.mp
  rw [← Complex.sub_re, ← Matrix.trace_sub, ← map_sub]
  have heq :
      (fun p : hρ.isHermitian.eigenvalueSet × IrrepLabel G ↦
        (((p.1 : ℝ) * Real.exp (u * (-Real.log (p.1 : ℝ) - s)) : ℝ) : ℂ)) -
      (fun p ↦ (((p.1 : ℝ) * Real.exp (u * (Real.log p.2.dim - s)) : ℝ) : ℂ)) =
      fun p ↦ (((p.1 : ℝ) * (Real.exp (u * (-Real.log (p.1 : ℝ) - s)) -
        Real.exp (u * (Real.log p.2.dim - s))) : ℝ) : ℂ) := by
    funext p
    simp only [Pi.sub_apply, Complex.ofReal_mul, Complex.ofReal_sub, mul_sub]
  rw [heq]
  apply (Complex.nonneg_iff.mp ?_).1
  apply Matrix.PosSemidef.trace_nonneg
  refine R.posSemidef_hom_of_ne_zero (isHermitian_joint hρ hinv) fun p hp ↦ ?_
  by_cases hzero : (p.1 : ℝ) = 0
  · simp [hzero]
  have hpos : 0 < (p.1 : ℝ) :=
    lt_of_le_of_ne (eigenvalue_nonneg hρ p.1) (Ne.symm hzero)
  have hd : (0 : ℝ) < p.2.dim := by exact_mod_cast p.2.dim_pos
  have hlog := Real.log_nonpos (mul_nonneg hpos.le hd.le)
    (mul_dim_le_one_of_ne_zero hρ hinv htr p hp)
  rw [Real.log_mul hpos.ne' hd.ne'] at hlog
  apply mul_nonneg hpos.le
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hu
  linarith

/-
Provenance-ID: 8753-qic-schur-label-moments-02
Original formalization, no upstream Lean proof text reused.
Declaration: PermutationRepresentation.re_trace_mul_exp_neg_centered_labelEntropy_le
Manuscript: September 24, 2026, comparator:signed-label-moments, lines 227–237.
-/

include hρ hinv in
/-- The negative centered label moment is controlled by two actual exponential
moments, by weighted trace Cauchy–Schwarz. This is the signed transfer in the
area-law manuscript, `07-comparators.tex`, lines 227–237. No trace normalization
or sign restriction on the parameter is needed for this comparison. -/
theorem re_trace_mul_exp_neg_centered_labelEntropy_le (s u : ℝ) :
    (ρ * NormedSpace.exp ((-u : ℂ) • (labelEntropy φ - (s : ℂ) • 1))).trace.re ≤
      Real.sqrt
        ((ρ * NormedSpace.exp ((-2 * u : ℂ) • (-CFC.log ρ - (s : ℂ) • 1))).trace.re *
          (ρ * NormedSpace.exp ((2 * u : ℂ) • (-CFC.log ρ - labelEntropy φ))).trace.re) := by
  classical
  let R := isOrthogonalResolution_joint hρ hinv
  let a : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℝ :=
    fun p ↦ -2 * u * (-Real.log (p.1 : ℝ) - s)
  let b : hρ.isHermitian.eigenvalueSet × IrrepLabel G → ℝ :=
    fun p ↦ 2 * u * (-Real.log (p.1 : ℝ) - Real.log p.2.dim)
  let A := R.hom (fun p ↦ (a p : ℂ))
  let B := R.hom (fun p ↦ (b p : ℂ))
  have hA : A.IsHermitian := R.isHermitian_hom (isHermitian_joint hρ hinv) a
  have hB : B.IsHermitian := R.isHermitian_hom (isHermitian_joint hρ hinv) b
  have hAB : Commute A B := by
    change R.hom _ * R.hom _ = R.hom _ * R.hom _
    rw [← map_mul, ← map_mul]
    congr 1
    exact mul_comm _ _
  have hAe : ((-2 * u : ℂ) • (-CFC.log ρ - (s : ℂ) • 1)) = A := by
    rw [neg_log_eq_joint_hom hρ hinv]
    simpa only [A, a, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] using
      centered_hom R (fun p ↦ -Real.log (p.1 : ℝ)) s (-2 * u)
  have hBe : ((2 * u : ℂ) • (-CFC.log ρ - labelEntropy φ)) = B := by
    rw [neg_log_eq_joint_hom hρ hinv, labelEntropy_eq_joint_hom hρ hinv,
      ← map_sub, ← map_smul]
    congr 1
    funext p
    simp only [b, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_neg, Complex.ofReal_ofNat]
  have hcenter : ((1 / 2 : ℝ) : ℂ) • A + ((1 - 1 / 2 : ℝ) : ℂ) • B =
      (-u : ℂ) • (labelEntropy φ - (s : ℂ) • 1) := by
    rw [labelEntropy_eq_joint_hom hρ hinv]
    have hc := centered_hom R (fun p ↦ Real.log p.2.dim) s (-u)
    rw [Complex.ofReal_neg] at hc
    rw [hc]
    change ((1 / 2 : ℝ) : ℂ) • R.hom _ + ((1 - 1 / 2 : ℝ) : ℂ) • R.hom _ = _
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    funext p
    simp only [a, b, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have h := hρ.re_trace_mul_exp_smul_add_le hA hB hAB (1 / 2) (by norm_num) (by norm_num)
  rw [hcenter] at h
  rw [hAe, hBe]
  refine h.trans_eq ?_
  rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    Real.sqrt_mul (hρ.re_trace_mul_exp_nonneg hA)]

end PermutationRepresentation

namespace TensorPower

open PermutationRepresentation

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
  {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}

/-
Provenance-ID: 8753-qic-schur-label-moments-03
Original formalization, no upstream Lean proof text reused.
Declaration: TensorPower.centered_labelEntropy_moments_le
Manuscript: September 24, 2026, comparator:signed-label-moments, lines 227–237.
-/

/-- Both centered label moments for the actual copy-permutation action. The
negative moment incurs only the polynomial Schur remainder, while the positive
moment is bounded directly by the supported surprisal moment. This is the
transfer step in OpenAI's area-law manuscript, `07-comparators.tex`, lines
227–237; estimates for the centered surprisal moments are separate. -/
theorem centered_labelEntropy_moments_le (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ σ, Commute (permOp (copyPerm Ω k) σ) ρ)
    (s u : ℝ) (hu : 0 ≤ u) (hu2 : 2 * u ≤ 1) :
    (ρ * NormedSpace.exp ((u : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re ≤
        (ρ * NormedSpace.exp ((u : ℂ) • (-CFC.log ρ - (s : ℂ) • 1))).trace.re ∧
    (ρ * NormedSpace.exp ((-u : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re ≤
        Real.sqrt ((ρ * NormedSpace.exp ((-2 * u : ℂ) •
          (-CFC.log ρ - (s : ℂ) • 1))).trace.re *
            ((k + 1) ^ (Fintype.card Ω ^ 2) : ℕ)) := by
  refine ⟨re_trace_mul_exp_centered_labelEntropy_le hρ hinv htr s u hu, ?_⟩
  have hA : ((-2 * u : ℂ) • (-CFC.log ρ - (s : ℂ) • 1)).IsHermitian := by
    apply Matrix.IsHermitian.smul
    · apply Matrix.IsHermitian.sub
      · exact IsSelfAdjoint.log.neg
      · exact Matrix.isHermitian_one.smul (by change star (s : ℂ) = (s : ℂ); simp)
    · change star (-2 * (u : ℂ)) = -2 * (u : ℂ)
      simp
  have hm := (schurSurprisal hρ htr hinv).2.2.2 (2 * u) hu2
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hm
  exact (re_trace_mul_exp_neg_centered_labelEntropy_le hρ hinv s u).trans
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hm
      (hρ.re_trace_mul_exp_nonneg hA)))

end TensorPower
