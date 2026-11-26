/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.Permutation.SchurSurprisal
import QICLean.Analysis.TraceInequality.WeightedTraceHolder

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

Independently formalized from the manuscript; no upstream Lean proof text is
reused.

It also contains the following results.

* `TensorPower.log_centered_labelEntropy_moments_le`,
  `TensorPower.log_centered_labelEntropy_moments_uniform`: quantitative transfer of centered
  surprisal moments to Schur labels.
-/

section SchurLabelMoments

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
Original formalization, no upstream Lean proof text reused.
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
Original formalization, no upstream Lean proof text reused.
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
Original formalization, no upstream Lean proof text reused.
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

end

end SchurLabelMoments

section SchurLabelMomentBounds

/-!
## Quantitative transfer of centered surprisal moments to Schur labels

For an actual permutation-invariant density on `k` copies, assume an explicit
quadratic bound for the logarithm of its centered surprisal moment on a
symmetric interval. The positive label moment has the same bound. The negative
label moment has twice the quadratic coefficient and an explicit logarithmic
loss from the polynomial Schur remainder.

This is the conditional scalar transfer in OpenAI's area-law manuscript,
September 24, 2026, `07-comparators.tex`, lines 227–238. The hypothesis is the
centered `k`-copy surprisal estimate. Identifying it with the tensor power of a
marginal and deriving it from the one-copy assumption `comparator:mgf-data`
(lines 75–85) are separate arguments. No label moment bound is assumed.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

/-- A nonzero positive trace weight pairs strictly positively with a Hermitian
exponential; the exponential is positive definite even when the weight is singular. -/
private theorem re_trace_mul_exp_pos {X : Type*} [Fintype X] [DecidableEq X]
    {ρ A : Matrix X X ℂ} (hρ : ρ.PosSemidef) (hne : ρ ≠ 0) (hA : A.IsHermitian) :
    0 < (ρ * NormedSpace.exp A).trace.re := by
  let _ : NormedAlgebra ℚ (Matrix X X ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hp : (NormedSpace.exp A).PosDef :=
    (show IsSelfAdjoint A from hA).exp_nonneg.posSemidef.posDef_iff_isUnit.mpr
      (NormedSpace.isUnit_exp A)
  exact (Complex.pos_iff.mp (hρ.trace_mul_pos_of_ne_zero_of_posDef hne hp)).1

end Matrix

namespace TensorPower

open PermutationRepresentation

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {k : ℕ}
  {ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ}

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:signed-label-moments, lines 227–238.
-/

/-- A centered surprisal logarithmic moment bound transfers to both label signs,
with explicit coefficients and the common range `u ≤ min(c₀,1)/(2√ℬ)`.
This is the conditional transfer in `07-comparators.tex`, lines 227–238;
the assumed moment estimate concerns the actual `k`-copy surprisal, not the label. -/
theorem log_centered_labelEntropy_moments_le (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ σ, Commute (permOp (copyPerm Ω k) σ) ρ)
    (s C₀ c₀ ℬ : ℝ) (hℬ : 1 ≤ ℬ)
    (hL : ∀ t : ℝ, |t| ≤ c₀ / Real.sqrt ℬ →
      Real.log (ρ * NormedSpace.exp ((t : ℂ) • (-CFC.log ρ - (s : ℂ) • 1))).trace.re ≤
        C₀ * k * ℬ * t ^ 2)
    (u : ℝ) (hu : 0 ≤ u) (hur : u ≤ (min c₀ 1 / 2) / Real.sqrt ℬ) :
    Real.log (ρ * NormedSpace.exp ((u : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re ≤ C₀ * k * ℬ * u ^ 2 ∧
    Real.log (ρ * NormedSpace.exp ((-u : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re ≤
        2 * C₀ * k * ℬ * u ^ 2 + ((Fintype.card Ω : ℝ) ^ 2 / 2) * Real.log (k + 1) := by
  have hsqrt : 1 ≤ Real.sqrt ℬ := (Real.one_le_sqrt).mpr hℬ
  have hsqrtpos : 0 < Real.sqrt ℬ := zero_lt_one.trans_le hsqrt
  have hmul := (le_div_iff₀ hsqrtpos).mp hur
  have hu_mul : u ≤ u * Real.sqrt ℬ := le_mul_of_one_le_right hu hsqrt
  have hsmall : 2 * u ≤ 1 := by linarith [min_le_right c₀ (1 : ℝ)]
  have hdouble : 2 * u ≤ c₀ / Real.sqrt ℬ := by
    apply (le_div_iff₀ hsqrtpos).mpr
    nlinarith [min_le_left c₀ (1 : ℝ)]
  have hplusrange : |u| ≤ c₀ / Real.sqrt ℬ := by
    rw [abs_of_nonneg hu]
    linarith
  have hminusrange : |-2 * u| ≤ c₀ / Real.sqrt ℬ := by
    rw [abs_of_nonpos (by linarith : -2 * u ≤ 0)]
    linarith
  have hne : ρ ≠ 0 := by
    intro hz
    simp [hz] at htr
  have hpos (A : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (hA : A.IsHermitian) (t : ℝ) :
      0 < (ρ * NormedSpace.exp ((t : ℂ) • (A - (s : ℂ) • 1))).trace.re := by
    apply Matrix.re_trace_mul_exp_pos hρ hne
    apply Matrix.IsHermitian.smul
    · exact hA.sub (Matrix.isHermitian_one.smul
        (by change star (s : ℂ) = (s : ℂ); simp))
    · change star (t : ℂ) = (t : ℂ)
      simp
  have hF := (posSemidef_labelEntropy (copyPerm Ω k)).isHermitian
  have hlog : (-CFC.log ρ).IsHermitian := IsSelfAdjoint.log.neg
  obtain ⟨hplus, hminus⟩ := centered_labelEntropy_moments_le hρ htr hinv s u hu hsmall
  refine ⟨(Real.log_le_log (hpos _ hF u) hplus).trans (hL u hplusrange), ?_⟩
  have hnpos : 0 < (ρ * NormedSpace.exp ((-u : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re := by
    simpa only [Complex.ofReal_neg] using hpos _ hF (-u)
  have hLpos : 0 < (ρ * NormedSpace.exp ((-2 * u : ℂ) •
      (-CFC.log ρ - (s : ℂ) • 1))).trace.re := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] using
      hpos _ hlog (-2 * u)
  have hpolypos : 0 < ((k : ℝ) + 1) ^ (Fintype.card Ω ^ 2) := by positivity
  have hm := Real.log_le_log hnpos hminus
  simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hm
  rw [Real.log_sqrt (mul_nonneg hLpos.le hpolypos.le),
    Real.log_mul hLpos.ne' hpolypos.ne', Real.log_pow] at hm
  have hminusL := hL (-2 * u) hminusrange
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat] at hminusL
  calc
    _ ≤ ((Real.log (ρ * NormedSpace.exp ((-2 * u : ℂ) •
          (-CFC.log ρ - (s : ℂ) • 1))).trace.re) +
            (Fintype.card Ω ^ 2 : ℕ) * Real.log ((k : ℝ) + 1)) / 2 := hm
    _ ≤ (C₀ * k * ℬ * (-2 * u) ^ 2 +
            (Fintype.card Ω ^ 2 : ℕ) * Real.log ((k : ℝ) + 1)) / 2 := by gcongr
    _ = _ := by push_cast; ring

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:signed-label-moments, lines 227–238.
-/

/-- Both signs satisfy one quadratic-plus-logarithmic bound on the same symmetric
interval. This is the conditional uniform form of `comparator:signed-label-moments`,
`07-comparators.tex`, lines 227–238. Its quadratic coefficient is independent of
the one-copy dimension; that dimension enters only the logarithmic remainder. -/
theorem log_centered_labelEntropy_moments_uniform
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hinv : ∀ σ, Commute (permOp (copyPerm Ω k) σ) ρ)
    (s C₀ c₀ ℬ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) (hℬ : 1 ≤ ℬ)
    (hL : ∀ t : ℝ, |t| ≤ c₀ / Real.sqrt ℬ →
      Real.log (ρ * NormedSpace.exp ((t : ℂ) • (-CFC.log ρ - (s : ℂ) • 1))).trace.re ≤
        C₀ * k * ℬ * t ^ 2) :
    0 < min c₀ 1 / 2 ∧
      ∀ t : ℝ, |t| ≤ (min c₀ 1 / 2) / Real.sqrt ℬ →
    Real.log (ρ * NormedSpace.exp ((t : ℂ) •
      (labelEntropy (copyPerm Ω k) - (s : ℂ) • 1))).trace.re ≤
        2 * C₀ * k * ℬ * t ^ 2 + ((Fintype.card Ω : ℝ) ^ 2 / 2) * Real.log (k + 1) := by
  refine ⟨div_pos (lt_min hc zero_lt_one) (by norm_num), ?_⟩
  intro t ht
  obtain ⟨hplus, hminus⟩ := log_centered_labelEntropy_moments_le
    hρ htr hinv s C₀ c₀ ℬ hℬ hL |t| (abs_nonneg t) ht
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0] at hplus
    have hquad : 0 ≤ C₀ * k * ℬ * t ^ 2 := by positivity
    have hlog : 0 ≤ Real.log ((k : ℝ) + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k])
    have hpoly : 0 ≤ ((Fintype.card Ω : ℝ) ^ 2 / 2) * Real.log ((k : ℝ) + 1) :=
      mul_nonneg (by positivity) hlog
    nlinarith
  · simpa only [abs_of_nonpos (le_of_lt (lt_of_not_ge ht0)), Complex.ofReal_neg,
      neg_neg, neg_sq] using hminus

end TensorPower

end

end SchurLabelMomentBounds
