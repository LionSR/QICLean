/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteKroneckerPowers
import QICLean.Analysis.QuantumNeymanPearson
import QICLean.Channel.Schwarz.PetzOverlapDataProcessing

/-!
# Finite-copy quantum Chernoff bounds

For density matrices `ρ, σ`, a prior `p ∈ [0,1]`, and `s ∈ [0,1]`, the optimal
binary testing error on `N` independent copies satisfies
`e_N ≤ p ^ s * (1-p) ^ (1-s) * (petzOverlap s ρ σ) ^ N`.
The same bound holds for independent, nonidentical factors with the product of
their overlaps. No invertibility, common eigenbasis, or support condition is required.

This is the direct finite-copy estimate towards Wolf, Equation (8.44), derived
from Equations (8.41) and (8.54), `Notes/WolfNoteTexSource/ch08_distance_measures.tex`,
lines 548–590 and 660–665. It does not prove the asymptotic equality in (8.44):
the converse bound on the exponent remains open. See
`docs/paper-gaps/wolf_ch8_chernoff_asymptotics.tex`.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
namespace Matrix

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The minimum binary error, defined by optimization over all effects.
Wolf, Equations (8.40)–(8.43), source lines 543–577. -/
def optimalHypothesisTestError (p : ℝ) (ρ σ : Matrix m m ℂ) : ℝ :=
  sInf {e | ∃ P : Matrix m m ℂ, 0 ≤ P ∧ P ≤ 1 ∧ hypothesisTestError p ρ σ P = e}

/-- The operational minimum agrees with the trace-norm formula of Wolf (8.41). -/
theorem optimalHypothesisTestError_eq {ρ σ : Matrix m m ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) (p : ℝ) :
    optimalHypothesisTestError p ρ σ =
      (1 - (CFC.abs (p • ρ - (1 - p) • σ)).trace.re) / 2 :=
  (isLeast_hypothesisTestError hρ hσ hρ1 hσ1 p).csInf_eq

/-- A single optimal effect attains the minimum, independently of the exponent used
later to bound it. -/
theorem exists_hypothesisTestError_eq_optimal {ρ σ : Matrix m m ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) (p : ℝ) :
    ∃ P : Matrix m m ℂ, 0 ≤ P ∧ P ≤ 1 ∧
      hypothesisTestError p ρ σ P = optimalHypothesisTestError p ρ σ := by
  rw [optimalHypothesisTestError_eq hρ hσ hρ1 hσ1]
  exact (isLeast_hypothesisTestError hρ hσ hρ1 hσ1 p).1

/-- The minimum error is bounded above by the error of any effect. -/
theorem optimalHypothesisTestError_le {ρ σ P : Matrix m m ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) (p : ℝ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) :
    optimalHypothesisTestError p ρ σ ≤ hypothesisTestError p ρ σ P := by
  rw [optimalHypothesisTestError_eq hρ hσ hρ1 hσ1]
  exact hypothesisTestError_ge hρ hσ hρ1 hσ1 p hP0 hP1

/-- For density matrices and a genuine prior the minimum error is nonnegative. -/
theorem optimalHypothesisTestError_nonneg {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ optimalHypothesisTestError p ρ σ := by
  obtain ⟨P, hP0, hP1, heq⟩ :=
    exists_hypothesisTestError_eq_optimal hρ.isHermitian hσ.isHermitian hρ1 hσ1 p
  rw [← heq, hypothesisTestError]
  exact add_nonneg
    (mul_nonneg hp.1 (hρ.re_trace_mul_nonneg (le_iff.mp hP1)))
    (mul_nonneg (sub_nonneg.mpr hp.2)
      (hσ.re_trace_mul_nonneg (nonneg_iff_posSemidef.mp hP0)))

/-- Constant guesses give the elementary upper bound on the minimum error. -/
theorem optimalHypothesisTestError_le_min {ρ σ : Matrix m m ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) (p : ℝ) :
    optimalHypothesisTestError p ρ σ ≤ min p (1 - p) := by
  apply le_min
  · simpa [hypothesisTestError, hρ1] using
      optimalHypothesisTestError_le hρ hσ hρ1 hσ1 p (P := 0) le_rfl zero_le_one
  · simpa [hypothesisTestError, hσ1] using
      optimalHypothesisTestError_le hρ hσ hρ1 hσ1 p (P := 1) zero_le_one le_rfl

/-- The ordinary overlap is nonnegative. -/
theorem petzOverlap_nonneg (s : ℝ) (ρ σ : Matrix m m ℂ) :
    0 ≤ petzOverlap s ρ σ :=
  (nonneg_iff_posSemidef.mp CFC.rpow_nonneg).re_trace_mul_nonneg
    (nonneg_iff_posSemidef.mp CFC.rpow_nonneg)

/-- Independent scalar weights factor out of the overlap. -/
theorem petzOverlap_smul {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (s : ℝ) :
    petzOverlap s (a • ρ) (b • σ) = a ^ s * b ^ (1 - s) * petzOverlap s ρ σ := by
  simp only [petzOverlap, hρ.smul_rpow ha, hσ.smul_rpow hb,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, trace_smul,
    Complex.smul_re, smul_eq_mul]
  ring

/-- Overlaps of independent positive matrix pairs multiply. -/
theorem petzOverlap_kronecker {A B : Matrix m m ℂ} {C D : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hC : C.PosSemidef)
    (hD : D.PosSemidef) (s : ℝ) :
    petzOverlap s (A ⊗ₖ C) (B ⊗ₖ D) = petzOverlap s A B * petzOverlap s C D := by
  have hAs : (A ^ s).PosSemidef := nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have hBs : (B ^ (1 - s)).PosSemidef := nonneg_iff_posSemidef.mp CFC.rpow_nonneg
  have him : (A ^ s * B ^ (1 - s)).trace.im = 0 :=
    (Complex.nonneg_iff.mp (hAs.trace_mul_nonneg hBs)).2.symm
  simp only [petzOverlap, hA.rpow_kronecker hC, hB.rpow_kronecker hD,
    ← mul_kronecker_mul, trace_kronecker, Complex.mul_re, him, zero_mul, sub_zero]

/-- A finite product of independent pairs has overlap equal to the product of
its single-factor overlaps. -/
theorem petzOverlap_finKronecker {N : ℕ} {I : Fin N → Type}
    [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    (A B : (i : Fin N) → Matrix (I i) (I i) ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef) (s : ℝ) :
    petzOverlap s (finKronecker A) (finKronecker B) = ∏ i, petzOverlap s (A i) (B i) := by
  have hreal (i : Fin N) : ((A i ^ s * B i ^ (1 - s)).trace.re : ℂ) =
      (A i ^ s * B i ^ (1 - s)).trace := by
    have hAs : (A i ^ s).PosSemidef := nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    have hBs : (B i ^ (1 - s)).PosSemidef := nonneg_iff_posSemidef.mp CFC.rpow_nonneg
    apply Complex.ext
    · simp
    · simpa using (Complex.nonneg_iff.mp (hAs.trace_mul_nonneg hBs)).2
  unfold petzOverlap
  rw [rpow_finKronecker A hA, rpow_finKronecker B hB,
    ← finKronecker_mul, trace_finKronecker]
  calc
    _ = (∏ i, ((A i ^ s * B i ^ (1 - s)).trace.re : ℂ)).re :=
      congrArg Complex.re (Finset.prod_congr rfl (fun i _ ↦ (hreal i).symm))
    _ = _ := by rw [← Complex.ofReal_prod, Complex.ofReal_re]

/-- The one-copy Chernoff upper bound, obtained from Wolf (8.54) and optimality
in (8.41). Singular states and endpoint priors and exponents are included. -/
theorem optimalHypothesisTestError_le_petzOverlap {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) {p s : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    optimalHypothesisTestError p ρ σ ≤
      p ^ s * (1 - p) ^ (1 - s) * petzOverlap s ρ σ := by
  rw [← petzOverlap_smul hρ hσ hp.1 (sub_nonneg.mpr hp.2),
    optimalHypothesisTestError_eq hρ.isHermitian hσ.isHermitian hρ1 hσ1]
  have h := re_trace_add_sub_two_mul_re_trace_rpow_mul_rpow_le
    (hρ.smul hp.1) (hσ.smul (sub_nonneg.mpr hp.2)) hs
  simp only [trace_add, trace_smul, Complex.add_re, Complex.smul_re,
    hρ1, hσ1, Complex.one_re, smul_eq_mul, mul_one] at h
  unfold petzOverlap
  linarith

/-- Finite-copy Chernoff bound for independent, not necessarily identical, density
matrices. This is a direct estimate towards Wolf (8.44), source lines 580–590. -/
theorem optimalHypothesisTestError_finKronecker_le {N : ℕ} {I : Fin N → Type}
    [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]
    (ρ σ : (i : Fin N) → Matrix (I i) (I i) ℂ)
    (hρ : ∀ i, (ρ i).PosSemidef) (hσ : ∀ i, (σ i).PosSemidef)
    (hρ1 : ∀ i, (ρ i).trace = 1) (hσ1 : ∀ i, (σ i).trace = 1)
    {p s : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    optimalHypothesisTestError p (finKronecker ρ) (finKronecker σ) ≤
      p ^ s * (1 - p) ^ (1 - s) * ∏ i, petzOverlap s (ρ i) (σ i) := by
  have h := optimalHypothesisTestError_le_petzOverlap
    (finKronecker_posSemidef ρ hρ) (finKronecker_posSemidef σ hσ)
    (by simp [trace_finKronecker, hρ1]) (by simp [trace_finKronecker, hσ1]) hp hs
  rwa [petzOverlap_finKronecker ρ σ hρ hσ] at h

/-- The optimal error on `N` identical copies is bounded by a power of the one-copy
overlap. This proves the finite-copy direct bound towards Wolf (8.44), not its converse. -/
theorem optimalHypothesisTestError_iid_le {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) {p s : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    optimalHypothesisTestError p (finKronecker (fun _ : Fin N ↦ ρ))
      (finKronecker (fun _ : Fin N ↦ σ)) ≤
        p ^ s * (1 - p) ^ (1 - s) * petzOverlap s ρ σ ^ N := by
  simpa using optimalHypothesisTestError_finKronecker_le
    (fun _ : Fin N ↦ ρ) (fun _ : Fin N ↦ σ)
    (fun _ ↦ hρ) (fun _ ↦ hσ) (fun _ ↦ hρ1) (fun _ ↦ hσ1) hp hs

/-- Optimizing the finite-copy bound over the exponent is valid even when the
infimum is not attained (as can happen at singular endpoint limits). -/
theorem optimalHypothesisTestError_iid_le_sInf {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) (N : ℕ) :
    optimalHypothesisTestError p (finKronecker (fun _ : Fin N ↦ ρ))
      (finKronecker (fun _ : Fin N ↦ σ)) ≤
        sInf ((fun s : ℝ ↦ p ^ s * (1 - p) ^ (1 - s) * petzOverlap s ρ σ ^ N) ''
          Set.Icc (0 : ℝ) 1) := by
  apply le_csInf
    ((Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)).image _)
  rintro _ ⟨s, hs, rfl⟩
  exact optimalHypothesisTestError_iid_le hρ hσ hρ1 hσ1 hp hs N

/-- A positive overlap gives an explicit exponential bound for every copy count.
The prior contributes at most one; the bound is uniform over all priors in `[0,1]`.
This is the direct rate estimate towards Wolf (8.44), source lines 580–590. -/
theorem optimalHypothesisTestError_iid_le_exp {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) {p s : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hq : 0 < petzOverlap s ρ σ) (N : ℕ) :
    optimalHypothesisTestError p (finKronecker (fun _ : Fin N ↦ ρ))
      (finKronecker (fun _ : Fin N ↦ σ)) ≤
        Real.exp (N * Real.log (petzOverlap s ρ σ)) := by
  have hc : p ^ s * (1 - p) ^ (1 - s) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul (Real.rpow_le_one hp.1 hp.2 hs.1)
        (Real.rpow_le_one (sub_nonneg.mpr hp.2) (by linarith [hp.1])
          (sub_nonneg.mpr hs.2))
        (Real.rpow_nonneg (sub_nonneg.mpr hp.2) _) zero_le_one
      _ = 1 := one_mul 1
  calc
    _ ≤ p ^ s * (1 - p) ^ (1 - s) * petzOverlap s ρ σ ^ N :=
      optimalHypothesisTestError_iid_le hρ hσ hρ1 hσ1 hp hs N
    _ ≤ petzOverlap s ρ σ ^ N := mul_le_of_le_one_left (pow_nonneg hq.le N) hc
    _ = Real.exp (N * Real.log (petzOverlap s ρ σ)) := by
      rw [Real.exp_nat_mul, Real.exp_log hq]

/-- An overlap strictly below one forces the optimal iid testing error to vanish.
This consequence of the finite-copy estimate does not assert the converse exponent. -/
theorem tendsto_optimalHypothesisTestError_iid_zero {ρ σ : Matrix m m ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1)
    (hσ1 : σ.trace = 1) {p s : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (hlt : petzOverlap s ρ σ < 1) :
    Filter.Tendsto (fun N : ℕ ↦ optimalHypothesisTestError p
      (finKronecker (fun _ : Fin N ↦ ρ)) (finKronecker (fun _ : Fin N ↦ σ)))
      Filter.atTop (nhds 0) := by
  apply squeeze_zero
    (fun N ↦ optimalHypothesisTestError_nonneg
      (finKronecker_posSemidef _ (fun _ ↦ hρ))
      (finKronecker_posSemidef _ (fun _ ↦ hσ))
      (by simp [trace_finKronecker, hρ1]) (by simp [trace_finKronecker, hσ1]) hp)
    (optimalHypothesisTestError_iid_le hρ hσ hρ1 hσ1 hp hs)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (petzOverlap_nonneg s ρ σ) hlt).const_mul
    (p ^ s * (1 - p) ^ (1 - s))

end Matrix
