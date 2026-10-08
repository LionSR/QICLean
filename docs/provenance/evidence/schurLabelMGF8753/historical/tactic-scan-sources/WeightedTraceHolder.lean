/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import QICLean.Analysis.OrthogonalResolution
import QICLean.Algebra.MatrixAux

/-!
# Weighted trace Hölder inequalities for commuting matrices

A positive semidefinite matrix defines a finite positive weight on the joint
spectral projections of commuting Hermitian matrices. Scalar weighted Hölder
therefore bounds the exponential trace of a convex combination by the product
of the separate exponential traces. Equal weights give the corresponding
inequality for any nonempty finite family.

This is the finite-dimensional analytic inequality used in OpenAI,
*A two-dimensional area law from a global spectral gap*, September 24, 2026,
`07-comparators.tex`, lines 553–560. The five-factor case supplies the Hölder
step of the sharp component estimate. The actual physical label moments,
merge moments and their assembly with the physical spectral projection are
separate arguments. The trace weight need not be normalized or commute with
the observables. A zero weight and an empty ambient coordinate set are included.
-/

open scoped BigOperators

namespace Real

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Finite weighted Hölder for exponentials, auxiliary to Section 7,
07-comparators.tex, lines 556–560. The finite weight need not be normalized. -/
private theorem weighted_exp_holder (μ : I → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    (s : J → ℝ) (hs : ∀ j, 0 ≤ s j) (hsum : ∑ j, s j = 1) (x : J → I → ℝ) :
    (∑ i, μ i * exp (∑ j, s j * x j i)) ≤
      ∏ j, (∑ i, μ i * exp (x j i)) ^ s j := by
  classical
  by_cases hz : ∀ i, μ i = 0
  · simp only [hz, zero_mul, Finset.sum_const_zero]
    exact Finset.prod_nonneg fun j _ => rpow_nonneg (le_refl 0) (s j)
  push Not at hz
  obtain ⟨i₀, hi₀⟩ := hz
  have hμ₀ : 0 < μ i₀ := lt_of_le_of_ne (hμ i₀) (Ne.symm hi₀)
  let M : J → ℝ := fun j => ∑ i, μ i * exp (x j i)
  have hM (j : J) : 0 < M j := by
    exact Finset.sum_pos' (fun i _ => mul_nonneg (hμ i) (exp_pos _).le)
      ⟨i₀, Finset.mem_univ i₀, mul_pos hμ₀ (exp_pos _)⟩
  let K := ∑ j, s j * log (M j)
  have hpoint (i : I) : exp (∑ j, s j * x j i) ≤
      exp K * ∑ j, s j * exp (x j i - log (M j)) := by
    have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := s) (p := fun j => x j i - log (M j))
      (fun j _ => hs j) hsum (fun j _ => Set.mem_univ (x j i - log (M j)))
    simp only [smul_eq_mul] at hJ
    calc
      exp (∑ j, s j * x j i) = exp K * exp (∑ j, s j * (x j i - log (M j))) := by
        rw [← exp_add]
        congr 1
        simp only [K, mul_sub, Finset.sum_sub_distrib]
        ring
      _ ≤ exp K * ∑ j, s j * exp (x j i - log (M j)) :=
        mul_le_mul_of_nonneg_left hJ (exp_pos K).le
  have hnormal (j : J) : (∑ i, μ i * exp (x j i - log (M j))) = 1 := by
    simp_rw [exp_sub, exp_log (hM j), ← mul_div_assoc]
    rw [← Finset.sum_div]
    exact div_self (hM j).ne'
  calc
    (∑ i, μ i * exp (∑ j, s j * x j i)) ≤
        ∑ i, μ i * (exp K * ∑ j, s j * exp (x j i - log (M j))) := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpoint i) (hμ i)
    _ = ∑ j, (exp K * s j) * (∑ i, μ i * exp (x j i - log (M j))) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    _ = exp K := by
      simp_rw [hnormal, mul_one]
      rw [← Finset.mul_sum, hsum, mul_one]
    _ = ∏ j, M j ^ s j := by
      simp_rw [rpow_def_of_pos (hM _)]
      rw [← exp_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end Real

open scoped ComplexOrder Matrix.Norms.Operator

namespace Matrix

variable {n I J : Type*} [Fintype n] [DecidableEq n] [Fintype I] [DecidableEq I]
  [Fintype J]

private theorem re_trace_mul_exp_resolution {P : I → Matrix n n ℂ}
    (hP : IsOrthogonalResolution P) (ρ : Matrix n n ℂ) (x : I → ℝ) :
    (ρ * NormedSpace.exp (hP.hom fun i => (x i : ℂ))).trace.re =
      ∑ i, Real.exp (x i) * (ρ * P i).trace.re := by
  rw [hP.exp_hom, hP.hom_apply, Finset.mul_sum]
  simp only [Matrix.mul_smul, trace_sum, trace_smul, smul_eq_mul, Complex.re_sum,
    ← Complex.ofReal_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

private theorem re_trace_mul_exp_resolution_holder {P : I → Matrix n n ℂ}
    (hP : IsOrthogonalResolution P) (hH : ∀ i, (P i).IsHermitian)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (s : J → ℝ) (hs : ∀ j, 0 ≤ s j) (hsum : ∑ j, s j = 1) (x : J → I → ℝ) :
    (ρ * NormedSpace.exp (hP.hom fun i => ((∑ j, s j * x j i : ℝ) : ℂ))).trace.re ≤
      ∏ j, (ρ * NormedSpace.exp (hP.hom fun i => (x j i : ℂ))).trace.re ^ s j := by
  have hw (i : I) : 0 ≤ (ρ * P i).trace.re :=
    (Complex.nonneg_iff.mp (hρ.trace_mul_nonneg
      ((hH i).posSemidef_of_mul_self (hP.mul_self i)))).1
  simp_rw [re_trace_mul_exp_resolution, mul_comm (Real.exp _) _]
  exact Real.weighted_exp_holder (fun i => (ρ * P i).trace.re) hw s hs hsum x

/-
Provenance-ID: 8753-qic-weighted-trace-holder-03
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.PosSemidef.re_trace_mul_exp_smul_add_le
Manuscript: September 24, 2026, comparator:component-inverse, lines 553–560.
-/

/-- Weighted trace Hölder for two actual commuting Hermitian matrices.
Auxiliary to OpenAI area-law Section 7, lines 553–560. -/
theorem PosSemidef.re_trace_mul_exp_smul_add_le {ρ A B : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (ρ * NormedSpace.exp ((t : ℂ) • A + ((1 - t : ℝ) : ℂ) • B)).trace.re ≤
      (ρ * NormedSpace.exp A).trace.re ^ t *
        (ρ * NormedSpace.exp B).trace.re ^ (1 - t) := by
  classical
  have hc (a : hA.eigenvalueSet) (b : hB.eigenvalueSet) :
      Commute (hA.spectralProj a) (hB.spectralProj b) :=
    (hB.commute_spectralProj (hA.commute_spectralProj hAB a).symm b).symm
  let R := hA.isOrthogonalResolution_spectralProj.prod
    hB.isOrthogonalResolution_spectralProj hc
  have hH (p : hA.eigenvalueSet × hB.eigenvalueSet) :
      (hA.spectralProj p.1 * hB.spectralProj p.2).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, (hA.isHermitian_spectralProj p.1).eq,
      (hB.isHermitian_spectralProj p.2).eq, (hc p.1 p.2).eq]
  have hmA : R.hom (fun p => ((p.1 : ℝ) : ℂ)) = A :=
    (hA.isOrthogonalResolution_spectralProj.prod_hom_fst
      hB.isOrthogonalResolution_spectralProj R _).trans hA.eq_hom.symm
  have hmB : R.hom (fun p => ((p.2 : ℝ) : ℂ)) = B :=
    (hA.isOrthogonalResolution_spectralProj.prod_hom_snd
      hB.isOrthogonalResolution_spectralProj R _).trans hB.eq_hom.symm
  have hm : R.hom (fun p => ((t * (p.1 : ℝ) + (1 - t) * (p.2 : ℝ) : ℝ) : ℂ)) =
      (t : ℂ) • A + ((1 - t : ℝ) : ℂ) • B := by
    calc
      _ = (t : ℂ) • R.hom (fun p => ((p.1 : ℝ) : ℂ)) +
          ((1 - t : ℝ) : ℂ) • R.hom (fun p => ((p.2 : ℝ) : ℂ)) := by
        rw [← map_smul, ← map_smul, ← map_add]
        congr 1
        funext p
        simp [Complex.ofReal_add, Complex.ofReal_mul]
      _ = _ := by rw [hmA, hmB]
  let s : Bool → ℝ := fun b => if b then t else 1 - t
  let x : Bool → hA.eigenvalueSet × hB.eigenvalueSet → ℝ :=
    fun b p => if b then p.1 else p.2
  have hs (b : Bool) : 0 ≤ s b := by
    cases b
    · exact sub_nonneg.mpr ht1
    · exact ht
  have hsum : ∑ b, s b = 1 := by simp [s]
  have h := re_trace_mul_exp_resolution_holder R hH hρ s hs hsum x
  simp only [s, x, Fintype.sum_bool, Fintype.prod_bool, Bool.false_eq_true,
    ite_true, ite_false] at h
  rw [hm, hmA, hmB] at h
  exact h

/-
Provenance-ID: 8753-qic-weighted-trace-holder-05
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.PosSemidef.re_trace_mul_exp_nonneg
Manuscript: September 24, 2026, comparator:component-inverse, lines 553–560.
-/

/-- A positive semidefinite trace weight has a nonnegative pairing with the
exponential of any Hermitian matrix. OpenAI area-law manuscript,
`07-comparators.tex`, lines 553–560, and the signed label-moment transfer at
lines 227–237. Neither normalization nor commutation with the weight is needed. -/
theorem PosSemidef.re_trace_mul_exp_nonneg {ρ A : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hA : A.IsHermitian) :
    0 ≤ (ρ * NormedSpace.exp A).trace.re := by
  rw [hA.eq_hom, re_trace_mul_exp_resolution]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.exp_pos _).le
    (Complex.nonneg_iff.mp (hρ.trace_mul_nonneg
      ((hA.isHermitian_spectralProj i).posSemidef_of_mul_self
        (hA.isOrthogonalResolution_spectralProj.mul_self i)))).1

/-
Provenance-ID: 8753-qic-weighted-trace-holder-04
Original formalization, no upstream Lean proof text reused.
Declaration: Matrix.PosSemidef.re_trace_mul_exp_sum_le_prod
Manuscript: September 24, 2026, comparator:component-inverse, lines 553–560.
-/

/-- Equal-weight trace Hölder for actual pairwise commuting Hermitian matrices,
with an arbitrary positive semidefinite trace weight. The family has `m + 1`
members and the real exponent is unrestricted. OpenAI, *A two-dimensional area
law from a global spectral gap*, September 24, 2026, `07-comparators.tex`,
lines 553–560. Taking `m = 4` gives the five-factor inequality used there. -/
theorem PosSemidef.re_trace_mul_exp_sum_le_prod {ρ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (m : ℕ) (A : Fin (m + 1) → Matrix n n ℂ)
    (hA : ∀ i, (A i).IsHermitian) (hcomm : ∀ i j, Commute (A i) (A j)) (a : ℝ) :
    (ρ * NormedSpace.exp ((a : ℂ) • ∑ i, A i)).trace.re ≤
      ∏ i, (ρ * NormedSpace.exp (((((m + 1 : ℕ) : ℝ) * a : ℝ) : ℂ) • A i)).trace.re ^
        (1 / ((m + 1 : ℕ) : ℝ)) := by
  induction m generalizing a with
  | zero => simp
  | succ m ih =>
    let N : ℝ := (m + 2 : ℕ)
    let K : ℝ := (m + 1 : ℕ)
    have hK : 0 < K := by dsimp [K]; positivity
    have hN : 0 < N := by dsimp [N]; positivity
    have hNK : N = K + 1 := by dsimp [N, K]; push_cast; ring
    let B := ∑ i : Fin (m + 1), A i.succ
    have hB : B.IsHermitian := by
      rw [IsHermitian, conjTranspose_sum]
      exact Finset.sum_congr rfl fun i _ => (hA i.succ).eq
    have hAB : Commute (A 0) B :=
      Commute.sum_right Finset.univ (fun i : Fin (m + 1) => A i.succ) _
        (fun i _ => hcomm 0 i.succ)
    have hAs : ((N * a : ℝ) : ℂ) • A 0 |>.IsHermitian :=
      (hA 0).smul (by simp [IsSelfAdjoint])
    have hBs : ((N * a / K : ℝ) : ℂ) • B |>.IsHermitian :=
      hB.smul (by simp [IsSelfAdjoint])
    have hcomms : Commute (((N * a : ℝ) : ℂ) • A 0)
        (((N * a / K : ℝ) : ℂ) • B) := by
      rw [Commute, SemiconjBy, smul_mul_smul_comm, smul_mul_smul_comm, hAB.eq]
      congr 1
      ring
    have ht : 0 ≤ 1 / N := by positivity
    have ht1 : 1 / N ≤ 1 := by rw [div_le_iff₀ hN]; rw [hNK]; linarith
    have hs : 0 ≤ 1 - 1 / N := sub_nonneg.mpr ht1
    have halg : ((1 / N : ℝ) : ℂ) • (((N * a : ℝ) : ℂ) • A 0) +
        ((1 - 1 / N : ℝ) : ℂ) • (((N * a / K : ℝ) : ℂ) • B) =
        (a : ℂ) • (A 0 + B) := by
      rw [smul_smul, smul_smul, smul_add]
      have hfirst : 1 / N * (N * a) = a := by field_simp
      have hrest : (1 - 1 / N) * (N * a / K) = a := by rw [hNK]; field_simp; ring
      simp only [← Complex.ofReal_mul, hfirst, hrest]
    have h := hρ.re_trace_mul_exp_smul_add_le hAs hBs hcomms (1 / N) ht ht1
    rw [halg] at h
    have hi := ih (fun i => A i.succ) (fun i => hA i.succ)
      (fun i j => hcomm i.succ j.succ) (N * a / K)
    have hscale : K * (N * a / K) = N * a := by field_simp
    change (ρ * NormedSpace.exp (((N * a / K : ℝ) : ℂ) • B)).trace.re ≤
      ∏ i : Fin (m + 1),
        (ρ * NormedSpace.exp (((K * (N * a / K) : ℝ) : ℂ) • A i.succ)).trace.re ^ (1 / K) at hi
    rw [hscale] at hi
    have hp (i : Fin (m + 2)) :
        0 ≤ (ρ * NormedSpace.exp (((N * a : ℝ) : ℂ) • A i)).trace.re :=
      hρ.re_trace_mul_exp_nonneg ((hA i).smul (by simp [IsSelfAdjoint]))
    have hpow := Real.rpow_le_rpow (hρ.re_trace_mul_exp_nonneg hBs) hi hs
    have hexp : 1 / K * (1 - 1 / N) = 1 / N := by rw [hNK]; field_simp; ring
    rw [← Real.finsetProd_rpow Finset.univ _
      (fun i _ => Real.rpow_nonneg (hp i.succ) _) (1 - 1 / N)] at hpow
    simp_rw [← Real.rpow_mul (hp _), hexp] at hpow
    rw [Fin.sum_univ_succ]
    change (ρ * NormedSpace.exp ((a : ℂ) • (A 0 + B))).trace.re ≤ _
    calc
      _ ≤ _ := h
      _ ≤ (ρ * NormedSpace.exp (((N * a : ℝ) : ℂ) • A 0)).trace.re ^ (1 / N) *
          ∏ i : Fin (m + 1),
            (ρ * NormedSpace.exp (((N * a : ℝ) : ℂ) • A i.succ)).trace.re ^ (1 / N) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (hp 0) _)
      _ = _ := by
        simpa only [N] using (Fin.prod_univ_succ
          (fun i : Fin (m + 2) =>
            (ρ * NormedSpace.exp (((N * a : ℝ) : ℂ) • A i)).trace.re ^ (1 / N))).symm

end Matrix
