/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceExponentialPerturbation
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Energy-normalized operator bounds for mandatory labels

A finite alternating sum of Hamiltonians with selected local terms removed
collects the words containing every selected label. A supplied scalar lower
bound for the full Hamiltonian controls its operator norm without a partition
function. This is an auxiliary estimate for the interaction-label expansion;
no spatial cut or matrix product operator construction is asserted.

This is a corrected auxiliary mandatory-label bound for ALVV,
arXiv:1602.08828v2, `thm:cluster-approx`, source lines 1270–1291 and
1935–1968.

**Local fix (energy normalization and interaction labels):** the printed
spatial approximation estimate is false under its stated hypotheses. The
result here instead controls a mandatory-label finite sum with an explicit
energy normalization. It does not assert the printed spatial theorem;
see https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Finset

namespace Matrix

variable {n κ : Type*} [Fintype n] [DecidableEq n] [DecidableEq κ]

/-- The decay-semigroup norm bound from an actual scalar spectral lower bound. -/
private theorem norm_exp_neg_smul_le {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {lambda t : ℝ} (hlo : (lambda : ℂ) • 1 ≤ H) (ht : 0 ≤ t) :
    ‖NormedSpace.exp (-(t • H))‖ ≤ Real.exp (-t * lambda) := by
  have hself : IsSelfAdjoint (-(t • H)) :=
    (hH.smul (IsSelfAdjoint.all t)).neg.isSelfAdjoint
  rw [← CFC.real_exp_eq_normedSpace_exp hself, ← neg_smul,
    ← cfc_const_mul_id (-t) H hH.isSelfAdjoint,
    ← cfc_comp' Real.exp (fun x : ℝ ↦ -t * x) H
      Real.continuous_exp.continuousOn (by fun_prop) hH.isSelfAdjoint]
  have hspec : ∀ x ∈ spectrum ℝ H, lambda ≤ x :=
    (algebraMap_le_iff_le_spectrum hH.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul] using hlo)
  exact norm_cfc_le (Real.exp_nonneg _) fun x hx ↦ by
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hspec x hx) (neg_nonpos.mpr ht))

private noncomputable def mandatoryExp (H : Matrix n n ℂ) (h : κ → Matrix n n ℂ)
    (S : Finset κ) (t : ℝ) : Matrix n n ℂ :=
  ∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card •
    NormedSpace.exp (-(t • (H - ∑ i ∈ T, h i)))

omit [DecidableEq κ] in
private theorem mandatoryExp_empty (H : Matrix n n ℂ) (h : κ → Matrix n n ℂ) (t : ℝ) :
    mandatoryExp H h ∅ t = NormedSpace.exp (-(t • H)) := by
  simp [mandatoryExp]

omit [Fintype n] [DecidableEq n] in
private theorem sum_powerset_sign_mem (S : Finset κ) {i : κ} (hi : i ∈ S)
    (F : Finset κ → Matrix n n ℂ) :
    (∑ T ∈ S.powerset, if i ∈ T then (-1 : ℂ) ^ T.card • F T else 0) =
      -(∑ U ∈ (S.erase i).powerset, (-1 : ℂ) ^ U.card • F (insert i U)) := by
  conv_lhs => rw [← Finset.insert_erase hi, Finset.sum_powerset_insert (notMem_erase i S)]
  have hzero : (∑ U ∈ (S.erase i).powerset,
      if i ∈ U then (-1 : ℂ) ^ U.card • F U else 0) = 0 :=
    Finset.sum_eq_zero fun U hU ↦
      ite_eq_right (notMem_mono (Finset.mem_powerset.mp hU) (notMem_erase i S))
  rw [hzero, zero_add, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun U hU ↦ ?_
  simp [Finset.card_insert_of_notMem
    (notMem_mono (Finset.mem_powerset.mp hU) (notMem_erase i S)), pow_succ]

omit [DecidableEq n] in
private theorem sum_powerset_smul_sum_mul (S : Finset κ) (h : κ → Matrix n n ℂ)
    (F : Finset κ → Matrix n n ℂ) :
    (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card • ((∑ i ∈ T, h i) * F T)) =
      -(∑ i ∈ S, h i *
        ∑ U ∈ (S.erase i).powerset, (-1 : ℂ) ^ U.card • F (insert i U)) := by
  have hinner (T : Finset κ) (hT : T ∈ S.powerset) :
      (-1 : ℂ) ^ T.card • ((∑ i ∈ T, h i) * F T) =
        ∑ i ∈ S, if i ∈ T then (-1 : ℂ) ^ T.card • (h i * F T) else 0 := by
    simp only [Finset.sum_ite_mem, Finset.inter_eq_right.mpr (Finset.mem_powerset.mp hT),
      Finset.sum_mul, Finset.smul_sum]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i hi ↦ by
    simpa only [Finset.mul_sum, Matrix.mul_smul] using
      sum_powerset_sign_mem S hi (fun T ↦ h i * F T)

private theorem hasDerivAt_mandatoryExp (H : Matrix n n ℂ) (h : κ → Matrix n n ℂ)
    (S : Finset κ) (t : ℝ) :
    HasDerivAt (mandatoryExp H h S)
      (-H * mandatoryExp H h S t -
        ∑ i ∈ S, h i * mandatoryExp (H - h i) h (S.erase i) t) t := by
  have hterm (T : Finset κ) :
      HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (-(s • (H - ∑ i ∈ T, h i))))
        (-(H - ∑ i ∈ T, h i) * NormedSpace.exp (-(t • (H - ∑ i ∈ T, h i)))) t := by
    simpa only [smul_neg] using
      hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-(H - ∑ i ∈ T, h i)) t
  have hd := HasDerivAt.fun_sum (u := S.powerset) fun T _ ↦
    HasDerivAt.fun_const_smul ((-1 : ℂ) ^ T.card) (hterm T)
  have hsmall (i : κ) :
      (∑ U ∈ (S.erase i).powerset, (-1 : ℂ) ^ U.card •
        NormedSpace.exp (-(t • (H - ∑ j ∈ insert i U, h j)))) =
        mandatoryExp (H - h i) h (S.erase i) t := by
    unfold mandatoryExp
    refine Finset.sum_congr rfl fun U hU ↦ ?_
    rw [Finset.sum_insert (notMem_mono (Finset.mem_powerset.mp hU)
      (notMem_erase i S)), sub_add_eq_sub_sub]
  convert hd using 1
  · rfl
  · simp_rw [neg_sub, sub_mul, smul_sub, Finset.sum_sub_distrib]
    simp_rw [← smul_sub]
    rw [sum_powerset_smul_sum_mul]
    simp_rw [hsmall, ← Matrix.mul_smul]
    rw [← Finset.mul_sum]
    change -H * mandatoryExp H h S t -
        (∑ i ∈ S, h i * mandatoryExp (H - h i) h (S.erase i) t) =
      -(∑ i ∈ S, h i * mandatoryExp (H - h i) h (S.erase i) t) -
        H * mandatoryExp H h S t
    noncomm_ring

omit [DecidableEq κ] in
private theorem mandatoryExp_zero (H : Matrix n n ℂ) (h : κ → Matrix n n ℂ)
    (S : Finset κ) (hS : S.Nonempty) : mandatoryExp H h S 0 = 0 := by
  have hsum : (∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card) = 0 := by
    exact_mod_cast Finset.sum_powerset_neg_one_pow_card_of_nonempty hS
  simp only [mandatoryExp, zero_smul, neg_zero, NormedSpace.exp_zero,
    ← Finset.sum_smul, hsum]

private theorem mandatoryExp_eq_neg_integral (H : Matrix n n ℂ) (h : κ → Matrix n n ℂ)
    (S : Finset κ) (hS : S.Nonempty) (t : ℝ) :
    mandatoryExp H h S t = -(∫ s in 0..t,
      NormedSpace.exp (-((t - s) • H)) *
        (∑ i ∈ S, h i * mandatoryExp (H - h i) h (S.erase i) s)) := by
  have hE (s : ℝ) :
      HasDerivAt (fun u : ℝ ↦ NormedSpace.exp (-((t - u) • H)))
        (NormedSpace.exp (-((t - s) • H)) * H) s := by
    convert (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-H) (t - s)).scomp s
      ((hasDerivAt_id s).const_sub t) using 1
    all_goals simp [Function.comp_def, smul_neg]
  have hF (s : ℝ) :
      HasDerivAt (fun u : ℝ ↦
        NormedSpace.exp (-((t - u) • H)) * mandatoryExp H h S u)
        (-(NormedSpace.exp (-((t - s) • H)) *
          (∑ i ∈ S, h i * mandatoryExp (H - h i) h (S.erase i) s))) s := by
    convert (hE s).mul (hasDerivAt_mandatoryExp H h S s) using 1
    noncomm_ring
  have hc (K : Matrix n n ℂ) (T : Finset κ) : Continuous (mandatoryExp K h T) :=
    continuous_iff_continuousAt.mpr fun s ↦
      (hasDerivAt_mandatoryExp K h T s).continuousAt
  have hint : IntervalIntegrable (fun s : ℝ ↦
      -(NormedSpace.exp (-((t - s) • H)) *
        (∑ i ∈ S, h i * mandatoryExp (H - h i) h (S.erase i) s)))
      MeasureTheory.volume 0 t :=
    ((continuous_iff_continuousAt.mpr fun s ↦ (hE s).continuousAt).mul
      (continuous_finsetSum S fun i _ ↦ continuous_const.mul
        (hc (H - h i) (S.erase i)))).neg.intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hF s) hint
  simpa only [sub_self, zero_smul, neg_zero, NormedSpace.exp_zero, one_mul,
    mandatoryExp_zero H h S hS, mul_zero, sub_zero, intervalIntegral.integral_neg] using
    hFTC.symm

private theorem integral_exp_sub_one_pow (k : ℕ) (hk : k ≠ 0) (t : ℝ) :
    (∫ s in 0..t, (k : ℝ) * Real.exp s * (Real.exp s - 1) ^ (k - 1)) =
      (Real.exp t - 1) ^ k := by
  have hd (s : ℝ) : HasDerivAt (fun u : ℝ ↦ (Real.exp u - 1) ^ k)
      ((k : ℝ) * Real.exp s * (Real.exp s - 1) ^ (k - 1)) s := by
    convert ((Real.hasDerivAt_exp s).sub_const 1).pow k using 1
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hd s)
    ((show Continuous (fun s : ℝ ↦
      (k : ℝ) * Real.exp s * (Real.exp s - 1) ^ (k - 1)) by fun_prop).intervalIntegrable 0 t)
  simpa only [Real.exp_zero, sub_self, zero_pow hk, sub_zero] using hFTC

omit [DecidableEq κ] in
private theorem norm_mandatoryExp_le (h : κ → Matrix n n ℂ) (S : Finset κ) :
    ∀ (H : Matrix n n ℂ) (lambda t : ℝ), H.IsHermitian →
      (lambda : ℂ) • 1 ≤ H →
      (∀ i ∈ S, (h i).IsHermitian) → (∀ i ∈ S, ‖h i‖ ≤ 1) → 0 ≤ t →
      ‖mandatoryExp H h S t‖ ≤ Real.exp (-t * lambda) * (Real.exp t - 1) ^ S.card := by
  classical
  refine S.strongInductionOn ?_
  intro S ih H lambda t hH hlo hh hnorm ht
  by_cases hS : S = ∅
  · subst S
    simpa only [mandatoryExp_empty, Finset.card_empty, pow_zero, mul_one] using
      norm_exp_neg_smul_le hH hlo ht
  · have hcap (i : κ) (hi : i ∈ S) : h i ≤ (1 : Matrix n n ℂ) := by
      have hiN := (hh i hi).isSelfAdjoint.le_algebraMap_norm_self
      rw [Algebra.algebraMap_eq_smul_one] at hiN
      simpa only [one_smul] using hiN.trans
        (smul_le_smul_of_nonneg_right (hnorm i hi) (show 0 ≤ (1 : Matrix n n ℂ) from zero_le_one))
    have hloi (i : κ) (hi : i ∈ S) :
        (((lambda - 1 : ℝ) : ℂ) • 1) ≤ H - h i := by
      simpa only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul] using
        sub_le_sub hlo (hcap i hi)
    have hsmall (i : κ) (hi : i ∈ S) (s : ℝ) (hs : 0 ≤ s) :
        ‖mandatoryExp (H - h i) h (S.erase i) s‖ ≤
          Real.exp (-s * (lambda - 1)) * (Real.exp s - 1) ^ (S.card - 1) := by
      simpa only [Finset.card_erase_of_mem hi] using
        ih (S.erase i) (Finset.erase_ssubset hi) (H - h i) (lambda - 1) s
          (hH.sub (hh i hi)) (hloi i hi)
          (fun j hj ↦ hh j (Finset.mem_erase.mp hj).2)
          (fun j hj ↦ hnorm j (Finset.mem_erase.mp hj).2) hs
    have hkernel (s : ℝ) (hs : s ∈ Set.Icc 0 t) :
        ‖NormedSpace.exp (-((t - s) • H)) *
          (∑ i ∈ S, h i * mandatoryExp (H - h i) h (S.erase i) s)‖ ≤
        Real.exp (-t * lambda) *
          ((S.card : ℝ) * Real.exp s * (Real.exp s - 1) ^ (S.card - 1)) := by
      have hterm (i : κ) (hi : i ∈ S) :
          ‖h i * mandatoryExp (H - h i) h (S.erase i) s‖ ≤
            Real.exp (-s * (lambda - 1)) * (Real.exp s - 1) ^ (S.card - 1) := by
        simpa only [one_mul] using
          (norm_mul_le (h i) (mandatoryExp (H - h i) h (S.erase i) s)).trans
            (mul_le_mul (hnorm i hi) (hsmall i hi s hs.1) (norm_nonneg _) zero_le_one)
      have hsum : ‖∑ i ∈ S, h i * mandatoryExp (H - h i) h (S.erase i) s‖ ≤
          (S.card : ℝ) *
            (Real.exp (-s * (lambda - 1)) * (Real.exp s - 1) ^ (S.card - 1)) := by
        simpa only [Finset.sum_const, nsmul_eq_mul] using
          (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
      refine (norm_mul_le _ _).trans
        ((mul_le_mul (norm_exp_neg_smul_le hH hlo (sub_nonneg.mpr hs.2))
          hsum (norm_nonneg _) (Real.exp_nonneg _)).trans_eq ?_)
      have he := congrArg Real.exp
        (show -(t - s) * lambda + -s * (lambda - 1) = -t * lambda + s by ring)
      rw [Real.exp_add, Real.exp_add] at he
      convert congrArg (fun x : ℝ ↦ x *
        ((S.card : ℝ) * (Real.exp s - 1) ^ (S.card - 1))) he using 1 <;> ring
    rw [mandatoryExp_eq_neg_integral H h S (Finset.nonempty_iff_ne_empty.mpr hS) t, norm_neg]
    refine (intervalIntegral.norm_integral_le_of_norm_le ht
      (Filter.Eventually.of_forall fun s hs ↦ hkernel s ⟨hs.1.le, hs.2⟩)
      ((show Continuous (fun s : ℝ ↦ Real.exp (-t * lambda) *
        ((S.card : ℝ) * Real.exp s * (Real.exp s - 1) ^ (S.card - 1))) by
          fun_prop).intervalIntegrable 0 t)).trans_eq ?_
    rw [intervalIntegral.integral_const_mul, integral_exp_sub_one_pow S.card
      (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)) t]

omit [DecidableEq κ] in
/-- The alternating sum requiring every label in a finite set has operator
norm at most `(exp t - 1) ^ S.card` after normalization by a supplied lower
energy. The background Hamiltonian need not be the sum of the selected
terms, and no spatial-support hypothesis is imposed. This is a
corrected auxiliary mandatory-label bound for ALVV, arXiv:1602.08828v2,
`thm:cluster-approx`, source lines 1270–1291 and 1935–1968. It does not
assert the false printed spatial approximation estimate, whose obstructions
are documented at
https://sirui-lu.com/TNLean/paper-gaps/alvv16_cluster_approximation.pdf. -/
theorem norm_sum_powerset_exp_sub_le_of_lower_bound
    (H : Matrix n n ℂ) (h : κ → Matrix n n ℂ) (S : Finset κ)
    (hH : H.IsHermitian) (hh : ∀ i ∈ S, (h i).IsHermitian)
    (hnorm : ∀ i ∈ S, ‖h i‖ ≤ 1) (lambda t : ℝ)
    (hlo : (lambda : ℂ) • 1 ≤ H) (ht : 0 ≤ t) :
    Real.exp (t * lambda) *
        ‖∑ T ∈ S.powerset, (-1 : ℂ) ^ T.card •
          NormedSpace.exp (-(t • (H - ∑ i ∈ T, h i)))‖ ≤
      (Real.exp t - 1) ^ S.card := by
  have hb := mul_le_mul_of_nonneg_left
    (norm_mandatoryExp_le h S H lambda t hH hlo hh hnorm ht) (Real.exp_nonneg (t * lambda))
  simpa only [mandatoryExp, ← mul_assoc, ← Real.exp_add, neg_mul, add_neg_cancel,
    Real.exp_zero, one_mul] using hb

end Matrix
