import QICLean.Analysis.MatrixBernsteinScalar
import QICLean.Analysis.TraceExponentialPerturbation
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma IsHermitian.exp_smul_eq_cfc {S : Matrix n n ℂ} (hS : S.IsHermitian) (θ : ℝ) :
    NormedSpace.exp (θ • S) = cfc (fun x ↦ Real.exp (θ * x)) S := by
  rw [← CFC.real_exp_eq_normedSpace_exp (hS.smul (IsSelfAdjoint.all θ)).isSelfAdjoint]
  exact (cfc_comp_smul θ Real.exp S).symm

theorem IsHermitian.exp_smul_le_one_add_add_bernsteinFactor_smul_sq {Y : Matrix n n ℂ}
    (hY : Y.IsHermitian) {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) (hYR : Y ≤ R • 1) :
    NormedSpace.exp (θ • Y) ≤ 1 + θ • Y + Real.bernsteinFactor R θ • Y ^ 2 := by
  have hspec : ∀ x ∈ spectrum ℝ Y, x ≤ R := by
    rw [← Algebra.algebraMap_eq_smul_one] at hYR
    exact (le_algebraMap_iff_spectrum_le (a := Y) hY.isSelfAdjoint).mp hYR
  have hrhs : cfc (fun x ↦ 1 + θ * x + Real.bernsteinFactor R θ * x ^ 2) Y =
      1 + θ • Y + Real.bernsteinFactor R θ • Y ^ 2 := by
    rw [cfc_add .., cfc_add .., cfc_const_one ℝ Y, cfc_const_mul .., cfc_const_mul ..,
      cfc_pow .., cfc_id' ℝ Y]
  rw [hY.exp_smul_eq_cfc, ← hrhs]
  exact cfc_mono fun x hx ↦
    Real.exp_mul_le_one_add_add_bernsteinFactor_mul_sq hR hθ (hspec x hx)

theorem PosDef.log_le_of_le_one_add {A C : Matrix n n ℂ} (hA : A.PosDef) (hC : C.PosSemidef)
    (hAC : A ≤ 1 + C) : CFC.log A ≤ C := by
  have h1 : CFC.log A ≤ CFC.log (1 + C) := CFC.log_le_log hAC hA.isStrictlyPositive
  refine h1.trans ?_
  have hsa : IsSelfAdjoint (1 + C) := (isHermitian_one.add hC.isHermitian).isSelfAdjoint
  have hone : (1 : Matrix n n ℂ) ≤ 1 + C := le_add_of_nonneg_right hC.nonneg
  have hspec : ∀ y ∈ spectrum ℝ (1 + C), 1 ≤ y := by
    rw [← map_one (algebraMap ℝ (Matrix n n ℂ))] at hone
    exact (algebraMap_le_iff_le_spectrum (a := 1 + C) hsa).mp hone
  have hsub : cfc (fun y : ℝ ↦ y - 1) (1 + C) = C := by
    rw [cfc_sub (R := ℝ) (fun y ↦ y) (fun _ ↦ 1) (1 + C), cfc_id' ℝ (1 + C),
      cfc_const_one ℝ (1 + C)]
    abel
  calc CFC.log (1 + C) = cfc Real.log (1 + C) := rfl
    _ ≤ cfc (fun y : ℝ ↦ y - 1) (1 + C) :=
        cfc_mono (fun y hy ↦ Real.log_le_sub_one_of_pos (by linarith [hspec y hy]))
          (Real.continuousOn_log.mono fun y hy ↦ by
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hspec y hy])
    _ = C := hsub

theorem IsHermitian.re_trace_exp_le_card_mul_exp_of_le {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {c : ℝ} (hMc : M ≤ c • 1) :
    (NormedSpace.exp M).trace.re ≤ Fintype.card n * Real.exp c := by
  have hc : (c • (1 : Matrix n n ℂ)).IsHermitian := isHermitian_one.smul (IsSelfAdjoint.all c)
  refine (hM.re_trace_exp_le hc hMc).trans_eq ?_
  have := exp_add_smul_one (0 : Matrix n n ℂ) c
  rw [zero_add, NormedSpace.exp_zero] at this
  rw [this, trace_smul, trace_one, Complex.real_smul, Complex.re_ofReal_mul]
  simp [mul_comm]

theorem IsHermitian.re_trace_exp_le_card_mul_exp_norm {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    (NormedSpace.exp M).trace.re ≤ Fintype.card n * Real.exp ‖M‖ := by
  refine hM.re_trace_exp_le_card_mul_exp_of_le ?_
  simpa [Algebra.algebraMap_eq_smul_one] using hM.isSelfAdjoint.le_algebraMap_norm_self

theorem IsHermitian.re_trace_exp_smul_eq_sum {S : Matrix n n ℂ} (hS : S.IsHermitian) (θ : ℝ) :
    (NormedSpace.exp (θ • S)).trace.re = ∑ i, Real.exp (θ * hS.eigenvalues i) := by
  rw [hS.exp_smul_eq_cfc, hS.cfc_eq]
  exact hS.trace_cfc_eq_sum_re _

theorem IsHermitian.exp_mul_le_re_trace_exp_smul {S : Matrix n n ℂ} (hS : S.IsHermitian)
    {θ t : ℝ} (hθ : 0 ≤ θ) {i : n} (hi : t ≤ hS.eigenvalues i) :
    Real.exp (θ * t) ≤ (NormedSpace.exp (θ • S)).trace.re := by
  rw [hS.re_trace_exp_smul_eq_sum]
  calc Real.exp (θ * t) ≤ Real.exp (θ * hS.eigenvalues i) := by gcongr
    _ ≤ ∑ j, Real.exp (θ * hS.eigenvalues j) :=
      Finset.single_le_sum (f := fun j ↦ Real.exp (θ * hS.eigenvalues j))
        (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)

theorem IsHermitian.exp_mul_le_re_trace_exp_smul_of_not_le {S : Matrix n n ℂ}
    (hS : S.IsHermitian) {θ t : ℝ} (hθ : 0 ≤ θ) (hSt : ¬ S ≤ t • 1) :
    Real.exp (θ * t) ≤ (NormedSpace.exp (θ • S)).trace.re := by
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le (a := S) hS.isSelfAdjoint,
    hS.spectrum_real_eq_range_eigenvalues] at hSt
  push Not at hSt
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hSt
  exact hS.exp_mul_le_re_trace_exp_smul hθ hi.le

end Matrix
