/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TraceHolderMulti
import QICLean.Analysis.TraceCFC

/-!
# Multi-factor Hölder inequality for traces with positive semidefinite factors

Let `X_0, …, X_{m-1}` be positive semidefinite, let `B_0, …, B_{m-1}` be arbitrary complex
square matrices, and let `θ_j ≥ 0` with `∑ θ_j = 1`. Then, for the ordered product,

`|Tr (B_0 X_0 B_1 X_1 ⋯ B_{m-1} X_{m-1})| ≤ ∏ ‖B_j‖ · ∏ ‖X_j‖_{1/θ_j}`,

with operator norms `‖B_j‖` and Schatten norms `‖X‖_p = (Tr X^p)^{1/p}`; for `θ_j = 0` the
Schatten norm `‖X_j‖_∞` is the operator norm.

For positive definite factors this is the exponential form
`Matrix.norm_trace_list_prod_mul_exp_smul_le` with `K_j = θ_j⁻¹ log X_j`; a factor with
`θ_j = 0` is absorbed into its neighbour `B_j`. Positive semidefinite factors follow by
continuity from `X_j + ε 1`, `ε > 0`.

## Main results

* `Matrix.schattenWeight`: the factor `‖X‖_{1/θ}` of the bound.
* `Matrix.norm_trace_list_prod_mul_le_of_posDef`: the inequality for positive definite factors.
* `Matrix.norm_trace_list_prod_mul_le_of_posSemidef`: the inequality for positive semidefinite
  factors.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, source
  file `proj3new.tex`, line 1141.
* R. Bhatia, *Matrix Analysis*, Springer (1997), Section IV.2 (Hölder inequalities for
  Schatten norms).
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Schatten norm `‖X‖_{1/θ}` of a matrix with weight `θ`: `(Tr X^{1/θ})^θ` for `θ ≠ 0`,
computed by the functional calculus, and the operator norm `‖X‖` for `θ = 0`. For positive
semidefinite `X` and `0 < θ ≤ 1` this is the Schatten `1/θ`-norm of `X`. -/
noncomputable def schattenWeight (X : Matrix n n ℂ) (θ : ℝ) : ℝ :=
  if θ = 0 then ‖X‖ else (cfc (fun x : ℝ ↦ x ^ (1 / θ)) X).trace.re ^ θ

theorem schattenWeight_of_eq_zero (X : Matrix n n ℂ) : schattenWeight X 0 = ‖X‖ := by
  simp [schattenWeight]

theorem schattenWeight_of_ne_zero (X : Matrix n n ℂ) {θ : ℝ} (hθ : θ ≠ 0) :
    schattenWeight X θ = (cfc (fun x : ℝ ↦ x ^ (1 / θ)) X).trace.re ^ θ := by
  simp [schattenWeight, hθ]

private theorem PosDef.pos_of_mem_spectrum {X : Matrix n n ℂ} (hX : X.PosDef) {x : ℝ}
    (hx : x ∈ spectrum ℝ X) : 0 < x := by
  rw [hX.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hX.eigenvalues_pos i

/-- For positive definite `X` and `θ ≠ 0`, the Hermitian matrix `K = θ⁻¹ log X` satisfies
`e^{θ K} = X` and `e^K = X^{1/θ}`. -/
private theorem PosDef.exp_smul_cfc_log {X : Matrix n n ℂ} (hX : X.PosDef) {θ : ℝ}
    (hθ : θ ≠ 0) :
    let K := cfc (fun x : ℝ ↦ θ⁻¹ * Real.log x) X
    K.IsHermitian ∧ NormedSpace.exp (θ • K) = X ∧
      NormedSpace.exp K = cfc (fun x : ℝ ↦ x ^ (1 / θ)) X := by
  intro K
  have hK : K.IsHermitian := IsSelfAdjoint.isHermitian (cfc_predicate _ X)
  have hexp (c : ℝ) : NormedSpace.exp (c • K) =
      cfc (fun x : ℝ ↦ Real.exp (c * (θ⁻¹ * Real.log x))) X := by
    rw [← CFC.real_exp_eq_normedSpace_exp (hK.smul (IsSelfAdjoint.all c)).isSelfAdjoint,
      ← cfc_comp_smul c Real.exp K]
    have hlog : ContinuousOn (fun x : ℝ ↦ θ⁻¹ * Real.log x) (spectrum ℝ X) :=
      continuousOn_const.mul (Real.continuousOn_log.mono fun x hx ↦
        (PosDef.pos_of_mem_spectrum hX hx).ne')
    exact (cfc_comp (fun y ↦ Real.exp (c * y)) (fun x ↦ θ⁻¹ * Real.log x) X
      hX.isHermitian.isSelfAdjoint (hf := hlog)).symm
  refine ⟨hK, ?_, ?_⟩
  · rw [hexp θ]
    conv_rhs => rw [← cfc_id' ℝ X]
    refine cfc_congr fun x hx ↦ ?_
    have hx0 := PosDef.pos_of_mem_spectrum hX hx
    rw [← mul_assoc, mul_inv_cancel₀ hθ, one_mul, Real.exp_log hx0]
  · have h1 := hexp 1
    rw [one_smul] at h1
    rw [h1]
    refine cfc_congr fun x hx ↦ ?_
    have hx0 := PosDef.pos_of_mem_spectrum hX hx
    rw [one_mul, Real.rpow_def_of_pos hx0, one_div, mul_comm]

/-- **Multi-factor Hölder inequality for positive definite factors.** For positive definite
`X_0, …, X_{m-1}`, arbitrary `B_0, …, B_{m-1}` and weights `θ_j ≥ 0` with `∑ θ_j = 1`,
`|Tr (B_0 X_0 ⋯ B_{m-1} X_{m-1})| ≤ ∏ ‖B_j‖ · ∏ ‖X_j‖_{1/θ_j}` for the ordered product. -/
theorem norm_trace_list_prod_mul_le_of_posDef {m : ℕ} (B X : Fin m → Matrix n n ℂ)
    (hX : ∀ j, (X j).PosDef) (θ : Fin m → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hsum : ∑ j, θ j = 1) :
    ‖(List.ofFn fun j ↦ B j * X j).prod.trace‖ ≤
      (∏ j, ‖B j‖) * ∏ j, schattenWeight (X j) (θ j) := by
  classical
  let B' : Fin m → Matrix n n ℂ := fun j ↦ if θ j = 0 then B j * X j else B j
  let K : Fin m → Matrix n n ℂ := fun j ↦
    if θ j = 0 then 0 else cfc (fun x : ℝ ↦ (θ j)⁻¹ * Real.log x) (X j)
  have hK : ∀ j, (K j).IsHermitian := by
    intro j
    by_cases h : θ j = 0
    · simp only [K, h, ite_true]
      exact isHermitian_zero
    · simp only [K, h, ite_false]
      exact (PosDef.exp_smul_cfc_log (hX j) h).1
  have hfac : ∀ j, B' j * NormedSpace.exp (θ j • K j) = B j * X j := by
    intro j
    by_cases h : θ j = 0
    · simp [B', K, h]
    · simp only [B', K, h, ite_false]
      rw [(PosDef.exp_smul_cfc_log (hX j) h).2.1]
  have hweight : ∀ j, ‖B' j‖ * (NormedSpace.exp (K j)).trace.re ^ θ j ≤
      ‖B j‖ * schattenWeight (X j) (θ j) := by
    intro j
    by_cases h : θ j = 0
    · simp only [B', K, h, ite_true, Real.rpow_zero, mul_one, schattenWeight_of_eq_zero]
      exact norm_mul_le _ _
    · simp only [B', K, h, ite_false, schattenWeight_of_ne_zero _ h]
      rw [(PosDef.exp_smul_cfc_log (hX j) h).2.2]
  have hmain := norm_trace_list_prod_mul_exp_smul_le B' K hK θ hθ hsum
  simp only [hfac] at hmain
  refine hmain.trans ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun j _ ↦ ?_) (fun j _ ↦ hweight j)
  exact mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (Complex.nonneg_iff.mp
      (nonneg_iff_posSemidef.mp (hK j).isSelfAdjoint.exp_nonneg).trace_nonneg).1 _)

/-- The trace of `(X + ε 1)^p` for Hermitian `X` is `∑ (λ_i + ε)^p` over the eigenvalues of `X`. -/
private theorem IsHermitian.re_trace_cfc_rpow_add_smul_one {X : Matrix n n ℂ}
    (hX : X.IsHermitian) {p : ℝ} (hp : 0 ≤ p) (ε : ℝ) :
    (cfc (fun x : ℝ ↦ x ^ p) (X + ε • 1)).trace.re = ∑ i, (hX.eigenvalues i + ε) ^ p := by
  have hshift : X + ε • (1 : Matrix n n ℂ) = cfc (fun x : ℝ ↦ x + ε) X := by
    have h := cfc_add_const ε (fun x : ℝ ↦ x) X continuousOn_id hX.isSelfAdjoint
    rw [h, cfc_id' ℝ X, Algebra.algebraMap_eq_smul_one]
  have hpow : ContinuousOn (fun x : ℝ ↦ x ^ p) ((fun x : ℝ ↦ x + ε) '' spectrum ℝ X) :=
    (Real.continuous_rpow_const hp).continuousOn
  rw [hshift, ← cfc_comp (fun x : ℝ ↦ x ^ p) (fun x : ℝ ↦ x + ε) X hX.isSelfAdjoint hpow,
    hX.cfc_eq]
  exact hX.trace_cfc_eq_sum_re _

/-- For Hermitian `X`, the Schatten weight of `X + ε 1` depends continuously on `ε`, provided
the weight `θ` is nonnegative. -/
private theorem IsHermitian.continuous_schattenWeight_add_smul_one {X : Matrix n n ℂ}
    (hX : X.IsHermitian) {θ : ℝ} (hθ : 0 ≤ θ) :
    Continuous fun ε : ℝ ↦ schattenWeight (X + ε • 1) θ := by
  by_cases h : θ = 0
  · simp only [h, schattenWeight_of_eq_zero]
    fun_prop
  · have hpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm h)
    have hp : 0 ≤ 1 / θ := le_of_lt (one_div_pos.mpr hpos)
    simp only [schattenWeight_of_ne_zero _ h, hX.re_trace_cfc_rpow_add_smul_one hp]
    refine (Real.continuous_rpow_const hθ).comp ?_
    exact continuous_finsetSum _ fun i _ ↦
      (Real.continuous_rpow_const hp).comp (continuous_const.add continuous_id)

/-- **Multi-factor Hölder inequality for traces.** For positive semidefinite
`X_0, …, X_{m-1}`, arbitrary `B_0, …, B_{m-1}` and weights `θ_j ≥ 0` with `∑ θ_j = 1`,
`|Tr (B_0 X_0 B_1 X_1 ⋯ B_{m-1} X_{m-1})| ≤ ∏ ‖B_j‖ · ∏ ‖X_j‖_{1/θ_j}` for the ordered
product, with operator norms `‖B_j‖` and Schatten norms `‖X‖_p = (Tr X^p)^{1/p}`; for
`θ_j = 0` the factor is the operator norm `‖X_j‖`. This is the trace Hölder inequality used by
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, line 1141. -/
theorem norm_trace_list_prod_mul_le_of_posSemidef {m : ℕ} (B X : Fin m → Matrix n n ℂ)
    (hX : ∀ j, (X j).PosSemidef) (θ : Fin m → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hsum : ∑ j, θ j = 1) :
    ‖(List.ofFn fun j ↦ B j * X j).prod.trace‖ ≤
      (∏ j, ‖B j‖) * ∏ j, schattenWeight (X j) (θ j) := by
  let F : ℝ → ℝ := fun ε ↦ ‖(List.ofFn fun j ↦ B j * (X j + ε • 1)).prod.trace‖
  let G : ℝ → ℝ := fun ε ↦ (∏ j, ‖B j‖) * ∏ j, schattenWeight (X j + ε • 1) (θ j)
  have hF : Continuous F := by
    have hl : Continuous fun ε : ℝ ↦ (List.ofFn fun j ↦ B j * (X j + ε • 1)).prod := by
      simp only [List.ofFn_eq_map]
      exact continuous_list_prod _ fun j _ ↦ by fun_prop
    exact continuous_norm.comp ((continuous_id.matrix_trace).comp hl)
  have hG : Continuous G := continuous_const.mul (continuous_finsetProd _ fun j _ ↦
    (hX j).isHermitian.continuous_schattenWeight_add_smul_one (hθ j))
  have hFG : ∀ ε : ℝ, 0 < ε → F ε ≤ G ε := fun ε hε ↦
    norm_trace_list_prod_mul_le_of_posDef B (fun j ↦ X j + ε • 1)
      (fun j ↦ PosDef.posSemidef_add (hX j) (PosDef.one.smul hε)) θ hθ hsum
  have hlim : F 0 ≤ G 0 :=
    le_of_tendsto_of_tendsto ((hF.tendsto 0).mono_left nhdsWithin_le_nhds)
      ((hG.tendsto 0).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun ε hε ↦ hFG ε (Set.mem_Ioi.mp hε))
  simpa only [F, G, zero_smul, add_zero] using hlim

end Matrix
