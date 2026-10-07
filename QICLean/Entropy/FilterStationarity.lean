/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.LocalLift
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Stationarity of a filter under unitary conjugation
-/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace Entropy

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The derivative at zero of `z ↦ exp (z B) K exp (-z B)` is `B K - K B`. -/
theorem hasDerivAt_exp_conj (B K : Matrix m m ℂ) :
    HasDerivAt (fun z : ℂ ↦ NormedSpace.exp (z • B) * K * NormedSpace.exp ((-z) • B))
      (B * K - K * B) 0 := by
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℂ) B (0 : ℂ)
  have h2 : HasDerivAt (fun z : ℂ ↦ NormedSpace.exp ((-z) • B)) (-B) 0 := by
    have := (hasDerivAt_exp_smul_const (𝕂 := ℂ) B (-0 : ℂ)).scomp (0 : ℂ) (hasDerivAt_neg 0)
    simpa [Function.comp_def] using this
  have h := (h1.mul_const K).mul h2
  convert h using 1
  simp [sub_eq_add_neg]

/-- The continuous linear map `X ↦ (A X) w`. -/
noncomputable def mulApplyCLM (A : Matrix m m ℂ) (w : EuclideanSpace ℂ m) :
    Matrix m m ℂ →L[ℂ] EuclideanSpace ℂ m :=
  LinearMap.mkContinuous
    { toFun := fun X ↦ toEuclideanLin (A * X) w
      map_add' := fun X Y ↦ by simp [Matrix.mul_add]
      map_smul' := fun c X ↦ by simp }
    (‖A‖ * ‖w‖) fun X ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      calc ‖toEuclideanLin (A * X) w‖ ≤ ‖A * X‖ * ‖w‖ := norm_toEuclideanLin_le _ _
        _ ≤ ‖A‖ * ‖X‖ * ‖w‖ := by gcongr; exact l2_opNorm_mul _ _
        _ = ‖A‖ * ‖w‖ * ‖X‖ := by ring

/-- **First-order condition under unitary conjugation.** If
`t ↦ ‖A e^{tB} K e^{-tB} w‖²` has a local maximum at `t = 0`, then
`Re ⟨A K w, A (B K - K B) w⟩ = 0`.
Area-law manuscript, proof of Lemma 3.2, `02-initial.tex`, lines 358–366. -/
theorem re_inner_commutator_eq_zero_of_isLocalMax (A K B : Matrix m m ℂ) (w : EuclideanSpace ℂ m)
    (hmax : IsLocalMax (fun t : ℝ ↦ ‖toEuclideanLin (A * (NormedSpace.exp ((t : ℂ) • B) * K *
      NormedSpace.exp ((-(t : ℂ)) • B))) w‖ ^ 2) 0) :
    (⟪toEuclideanLin (A * K) w, toEuclideanLin (A * (B * K - K * B)) w⟫_ℂ).re = 0 := by
  have hMF := ((hasDerivAt_exp_conj B K).hasFDerivAt.restrictScalars ℝ)
  have hMF' : HasFDerivAt (fun z : ℂ ↦ NormedSpace.exp (z • B) * K * NormedSpace.exp ((-z) • B))
      ((ContinuousLinearMap.toSpanSingleton ℂ (B * K - K * B)).restrictScalars ℝ)
      ((fun t : ℝ ↦ (t : ℂ)) 0) := by simpa using hMF
  have hM := hMF'.comp_hasDerivAt (0 : ℝ) (Complex.ofRealCLM.hasDerivAt (x := 0))
  have hv := ((mulApplyCLM A w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hM
  set v := ⇑((mulApplyCLM A w).restrictScalars ℝ) ∘
    (fun z : ℂ ↦ NormedSpace.exp (z • B) * K * NormedSpace.exp ((-z) • B)) ∘ ofReal
  have hvv := hv.inner ℂ hv
  have hre := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt (0 : ℝ) hvv
  have hfun : (⇑Complex.reCLM ∘ fun t ↦ ⟪v t, v t⟫_ℂ) =
      fun t : ℝ ↦ ‖toEuclideanLin (A * (NormedSpace.exp ((t : ℂ) • B) * K *
        NormedSpace.exp ((-(t : ℂ)) • B))) w‖ ^ 2 := by
    funext t
    simp only [Function.comp_apply, Complex.reCLM_apply]
    have hvt : v t = toEuclideanLin (A * (NormedSpace.exp ((t : ℂ) • B) * K *
        NormedSpace.exp ((-(t : ℂ)) • B))) w := rfl
    rw [hvt, ← RCLike.re_to_complex, ← @norm_sq_eq_re_inner ℂ]
  rw [hfun] at hre
  have h0 := hmax.hasDerivAt_eq_zero hre
  simp only [v, Function.comp_apply, Complex.reCLM_apply, Complex.add_re,
    Complex.ofReal_zero, zero_smul, neg_zero, NormedSpace.exp_zero, Matrix.one_mul,
    Matrix.mul_one, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, Complex.ofRealCLM_apply, Complex.ofReal_one,
    one_smul] at h0
  rw [← inner_conj_symm (mulApplyCLM A w (B * K - K * B)), Complex.conj_re] at h0
  change (⟪toEuclideanLin (A * K) w, toEuclideanLin (A * (B * K - K * B)) w⟫_ℂ).re +
    (⟪toEuclideanLin (A * K) w, toEuclideanLin (A * (B * K - K * B)) w⟫_ℂ).re = 0 at h0
  linarith

end Entropy
