/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import QICLean.Analysis.ContractionChain
import QICLean.Analysis.TraceMulBound

/-!
# Multi-factor Hölder inequality for traces with positive definite factors

Let `K_0, …, K_{m-1}` be Hermitian, let `B_0, …, B_{m-1}` be arbitrary complex square
matrices, and let `θ_j ≥ 0` with `∑ θ_j = 1`. Then, for the ordered product,

`|Tr (B_0 e^{θ_0 K_0} B_1 e^{θ_1 K_1} ⋯ B_{m-1} e^{θ_{m-1} K_{m-1}})|
  ≤ ∏ ‖B_j‖ · ∏ (Tr e^{K_j})^{θ_j}`,

with operator norms `‖B_j‖`. Writing `X_j = e^{θ_j K_j}` and `p_j = 1/θ_j`, this is the
Hölder inequality `|Tr (B_0 X_0 ⋯ B_{m-1} X_{m-1})| ≤ ∏ ‖B_j‖ ∏ ‖X_j‖_{p_j}` for positive
definite `X_j`, with Schatten norms `‖X‖_p = (Tr X^p)^{1/p}`; a factor with `θ_j = 0` is the
identity.

The special case `K_j = -β H` for one Hermitian `H` gives the imaginary-time bound

`|Tr (B_0 e^{-a_0 H} ⋯ B_k e^{-a_k H})| ≤ ∏ ‖B_j‖ · Tr e^{-β H}`

for `a_j ≥ 0` with `∑ a_j = β`, which controls the clusters of a high-temperature expansion.

## Proof

The proof is Hadamard's three-lines theorem, applied by induction on the number of factors.
For complex weights `w_j` the factor `e^{w_j K_j}` is a unitary times `e^{(Re w_j) K_j}`,
so only the real parts of the weights matter for the bound. If all weights but the first
have real part zero, the bound is `|Tr (e^{K_0} C)| ≤ Tr e^{K_0} ‖C‖`. Otherwise the first
weight `t = Re w_0` is moved along the strip `0 ≤ Re z ≤ 1`: on `Re z = 0` the first factor
is a unitary and merges with its neighbour, so the inductive hypothesis applies with one
factor fewer and the remaining weights rescaled by `1/(1-t)`; on `Re z = 1` the remaining
weights have real part zero. The three-lines bound at `z = t` interpolates these two bounds.

## Main results

* `Matrix.norm_trace_list_prod_mul_exp_smul_le`: the multi-factor Hölder inequality above.
* `Matrix.IsHermitian.norm_trace_list_prod_mul_exp_neg_smul_le`: the commuting case
  `X_j = e^{-a_j H}`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3, source
  file `proj3new.tex`, lines 1141–1151: the bound
  `Z⁻¹ |Tr (O O_1(iτ_1) ⋯ O_k(iτ_k) e^{-βH})| ≤ ‖O‖ ∏ ‖O_j‖`, `Z = Tr e^{-βH}`, for
  imaginary-time evolved operators `O(iτ) = e^{-τH} O e^{τH}` with
  `0 ≤ τ_1 ≤ ⋯ ≤ τ_k ≤ β`. The product equals
  `O e^{-τ_1 H} O_1 e^{-(τ_2 - τ_1) H} ⋯ O_k e^{-(β - τ_k) H}`, an instance of the
  imaginary-time bound above.
* R. Bhatia, *Matrix Analysis*, Springer (1997), Section IV.2 (Hölder inequalities for
  Schatten norms).
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section Factor

/-- The exponential of an imaginary multiple of a Hermitian matrix is unitary. -/
private theorem exp_smul_mem_unitary {K : Matrix n n ℂ} (hK : K.IsHermitian) (y : ℝ) :
    NormedSpace.exp (((y : ℂ) * Complex.I) • K) ∈ unitary (Matrix n n ℂ) := by
  have hstar : star (NormedSpace.exp (((y : ℂ) * Complex.I) • K)) =
      NormedSpace.exp (-(((y : ℂ) * Complex.I) • K)) := by
    rw [star_eq_conjTranspose, ← exp_conjTranspose, conjTranspose_smul, hK.eq, ← neg_smul]
    congr 2
    simp
  set A := ((y : ℂ) * Complex.I) • K
  rw [Unitary.mem_iff, hstar, ← exp_add_of_commute _ _ (Commute.refl A).neg_left,
    ← exp_add_of_commute _ _ (Commute.refl A).neg_right, neg_add_cancel, add_neg_cancel,
    NormedSpace.exp_zero]
  exact ⟨rfl, rfl⟩

/-- A complex weight splits into a unitary factor and the exponential of its real part. -/
private theorem exp_smul_eq_mul (K : Matrix n n ℂ) (w : ℂ) :
    NormedSpace.exp (w • K) =
      NormedSpace.exp (((w.im : ℂ) * Complex.I) • K) * NormedSpace.exp ((w.re : ℂ) • K) := by
  have hw : w • K = ((w.im : ℂ) * Complex.I) • K + (w.re : ℂ) • K := by
    rw [← add_smul, add_comm, Complex.re_add_im]
  rw [hw, exp_add_of_commute _ _ (((Commute.refl K).smul_left _).smul_right _)]

/-- Only the real part of the weight enters the norm of `B e^{w K}`. -/
private theorem norm_mul_exp_smul_le {K : Matrix n n ℂ} (hK : K.IsHermitian)
    (B : Matrix n n ℂ) (w : ℂ) :
    ‖B * NormedSpace.exp (w • K)‖ ≤ ‖B‖ * ‖NormedSpace.exp ((w.re : ℂ) • K)‖ := by
  rw [exp_smul_eq_mul, ← Matrix.mul_assoc]
  refine (norm_mul_le _ _).trans_eq ?_
  rw [CStarRing.norm_mul_coe_unitary B ⟨_, exp_smul_mem_unitary hK w.im⟩]

/-- A factor `B e^{w K}` with `Re w = 0` has norm at most `‖B‖`. -/
private theorem norm_mul_exp_smul_le_of_re_eq_zero {K : Matrix n n ℂ} (hK : K.IsHermitian)
    (B : Matrix n n ℂ) {w : ℂ} (hw : w.re = 0) : ‖B * NormedSpace.exp (w • K)‖ ≤ ‖B‖ := by
  have h := norm_mul_exp_smul_le hK B w
  rw [hw, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at h
  exact h.trans (mul_le_of_le_one_right (norm_nonneg B) (l2_opNorm_one_le (n := n)))

/-- The derivative of `u ↦ e^{u K}` exists everywhere. -/
private theorem differentiable_exp_smul (K : Matrix n n ℂ) :
    Differentiable ℂ fun u : ℂ ↦ NormedSpace.exp (u • K) :=
  fun u ↦ (hasDerivAt_exp_smul_const K u).differentiableAt

/-- Composition of `u ↦ e^{u K}` with a holomorphic weight. -/
private theorem differentiable_exp_smul_comp (K : Matrix n n ℂ) {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) : Differentiable ℂ fun z ↦ NormedSpace.exp (g z • K) :=
  (differentiable_exp_smul K).comp hg

/-- An ordered product of matrices has norm at most the product of the bounds of its factors. -/
private theorem norm_list_prod_le {α : Type*} (L : List α) (f : α → Matrix n n ℂ) (g : α → ℝ)
    (h : ∀ x ∈ L, ‖f x‖ ≤ g x ∧ 0 ≤ g x) : ‖(L.map f).prod‖ ≤ (L.map g).prod := by
  induction L with
  | nil => simpa using (l2_opNorm_one_le (n := n))
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons]
    have hx := h x (by simp)
    have ih := ih fun y hy ↦ h y (by simp [hy])
    calc _ ≤ ‖f x‖ * ‖(L.map f).prod‖ := norm_mul_le _ _
      _ ≤ g x * (L.map g).prod := mul_le_mul hx.1 ih (norm_nonneg _) hx.2

/-- An ordered product of matrix-valued holomorphic functions is holomorphic. -/
private theorem differentiable_list_prod {α : Type*} (L : List α) (F : α → ℂ → Matrix n n ℂ)
    (h : ∀ x ∈ L, Differentiable ℂ (F x)) :
    Differentiable ℂ fun z ↦ (L.map fun x ↦ F x z).prod := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h x (by simp)).mul (ih fun y hy ↦ h y (by simp [hy]))

end Factor

section Real

/-- A real power of a list product of nonnegative powers. -/
private theorem list_prod_map_rpow_rpow {α : Type*} (L : List α) (a c : α → ℝ)
    (ha : ∀ x ∈ L, 0 ≤ a x) (s : ℝ) :
    (L.map fun x ↦ a x ^ c x).prod ^ s = (L.map fun x ↦ a x ^ (c x * s)).prod := by
  rw [← Real.list_prod_map_rpow' L (fun x ↦ a x ^ c x)
    (fun x hx ↦ Real.rpow_nonneg (ha x hx) _) s]
  congr 1
  exact List.map_congr_left fun x hx ↦ (Real.rpow_mul (ha x hx) _ _).symm

/-- A list product of zeroth powers is one. -/
private theorem list_prod_map_rpow_eq_one {α : Type*} (L : List α) (a c : α → ℝ)
    (hc : ∀ x ∈ L, c x = 0) : (L.map fun x ↦ a x ^ c x).prod = 1 :=
  List.prod_eq_one fun b hb ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    rw [hc y hy, Real.rpow_zero]

end Real

section Interpolation

/-- A factor `B e^{w K}` of an ordered product: an arbitrary matrix `B`, an exponent direction
`K` and a complex weight `w`. Auxiliary to the interpolation argument. -/
private structure HolderFactor (n : Type*) where
  /-- The arbitrary matrix of the factor. -/
  B : Matrix n n ℂ
  /-- The exponent direction, Hermitian in all uses. -/
  K : Matrix n n ℂ
  /-- The complex weight. -/
  w : ℂ

/-- The matrix `B e^{w K}` of a factor. -/
private noncomputable def HolderFactor.mat (x : HolderFactor n) : Matrix n n ℂ :=
  x.B * NormedSpace.exp (x.w • x.K)

/-- The trace `Re Tr e^{K}` entering the bound. -/
private noncomputable def HolderFactor.tr (x : HolderFactor n) : ℝ :=
  (NormedSpace.exp x.K).trace.re

/-- The Hölder bound `∏ ‖B_j‖ · ∏ (Tr e^{K_j})^{Re w_j}` of a list of factors. -/
private noncomputable def holderBound (L : List (HolderFactor n)) : ℝ :=
  (L.map fun x ↦ ‖x.B‖).prod * (L.map fun x ↦ x.tr ^ x.w.re).prod

private theorem posSemidef_exp {K : Matrix n n ℂ} (hK : K.IsHermitian) :
    (NormedSpace.exp K).PosSemidef :=
  nonneg_iff_posSemidef.mp hK.isSelfAdjoint.exp_nonneg

/-- The trace of the exponential of a Hermitian matrix has nonnegative real part. -/
private theorem trace_exp_re_nonneg {K : Matrix n n ℂ} (hK : K.IsHermitian) :
    0 ≤ (NormedSpace.exp K).trace.re :=
  (Complex.nonneg_iff.mp (posSemidef_exp hK).trace_nonneg).1

private theorem HolderFactor.tr_nonneg {x : HolderFactor n} (hK : x.K.IsHermitian) :
    0 ≤ x.tr :=
  trace_exp_re_nonneg hK

private theorem prod_tr_rpow_nonneg (L : List (HolderFactor n))
    (hK : ∀ x ∈ L, x.K.IsHermitian) : 0 ≤ (L.map fun x ↦ x.tr ^ x.w.re).prod :=
  List.prod_nonneg fun b hb ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact Real.rpow_nonneg (HolderFactor.tr_nonneg (hK y hy)) _

/-- **Base case.** If the first weight has real part one and all others real part zero, the
trace is bounded by `∏ ‖B_j‖ · Tr e^{K_0}`. -/
private theorem norm_trace_le_of_re_eq_zero (x₀ : HolderFactor n) (R : List (HolderFactor n))
    (hK : ∀ x ∈ x₀ :: R, x.K.IsHermitian) (h₀ : x₀.w.re = 1) (hR : ∀ x ∈ R, x.w.re = 0) :
    ‖((x₀ :: R).map HolderFactor.mat).prod.trace‖ ≤ holderBound (x₀ :: R) := by
  have hK₀ := hK x₀ (by simp)
  set P := (R.map HolderFactor.mat).prod
  set U := NormedSpace.exp (((x₀.w.im : ℂ) * Complex.I) • x₀.K)
  have hU : U ∈ unitary (Matrix n n ℂ) := exp_smul_mem_unitary hK₀ _
  have hmat : x₀.mat = x₀.B * U * NormedSpace.exp x₀.K := by
    rw [HolderFactor.mat, exp_smul_eq_mul, h₀, Complex.ofReal_one, one_smul, Matrix.mul_assoc]
  have htr : ((x₀ :: R).map HolderFactor.mat).prod.trace =
      (NormedSpace.exp x₀.K * (P * (x₀.B * U))).trace := by
    rw [List.map_cons, List.prod_cons, hmat, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  have hP : ‖P‖ ≤ (R.map fun x ↦ ‖x.B‖).prod :=
    norm_list_prod_le R _ _ fun x hx ↦
      ⟨norm_mul_exp_smul_le_of_re_eq_zero (hK x (by simp [hx])) x.B (hR x hx), norm_nonneg _⟩
  have hBU : ‖x₀.B * U‖ = ‖x₀.B‖ := CStarRing.norm_mul_coe_unitary x₀.B ⟨U, hU⟩
  have hbound : holderBound (x₀ :: R) = x₀.tr * ((R.map fun x ↦ ‖x.B‖).prod * ‖x₀.B‖) := by
    simp only [holderBound, List.map_cons, List.prod_cons, h₀, Real.rpow_one,
      list_prod_map_rpow_eq_one R _ _ hR]
    ring
  rw [htr, hbound]
  calc _ ≤ x₀.tr * ‖P * (x₀.B * U)‖ := (posSemidef_exp hK₀).norm_trace_mul_le _
    _ ≤ x₀.tr * (‖P‖ * ‖x₀.B * U‖) := by
        gcongr
        · exact HolderFactor.tr_nonneg hK₀
        · exact norm_mul_le _ _
    _ ≤ _ := by
        rw [hBU]
        gcongr
        exact HolderFactor.tr_nonneg hK₀

/-- **Merging.** A leading factor whose weight has real part zero merges with the next one,
without increasing the bound. -/
private theorem merge_head (x₀ x₁ : HolderFactor n) (R : List (HolderFactor n))
    (hK₀ : x₀.K.IsHermitian) (h₀ : x₀.w.re = 0) (hR : ∀ x ∈ x₁ :: R, x.K.IsHermitian) :
    ((x₀ :: x₁ :: R).map HolderFactor.mat).prod =
        ((⟨x₀.mat * x₁.B, x₁.K, x₁.w⟩ :: R : List (HolderFactor n)).map HolderFactor.mat).prod ∧
      holderBound (⟨x₀.mat * x₁.B, x₁.K, x₁.w⟩ :: R) ≤ holderBound (x₀ :: x₁ :: R) := by
  refine ⟨by simp [HolderFactor.mat, Matrix.mul_assoc], ?_⟩
  have hN : 0 ≤ (R.map fun x ↦ ‖x.B‖).prod :=
    List.prod_nonneg fun b hb ↦ by obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb; exact norm_nonneg _
  have hmul : ‖x₀.mat * x₁.B‖ ≤ ‖x₀.B‖ * ‖x₁.B‖ :=
    (norm_mul_le _ _).trans (by
      gcongr
      exact norm_mul_exp_smul_le_of_re_eq_zero hK₀ x₀.B h₀)
  have hT' : 0 ≤ x₁.tr ^ x₁.w.re * (R.map fun x ↦ x.tr ^ x.w.re).prod := by
    simpa using prod_tr_rpow_nonneg (x₁ :: R) hR
  simp only [holderBound, List.map_cons, List.prod_cons, h₀, Real.rpow_zero, one_mul]
  calc ‖x₀.mat * x₁.B‖ * (R.map fun x ↦ ‖x.B‖).prod *
        (HolderFactor.tr ⟨x₀.mat * x₁.B, x₁.K, x₁.w⟩ ^ x₁.w.re *
          (R.map fun x ↦ x.tr ^ x.w.re).prod)
      = ‖x₀.mat * x₁.B‖ * (R.map fun x ↦ ‖x.B‖).prod *
          (x₁.tr ^ x₁.w.re * (R.map fun x ↦ x.tr ^ x.w.re).prod) := rfl
    _ ≤ ‖x₀.B‖ * ‖x₁.B‖ * (R.map fun x ↦ ‖x.B‖).prod *
          (x₁.tr ^ x₁.w.re * (R.map fun x ↦ x.tr ^ x.w.re).prod) := by gcongr
    _ = _ := by ring

/-- A crude bound used for the boundedness of the interpolating function on the strip. -/
private theorem norm_trace_le_crude (L : List (HolderFactor n)) (hK : ∀ x ∈ L, x.K.IsHermitian) :
    ‖(L.map HolderFactor.mat).prod.trace‖ ≤ (1 : Matrix n n ℂ).trace.re *
      (L.map fun x ↦ ‖x.B‖ * ‖NormedSpace.exp ((x.w.re : ℂ) • x.K)‖).prod := by
  have h1 := PosSemidef.one.norm_trace_mul_le (n := n) (L.map HolderFactor.mat).prod
  rw [Matrix.one_mul] at h1
  refine h1.trans ?_
  gcongr
  · exact (Complex.nonneg_iff.mp (PosSemidef.one (n := n)).trace_nonneg).1
  · exact norm_list_prod_le L _ _ fun x hx ↦
      ⟨norm_mul_exp_smul_le (hK x hx) x.B x.w, by positivity⟩

omit [Fintype n] [DecidableEq n] in
/-- The first factor of the interpolating family, with weight `i Im w_0 + z`. -/
private def interpHead (x₀ : HolderFactor n) (z : ℂ) : HolderFactor n :=
  ⟨x₀.B, x₀.K, (x₀.w.im : ℂ) * Complex.I + z⟩

omit [Fintype n] [DecidableEq n] in
/-- A later factor of the interpolating family, with weight `i Im w + (1 - z) Re w / S`. -/
private noncomputable def interpTail (S : ℝ) (z : ℂ) (x : HolderFactor n) : HolderFactor n :=
  ⟨x.B, x.K, (x.w.im : ℂ) * Complex.I + (1 - z) * ((x.w.re / S : ℝ) : ℂ)⟩

omit [Fintype n] [DecidableEq n] in
private theorem interpHead_re (x₀ : HolderFactor n) (z : ℂ) :
    (interpHead x₀ z).w.re = z.re := by
  simp [interpHead]

omit [Fintype n] [DecidableEq n] in
private theorem interpTail_re (S : ℝ) (z : ℂ) (x : HolderFactor n) :
    (interpTail S z x).w.re = (1 - z.re) * (x.w.re / S) := by
  simp [interpTail]

omit [Fintype n] [DecidableEq n] in
private theorem interpHead_self (x₀ : HolderFactor n) : interpHead x₀ (x₀.w.re : ℂ) = x₀ := by
  obtain ⟨B, K, w⟩ := x₀
  simp [interpHead, Complex.ext_iff]

omit [Fintype n] [DecidableEq n] in
private theorem interpTail_self {S : ℝ} (hS : S ≠ 0) (x : HolderFactor n) :
    interpTail S ((1 - S : ℝ) : ℂ) x = x := by
  obtain ⟨B, K, w⟩ := x
  simp only [interpTail, HolderFactor.mk.injEq, true_and]
  apply Complex.ext <;> simp
  field_simp

/-- **Interpolation step.** If the bound holds for lists of `N` factors, it holds for lists of
`N + 1` factors whose later weights have positive total real part. The first weight is moved
along the strip `0 ≤ Re z ≤ 1`, and Hadamard's three-lines theorem interpolates between the
merged list on `Re z = 0` and the base case on `Re z = 1`. -/
private theorem norm_trace_le_of_interp (N : ℕ)
    (ih : ∀ L : List (HolderFactor n), L.length = N →
      (∀ x ∈ L, x.K.IsHermitian ∧ 0 ≤ x.w.re) → (L.map fun x ↦ x.w.re).sum = 1 →
        ‖(L.map HolderFactor.mat).prod.trace‖ ≤ holderBound L)
    (x₀ x₁ : HolderFactor n) (R : List (HolderFactor n)) (hlen : R.length + 1 = N)
    (hadm : ∀ x ∈ x₀ :: x₁ :: R, x.K.IsHermitian ∧ 0 ≤ x.w.re)
    (hsum : x₀.w.re + ((x₁ :: R).map fun x ↦ x.w.re).sum = 1)
    (hS : 0 < ((x₁ :: R).map fun x ↦ x.w.re).sum) :
    ‖((x₀ :: x₁ :: R).map HolderFactor.mat).prod.trace‖ ≤ holderBound (x₀ :: x₁ :: R) := by
  set T := x₁ :: R with hTdef
  set S := (T.map fun x ↦ x.w.re).sum with hSdef
  have hK : ∀ x ∈ x₀ :: T, x.K.IsHermitian := fun x hx ↦ (hadm x hx).1
  have hK₀ : x₀.K.IsHermitian := hK x₀ (by simp)
  have hKT : ∀ x ∈ T, x.K.IsHermitian := fun x hx ↦ hK x (by simp [hx])
  have hT0 : ∀ x ∈ T, 0 ≤ x.w.re := fun x hx ↦ (hadm x (by simp [hx])).2
  have ht0 : 0 ≤ x₀.w.re := (hadm x₀ (by simp)).2
  have hSt : 1 - x₀.w.re = S := by linarith
  -- The interpolating family and its trace.
  set Lz : ℂ → List (HolderFactor n) := fun z ↦ interpHead x₀ z :: T.map (interpTail S z)
    with hLz
  set f : ℂ → ℂ := fun z ↦ ((Lz z).map HolderFactor.mat).prod.trace with hf
  have hK_Lz (z : ℂ) : ∀ x ∈ Lz z, x.K.IsHermitian := by
    intro x hx
    simp only [hLz, List.mem_cons, List.mem_map] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · exact hK₀
    · exact hKT y hy
  have hre_nonneg {z : ℂ} (hz : z.re ≤ 1) : ∀ x ∈ T, 0 ≤ (interpTail S z x).w.re := by
    intro x hx
    rw [interpTail_re]
    exact mul_nonneg (by linarith) (div_nonneg (hT0 x hx) hS.le)
  have hsum_tail (z : ℂ) : ((T.map (interpTail S z)).map fun x ↦ x.w.re).sum = 1 - z.re := by
    rw [List.map_map]
    have : ((fun x : HolderFactor n ↦ x.w.re) ∘ interpTail S z) =
        fun x ↦ ((1 - z.re) / S) * x.w.re := by
      funext x
      simp only [Function.comp, interpTail_re]
      ring
    rw [this, List.sum_map_mul_left, ← hSdef, div_mul_cancel₀ _ hS.ne']
  set P := ‖x₀.B‖ * (T.map fun x ↦ ‖x.B‖).prod with hP
  have hbound (z : ℂ) : holderBound (Lz z) =
      P * (x₀.tr ^ z.re * (T.map fun x ↦ x.tr ^ ((1 - z.re) * (x.w.re / S))).prod) := by
    simp only [holderBound, hLz, List.map_cons, List.prod_cons, List.map_map, Function.comp_def,
      interpHead_re, interpTail_re, hP]
    simp only [interpHead, interpTail, HolderFactor.tr]
  -- The bound on the line `Re z = 0`.
  set Q := (T.map fun x ↦ x.tr ^ (x.w.re / S)).prod with hQ
  have h0 : ∀ z ∈ Complex.re ⁻¹' {0}, ‖f z‖ ≤ P * Q := by
    intro z hz
    have hz : z.re = 0 := hz
    obtain ⟨hprod, hle⟩ := merge_head (interpHead x₀ z) (interpTail S z x₁)
      (R.map (interpTail S z)) hK₀ (by rw [interpHead_re, hz])
      (fun x hx ↦ hK_Lz z x (List.mem_cons_of_mem _ hx))
    have hadm' : ∀ x ∈ (⟨(interpHead x₀ z).mat * (interpTail S z x₁).B,
        (interpTail S z x₁).K, (interpTail S z x₁).w⟩ :: R.map (interpTail S z) :
          List (HolderFactor n)), x.K.IsHermitian ∧ 0 ≤ x.w.re := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · have hx₁ : x₁ ∈ T := by rw [hTdef]; exact List.mem_cons_self
        exact ⟨hKT x₁ hx₁, hre_nonneg (by rw [hz]; norm_num) x₁ hx₁⟩
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        have hyT : y ∈ T := by rw [hTdef]; exact List.mem_cons_of_mem _ hy
        exact ⟨hKT y hyT, hre_nonneg (by rw [hz]; norm_num) y hyT⟩
    have hih := ih _ (by simp [← hlen]) hadm' (by
      have := hsum_tail z
      simp only [hTdef, List.map_cons, List.sum_cons] at this ⊢
      rw [this, hz, sub_zero])
    calc ‖f z‖ = ‖((⟨(interpHead x₀ z).mat * (interpTail S z x₁).B,
          (interpTail S z x₁).K, (interpTail S z x₁).w⟩ :: R.map (interpTail S z) :
            List (HolderFactor n)).map HolderFactor.mat).prod.trace‖ := by
          rw [hf, hLz]
          simp only [hTdef, List.map_cons] at hprod ⊢
          rw [hprod]
      _ ≤ _ := hih
      _ ≤ holderBound (Lz z) := hle
      _ = P * Q := by
          rw [hbound, hz]
          simp [hQ]
  -- The bound on the line `Re z = 1`.
  have h1 : ∀ z ∈ Complex.re ⁻¹' {1}, ‖f z‖ ≤ P * x₀.tr := by
    intro z hz
    have hz : z.re = 1 := hz
    refine (norm_trace_le_of_re_eq_zero (interpHead x₀ z) (T.map (interpTail S z)) (hK_Lz z)
      (by rw [interpHead_re, hz]) fun x hx ↦ ?_).trans_eq ?_
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      rw [interpTail_re, hz, sub_self, zero_mul]
    · rw [hbound, hz]
      simp
  -- Holomorphy and boundedness on the strip.
  have hdiff : Differentiable ℂ f := by
    have hF : Differentiable ℂ fun z ↦ ((Lz z).map HolderFactor.mat).prod := by
      simp only [hLz, List.map_cons, List.prod_cons, List.map_map, Function.comp_def]
      refine Differentiable.mul ?_ (differentiable_list_prod T _ fun x _ ↦ ?_)
      all_goals exact (differentiable_const _).mul (differentiable_exp_smul_comp _ (by fun_prop))
    let tr := LinearMap.toContinuousLinearMap (traceLinearMap n ℂ ℂ)
    have htr : f = fun z ↦ tr (((Lz z).map HolderFactor.mat).prod) := by
      funext z
      simp [hf, tr]
    rw [htr]
    exact tr.differentiable.comp hF
  have hbdd : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    let G : ℝ → ℝ := fun s ↦ (1 : Matrix n n ℂ).trace.re *
      ((‖x₀.B‖ * ‖NormedSpace.exp ((s : ℂ) • x₀.K)‖) *
        (T.map fun x ↦ ‖x.B‖ * ‖NormedSpace.exp ((((1 - s) * (x.w.re / S) : ℝ) : ℂ) • x.K)‖).prod)
    have hG : Continuous G := by
      refine continuous_const.mul (Continuous.mul (continuous_const.mul ?_)
        (continuous_list_prod _ fun x _ ↦ continuous_const.mul ?_))
      · exact continuous_norm.comp
          ((differentiable_exp_smul x₀.K).continuous.comp Complex.continuous_ofReal)
      · exact continuous_norm.comp ((differentiable_exp_smul x.K).continuous.comp
          (Complex.continuous_ofReal.comp (by fun_prop)))
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hG.continuousOn
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hcrude := norm_trace_le_crude (Lz z) (hK_Lz z)
    have heq : (1 : Matrix n n ℂ).trace.re * ((Lz z).map fun x ↦
        ‖x.B‖ * ‖NormedSpace.exp ((x.w.re : ℂ) • x.K)‖).prod = G z.re := by
      simp only [hLz, G, List.map_cons, List.prod_cons, List.map_map, Function.comp_def,
        interpHead_re, interpTail_re]
      rfl
    exact hcrude.trans (heq.le.trans ((le_abs_self _).trans (by simpa using hC _ hz)))
  -- Hadamard's three-lines theorem at `z = Re w_0`.
  have hmem : (x₀.w.re : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    change (x₀.w.re : ℂ).re ∈ Set.Icc (0 : ℝ) 1
    simp only [Complex.ofReal_re, Set.mem_Icc]
    constructor <;> linarith
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' f hmem
    hdiff.diffContOnCl hbdd h0 h1
  have hft : f (x₀.w.re : ℂ) = ((x₀ :: T).map HolderFactor.mat).prod.trace := by
    have htail : T.map (interpTail S (x₀.w.re : ℂ)) = T := by
      have h : ((x₀.w.re : ℝ) : ℂ) = ((1 - S : ℝ) : ℂ) := by rw [← hSt]; ring_nf
      rw [h]
      conv_rhs => rw [← List.map_id T]
      exact List.map_congr_left fun x _ ↦ interpTail_self hS.ne' x
    simp only [hf, hLz, interpHead_self, htail]
  rw [← hft]
  refine key.trans_eq ?_
  simp only [Complex.ofReal_re]
  have hP0 : 0 ≤ P := mul_nonneg (norm_nonneg _) (List.prod_nonneg fun b hb ↦ by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hb; exact norm_nonneg _)
  have hQ0 : 0 ≤ Q := List.prod_nonneg fun b hb ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact Real.rpow_nonneg (HolderFactor.tr_nonneg (hKT y hy)) _
  have htr0 : 0 ≤ x₀.tr := HolderFactor.tr_nonneg hK₀
  have hPP : P ^ S * P ^ x₀.w.re = P := by
    rw [← Real.rpow_add' hP0 (by linarith), show S + x₀.w.re = 1 by linarith, Real.rpow_one]
  have hQS : Q ^ S = (T.map fun x ↦ x.tr ^ x.w.re).prod := by
    rw [hQ, list_prod_map_rpow_rpow T _ _ (fun x hx ↦ HolderFactor.tr_nonneg (hKT x hx)) S]
    congr 1
    exact List.map_congr_left fun x _ ↦ by rw [div_mul_cancel₀ _ hS.ne']
  rw [hSt, Real.mul_rpow hP0 hQ0, Real.mul_rpow hP0 htr0, hQS]
  calc _ = (P ^ S * P ^ x₀.w.re) * (x₀.tr ^ x₀.w.re * (T.map fun x ↦ x.tr ^ x.w.re).prod) := by
        ring
    _ = holderBound (x₀ :: T) := by
        rw [hPP, hP]
        simp only [holderBound, List.map_cons, List.prod_cons]

/-- The multi-factor Hölder bound for lists of factors, by induction on the length. -/
private theorem norm_trace_le_holderBound (N : ℕ) :
    ∀ L : List (HolderFactor n), L.length = N →
      (∀ x ∈ L, x.K.IsHermitian ∧ 0 ≤ x.w.re) → (L.map fun x ↦ x.w.re).sum = 1 →
        ‖(L.map HolderFactor.mat).prod.trace‖ ≤ holderBound L := by
  induction N with
  | zero =>
    intro L hL _ hs
    rw [List.length_eq_zero_iff.1 hL] at hs
    simp at hs
  | succ N ih =>
    intro L hL hadm hs
    obtain ⟨x₀, T, rfl⟩ := List.exists_cons_of_length_eq_add_one hL
    have hT0 : ∀ a ∈ T.map fun x ↦ x.w.re, 0 ≤ a := fun a ha ↦ by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
      exact (hadm y (by simp [hy])).2
    have hsum : x₀.w.re + (T.map fun x ↦ x.w.re).sum = 1 := by simpa using hs
    rcases (List.sum_nonneg hT0).eq_or_lt with hS | hS
    · refine norm_trace_le_of_re_eq_zero x₀ T (fun x hx ↦ (hadm x hx).1) (by linarith)
        fun x hx ↦ le_antisymm ?_ (hT0 _ (List.mem_map_of_mem hx))
      exact (List.single_le_sum hT0 _ (List.mem_map_of_mem hx)).trans hS.symm.le
    · cases T with
      | nil => simp at hS
      | cons x₁ R =>
        exact norm_trace_le_of_interp N ih x₀ x₁ R (by simpa using hL) hadm hsum hS

end Interpolation

/-- **Multi-factor Hölder inequality for traces.** For Hermitian `K_0, …, K_{m-1}`, arbitrary
`B_0, …, B_{m-1}` and weights `θ_j ≥ 0` with `∑ θ_j = 1`,
`|Tr (B_0 e^{θ_0 K_0} ⋯ B_{m-1} e^{θ_{m-1} K_{m-1}})| ≤ ∏ ‖B_j‖ · ∏ (Tr e^{K_j})^{θ_j}`
for the ordered product, with operator norms `‖B_j‖`. With `X_j = e^{θ_j K_j}` and
`p_j = 1/θ_j` the right side is `∏ ‖B_j‖ ∏ ‖X_j‖_{p_j}` in Schatten norms. -/
theorem norm_trace_list_prod_mul_exp_smul_le {m : ℕ} (B K : Fin m → Matrix n n ℂ)
    (hK : ∀ j, (K j).IsHermitian) (θ : Fin m → ℝ) (hθ : ∀ j, 0 ≤ θ j) (hsum : ∑ j, θ j = 1) :
    ‖(List.ofFn fun j ↦ B j * NormedSpace.exp (θ j • K j)).prod.trace‖ ≤
      (∏ j, ‖B j‖) * ∏ j, (NormedSpace.exp (K j)).trace.re ^ θ j := by
  have h := norm_trace_le_holderBound _ (List.ofFn fun j ↦ (⟨B j, K j, (θ j : ℂ)⟩ :
    HolderFactor n)) rfl (by simp [List.mem_ofFn, hK, hθ]) (by simp [List.sum_ofFn, hsum])
  simpa [holderBound, HolderFactor.mat, HolderFactor.tr, List.map_ofFn, Function.comp_def,
    List.prod_ofFn, Complex.coe_smul] using h

/-- **Hölder bound for imaginary-time products.** For Hermitian `H`, arbitrary
`B_0, …, B_k` and `a_j ≥ 0` with `∑ a_j = β`,
`|Tr (B_0 e^{-a_0 H} B_1 e^{-a_1 H} ⋯ B_k e^{-a_k H})| ≤ ∏ ‖B_j‖ · Tr e^{-β H}`
for the ordered product. This gives the bound of Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1141–1151, on traces of products of imaginary-time evolved operators. -/
theorem IsHermitian.norm_trace_list_prod_mul_exp_neg_smul_le {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {k : ℕ} (B : Fin (k + 1) → Matrix n n ℂ) (a : Fin (k + 1) → ℝ)
    (ha : ∀ j, 0 ≤ a j) {β : ℝ} (hβ : ∑ j, a j = β) :
    ‖(List.ofFn fun j ↦ B j * NormedSpace.exp ((-a j) • H)).prod.trace‖ ≤
      (∏ j, ‖B j‖) * (NormedSpace.exp ((-β) • H)).trace.re := by
  have hβ0 : 0 ≤ β := hβ ▸ Finset.sum_nonneg fun j _ ↦ ha j
  rcases hβ0.eq_or_lt with h0 | hpos
  · -- All weights vanish: compare with the weight `1` on the first factor and `K = 0`.
    have ha0 : ∀ j, a j = 0 := fun j ↦
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ ha j).1 (hβ.trans h0.symm) j (by simp)
    have h := norm_trace_list_prod_mul_exp_smul_le B (fun _ ↦ 0) (fun _ ↦ isHermitian_zero)
      (fun j ↦ if j = 0 then 1 else 0) (fun j ↦ by split_ifs <;> norm_num) (by simp)
    simpa [ha0, ← h0] using h
  · -- Otherwise take `K_j = -β H` and `θ_j = a_j / β`.
    have hK : ((-β) • H).IsHermitian := hH.smul (IsSelfAdjoint.all _)
    have h := norm_trace_list_prod_mul_exp_smul_le B (fun _ ↦ (-β) • H) (fun _ ↦ hK)
      (fun j ↦ a j / β) (fun j ↦ div_nonneg (ha j) hpos.le)
      (by rw [← Finset.sum_div, hβ, div_self hpos.ne'])
    have hfac : ∀ j, (a j / β) • (-β) • H = (-a j) • H := fun j ↦ by
      rw [smul_smul]
      congr 1
      field_simp
    have htr : 0 ≤ (NormedSpace.exp ((-β) • H)).trace.re := trace_exp_re_nonneg hK
    rw [← Real.rpow_sum_of_nonneg htr fun j _ ↦ div_nonneg (ha j) hpos.le, ← Finset.sum_div, hβ,
      div_self hpos.ne', Real.rpow_one] at h
    simpa only [hfac] using h

end Matrix
