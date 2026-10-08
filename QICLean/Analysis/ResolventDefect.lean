/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The resolvent defect of a compression

Let `A` and `B` be positive definite operators given by orthonormal eigenbases
`U_A, U_B` and positive eigenvalues `λ, μ`, and let `V` be an isometry with
`V* A V = B`.  For a vector `b₀` put `a₀ = V b₀`.  For `v > 0` the **resolvent
defect** is
$$h(v)=\langle a_0,(A+v)^{-1}a_0\rangle-\langle b_0,(B+v)^{-1}b_0\rangle,$$
and the **resolvent discrepancy** is `δ_v = (A + v)⁻¹ a₀ - V (B + v)⁻¹ b₀`.  Expanding
`⟨δ_v, (A + v) δ_v⟩` with `V* (A + v) V = B + v` gives the identity
`⟨δ_v, (A + v) δ_v⟩ = h(v)` (Carlen--Vershynina, Lemma 2.1), so `h ≥ 0` and
`‖δ_v‖² ≤ h(v) / v`.

All functions of `A` and `B` are taken through the given eigenbases:
`spectralFun U f = U diag(f) U*`.

## Main definitions

* `Matrix.spectralFun` — `U diag(f) U*`.
* `Matrix.ResolventCompression` — the data `A, B, V, b₀` with the hypotheses above.
* `Matrix.ResolventCompression.defect`, `Matrix.ResolventCompression.discrepancy`.

## Main results

* `Matrix.ResolventCompression.defect_eq_quadratic` — `h(v) = ⟨δ_v, (A + v) δ_v⟩`.
* `Matrix.ResolventCompression.defect_nonneg` — `h(v) ≥ 0`.
* `Matrix.ResolventCompression.norm_discrepancy_sq_le` — `v ‖δ_v‖² ≤ h(v)`.

## References

* Two-dimensional area-law manuscript (September 24, 2026), proof of Lemma 5.2,
  `04-conditional.tex`, lines 352–379.
* E. A. Carlen and A. Vershynina, *Recovery map stability for the data processing
  inequality*, J. Phys. A 53 (2020), Lemma 2.1.
-/

open scoped Matrix ComplexOrder

noncomputable section

namespace Matrix

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The function `f` of the operator with orthonormal eigenbasis `U`:
`U diag(f) U*`. -/
def spectralFun (U : unitary (Matrix n n ℂ)) (f : n → ℂ) : Matrix n n ℂ :=
  (U : Matrix n n ℂ) * diagonal f * star (U : Matrix n n ℂ)

theorem spectralFun_mul (U : unitary (Matrix n n ℂ)) (f g : n → ℂ) :
    spectralFun U f * spectralFun U g = spectralFun U (f * g) := by
  simp only [spectralFun]
  rw [show (U : Matrix n n ℂ) * diagonal f * star (U : Matrix n n ℂ) *
      ((U : Matrix n n ℂ) * diagonal g * star (U : Matrix n n ℂ)) =
      (U : Matrix n n ℂ) * diagonal f * (star (U : Matrix n n ℂ) * (U : Matrix n n ℂ)) *
        diagonal g * star (U : Matrix n n ℂ) by simp only [Matrix.mul_assoc],
    Unitary.star_mul_self_of_mem U.2, Matrix.mul_one, Matrix.mul_assoc (U : Matrix n n ℂ),
    diagonal_mul_diagonal]
  rfl

theorem spectralFun_add (U : unitary (Matrix n n ℂ)) (f g : n → ℂ) :
    spectralFun U (f + g) = spectralFun U f + spectralFun U g := by
  rw [spectralFun, spectralFun, spectralFun, show diagonal (f + g) = diagonal f + diagonal g from
    (diagonal_add f g).symm, Matrix.mul_add, Matrix.add_mul]

theorem spectralFun_const (U : unitary (Matrix n n ℂ)) (c : ℂ) :
    spectralFun U (fun _ => c) = c • 1 := by
  simp only [spectralFun]
  rw [show diagonal (fun _ : n => c) = c • (1 : Matrix n n ℂ) by
      ext i j; by_cases h : i = j <;> simp [h, diagonal],
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Unitary.mul_star_self_of_mem U.2]

theorem spectralFun_one (U : unitary (Matrix n n ℂ)) :
    spectralFun U (fun _ => 1) = 1 := by
  rw [spectralFun_const, one_smul]

theorem conjTranspose_spectralFun (U : unitary (Matrix n n ℂ)) (f : n → ℂ) :
    (spectralFun U f)ᴴ = spectralFun U (star f) := by
  simp only [spectralFun, conjTranspose_mul, star_eq_conjTranspose, conjTranspose_conjTranspose,
    diagonal_conjTranspose, Matrix.mul_assoc]

/-- The quadratic form of a spectral function in eigencoordinates:
`⟨x, f(A) x⟩ = ∑ₖ f(λₖ) |(U* x)ₖ|²`. -/
theorem dotProduct_spectralFun_mulVec (U : unitary (Matrix n n ℂ)) (f : n → ℂ) (x : n → ℂ) :
    star x ⬝ᵥ (spectralFun U f *ᵥ x) =
      ∑ k, f k * ((Complex.normSq ((star (U : Matrix n n ℂ) *ᵥ x) k) : ℝ) : ℂ) := by
  set c := star (U : Matrix n n ℂ) *ᵥ x
  have hx : star x ⬝ᵥ (spectralFun U f *ᵥ x) = star c ⬝ᵥ (diagonal f *ᵥ c) := by
    simp only [spectralFun, c, ← mulVec_mulVec]
    rw [dotProduct_mulVec, star_mulVec, star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [hx]
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [RCLike.star_def]
  ring

omit [DecidableEq n] [DecidableEq m] in
theorem star_mulVec_dotProduct (W : Matrix n m ℂ) (x : m → ℂ) (y : n → ℂ) :
    star (W *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (Wᴴ *ᵥ y) := by
  rw [star_mulVec, ← dotProduct_mulVec]

omit [DecidableEq n] in
theorem star_mulVec_dotProduct_of_isHermitian {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (x y : n → ℂ) : star (H *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (H *ᵥ y) := by
  rw [star_mulVec_dotProduct, hH.eq]

/-- The data of a resolvent compression: positive definite `A = U_A diag(λ) U_A*` and
`B = U_B diag(μ) U_B*`, an isometry `V` with `V* A V = B`, and a vector `b₀`.
Area-law manuscript, proof of Lemma 5.2, `04-conditional.tex`, lines 352–367. -/
structure ResolventCompression (n m : Type*) [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] where
  /-- Eigenbasis of `A`. -/
  UA : unitary (Matrix n n ℂ)
  /-- Eigenvalues of `A`. -/
  lam : n → ℝ
  /-- Eigenbasis of `B`. -/
  UB : unitary (Matrix m m ℂ)
  /-- Eigenvalues of `B`. -/
  mu : m → ℝ
  /-- The compressing isometry. -/
  V : Matrix n m ℂ
  /-- The vector `b₀`. -/
  b0 : m → ℂ
  lam_pos : ∀ k, 0 < lam k
  mu_pos : ∀ j, 0 < mu j
  isometry : Vᴴ * V = 1
  compress : Vᴴ * spectralFun UA (fun k => (lam k : ℂ)) * V = spectralFun UB (fun j => (mu j : ℂ))

namespace ResolventCompression

variable (R : ResolventCompression n m)

/-- The operator `A`. -/
def opA : Matrix n n ℂ := spectralFun R.UA (fun k => (R.lam k : ℂ))

/-- The operator `B`. -/
def opB : Matrix m m ℂ := spectralFun R.UB (fun j => (R.mu j : ℂ))

/-- The vector `a₀ = V b₀`. -/
def a0 : n → ℂ := R.V *ᵥ R.b0

/-- The resolvent `(A + v)⁻¹`. -/
def resA (v : ℝ) : Matrix n n ℂ := spectralFun R.UA (fun k => ((R.lam k + v)⁻¹ : ℝ))

/-- The resolvent `(B + v)⁻¹`. -/
def resB (v : ℝ) : Matrix m m ℂ := spectralFun R.UB (fun j => ((R.mu j + v)⁻¹ : ℝ))

/-- The resolvent defect `h(v) = ⟨a₀, (A + v)⁻¹ a₀⟩ - ⟨b₀, (B + v)⁻¹ b₀⟩`.
Area-law manuscript, `04-conditional.tex`, lines 374–379. -/
noncomputable def defect (v : ℝ) : ℝ :=
  (star R.a0 ⬝ᵥ (R.resA v *ᵥ R.a0)).re - (star R.b0 ⬝ᵥ (R.resB v *ᵥ R.b0)).re

/-- The resolvent discrepancy `δ_v = (A + v)⁻¹ a₀ - V (B + v)⁻¹ b₀`.
Area-law manuscript, `04-conditional.tex`, line 369. -/
def discrepancy (v : ℝ) : n → ℂ := R.resA v *ᵥ R.a0 - R.V *ᵥ (R.resB v *ᵥ R.b0)

theorem opA_add_mul_resA {v : ℝ} (hv : 0 ≤ v) : (R.opA + (v : ℂ) • 1) * R.resA v = 1 := by
  rw [opA, ← spectralFun_const R.UA (v : ℂ), ← spectralFun_add, resA, spectralFun_mul,
    ← spectralFun_one R.UA]
  congr 1
  funext k
  have : ((R.lam k : ℂ) + v) ≠ 0 := by
    exact_mod_cast (add_pos_of_pos_of_nonneg (R.lam_pos k) hv).ne'
  simp only [Pi.mul_apply, Pi.add_apply]
  push_cast
  field_simp

theorem resB_mul_opB_add {v : ℝ} (hv : 0 ≤ v) : R.resB v * (R.opB + (v : ℂ) • 1) = 1 := by
  rw [opB, ← spectralFun_const R.UB (v : ℂ), ← spectralFun_add, resB, spectralFun_mul,
    ← spectralFun_one R.UB]
  congr 1
  funext k
  have : ((R.mu k : ℂ) + v) ≠ 0 := by
    exact_mod_cast (add_pos_of_pos_of_nonneg (R.mu_pos k) hv).ne'
  simp only [Pi.mul_apply, Pi.add_apply]
  push_cast
  field_simp

theorem compress_add (v : ℝ) : R.Vᴴ * (R.opA + (v : ℂ) • 1) * R.V = R.opB + (v : ℂ) • 1 := by
  rw [Matrix.mul_add, Matrix.add_mul, opA, R.compress, opB, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, R.isometry]

theorem resA_isHermitian (v : ℝ) : (R.resA v).IsHermitian := by
  rw [IsHermitian, resA, conjTranspose_spectralFun]
  congr 1
  funext k
  simp

theorem resB_isHermitian (v : ℝ) : (R.resB v).IsHermitian := by
  rw [IsHermitian, resB, conjTranspose_spectralFun]
  congr 1
  funext k
  simp

theorem opA_isHermitian : R.opA.IsHermitian := by
  rw [IsHermitian, opA, conjTranspose_spectralFun]
  congr 1
  funext k
  simp

theorem opB_add_mul_resB {v : ℝ} (hv : 0 ≤ v) : (R.opB + (v : ℂ) • 1) * R.resB v = 1 := by
  rw [opB, ← spectralFun_const R.UB (v : ℂ), ← spectralFun_add, resB, spectralFun_mul,
    ← spectralFun_one R.UB]
  congr 1
  funext k
  have : ((R.mu k : ℂ) + v) ≠ 0 := by
    exact_mod_cast (add_pos_of_pos_of_nonneg (R.mu_pos k) hv).ne'
  simp only [Pi.mul_apply, Pi.add_apply]
  push_cast
  field_simp

theorem opA_add_eq_spectralFun (v : ℝ) :
    R.opA + (v : ℂ) • 1 = spectralFun R.UA (fun k => ((R.lam k + v : ℝ) : ℂ)) := by
  rw [opA, ← spectralFun_const R.UA (v : ℂ), ← spectralFun_add]
  congr 1
  funext k
  simp

theorem opA_add_isHermitian (v : ℝ) : (R.opA + (v : ℂ) • 1).IsHermitian := by
  rw [opA_add_eq_spectralFun, IsHermitian, conjTranspose_spectralFun]
  congr 1
  funext k
  simp

/-- The resolvent compression identity `⟨δ_v, (A + v) δ_v⟩ = ⟨a₀, (A + v)⁻¹ a₀⟩ -
⟨b₀, (B + v)⁻¹ b₀⟩` (Carlen--Vershynina, Lemma 2.1).  Area-law manuscript,
`04-conditional.tex`, lines 371–379. -/
theorem discrepancy_quadratic {v : ℝ} (hv : 0 ≤ v) :
    star (R.discrepancy v) ⬝ᵥ ((R.opA + (v : ℂ) • 1) *ᵥ R.discrepancy v) =
      star R.a0 ⬝ᵥ (R.resA v *ᵥ R.a0) - star R.b0 ⬝ᵥ (R.resB v *ᵥ R.b0) := by
  set M := R.opA + (v : ℂ) • 1
  set y := R.resB v *ᵥ R.b0
  have hM : M.IsHermitian := R.opA_add_isHermitian v
  have e1 : M *ᵥ (R.resA v *ᵥ R.a0) = R.a0 := by
    rw [mulVec_mulVec, R.opA_add_mul_resA hv, one_mulVec]
  have e2 : (R.opB + (v : ℂ) • 1) *ᵥ y = R.b0 := by
    rw [mulVec_mulVec, R.opB_add_mul_resB hv, one_mulVec]
  have hVV : R.Vᴴ *ᵥ (R.V *ᵥ R.b0) = R.b0 := by rw [mulVec_mulVec, R.isometry, one_mulVec]
  have hVVy : R.Vᴴ *ᵥ (R.V *ᵥ y) = y := by rw [mulVec_mulVec, R.isometry, one_mulVec]
  have hy : star y ⬝ᵥ R.b0 = star R.b0 ⬝ᵥ y :=
    star_mulVec_dotProduct_of_isHermitian (R.resB_isHermitian v) _ _
  have t1 : star (R.resA v *ᵥ R.a0) ⬝ᵥ R.a0 = star R.a0 ⬝ᵥ (R.resA v *ᵥ R.a0) :=
    star_mulVec_dotProduct_of_isHermitian (R.resA_isHermitian v) _ _
  have t2 : star (R.resA v *ᵥ R.a0) ⬝ᵥ (M *ᵥ (R.V *ᵥ y)) = star R.b0 ⬝ᵥ y := by
    rw [← star_mulVec_dotProduct_of_isHermitian hM, e1, a0, star_mulVec_dotProduct, hVVy]
  have t3 : star (R.V *ᵥ y) ⬝ᵥ R.a0 = star R.b0 ⬝ᵥ y := by
    rw [a0, star_mulVec_dotProduct, hVV, hy]
  have t4 : star (R.V *ᵥ y) ⬝ᵥ (M *ᵥ (R.V *ᵥ y)) = star R.b0 ⬝ᵥ y := by
    rw [star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec, R.compress_add v, e2, hy]
  rw [discrepancy, mulVec_sub, e1, star_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    t1, t2, t3, t4]
  ring

theorem re_dotProduct_spectralFun_ge (U : unitary (Matrix n n ℂ)) (f : n → ℝ) {c : ℝ}
    (hf : ∀ k, c ≤ f k) (x : n → ℂ) :
    c * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (spectralFun U (fun k => (f k : ℂ)) *ᵥ x)).re := by
  have h1 := dotProduct_spectralFun_mulVec U (fun _ => (1 : ℂ)) x
  rw [spectralFun_one, one_mulVec] at h1
  rw [h1, dotProduct_spectralFun_mulVec]
  simp only [one_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hf k) (Complex.normSq_nonneg _)

/-- `v ‖δ_v‖² ≤ h(v)`.  Area-law manuscript, `04-conditional.tex`, line 407. -/
theorem mul_norm_discrepancy_sq_le {v : ℝ} (hv : 0 ≤ v) :
    v * (star (R.discrepancy v) ⬝ᵥ R.discrepancy v).re ≤ R.defect v := by
  have h := re_dotProduct_spectralFun_ge R.UA (fun k => R.lam k + v)
    (c := v) (fun k => by linarith [R.lam_pos k]) (R.discrepancy v)
  rw [← opA_add_eq_spectralFun, R.discrepancy_quadratic hv, Complex.sub_re] at h
  exact h

/-- The resolvent defect is nonnegative.  Area-law manuscript, `04-conditional.tex`,
line 378. -/
theorem defect_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ R.defect v := by
  have h := re_dotProduct_spectralFun_ge R.UA (fun k => R.lam k + v)
    (c := 0) (fun k => by linarith [R.lam_pos k]) (R.discrepancy v)
  rw [← opA_add_eq_spectralFun, R.discrepancy_quadratic hv, Complex.sub_re, zero_mul] at h
  exact h

end ResolventCompression

end Matrix

end
