/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.BetaHalfLine
import QICLean.Representation.Alternant
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The gamma integral of the replica metrics

On the positive orthant of `ℝ^d` with Lebesgue measure, the proof of Lemma 6.2 of the area-law
paper (*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
lines 347–364) integrates `Δ(s) det[s_i^{t l_j}]` and obtains

`d! / Γ(c + t k) · det[Γ(1 + t l_i + d - j)]`,

which equals `∏_i Γ(1 + t l_i)` times `t^{binom(d,2)} Δ(l)` up to the normalization. The paper
integrates over the simplex; here the variables range over the whole orthant with the weight
`(∑ x)^{-a} e^{-∑ x}`, which gives the same quotient of gamma values. Concretely, with
`δ_j = d - 1 - j`, `D = d + ∑_j δ_j + t ∑_j l_j` and `0 ≤ a < D`,

`∫ a_δ(x) a_l(x^t) (∑ x)^{-a} e^{-∑ x} dx =
  d! t^{binom(d,2)} ∏_j Γ(1 + t l_j) a_δ(l) Γ(D - a)/Γ(D)`,

where `a_α(y) = det [y_i ^ α_j]`. The radial factor comes from
`Γ(a) r^{-a} = ∫_0^∞ v^{a-1} e^{-r v} dv` and the half-line Beta integral; the determinant from
`Γ(1 + t l + n) = Γ(1 + t l) (1 + t l)(2 + t l) ⋯ (n + t l)`, a monic polynomial of degree `n`
in `t l`.

The proofs are written from the paper and the standard theory; no Lean source was adapted.

## Main declarations

* `Partition.orthant d` — Lebesgue measure on the positive orthant.
* `Partition.integral_monomial`, `Partition.integral_monomial_mul_rpow_sum` — orthMono
  integrals.
* `Partition.alternant_shiftedPart_zero` — `a_δ(y) = ε_d V(y)` with `ε_d = ±1`.
* `Partition.integral_alternant_mul_alternant` — **the gamma integral**.
-/

open MeasureTheory Set Finset Real Matrix Polynomial

namespace Partition

variable {d : ℕ}

/-! ### Monomial integrals on the positive orthant -/

/-- Lebesgue measure on the positive orthant `(0, ∞)^d`. -/
noncomputable def orthant (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun _ => volume.restrict (Ioi (0 : ℝ))

instance : SigmaFinite (orthant d) := by
  unfold orthant; infer_instance

theorem ae_orthant_pos : ∀ᵐ x ∂(orthant d), ∀ i, 0 < x i := by
  rw [ae_all_iff]
  intro i
  exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioi)

/-- The orthMono `∏_i x_i^{u_i} e^{-b x_i}`. -/
noncomputable def orthMono (u : Fin d → ℝ) (b : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, x i ^ u i * exp (-b * x i)

theorem integrableOn_coord (s : ℝ) (hs : -1 < s) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (-b * x)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hs one_pos hb
  simpa using h

theorem integrable_monomial (u : Fin d → ℝ) (hu : ∀ i, -1 < u i) {b : ℝ} (hb : 0 < b) :
    Integrable (orthMono u b) (orthant d) :=
  Integrable.fintype_prod (f := fun i (x : ℝ) => x ^ u i * exp (-b * x))
    fun i => integrableOn_coord (u i) (hu i) hb

theorem integral_monomial (u : Fin d → ℝ) (hu : ∀ i, -1 < u i) {b : ℝ} (hb : 0 < b) :
    ∫ x, orthMono u b x ∂(orthant d) = ∏ i, (Gamma (1 + u i) * (1 / b) ^ (1 + u i)) := by
  change ∫ x, ∏ i, x i ^ u i * exp (-b * x i) ∂(orthant d) = _
  rw [orthant, integral_fintype_prod_eq_prod
    (f := fun i (x : ℝ) => x ^ u i * exp (-b * x))]
  refine prod_congr rfl fun i _ => ?_
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := 1 + u i) (by linarith [hu i]) hb
  rw [show 1 + u i - 1 = u i by ring] at h
  simp only [neg_mul] at h ⊢
  rw [h, mul_comm]

theorem monomial_nonneg (u : Fin d → ℝ) (b : ℝ) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) :
    0 ≤ orthMono u b x :=
  prod_nonneg fun i _ => mul_nonneg (rpow_nonneg (hx i).le _) (exp_pos _).le

theorem measurable_monomial (u : Fin d → ℝ) (b : ℝ) : Measurable (orthMono u b) := by
  change Measurable (fun x : Fin d → ℝ => ∏ i, x i ^ u i * exp (-b * x i))
  fun_prop

/-- **Monomial integrals with a radial weight**: for `0 < a < D = d + ∑ u`,
`∫ ∏ x_i^{u_i} (∑ x)^{-a} e^{-∑ x} = ∏ Γ(1 + u_i) · Γ(D - a)/Γ(D)`. -/
theorem integral_monomial_mul_rpow_sum (hd : 0 < d) (u : Fin d → ℝ) (hu : ∀ i, -1 < u i)
    {a : ℝ} (ha : 0 < a) (hDa : a < d + ∑ i, u i) :
    ∫ x, orthMono u 1 x * (∑ i, x i) ^ (-a) ∂(orthant d) =
      (∏ i, Gamma (1 + u i)) * Gamma (d + ∑ i, u i - a) / Gamma (d + ∑ i, u i) := by
  set D := (d : ℝ) + ∑ i, u i
  set μv := volume.restrict (Ioi (0 : ℝ))
  -- the integrand of the double integral
  set f : (Fin d → ℝ) → ℝ → ℝ := fun x v => v ^ (a - 1) * orthMono u (1 + v) x
  have hsum_pos : ∀ x : Fin d → ℝ, (∀ i, 0 < x i) → 0 < ∑ i, x i := fun x hx =>
    sum_pos (fun i _ => hx i) ⟨⟨0, hd⟩, mem_univ _⟩
  -- inner integral over `v`
  have hinner : ∀ x : Fin d → ℝ, (∀ i, 0 < x i) →
      ∫ v, f x v ∂μv = Gamma a * (orthMono u 1 x * (∑ i, x i) ^ (-a)) := by
    intro x hx
    have hr := hsum_pos x hx
    have hmon : ∀ v, orthMono u (1 + v) x = orthMono u 1 x * exp (-(v * ∑ i, x i)) := by
      intro v
      simp only [orthMono, mul_sum, ← sum_neg_distrib, exp_sum, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      rw [mul_assoc, ← exp_add]
      congr 2
      ring
    simp only [f, hmon]
    have h := integral_rpow_mul_exp_neg_mul_Ioi ha hr
    calc ∫ v, v ^ (a - 1) * (orthMono u 1 x * exp (-(v * ∑ i, x i))) ∂μv
        = orthMono u 1 x * ∫ v in Ioi 0, v ^ (a - 1) * exp (-((∑ i, x i) * v)) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (ae_of_all _ fun v => ?_)
          simp only [mul_comm v]
          ring
      _ = Gamma a * (orthMono u 1 x * (∑ i, x i) ^ (-a)) := by
          rw [h, one_div, inv_rpow hr.le, ← rpow_neg hr.le]
          ring
  -- inner integral over `x`
  have hinner' : ∀ v : ℝ, 0 < v → ∫ x, f x v ∂(orthant d) =
      (∏ i, Gamma (1 + u i)) * (v ^ (a - 1) * (1 + v) ^ (-D)) := by
    intro v hv
    have h1v : (0 : ℝ) < 1 + v := by linarith
    simp only [f]
    rw [integral_const_mul, integral_monomial u hu h1v, prod_mul_distrib]
    have : ∏ i, (1 / (1 + v)) ^ (1 + u i) = (1 + v) ^ (-D) := by
      rw [← rpow_sum_of_pos (by positivity), sum_add_distrib, one_div, inv_rpow h1v.le,
        ← rpow_neg h1v.le]
      simp [D]
    rw [this]
    ring
  -- integrability on the product
  have hmeas : Measurable (Function.uncurry f) := by
    simp only [f, orthMono]
    fun_prop
  have hint : Integrable (Function.uncurry f) ((orthant d).prod μv) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      change Integrable (fun x => v ^ (a - 1) * orthMono u (1 + v) x) (orthant d)
      exact (integrable_monomial u hu (by linarith [mem_Ioi.mp hv] : (0 : ℝ) < 1 + v)).const_mul _
    · have hB := integrableOn_rpow_mul_one_add_rpow ha (by linarith : 0 < D - a)
      rw [show a + (D - a) = D by ring] at hB
      refine (hB.const_mul (∏ i, Gamma (1 + u i))).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hv' : (0 : ℝ) < v := hv
      rw [← hinner' v hv']
      refine integral_congr_ae ?_
      filter_upwards [ae_orthant_pos] with x hx
      simp only [Function.uncurry_apply_pair, f]
      rw [Real.norm_of_nonneg (mul_nonneg (rpow_nonneg hv'.le _) (monomial_nonneg u _ hx))]
  -- swap the order of integration
  have hswap := integral_integral_swap hint
  have hlhs : ∫ x, ∫ v, f x v ∂μv ∂(orthant d) =
      Gamma a * ∫ x, orthMono u 1 x * (∑ i, x i) ^ (-a) ∂(orthant d) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_orthant_pos] with x hx
    exact hinner x hx
  have hrhs : ∫ v, ∫ x, f x v ∂(orthant d) ∂μv =
      (∏ i, Gamma (1 + u i)) * (Gamma a * Gamma (D - a) / Gamma D) := by
    have hB := Real.integral_rpow_mul_one_add_rpow ha (by linarith : 0 < D - a)
    rw [show a + (D - a) = D by ring] at hB
    rw [← hB, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun v hv => hinner' v hv
  rw [hlhs, hrhs] at hswap
  have hGa : 0 < Gamma a := Gamma_pos_of_pos ha
  field_simp at hswap ⊢
  linear_combination hswap

/-! ### Expanding the alternants -/

/-- The descending exponents `δ_j = d - 1 - j`. -/
abbrev delta (d : ℕ) : Fin d → ℕ := shiftedPart (0 : Fin d → ℕ)

theorem prod_perm_pow (σ : Equiv.Perm (Fin d)) (α : Fin d → ℕ) (y : Fin d → ℝ) :
    ∏ i, y (σ i) ^ α i = ∏ i, y i ^ α (σ⁻¹ i) :=
  Fintype.prod_equiv σ _ _ fun i => by simp

/-- On the positive orthant, `a_α(x) a_β(x^t)` is a signed sum of monomials. -/
theorem alternant_mul_alternant_rpow (α β : Fin d → ℕ) (t : ℝ) {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) :
    alternant α x * alternant β (fun i => x i ^ t) =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        ((Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign τ) *
          ∏ i, x i ^ ((α (σ⁻¹ i) : ℝ) + t * β (τ⁻¹ i)) := by
  rw [alternant_eq_sum, alternant_eq_sum, sum_mul_sum]
  refine sum_congr rfl fun σ _ => sum_congr rfl fun τ _ => ?_
  rw [prod_perm_pow, prod_perm_pow τ β (fun i => x i ^ t)]
  have : ∀ i, x i ^ α (σ⁻¹ i) * (x i ^ t) ^ β (τ⁻¹ i) =
      x i ^ ((α (σ⁻¹ i) : ℝ) + t * β (τ⁻¹ i)) := by
    intro i
    rw [← rpow_natCast (x i ^ t), ← rpow_mul (hx i).le, ← rpow_natCast (x i),
      ← rpow_add (hx i)]
  rw [mul_mul_mul_comm, ← prod_mul_distrib]
  simp only [this]

/-! ### The determinant -/

/-- The rising factorial `(z + 1)(z + 2) ⋯ (z + n)` as a polynomial in `z`. -/
noncomputable def risingPoly (n : ℕ) : ℝ[X] := (ascPochhammer ℝ n).comp (X + 1)

theorem risingPoly_monic (n : ℕ) : (risingPoly n).Monic :=
  (monic_ascPochhammer ℝ n).comp (monic_X_add_C 1) (by simp)

theorem natDegree_risingPoly (n : ℕ) : (risingPoly n).natDegree = n := by
  rw [risingPoly, natDegree_comp]
  simp

theorem Gamma_add_nat {z : ℝ} (hz : 0 < z) (n : ℕ) :
    Gamma (z + n) = Gamma z * (ascPochhammer ℝ n).eval z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one (by positivity), ih, ascPochhammer_succ_right,
      eval_mul]
    simp
    ring

theorem Gamma_one_add_add_nat {z : ℝ} (hz : 0 ≤ z) (n : ℕ) :
    Gamma (1 + z + n) = Gamma (1 + z) * (risingPoly n).eval z := by
  rw [Gamma_add_nat (by positivity), risingPoly, eval_comp]
  simp [add_comm z]

/-- The reversal of the rows `j ↦ d - 1 - j`. -/
def revPerm (d : ℕ) : Equiv.Perm (Fin d) := Fin.revPerm

theorem delta_eq_revPerm (j : Fin d) : delta d j = (revPerm d j : ℕ) := by
  simp only [shiftedPart, revPerm, Fin.revPerm_apply, Fin.val_rev, Pi.zero_apply, zero_add]
  omega

/-- The alternant with descending exponents is a sign times the Vandermonde determinant. -/
theorem alternant_delta_eq (y : Fin d → ℝ) :
    alternant (delta d) y = (Equiv.Perm.sign (revPerm d) : ℝ) * (vandermonde y).det := by
  have : (Matrix.of fun i j => y i ^ delta d j) = (vandermonde y).submatrix id (revPerm d) := by
    ext i j
    simp only [of_apply, submatrix_apply, id, vandermonde_apply, delta_eq_revPerm]
  rw [alternant, this, det_permute']

/-- `det [P_{δ_i}(z_j)] = a_δ(z)` for the rising factorials `P_n`. -/
theorem det_risingPoly (z : Fin d → ℝ) :
    (Matrix.of fun i j => (risingPoly (delta d i)).eval (z j)).det = alternant (delta d) z := by
  have hp := det_eval_matrixOfPolynomials_eq_det_vandermonde z (fun j : Fin d => risingPoly j)
    (fun j => natDegree_risingPoly j) (fun j => risingPoly_monic j)
  rw [alternant_delta_eq, hp, ← det_transpose]
  have : (Matrix.of fun i j => (risingPoly (delta d i)).eval (z j))ᵀ =
      (Matrix.of fun i (j : Fin d) => (risingPoly j).eval (z i)).submatrix id (revPerm d) := by
    ext i j
    simp only [transpose_apply, of_apply, submatrix_apply, id, delta_eq_revPerm]
  rw [this, det_permute']

end Partition
