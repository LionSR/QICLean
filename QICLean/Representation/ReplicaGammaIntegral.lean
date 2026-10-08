/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.BetaHalfLine
import QICLean.Representation.Alternant
import QICLean.Representation.ReplicaWeight
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
theorem integrable_and_integral_monomial_mul_rpow_sum (hd : 0 < d) (u : Fin d → ℝ)
    (hu : ∀ i, -1 < u i) {a : ℝ} (ha : 0 < a) (hDa : a < d + ∑ i, u i) :
    Integrable (fun x => orthMono u 1 x * (∑ i, x i) ^ (-a)) (orthant d) ∧
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
  refine ⟨?_, ?_⟩
  · refine (hint.integral_prod_left.const_mul (Gamma a)⁻¹).congr ?_
    filter_upwards [ae_orthant_pos] with x hx
    simp only [Function.uncurry_apply_pair]
    rw [hinner x hx]
    field_simp
  · field_simp at hswap ⊢
    linear_combination hswap

theorem integral_monomial_mul_rpow_sum (hd : 0 < d) (u : Fin d → ℝ) (hu : ∀ i, -1 < u i)
    {a : ℝ} (ha : 0 < a) (hDa : a < d + ∑ i, u i) :
    ∫ x, orthMono u 1 x * (∑ i, x i) ^ (-a) ∂(orthant d) =
      (∏ i, Gamma (1 + u i)) * Gamma (d + ∑ i, u i - a) / Gamma (d + ∑ i, u i) :=
  (integrable_and_integral_monomial_mul_rpow_sum hd u hu ha hDa).2

/-- The radial weight with exponent `0 ≤ a < D` keeps monomials integrable. -/
theorem integrable_monomial_mul_rpow_sum (hd : 0 < d) (u : Fin d → ℝ) (hu : ∀ i, -1 < u i)
    {a : ℝ} (ha : 0 ≤ a) (hDa : a < d + ∑ i, u i) :
    Integrable (fun x => orthMono u 1 x * (∑ i, x i) ^ (-a)) (orthant d) := by
  rcases ha.lt_or_eq with ha | rfl
  · exact (integrable_and_integral_monomial_mul_rpow_sum hd u hu ha hDa).1
  · simpa using integrable_monomial u hu one_pos

/-- The same with `a = 0` included. -/
theorem integral_monomial_mul_rpow_sum' (hd : 0 < d) (u : Fin d → ℝ) (hu : ∀ i, -1 < u i)
    {a : ℝ} (ha : 0 ≤ a) (hDa : a < d + ∑ i, u i) :
    ∫ x, orthMono u 1 x * (∑ i, x i) ^ (-a) ∂(orthant d) =
      (∏ i, Gamma (1 + u i)) * Gamma (d + ∑ i, u i - a) / Gamma (d + ∑ i, u i) := by
  rcases ha.lt_or_eq with ha | rfl
  · exact integral_monomial_mul_rpow_sum hd u hu ha hDa
  · have hD : 0 < (d : ℝ) + ∑ i, u i := by
      have : ∑ i, (-1 : ℝ) < ∑ i, u i :=
        sum_lt_sum_of_nonempty ⟨⟨0, hd⟩, mem_univ _⟩ fun i _ => hu i
      simp at this
      linarith
    simp only [neg_zero, rpow_zero, mul_one, sub_zero]
    rw [integral_monomial u hu one_pos, mul_div_assoc, div_self (Gamma_pos_of_pos hD).ne',
      mul_one]
    simp

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

/-- Alternants are homogeneous: `a_α(c y) = c^{∑ α} a_α(y)`. -/
theorem alternant_mul_left (α : Fin d → ℕ) (c : ℝ) (y : Fin d → ℝ) :
    alternant α (fun i => c * y i) = c ^ (∑ i, α i) * alternant α y := by
  simp only [alternant_eq_sum, mul_sum]
  refine sum_congr rfl fun σ _ => ?_
  simp only [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum]
  ring

theorem sum_delta (d : ℕ) : ∑ i : Fin d, delta d i = d.choose 2 := by
  have h : ∑ i : Fin d, delta d i = ∑ i ∈ range d, i := by
    have e : ∀ i : Fin d, delta d i = d - 1 - (i : ℕ) := fun i => by simp [shiftedPart]
    simp only [e]
    rw [Fin.sum_univ_eq_sum_range (fun i => d - 1 - i) d, ← sum_range_reflect]
    refine sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    omega
  rw [h, sum_range_id, Nat.choose_two_right]

/-- The gamma integral `J_a(l) = ∫ a_δ(x) a_l(x^t) (∑ x)^{-a} e^{-∑ x} dx` over the positive
orthant. -/
noncomputable def gammaIntegral (d : ℕ) (t : ℝ) (l : Fin d → ℕ) (a : ℝ) : ℝ :=
  ∫ x, alternant (delta d) x * alternant l (fun i => x i ^ t) * (∑ i, x i) ^ (-a) *
    exp (-∑ i, x i) ∂(orthant d)

/-- The exponents `δ_{σ⁻¹ i} + t l_{τ⁻¹ i}` of one monomial of the expansion. -/
noncomputable def termExp (t : ℝ) (l : Fin d → ℕ) (σ τ : Equiv.Perm (Fin d)) : Fin d → ℝ :=
  fun i => (delta d (σ⁻¹ i) : ℝ) + t * l (τ⁻¹ i)

theorem termExp_gt {t : ℝ} (ht : 0 ≤ t) (l : Fin d → ℕ) (σ τ : Equiv.Perm (Fin d)) (i : Fin d) :
    -1 < termExp t l σ τ i := by
  have : 0 ≤ termExp t l σ τ i := by unfold termExp; positivity
  linarith

theorem sum_termExp (t : ℝ) (l : Fin d → ℕ) (σ τ : Equiv.Perm (Fin d)) :
    ∑ i, termExp t l σ τ i = (∑ i, delta d i : ℕ) + t * ∑ i, (l i : ℝ) := by
  simp only [termExp, sum_add_distrib, ← mul_sum]
  push_cast
  rw [Fintype.sum_equiv σ⁻¹ (fun i => ((delta d (σ⁻¹ i) : ℕ) : ℝ))
      (fun i => ((delta d i : ℕ) : ℝ)) fun i => rfl,
    Fintype.sum_equiv τ⁻¹ (fun i => ((l (τ⁻¹ i) : ℕ) : ℝ)) (fun i => ((l i : ℕ) : ℝ))
      fun i => rfl]

theorem orthMono_one (u : Fin d → ℝ) (x : Fin d → ℝ) :
    orthMono u 1 x = (∏ i, x i ^ u i) * exp (-∑ i, x i) := by
  simp only [orthMono, neg_mul, one_mul, prod_mul_distrib, ← sum_neg_distrib, exp_sum]

theorem gammaIntegrand_eq (t : ℝ) (l : Fin d → ℕ) (a : ℝ) {x : Fin d → ℝ} (hx : ∀ i, 0 < x i) :
    alternant (delta d) x * alternant l (fun i => x i ^ t) * (∑ i, x i) ^ (-a) *
        exp (-∑ i, x i) =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        ((Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign τ) *
          (orthMono (termExp t l σ τ) 1 x * (∑ i, x i) ^ (-a)) := by
  rw [alternant_mul_alternant_rpow _ _ t hx, sum_mul, sum_mul]
  refine sum_congr rfl fun σ _ => ?_
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun τ _ => ?_
  rw [orthMono_one]
  simp only [termExp]
  ring

/-- **The gamma integral as a sum over pairs of permutations.** -/
theorem gammaIntegral_eq_sum (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) (l : Fin d → ℕ) {a : ℝ}
    (ha : 0 ≤ a) (hDa : a < d + (∑ i, delta d i : ℕ) + t * ∑ i, (l i : ℝ)) :
    gammaIntegral d t l a =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        ((Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign τ) *
          ((∏ i, Gamma (1 + termExp t l σ τ i)) *
            Gamma (d + (∑ i, delta d i : ℕ) + t * ∑ i, (l i : ℝ) - a) /
              Gamma (d + (∑ i, delta d i : ℕ) + t * ∑ i, (l i : ℝ))) := by
  have hD : ∀ σ τ : Equiv.Perm (Fin d), a < d + ∑ i, termExp t l σ τ i := fun σ τ => by
    rw [sum_termExp, ← add_assoc]; exact hDa
  have hint : ∀ σ τ : Equiv.Perm (Fin d),
      Integrable (fun x => orthMono (termExp t l σ τ) 1 x * (∑ i, x i) ^ (-a)) (orthant d) :=
    fun σ τ => integrable_monomial_mul_rpow_sum hd _ (termExp_gt ht l σ τ) ha (hD σ τ)
  rw [gammaIntegral, integral_congr_ae (ae_orthant_pos.mono fun x hx =>
    gammaIntegrand_eq t l a hx)]
  rw [integral_finsetSum _ fun σ _ => integrable_finsetSum _ fun τ _ => (hint σ τ).const_mul _]
  refine sum_congr rfl fun σ _ => ?_
  rw [integral_finsetSum _ fun τ _ => (hint σ τ).const_mul _]
  refine sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, integral_monomial_mul_rpow_sum' hd _ (termExp_gt ht l σ τ) ha (hD σ τ),
    sum_termExp, ← add_assoc]

/-- The gamma integrand is integrable. -/
theorem integrable_gammaIntegrand (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) (l : Fin d → ℕ) {a : ℝ}
    (ha : 0 ≤ a) (hDa : a < d + (∑ i, delta d i : ℕ) + t * ∑ i, (l i : ℝ)) :
    Integrable (fun x => alternant (delta d) x * alternant l (fun i => x i ^ t) *
      (∑ i, x i) ^ (-a) * exp (-∑ i, x i)) (orthant d) := by
  have hD : ∀ σ τ : Equiv.Perm (Fin d), a < d + ∑ i, termExp t l σ τ i := fun σ τ => by
    rw [sum_termExp, ← add_assoc]; exact hDa
  have hint : ∀ σ τ : Equiv.Perm (Fin d),
      Integrable (fun x => orthMono (termExp t l σ τ) 1 x * (∑ i, x i) ^ (-a)) (orthant d) :=
    fun σ τ => integrable_monomial_mul_rpow_sum hd _ (termExp_gt ht l σ τ) ha (hD σ τ)
  refine (integrable_finsetSum univ fun σ _ => integrable_finsetSum univ fun τ _ =>
    (hint σ τ).const_mul ((Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign τ)).congr ?_
  filter_upwards [ae_orthant_pos] with x hx
  rw [gammaIntegrand_eq t l a hx]

/-- The double sum over permutations is `d!` times a determinant of gamma values. -/
theorem sum_sign_prod_Gamma (t : ℝ) (l : Fin d → ℕ) :
    ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        ((Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign τ) * ∏ i, Gamma (1 + termExp t l σ τ i) =
      d.factorial * (Matrix.of fun i j => Gamma (1 + (delta d i : ℝ) + t * l j)).det := by
  rw [sum_comm]
  have h : ∀ τ : Equiv.Perm (Fin d), ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign τ) * ∏ i, Gamma (1 + termExp t l σ τ i) =
      (Matrix.of fun i j => Gamma (1 + (delta d i : ℝ) + t * l j)).det := by
    intro τ
    rw [det_apply]
    refine Fintype.sum_equiv ((Equiv.inv _).trans (Equiv.mulRight τ)) _ _ fun σ => ?_
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight, Units.smul_def,
      zsmul_eq_mul, of_apply, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    push_cast
    congr 1
    exact Fintype.prod_equiv τ⁻¹ _ _ fun i => by
      simp [termExp, add_assoc]
  rw [sum_congr rfl fun τ _ => h τ, sum_const, card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

/-- **The determinant of gamma values**:
`det [Γ(1 + δ_i + t l_j)] = ∏_j Γ(1 + t l_j) · a_δ(t l)`. -/
theorem det_Gamma {t : ℝ} (ht : 0 ≤ t) (l : Fin d → ℕ) :
    (Matrix.of fun i j => Gamma (1 + (delta d i : ℝ) + t * l j)).det =
      (∏ j, Gamma (1 + t * l j)) * alternant (delta d) (fun j => t * l j) := by
  have h : (Matrix.of fun i j => Gamma (1 + (delta d i : ℝ) + t * l j)) =
      Matrix.of fun i j => Gamma (1 + t * l j) * (risingPoly (delta d i)).eval (t * l j) := by
    ext i j
    simp only [of_apply]
    rw [← Gamma_one_add_add_nat (by positivity)]
    congr 1
    ring
  have hrow := det_mul_row (fun j => Gamma (1 + t * l j))
    (Matrix.of fun i j => (risingPoly (delta d i)).eval (t * l j))
  simp only [of_apply] at hrow
  rw [h, hrow, det_risingPoly]

/-- **The gamma integral** (`05-replicas.tex`, lines 347–364): with `N = binom(d, 2)` and
`D = d + N + t ∑_j l_j`, for `0 ≤ a < D`,
`J_a(l) = d! t^N ∏_j Γ(1 + t l_j) a_δ(l) Γ(D - a)/Γ(D)`. -/
theorem gammaIntegral_eq (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) (l : Fin d → ℕ) {a : ℝ}
    (ha : 0 ≤ a) (hDa : a < d + (d.choose 2 : ℕ) + t * ∑ i, (l i : ℝ)) :
    gammaIntegral d t l a =
      d.factorial * t ^ d.choose 2 * (∏ j, Gamma (1 + t * l j)) *
        alternant (delta d) (fun j => (l j : ℝ)) *
          (Gamma (d + (d.choose 2 : ℕ) + t * ∑ i, (l i : ℝ) - a) /
            Gamma (d + (d.choose 2 : ℕ) + t * ∑ i, (l i : ℝ))) := by
  rw [← sum_delta] at hDa ⊢
  rw [gammaIntegral_eq_sum hd ht l ha hDa]
  set R := Gamma (d + ((∑ i, delta d i : ℕ) : ℝ) + t * ∑ i, (l i : ℝ) - a) /
    Gamma (d + ((∑ i, delta d i : ℕ) : ℝ) + t * ∑ i, (l i : ℝ))
  have e : ∀ σ τ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign τ) *
      ((∏ i, Gamma (1 + termExp t l σ τ i)) * Gamma (d + ((∑ i, delta d i : ℕ) : ℝ) +
        t * ∑ i, (l i : ℝ) - a) / Gamma (d + ((∑ i, delta d i : ℕ) : ℝ) + t * ∑ i, (l i : ℝ))) =
      (((Equiv.Perm.sign σ : ℝ) * Equiv.Perm.sign τ) * ∏ i, Gamma (1 + termExp t l σ τ i)) * R :=
    fun σ τ => by simp only [R]; ring
  simp only [e, ← sum_mul]
  rw [sum_sign_prod_Gamma, det_Gamma ht, alternant_mul_left]
  ring

/-! ### The normalized ratio is the common label function -/

theorem sign_revPerm_mul_self :
    (Equiv.Perm.sign (revPerm d) : ℝ) * Equiv.Perm.sign (revPerm d) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

/-- The density `a_δ(x) a_δ(x^t)` is nonnegative on the positive orthant. -/
theorem alternant_delta_mul_rpow_nonneg {t : ℝ} (ht : 0 ≤ t) {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) : 0 ≤ alternant (delta d) x * alternant (delta d) (fun i => x i ^ t) := by
  rw [alternant_delta_eq, alternant_delta_eq, det_vandermonde, det_vandermonde]
  have e : (Equiv.Perm.sign (revPerm d) : ℝ) * (∏ i, ∏ j ∈ Ioi i, (x j - x i)) *
      ((Equiv.Perm.sign (revPerm d) : ℝ) * ∏ i, ∏ j ∈ Ioi i, (x j ^ t - x i ^ t)) =
      ∏ i, ∏ j ∈ Ioi i, ((x j - x i) * (x j ^ t - x i ^ t)) := by
    rw [mul_mul_mul_comm, sign_revPerm_mul_self, one_mul, ← prod_mul_distrib]
    exact prod_congr rfl fun i _ => (prod_mul_distrib).symm
  rw [e]
  refine prod_nonneg fun i _ => prod_nonneg fun j _ => ?_
  rcases le_total (x i) (x j) with h | h
  · exact mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (rpow_le_rpow (hx i).le h ht))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
      (sub_nonpos.mpr (rpow_le_rpow (hx j).le h ht))

theorem alternant_delta_eq_vand (y : Fin d → ℝ) :
    alternant (delta d) y =
      (Equiv.Perm.sign (revPerm d) : ℝ) * (-1) ^ (rowPairs d).card * vand y := by
  rw [alternant_delta_eq, det_vandermonde, prod_Ioi_eq_vand]
  ring

theorem vand_ne_zero_of_injective {y : Fin d → ℝ} (hy : Function.Injective y) :
    vand y ≠ 0 :=
  prod_ne_zero_iff.mpr fun _ hij => sub_ne_zero.mpr fun h =>
    (ne_of_lt (mem_filter.mp hij).2) (hy h)

theorem alternant_delta_ne_zero {y : Fin d → ℝ} (hy : Function.Injective y) :
    alternant (delta d) y ≠ 0 := by
  rw [alternant_delta_eq_vand]
  have hs : (Equiv.Perm.sign (revPerm d) : ℝ) ≠ 0 := by
    intro h; have := sign_revPerm_mul_self (d := d); rw [h, zero_mul] at this; norm_num at this
  exact mul_ne_zero (mul_ne_zero hs (pow_ne_zero _ (by norm_num))) (vand_ne_zero_of_injective hy)

theorem cast_delta (i : Fin d) : ((delta d i : ℕ) : ℝ) = (d - 1 - i : ℕ) := by
  simp [shiftedPart]

theorem vand_delta :
    vand (fun i => ((delta d i : ℕ) : ℝ)) = ∏ ij ∈ rowPairs d, ((ij.2 : ℝ) - ij.1) := by
  refine prod_congr rfl fun ij _ => ?_
  have h1 := ij.1.2
  have h2 := ij.2.2
  have e : delta d ij.1 + ij.1 = delta d ij.2 + ij.2 := by
    simp only [shiftedPart, Pi.zero_apply, zero_add]
    omega
  have e' := congrArg (Nat.cast : ℕ → ℝ) e
  push_cast at e'
  linarith

/-- The Weyl dimension formula is the quotient `a_δ(l)/a_δ(δ)`. -/
theorem weylFormula_eq_alternant_div (p : Fin d → ℕ) :
    weylFormula p = alternant (delta d) (fun i => (shiftedPart p i : ℝ)) /
      alternant (delta d) (fun i => ((delta d i : ℕ) : ℝ)) := by
  have hinj : Function.Injective (fun i => ((delta d i : ℕ) : ℝ)) := by
    intro i j h
    have h' : delta d i = delta d j := by
      have h'' : ((delta d i : ℕ) : ℝ) = delta d j := h
      exact_mod_cast h''
    simp only [shiftedPart, Pi.zero_apply, zero_add] at h'
    exact Fin.ext (by have := i.2; have := j.2; omega)
  have hne := alternant_delta_ne_zero hinj
  rw [eq_div_iff hne, alternant_delta_eq_vand, alternant_delta_eq_vand, vand_delta,
    weylFormula_eq_vand]
  have hden := (rowPairs_denom_pos (q := d)).ne'
  field_simp

theorem sum_shiftedPart_nat (p : Fin d → ℕ) :
    ∑ i, shiftedPart p i = ∑ i, p i + d.choose 2 := by
  rw [← sum_delta]
  simp only [shiftedPart, Pi.zero_apply, zero_add, sum_add_distrib]

/-- **The normalized gamma integral is the common label function** (`05-replicas.tex`,
lines 347–368): for a partition `λ` with at most `d` rows and `k = |λ|`,
`w_k(λ) = J_{tk}(l) / (J_0(δ) W_λ)`, with `l` the shifted parts and `W_λ` the Weyl dimension
formula. -/
theorem replicaWeight_eq_gammaIntegral (hd : 0 < d) {t : ℝ} (ht : 0 < t) {p : Fin d → ℕ}
    (hp : Antitone p) :
    replicaWeight t p = gammaIntegral d t (shiftedPart p) (t * (∑ i, p i : ℕ)) /
      (gammaIntegral d t (delta d) 0 * weylFormula p) := by
  set N := d.choose 2
  set k := ∑ i, p i
  have hc : (1 : ℝ) ≤ replicaConst d t := one_le_replicaConst hd ht.le
  have hsumL : ∑ i, ((shiftedPart p i : ℕ) : ℝ) = k + N := by
    rw [← Nat.cast_sum, sum_shiftedPart_nat, Nat.cast_add]
  have hsumD : ∑ i, ((delta d i : ℕ) : ℝ) = N := by
    rw [← Nat.cast_sum, sum_delta]
  have hD1 : (d : ℝ) + (N : ℕ) + t * ∑ i, ((shiftedPart p i : ℕ) : ℝ) =
      replicaConst d t + t * k := by
    rw [hsumL, replicaConst]; ring
  have hD0 : (d : ℝ) + (N : ℕ) + t * ∑ i, ((delta d i : ℕ) : ℝ) = replicaConst d t := by
    rw [hsumD, replicaConst]; ring
  have hk : (0 : ℝ) ≤ t * k := by positivity
  rw [gammaIntegral_eq hd ht.le (shiftedPart p) hk (by rw [hD1]; linarith),
    gammaIntegral_eq hd ht.le (delta d) le_rfl (by rw [hD0]; linarith), hD1, hD0,
    weylFormula_eq_alternant_div, replicaWeight]
  rw [show replicaConst d t + t * k - t * k = replicaConst d t by ring, sub_zero,
    div_self (Gamma_pos_of_pos (by linarith)).ne']
  have hinjL : Function.Injective (fun i => ((shiftedPart p i : ℕ) : ℝ)) :=
    fun i j h => shiftedPart_injective hp (by exact_mod_cast h)
  have hinjD : Function.Injective (fun i => ((delta d i : ℕ) : ℝ)) := by
    intro i j h
    have h' : delta d i = delta d j := by
      have h'' : ((delta d i : ℕ) : ℝ) = delta d j := h
      exact_mod_cast h''
    simp only [shiftedPart, Pi.zero_apply, zero_add] at h'
    exact Fin.ext (by have := i.2; have := j.2; omega)
  have hL := alternant_delta_ne_zero hinjL
  have hδ := alternant_delta_ne_zero hinjD
  have hG : ∀ i : Fin d, 0 < Gamma (1 + t * ((delta d i : ℕ) : ℝ)) := fun i =>
    Gamma_pos_of_pos (by positivity)
  have hGp : (0 : ℝ) < ∏ i : Fin d, Gamma (1 + t * ((delta d i : ℕ) : ℝ)) :=
    prod_pos fun i _ => hG i
  have hGc : 0 < Gamma (replicaConst d t + t * k) := Gamma_pos_of_pos (by linarith)
  have ht' : t ^ N ≠ 0 := pow_ne_zero _ ht.ne'
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
  rw [prod_div_distrib]
  simp only [cast_delta]
  field_simp
  have hδ' : (alternant (delta d) fun j => ((d - 1 - j : ℕ) : ℝ)) ≠ 0 := by
    simpa only [cast_delta] using hδ
  rw [mul_div_assoc, div_self hδ', mul_one]

end Partition
