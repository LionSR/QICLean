/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.LorentzNormalForm.SpinorCover
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Exponential formulas for the Lorentz spinor cover

This module formalizes Wolf's rotation and boost exponentials from Equation
(2.44), `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 1037–1081.
For a unit spatial axis `n`, it proves the closed forms for
`exp(t n·σ)`, `exp(-i t n·σ)`, `exp(t n·B)`, and `exp(t n·R)`, identifies the
boost exponential with the canonical Lorentz boost, and verifies both formulas
under the concrete spinor map.

The rotation formula follows the actual congruence action: Wolf's displayed
spinor `exp(-i t n·σ/2)` maps to `exp(+t n·R)`.  The printed negative sign is
recorded in `docs/paper-gaps/wolf_ch2_spinor_rotation_sign.tex`.

## Main results

* `Wolf.exp_smul_pauliVector` — closed boost-spinor exponential.
* `Wolf.exp_smul_boostGenerator` — hyperbolic Rodrigues formula.
* `Wolf.lorentzBoost_rapidityMinkowski_eq_exp` — Lorentz boost exponential.
* `Wolf.exp_neg_I_smul_pauliVector` — closed rotation-spinor exponential.
* `Wolf.exp_smul_rotationGenerator` — Rodrigues rotation formula.
* `Wolf.spinorMatrix_boostExpSL2` — boost identity under the spinor map.
* `Wolf.spinorMatrix_rotationExpSL2` — corrected-sign rotation identity.
-/

open scoped Matrix MatrixGroups BigOperators ComplexOrder Nat
open Matrix Finset

noncomputable section

namespace Wolf

/-! ### The even/odd split of the exponential series -/

set_option maxHeartbeats 800000 in
-- Elaborating this generic exponential-series rearrangement exceeds the project default.
/-- The even/odd split of the exponential series: if the even subseries of the
exponential series of `a` sums to `E` and the odd subseries to `O`, then
`exp a = E + O`. -/
theorem exp_eq_add_of_even_odd {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (a E O : 𝔸)
    (hE : HasSum (fun n ↦ NormedSpace.expSeries ℝ 𝔸 (2 * n) (fun _ ↦ a)) E)
    (hO : HasSum (fun n ↦ NormedSpace.expSeries ℝ 𝔸 (2 * n + 1) (fun _ ↦ a)) O) :
    NormedSpace.exp a = E + O := by
  have hsum : HasSum (fun n ↦ NormedSpace.expSeries ℝ 𝔸 n (fun _ ↦ a)) (E + O) :=
    hE.even_add_odd hO
  rw [congrFun (NormedSpace.exp_eq_tsum ℝ) a]
  simpa only [NormedSpace.expSeries_apply_eq] using hsum.tsum_eq

/-! ### Scalar series tails -/

/-- The even tail of the cosh series. -/
theorem hasSum_cosh_sub_one (x : ℝ) :
    HasSum (fun n ↦ x ^ (2 * (n + 1)) / (2 * (n + 1))!) (Real.cosh x - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_cosh x)
  rw [Finset.sum_range_one] at h
  simpa using h

/-- The even tail of the cos series, as `1 - cos x`. -/
theorem hasSum_one_sub_cos (x : ℝ) :
    HasSum (fun n ↦ (-1) ^ n * x ^ (2 * (n + 1)) / (2 * (n + 1))!) (1 - Real.cos x) := by
  have h := (hasSum_nat_add_iff' 1).mpr (Real.hasSum_cos x)
  rw [Finset.sum_range_one] at h
  norm_num [pow_zero] at h
  have hneg := h.neg
  have hfun : (fun n ↦ (-1) ^ n * x ^ (2 * (n + 1)) / (2 * (n + 1))!) =
      fun n ↦ -((-1) ^ (n + 1) * x ^ (2 * (n + 1)) / (2 * (n + 1))!) := by
    funext n
    rw [pow_succ (-1 : ℝ) n]
    ring
  rw [hfun]
  simpa only [neg_sub] using hneg


/-! ### Wolf's boost and rotation generators -/

/-- The Pauli contraction `n·σ` for a real spatial vector `n`. -/
def pauliVector (n : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ k : Fin 3, (n k : ℂ) • SpinCover.pauli k

/-- The Lorentz boost generator `n·B` from Wolf, Equation (2.44). -/
def boostGenerator (n : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ if hi : i = 0 then (if _hj : j = 0 then 0 else n (Fin.pred j _hj))
    else if _hj : j = 0 then n (Fin.pred i hi) else 0

@[simp] theorem boostGenerator_zero_zero (n : Fin 3 → ℝ) : boostGenerator n 0 0 = 0 := by
  simp [boostGenerator]

@[simp] theorem boostGenerator_zero_succ (n : Fin 3 → ℝ) (j : Fin 3) :
    boostGenerator n 0 j.succ = n j := by
  simp [boostGenerator]

@[simp] theorem boostGenerator_succ_zero (n : Fin 3 → ℝ) (i : Fin 3) :
    boostGenerator n i.succ 0 = n i := by
  simp [boostGenerator]

@[simp] theorem boostGenerator_succ_succ (n : Fin 3 → ℝ) (i j : Fin 3) :
    boostGenerator n i.succ j.succ = 0 := by
  simp [boostGenerator]

/-- The spatial generator `n·R` with Wolf's convention
`Rᵢ = ∑ⱼₖ εᵢⱼₖ |k⟩⟨j|`.  Thus the third generator sends the first spatial
coordinate toward the positive second coordinate. -/
def rotationGenerator3 (n : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -n 2, n 1; n 2, 0, -n 0; -n 1, n 0, 0]

/-- The four-dimensional rotation generator, trivial on the time axis. -/
def rotationGenerator (n : Fin 3 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j ↦ if h0 : i = 0 then 0 else if h1 : j = 0 then 0
    else rotationGenerator3 n (Fin.pred i h0) (Fin.pred j h1)

@[simp] theorem rotationGenerator_zero_apply (n : Fin 3 → ℝ) (j : Fin 4) :
    rotationGenerator n 0 j = 0 := by simp [rotationGenerator]

@[simp] theorem rotationGenerator_apply_zero (n : Fin 3 → ℝ) (i : Fin 4) :
    rotationGenerator n i 0 = 0 := by simp [rotationGenerator]

@[simp] theorem rotationGenerator_succ_succ (n : Fin 3 → ℝ) (i j : Fin 3) :
    rotationGenerator n i.succ j.succ = rotationGenerator3 n i j := by
  simp [rotationGenerator]

/-- A unit spatial Pauli contraction squares to the identity. -/
theorem pauliVector_sq (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) :
    pauliVector n ^ 2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVector, SpinCover.pauli, pow_two, Matrix.mul_apply, Fin.sum_univ_two,
      Fin.sum_univ_three] at hn ⊢ <;>
    ring_nf at hn ⊢ <;> try simp_all [Complex.I_sq]
  all_goals norm_cast <;> try nlinarith [hn]

/-- A unit boost generator satisfies `(n·B)³ = n·B`. -/
theorem boostGenerator_cube (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) :
    boostGenerator n ^ 3 = boostGenerator n := by
  have h0 := congrArg (fun x : ℝ ↦ n 0 * x) hn
  have h1 := congrArg (fun x : ℝ ↦ n 1 * x) hn
  have h2 := congrArg (fun x : ℝ ↦ n 2 * x) hn
  simp only [Fin.sum_univ_three, mul_one] at h0 h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three,
      boostGenerator] at hn ⊢ <;>
    ring_nf at hn ⊢ <;> try rfl
  all_goals linarith [h0, h1, h2]

/-- A unit rotation generator satisfies `(n·R)³ = -(n·R)`. -/
theorem rotationGenerator_cube (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) :
    rotationGenerator n ^ 3 = -rotationGenerator n := by
  have h0 := congrArg (fun x : ℝ ↦ n 0 * x) hn
  have h1 := congrArg (fun x : ℝ ↦ n 1 * x) hn
  have h2 := congrArg (fun x : ℝ ↦ n 2 * x) hn
  simp only [Fin.sum_univ_three, mul_one] at h0 h1 h2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four, rotationGenerator,
      rotationGenerator3, Fin.sum_univ_three] at hn ⊢ <;>
    ring_nf at hn ⊢ <;> try rfl
  all_goals linarith [h0, h1, h2]


/-! ### Closed forms for exponentials of quadratic and cubic generators -/

/-- Exponential closed form for a scalar multiple of an element whose square is
`ε • 1`. -/
theorem exp_smul_eq_of_sq_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (q : 𝔸) (ε t c s : ℝ) (hq : q ^ 2 = ε • 1)
    (hc : HasSum (fun n ↦ ε ^ n * t ^ (2 * n) / (2 * n)!) c)
    (hs : HasSum (fun n ↦ ε ^ n * t ^ (2 * n + 1) / (2 * n + 1)!) s) :
    NormedSpace.exp (t • q) = c • 1 + s • q := by
  have hEven : ∀ n : ℕ, q ^ (2 * n) = ε ^ n • (1 : 𝔸) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add, ih, hq,
          smul_mul_assoc, one_mul, smul_smul, pow_succ]
  have hOdd : ∀ n : ℕ, q ^ (2 * n + 1) = ε ^ n • q := by
    intro n
    rw [pow_succ, hEven n, smul_one_mul]
  have heqE : (fun n ↦ NormedSpace.expSeries ℝ 𝔸 (2 * n) (fun _ ↦ t • q)) =
      fun n ↦ (ε ^ n * t ^ (2 * n) / (2 * n)!) • (1 : 𝔸) := by
    funext n
    rw [NormedSpace.expSeries_apply_eq, smul_pow, hEven, smul_smul, smul_smul]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have heqO : (fun n ↦ NormedSpace.expSeries ℝ 𝔸 (2 * n + 1) (fun _ ↦ t • q)) =
      fun n ↦ (ε ^ n * t ^ (2 * n + 1) / (2 * n + 1)!) • q := by
    funext n
    rw [NormedSpace.expSeries_apply_eq, smul_pow, hOdd, smul_smul, smul_smul]
    congr 1
    rw [div_eq_mul_inv]
    ring
  exact exp_eq_add_of_even_odd (t • q) (c • 1) (s • q)
    (heqE ▸ hc.smul_const (1 : 𝔸)) (heqO ▸ hs.smul_const q)

/-- Exponential closed form for a scalar multiple of an element satisfying
`q³ = ε • q`. -/
theorem exp_smul_eq_of_cubic_smul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] (q : 𝔸) (ε t c₂ s : ℝ) (hq : q ^ 3 = ε • q)
    (hc : HasSum (fun n ↦ ε ^ n * t ^ (2 * (n + 1)) / (2 * (n + 1))!) c₂)
    (hs : HasSum (fun n ↦ ε ^ n * t ^ (2 * n + 1) / (2 * n + 1)!) s) :
    NormedSpace.exp (t • q) = 1 + c₂ • q ^ 2 + s • q := by
  have hq4 : q ^ 4 = ε • q ^ 2 := by
    rw [pow_succ, hq, smul_mul_assoc, pow_two]
  have hEven : ∀ n : ℕ, q ^ (2 * (n + 1)) = ε ^ n • q ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 2 by omega, pow_add, ih,
          smul_mul_assoc, show q ^ 2 * q ^ 2 = q ^ 4 by rw [← pow_add], hq4,
          smul_smul]
        congr 1
  have hOdd : ∀ n : ℕ, q ^ (2 * n + 1) = ε ^ n • q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, pow_add, ih,
          smul_mul_assoc, ← pow_succ', hq, smul_smul, pow_succ]
  have heqE : (fun n ↦ NormedSpace.expSeries ℝ 𝔸 (2 * (n + 1)) (fun _ ↦ t • q)) =
      fun n ↦ (ε ^ n * t ^ (2 * (n + 1)) / (2 * (n + 1))!) • q ^ 2 := by
    funext n
    rw [NormedSpace.expSeries_apply_eq, smul_pow, hEven, smul_smul, smul_smul]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have heqO : (fun n ↦ NormedSpace.expSeries ℝ 𝔸 (2 * n + 1) (fun _ ↦ t • q)) =
      fun n ↦ (ε ^ n * t ^ (2 * n + 1) / (2 * n + 1)!) • q := by
    funext n
    rw [NormedSpace.expSeries_apply_eq, smul_pow, hOdd, smul_smul, smul_smul]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have htail : HasSum
      (fun n ↦ NormedSpace.expSeries ℝ 𝔸 (2 * (n + 1)) (fun _ ↦ t • q))
      (c₂ • q ^ 2) := heqE ▸ hc.smul_const (q ^ 2)
  have hzero : NormedSpace.expSeries ℝ 𝔸 0 (fun _ ↦ t • q) = 1 := by
    simp [NormedSpace.expSeries_apply_eq]
  have hE : HasSum (fun n ↦ NormedSpace.expSeries ℝ 𝔸 (2 * n) (fun _ ↦ t • q))
      (1 + c₂ • q ^ 2) := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa only [Finset.sum_range_one, hzero, add_sub_cancel_left] using htail
  exact exp_eq_add_of_even_odd (t • q) (1 + c₂ • q ^ 2) (s • q) hE
    (heqO ▸ hs.smul_const q)

/-- The boost spinor exponential `exp(t n·σ)`. -/
theorem exp_smul_pauliVector (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    NormedSpace.exp (t • pauliVector n) =
      Real.cosh t • 1 + Real.sinh t • pauliVector n := by
  let _ : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  apply exp_smul_eq_of_sq_smul (pauliVector n) 1 t
  · simpa using pauliVector_sq n hn
  · simpa using Real.hasSum_cosh t
  · simpa using Real.hasSum_sinh t

/-- Rodrigues' hyperbolic formula for the Lorentz boost exponential. -/
theorem exp_smul_boostGenerator (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    NormedSpace.exp (t • boostGenerator n) =
      1 + (Real.cosh t - 1) • boostGenerator n ^ 2 +
        Real.sinh t • boostGenerator n := by
  let _ : NormedRing (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.linftyOpNormedAlgebra
  apply exp_smul_eq_of_cubic_smul (boostGenerator n) 1 t
  · simpa using boostGenerator_cube n hn
  · simpa using hasSum_cosh_sub_one t
  · simpa using Real.hasSum_sinh t

/-- The corrected-sign rotation spinor exponential
`exp(-i t n·σ) = cos(t)I - i sin(t)n·σ`. -/
theorem exp_neg_I_smul_pauliVector (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    NormedSpace.exp (t • ((-Complex.I) • pauliVector n)) =
      Real.cos t • 1 + Real.sin t • ((-Complex.I) • pauliVector n) := by
  let _ : NormedRing (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin 2) (Fin 2) ℂ) := Matrix.linftyOpNormedAlgebra
  apply exp_smul_eq_of_sq_smul ((-Complex.I) • pauliVector n) (-1) t
  · rw [smul_pow, pauliVector_sq n hn]
    norm_num [Complex.I_sq]
  · simpa [mul_assoc] using Real.hasSum_cos t
  · simpa [mul_assoc] using Real.hasSum_sin t

/-- Rodrigues' formula for the Lorentz rotation exponential.  With Wolf's
printed generators this has the positive sign matching the congruence action. -/
theorem exp_smul_rotationGenerator (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    NormedSpace.exp (t • rotationGenerator n) =
      1 + (1 - Real.cos t) • rotationGenerator n ^ 2 +
        Real.sin t • rotationGenerator n := by
  let _ : NormedRing (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin 4) (Fin 4) ℝ) := Matrix.linftyOpNormedAlgebra
  apply exp_smul_eq_of_cubic_smul (rotationGenerator n) (-1) t
  · simpa using rotationGenerator_cube n hn
  · simpa [mul_assoc] using hasSum_one_sub_cos t
  · simpa [mul_assoc] using Real.hasSum_sin t



/-! ### Rapidity coordinates for the canonical boost -/

/-- The future unit-hyperboloid point
`(cosh t, sinh t n₁, sinh t n₂, sinh t n₃)` for a spatial axis `n`. -/
def rapidityMinkowski (n : Fin 3 → ℝ) (t : ℝ) : MinkowskiSpace :=
  Fin.cons (Real.cosh t) fun k ↦ Real.sinh t * n k

@[simp] theorem rapidityMinkowski_zero (n : Fin 3 → ℝ) (t : ℝ) :
    rapidityMinkowski n t 0 = Real.cosh t := by
  simp [rapidityMinkowski]

@[simp] theorem rapidityMinkowski_succ (n : Fin 3 → ℝ) (t : ℝ) (k : Fin 3) :
    rapidityMinkowski n t k.succ = Real.sinh t * n k := by
  simp [rapidityMinkowski]

/-- Rapidity coordinates lie on the unit hyperboloid. -/
theorem minkowskiQuadratic_rapidityMinkowski (n : Fin 3 → ℝ)
    (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    minkowskiQuadratic (rapidityMinkowski n t) = 1 := by
  rw [minkowskiQuadratic_eq_sub_sum]
  simp only [rapidityMinkowski_zero, rapidityMinkowski_succ, mul_pow,
    ← Finset.mul_sum]
  rw [hn, mul_one]
  exact Real.cosh_sq_sub_sinh_sq t

/-- The Lorentz exponential `exp(t n·B)` is the canonical boost with rapidity
`t` and unit spatial axis `n`. -/
theorem lorentzBoost_rapidityMinkowski_eq_exp (n : Fin 3 → ℝ)
    (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    lorentzBoost (rapidityMinkowski n t) = NormedSpace.exp (t • boostGenerator n) := by
  rw [exp_smul_boostGenerator n hn]
  have hpos : 0 < 1 + Real.cosh t := by
    nlinarith [Real.cosh_pos t]
  have hquot : Real.sinh t ^ 2 / (1 + Real.cosh t) = Real.cosh t - 1 := by
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hquot' : Real.sinh t ^ 2 * (1 + Real.cosh t)⁻¹ = Real.cosh t - 1 := by
    simpa [div_eq_mul_inv] using hquot
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hn
  ext i j
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero =>
          simp [lorentzBoost, rapidityMinkowski, boostGenerator, pow_two,
            Matrix.mul_apply, Fin.sum_univ_succ]
          nlinarith [hn']
      | succ j =>
          simpa [lorentzBoost, rapidityMinkowski, boostGenerator, pow_two,
            Matrix.mul_apply, Matrix.one_apply] using (Fin.succ_ne_zero j).symm
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          simp [lorentzBoost, rapidityMinkowski, boostGenerator, pow_two,
            Matrix.mul_apply, Fin.sum_univ_succ]
      | succ j =>
          simp [lorentzBoost, rapidityMinkowski, boostGenerator, pow_two,
            Matrix.mul_apply, Matrix.one_apply]
          simp only [← hquot']
          ring

/-! ### Exponential spinors and the spinor-map identities -/

/-- The closed boost exponential `exp(t n·σ/2)`. -/
def boostExpMatrix (n : Fin 3 → ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cosh (t / 2) + Real.sinh (t / 2) * n 2 : ℝ),
      (Real.sinh (t / 2) * n 0 : ℝ) - Complex.I * (Real.sinh (t / 2) * n 1 : ℝ);
    (Real.sinh (t / 2) * n 0 : ℝ) + Complex.I * (Real.sinh (t / 2) * n 1 : ℝ),
      (Real.cosh (t / 2) - Real.sinh (t / 2) * n 2 : ℝ)]

/-- The closed rotation exponential `exp(-i t n·σ/2)`. -/
def rotationExpMatrix (n : Fin 3 → ℝ) (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (t / 2) : ℂ) - Complex.I * (Real.sin (t / 2) * n 2 : ℝ),
      (-Real.sin (t / 2) * n 1 : ℝ) - Complex.I * (Real.sin (t / 2) * n 0 : ℝ);
    (Real.sin (t / 2) * n 1 : ℝ) - Complex.I * (Real.sin (t / 2) * n 0 : ℝ),
      (Real.cos (t / 2) : ℂ) + Complex.I * (Real.sin (t / 2) * n 2 : ℝ)]

/-- The boost exponential has determinant one for a unit axis. -/
theorem boostExpMatrix_det (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    (boostExpMatrix n t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [boostExpMatrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  have h := Real.cosh_sq_sub_sinh_sq (t / 2)
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hn
  have hsn := congrArg (fun x : ℝ ↦ Real.sinh (t / 2) ^ 2 * x) hn'
  simp only [mul_one] at hsn
  apply Complex.ext <;> simp [-Complex.ofReal_cosh, -Complex.ofReal_sinh]
  · ring_nf at hn hsn h ⊢
    linear_combination h - hsn
  · ring

/-- The rotation exponential has determinant one for a unit axis. -/
theorem rotationExpMatrix_det (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    (rotationExpMatrix n t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [rotationExpMatrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply]
  have h := Real.cos_sq_add_sin_sq (t / 2)
  have hn' : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hn
  have hsn := congrArg (fun x : ℝ ↦ Real.sin (t / 2) ^ 2 * x) hn'
  simp only [mul_one] at hsn
  apply Complex.ext <;> simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
  · ring_nf at hn hsn h ⊢
    linear_combination h + hsn
  · ring

/-- `exp(t n·σ/2)` as an element of `SL(2,ℂ)`. -/
def boostExpSL2 (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) : SL(2, ℂ) :=
  ⟨boostExpMatrix n t, boostExpMatrix_det n hn t⟩

/-- `exp(-i t n·σ/2)` as an element of `SL(2,ℂ)`. -/
def rotationExpSL2 (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) : SL(2, ℂ) :=
  ⟨rotationExpMatrix n t, rotationExpMatrix_det n hn t⟩

/-- The closed boost spinor is the matrix exponential `exp(t n·σ/2)`. -/
theorem boostExpSL2_coe_eq_exp (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    (boostExpSL2 n hn t).1 = NormedSpace.exp ((t / 2) • pauliVector n) := by
  rw [exp_smul_pauliVector n hn]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostExpSL2, boostExpMatrix, pauliVector, SpinCover.pauli, Fin.sum_univ_three] <;>
    ring

/-- The closed rotation spinor is the matrix exponential `exp(-i t n·σ/2)`. -/
theorem rotationExpSL2_coe_eq_exp (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    (rotationExpSL2 n hn t).1 =
      NormedSpace.exp ((t / 2) • ((-Complex.I) • pauliVector n)) := by
  rw [exp_neg_I_smul_pauliVector n hn]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    apply Complex.ext <;>
      simp [rotationExpSL2, rotationExpMatrix, pauliVector, SpinCover.pauli,
        Fin.sum_univ_three, Complex.mul_re, Complex.mul_im] <;>
      ring

/-- Wolf's boost identity in Equation (2.44): the spinor map sends
`exp(t n·σ/2)` to `exp(t n·B)`. -/
theorem spinorMatrix_boostExpSL2 (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    spinorMatrix (boostExpSL2 n hn t) = NormedSpace.exp (t • boostGenerator n) := by
  rw [exp_smul_boostGenerator n hn]
  have hc : Real.cosh t = Real.cosh (t / 2) ^ 2 + Real.sinh (t / 2) ^ 2 := by
    convert Real.cosh_two_mul (t / 2) using 1; ring
  have hs : Real.sinh t = 2 * Real.sinh (t / 2) * Real.cosh (t / 2) := by
    convert Real.sinh_two_mul (t / 2) using 1; ring
  have hu : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hn
  have hh := Real.cosh_sq_sub_sinh_sq (t / 2)
  have hk : Real.cosh t = 1 + 2 * Real.sinh (t / 2) ^ 2 := by
    nlinarith [hc, hh]
  have hus := congrArg (fun x : ℝ ↦ Real.sinh (t / 2) ^ 2 * x) hu
  simp only [mul_one] at hus
  ext i j
  rw [spinorMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [boostExpSL2, boostExpMatrix, pauliMatrices,
      Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Fin.sum_univ_four, boostGenerator, pow_two,
      -Complex.ofReal_cosh, -Complex.ofReal_sinh] <;>
    simp only [hk, hs]
  all_goals ring_nf at hu hh hus ⊢ <;> linarith [hh, hus]

/-- Corrected-sign rotation identity for Wolf, Equation (2.44): with the
printed generators `Rᵢ`, the congruence action sends `exp(-i t n·σ/2)` to
`exp(+t n·R)`, not to the printed negative exponential.

**Local fix (Wolf Eq. (2.44), ch02 lines 1070–1077):** the printed minus sign
on the Lorentz exponential conflicts with the Pauli and column-vector
conventions.  See `docs/paper-gaps/wolf_ch2_spinor_rotation_sign.tex`. -/
theorem spinorMatrix_rotationExpSL2 (n : Fin 3 → ℝ) (hn : ∑ k, n k ^ 2 = 1) (t : ℝ) :
    spinorMatrix (rotationExpSL2 n hn t) =
      NormedSpace.exp (t • rotationGenerator n) := by
  rw [exp_smul_rotationGenerator n hn]
  have hc : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (t / 2) using 1; ring
  have hs : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    convert Real.sin_two_mul (t / 2) using 1; ring
  have hu : n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 := by
    simpa [Fin.sum_univ_three] using hn
  have hh := Real.cos_sq_add_sin_sq (t / 2)
  have hk : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    nlinarith [hc, hh]
  have hus := congrArg (fun x : ℝ ↦ Real.sin (t / 2) ^ 2 * x) hu
  simp only [mul_one] at hus
  ext i j
  rw [spinorMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [rotationExpSL2, rotationExpMatrix, pauliMatrices,
      Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Fin.sum_univ_four, rotationGenerator,
      rotationGenerator3, pow_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    try simp only [hk, hs]
  all_goals ring_nf at hu hh hus ⊢ <;> linarith [hh, hus]

end Wolf
end
