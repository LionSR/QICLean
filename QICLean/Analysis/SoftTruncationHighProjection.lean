/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CfcScalarShift
import QICLean.Analysis.SoftTruncationHardResidual

/-!
# A high-energy floor for the actual soft truncation

Monotonicity and the polynomial remainder give a quantitative lower bound above a chosen
energy threshold. The resulting same-matrix projection order is an input to a reverse
low-energy estimate; no reverse residual or spectral gap is assumed or asserted here.
This auxiliary supports ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255.
The independent soft scale and order remain explicit.
-/

namespace Real

/-- Above a nonnegative threshold, the soft function is bounded below by that threshold
minus its actual polynomial remainder bound. Auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx`, lines 1195–1255. -/
theorem softTruncation_high_energy_floor
    (t : ℝ) (m : ℕ) (T x : ℝ) (ht : 0 < t) (hm : 1 ≤ m)
    (hT : 0 ≤ T) (hTx : T ≤ x) :
    T - (t / (m : ℝ)) * (T / t) ^ m ≤ softTruncation t m x := by
  have hband := (softTruncation_bounds t m T ht hm hT).2.2.1
  have hmono := monotoneOn_softTruncation t m ht hT (hT.trans hTx) hTx
  linarith only [hband, hmono]

/-- At scale at least twice the low-energy width plus sixteen, every order at least two
leaves a positive reverse Sylvester denominator. The energy and bond-count bounds are
explicit inputs to this scalar auxiliary; a physical application must derive them.
ALVV, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem softTruncation_reverse_barrier_margin
    (t : ℝ) (m : ℕ) (eta E : ℝ) (c : ℕ)
    (hm : 2 ≤ m) (heta : 0 ≤ eta) (hE : E ≤ 2) (hc : c ≤ 2)
    (hscale : 2 * (eta + 8) ≤ t) :
    let U := 2 * (eta + 8)
    let b := U - (t / (m : ℝ)) * (U / t) ^ m
    0 ≤ U ∧ eta + 8 ≤ b ∧
      (∀ x, U ≤ x → b ≤ softTruncation t m x) ∧
      2 ≤ b - (E + eta) - 2 * (c : ℝ) := by
  intro U b
  have hU : 0 ≤ U := by dsimp only [U]; linarith only [heta]
  have ht : 0 < t := by linarith only [hscale, heta]
  have hUt : U ≤ t := hscale
  have hm' : 1 ≤ m := by omega
  have hmcast : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hb0 : 0 ≤ U / t := div_nonneg hU ht.le
  have hb1 : U / t ≤ 1 := (div_le_one ht).mpr hUt
  have hp : (U / t) ^ m ≤ U / t := by
    simpa only [pow_one] using pow_le_pow_of_le_one hb0 hb1 hm'
  have herror : (t / (m : ℝ)) * (U / t) ^ m ≤ U / 2 := by
    calc
      _ ≤ (t / (m : ℝ)) * (U / t) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = U / (m : ℝ) := by field_simp
      _ ≤ U / 2 := div_le_div_of_nonneg_left hU (by norm_num) hmcast
  have hfloor : eta + 8 ≤ b := by dsimp only [b, U] at *; linarith only [herror]
  have hc' : (c : ℝ) ≤ 2 := by exact_mod_cast hc
  refine ⟨hU, hfloor,
    fun x hx ↦ softTruncation_high_energy_floor t m U x ht hm' hU hx, ?_⟩
  linarith only [hfloor, hE, hc']

end Real

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

/-- The actual soft function of an energy-centered Hermitian matrix dominates the original
high-energy projection with the derived floor. The lower regional energy is explicit;
no commutativity or high-projection inequality is supplied. Auxiliary to ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem IsHermitian.smul_spectralProjectionGE_le_softTruncation
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (e t T : ℝ) (m : ℕ)
    (he : (e : ℂ) • (1 : Matrix ι ι ℂ) ≤ A)
    (ht : 0 < t) (hm : 1 ≤ m) (hT : 0 ≤ T) :
    (T - (t / (m : ℝ)) * (T / t) ^ m) • spectralProjectionGE A (e + T) ≤
      cfc (Real.softTruncation t m) (A - (e : ℂ) • 1) := by
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ A) :=
    A.finite_real_spectrum.continuousOn f
  have hspec : ∀ x ∈ spectrum ℝ A, e ≤ x :=
    (algebraMap_le_iff_le_spectrum hA.isSelfAdjoint).mp (by
      simpa only [Algebra.algebraMap_eq_smul_one, Complex.coe_smul] using he)
  rw [hA.cfc_sub_smul_one (Real.softTruncation t m) e]
  change (T - (t / (m : ℝ)) * (T / t) ^ m) •
    cfc (fun x : ℝ ↦ if e + T ≤ x then 1 else 0) A ≤ _
  rw [← cfc_smul _ _ A (hc _)]
  refine cfc_mono (fun x hx ↦ ?_) (hc _) (hc _)
  by_cases hhigh : e + T ≤ x
  · simp only [hhigh, ite_true, smul_eq_mul, mul_one]
    exact Real.softTruncation_high_energy_floor t m T (x - e) ht hm hT (by linarith)
  · simp only [hhigh, ite_false, smul_zero]
    exact (Real.softTruncation_bounds t m (x - e) ht hm
      (sub_nonneg.mpr (hspec x hx))).1

end Matrix
