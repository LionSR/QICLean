/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityPowers
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Recovering commutation from a regularized filter

A nonzero real power of a positive definite matrix has the same commutant as
the original matrix. In particular, commutation with a shifted inverse-power
filter implies commutation with its defining positive semidefinite matrix.

Source: OpenAI, polynomial PEPS manuscript, September 24, 2026,
`03-patches.tex`, lines 160–168, `eq:patch-stationarity-commutation`,
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is a spectral implication; stationarity of the ordered patch objective
and commutation of its filter with the output marginal remain separate steps.
The proof implementation is retained from QICLean pull request 607. Its original
proofs were independently written from the manuscript and Mathlib; no upstream
OpenAI Lean proof text was reused.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonzero real power of a positive definite matrix has the same commutant.
Source: OpenAI `03-patches.tex`, lines 160–168, the functional-calculus step of
`eq:patch-stationarity-commutation`. -/
theorem PosDef.commute_rpow_iff {A ρ : Matrix n n ℂ} (hA : A.PosDef)
    {r : ℝ} (hr : r ≠ 0) : Commute (A ^ r) ρ ↔ Commute A ρ := by
  constructor
  · intro hc
    have hinv := hc.cfc_real (fun t : ℝ ↦ t ^ r⁻¹)
    rw [← CFC.rpow_eq_cfc_real CFC.rpow_nonneg,
      CFC.rpow_rpow_inv A r hr hA.isStrictlyPositive] at hinv
    exact hinv
  · intro hc
    simpa only [CFC.rpow_eq_cfc_real hA.posSemidef.nonneg] using
      hc.cfc_real (fun t : ℝ ↦ t ^ r)

/-- A nonzero real power of a positively shifted matrix has the same commutant
as the unshifted positive semidefinite matrix. Source: OpenAI
`03-patches.tex`, lines 160–168, `eq:patch-stationarity-commutation`. -/
theorem PosSemidef.commute_add_smul_one_rpow_iff {x ρ : Matrix n n ℂ}
    (hx : x.PosSemidef) {b r : ℝ} (hb : 0 < b) (hr : r ≠ 0) :
    Commute ((x + b • (1 : Matrix n n ℂ)) ^ r) ρ ↔ Commute x ρ := by
  rw [(hx.add_smul_one_posDef hb).commute_rpow_iff hr]
  simp [commute_iff_eq, add_mul, mul_add]

/-- Commutation of a marginal with its regularized inverse-power filter implies
commutation with the defining matrix. The second matrix need not be Hermitian,
positive, or normalized. Source: OpenAI `03-patches.tex`, lines 160–168,
`eq:patch-stationarity-commutation`. -/
theorem PosSemidef.commute_of_commute_shifted_inverse_power {x ρ : Matrix n n ℂ}
    (hx : x.PosSemidef) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hcomm : Commute ρ ((x + b • (1 : Matrix n n ℂ)) ^ (-a / 2))) :
    Commute ρ x := by
  exact ((hx.commute_add_smul_one_rpow_iff hb
    (div_ne_zero (neg_ne_zero.mpr ha.ne') (by norm_num))).mp hcomm.symm).symm

end Matrix
