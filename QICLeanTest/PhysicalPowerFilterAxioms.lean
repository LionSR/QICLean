/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PhysicalPowerFilter

/-!
# Axiom check and a two-level example for the physical power estimate

The example proves all hypotheses for one positive contraction with energies
zero and one. The resulting estimate holds at every natural power, including zero.
-/

set_option autoImplicit false
set_option linter.hashCommand false

/-- info:
'Matrix.power_filter_spec_of_posSemidef_terms'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.power_filter_spec_of_posSemidef_terms

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder InnerProductSpace

private def twoLevelH : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun i => if i = 0 then 0 else 1)

private noncomputable def twoLevelΩ : EuclideanSpace ℂ (Fin 2) := EuclideanSpace.single 0 1

private theorem twoLevelH_pos : twoLevelH.PosSemidef := by
  simp only [twoLevelH, posSemidef_diagonal_iff]
  exact fun i => ite_nonneg le_rfl zero_le_one

private theorem twoLevel_complement :
    1 - twoLevelH = vecMulVec (WithLp.ofLp twoLevelΩ) (star (WithLp.ofLp twoLevelΩ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twoLevelH, twoLevelΩ, vecMulVec]

private theorem twoLevelH_upper : twoLevelH ≤ 1 :=
  sub_nonneg.mp (nonneg_iff_posSemidef.mpr
    (twoLevel_complement.symm ▸ posSemidef_vecMulVec_self_star (WithLp.ofLp twoLevelΩ)))

private theorem twoLevelΩ_unit : ‖twoLevelΩ‖ = 1 := by
  simp [twoLevelΩ]

private theorem twoLevel_ground :
    twoLevelH *ᵥ WithLp.ofLp twoLevelΩ = (0 : ℂ) • WithLp.ofLp twoLevelΩ := by
  simp [twoLevelH, twoLevelΩ]

private theorem twoLevel_gap :
    (twoLevelH - (0 : ℂ) • 1 - (1 : ℂ) •
      (1 - vecMulVec (WithLp.ofLp twoLevelΩ) (star (WithLp.ofLp twoLevelΩ)))).PosSemidef := by
  simpa only [zero_smul, sub_zero, one_smul, ← twoLevel_complement,
    sub_sub_cancel, sub_self] using
    (PosSemidef.zero : (0 : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef)

private theorem twoLevel_attain : (1 : ℝ) ∈ spectrum ℝ twoLevelH :=
  spectrum.of_algebraMap_mem ℂ (by
    simpa only [twoLevelH, spectrum_diagonal, map_one] using
      (show (1 : ℂ) ∈ Set.range (fun i : Fin 2 => if i = 0 then (0 : ℂ) else 1) from
        ⟨1, by norm_num⟩))

-- One actual positive contraction has an attained excited energy; N=2 and rate=1/2.
-- This includes exponent zero and gives a nonvacuous family satisfying all hypotheses.
example (m : ℕ) :
    ‖(1 - (1 / 2 : ℝ) • twoLevelH) ^ m -
      vecMulVec (WithLp.ofLp twoLevelΩ) (star (WithLp.ofLp twoLevelΩ))‖ ≤ (1 / 2 : ℝ) ^ m := by
  have hs := Matrix.power_filter_spec_of_posSemidef_terms
    (fun _ : Unit => twoLevelH) (fun _ => twoLevelH_pos) (fun _ => twoLevelH_upper)
    (E0 := 0) (Δ := 1) (Ω := twoLevelΩ) twoLevelΩ_unit
    (by simpa using twoLevel_ground) (by simpa using twoLevel_gap)
    zero_lt_one (by simpa using twoLevel_attain) m
  convert hs.2.2.2.1 using 1 <;> norm_num
