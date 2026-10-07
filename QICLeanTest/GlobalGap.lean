/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GlobalGap

/-! Regressions for the global-gap equivalence with a negative ground energy. -/

open Complex Matrix
open scoped InnerProductSpace ComplexOrder

namespace GlobalGapTest

/-- A two-level Hamiltonian with ground energy `-7` and gap `2` above the vector `Ω`. -/
private noncomputable def H (Ω : EuclideanSpace ℂ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((-7 : ℝ) : ℂ) • 1 + ((2 : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))

private theorem posSemidef_gap (Ω : EuclideanSpace ℂ (Fin 2)) :
    (H Ω - ((-7 : ℝ) : ℂ) • 1 -
      ((2 : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef := by
  rw [H, add_sub_cancel_left, sub_self]
  exact PosSemidef.zero

-- The quadratic-form gap holds at every vector, with no orthogonality to `Ω`.
example (Ω ψ : EuclideanSpace ℂ (Fin 2)) :
    2 * (‖ψ‖ ^ 2 - ‖⟪Ω, ψ⟫_ℂ‖ ^ 2) ≤ (⟪ψ, toEuclideanLin (H Ω) ψ⟫_ℂ).re - (-7) * ‖ψ‖ ^ 2 :=
  (posSemidef_gap Ω).gap_le ψ

-- The energy-to-phase-error bound with the negative ground energy.
example (Ω ψ : EuclideanSpace ℂ (Fin 2)) (hΩ : ‖Ω‖ = 1) (hψ : ‖ψ‖ = 1) :
    ⨅ θ : ℝ, ‖ψ - exp (θ * I) • Ω‖ ^ 2 ≤ 2 * ((⟪ψ, toEuclideanLin (H Ω) ψ⟫_ℂ).re - (-7)) / 2 :=
  iInf_sq_norm_sub_exp_smul_le_of_posSemidef_gap (posSemidef_gap Ω) two_pos hΩ hψ

end GlobalGapTest
