/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PolarUnitaryCorrection

/-!
# Polar correction with an arbitrary spectator

A fixed unitary polar factor on a local Hilbert space retains both vectorwise
correction estimates after tensoring with an identity. The vectors in the
product space may be entangled. The local unitary is chosen before the
spectator space, so the construction is coherent across all finite spectators.

## References

* Polynomial-PEPS, September 24, 2026, Section 2, `info-reset-unitary`,
  lines 580–595.
* Area-law, September 24, 2026, Section 9, `amplification-unitary-error`,
  lines 524–545.
-/

open scoped Matrix Kronecker MatrixOrder ComplexOrder

/-!
## Declaration provenance

Provenance-ID: 8766-unitary_polar_correction_kronecker_one
Downstream declaration: Matrix.unitary_polar_correction_kronecker_one
Source: September 24, 2026, eq:info-reset-polar-errors and eq:info-reset-unitary.
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/02-information.tex>
Source: September 24, 2026, eq:amplification-unitary-error.
<https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/09-amplification.tex>
Independently formalized; no upstream Lean proof text reused.
These generic matrix estimates do not formalize the geometric reset or complete area-law result.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {m : Type*} [Fintype m] [DecidableEq m]

local notation "L₂" => toEuclideanCLM (n := n × m) (𝕜 := ℂ)

/-- Tensoring a fixed local polar unitary with the identity preserves the
polar factorization and both correction estimates, on arbitrary vectors of
the product Hilbert space.

Polynomial-PEPS, September 24, 2026, `info-reset-unitary`, lines 580–595;
Area-law, September 24, 2026, `amplification-unitary-error`, lines 524–545. -/
theorem unitary_polar_correction_kronecker_one
    (D : Matrix n n ℂ) (U : unitaryGroup n ℂ)
    (hD : D = (U : Matrix n n ℂ) * CFC.sqrt (Dᴴ * D)) :
    let V := (U : Matrix n n ℂ) ⊗ₖ (1 : Matrix m m ℂ)
    let E := D ⊗ₖ (1 : Matrix m m ℂ)
    V ∈ unitaryGroup (n × m) ℂ ∧
      E = V * CFC.sqrt (Eᴴ * E) ∧
      (∀ x : EuclideanSpace ℂ (n × m),
        ‖L₂ (V - E) x‖ ≤ ‖L₂ (1 - Eᴴ * E) x‖) ∧
      (∀ x y : EuclideanSpace ℂ (n × m),
        ‖L₂ V x - y‖ ≤ ‖L₂ E x - y‖ + ‖L₂ Eᴴ y - x‖) := by
  let V : unitaryGroup (n × m) ℂ :=
    ⟨(U : Matrix n n ℂ) ⊗ₖ (1 : Matrix m m ℂ),
      kronecker_mem_unitary U.prop (one_mem _)⟩
  let E := D ⊗ₖ (1 : Matrix m m ℂ)
  let P := CFC.sqrt (Eᴴ * E)
  have hP : P.PosSemidef := nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hsq : P * P = Eᴴ * E :=
    CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self E).nonneg
  have hroot : P = CFC.sqrt (Dᴴ * D) ⊗ₖ (1 : Matrix m m ℂ) := by
    dsimp [P, E]
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, one_mul,
      (posSemidef_conjTranspose_mul_self D).sqrt_kronecker PosSemidef.one,
      CFC.sqrt_one]
  have hpolar : E = (V : Matrix (n × m) (n × m) ℂ) * P := by
    rw [hroot]
    change D ⊗ₖ (1 : Matrix m m ℂ) =
      ((U : Matrix n n ℂ) ⊗ₖ 1) * (CFC.sqrt (Dᴴ * D) ⊗ₖ 1)
    rw [← mul_kronecker_mul, one_mul, ← hD]
  refine ⟨V.prop, hpolar, ?_, ?_⟩
  · intro x
    change ‖L₂ ((V : Matrix (n × m) (n × m) ℂ) - E) x‖ ≤
      ‖L₂ (1 - Eᴴ * E) x‖
    have hdiff : (V : Matrix (n × m) (n × m) ℂ) - E =
        (V : Matrix (n × m) (n × m) ℂ) * (1 - P) := by
      rw [hpolar, mul_sub, mul_one]
    rw [hdiff, map_mul, mul_apply_eq_comp,
      ContinuousLinearMap.norm_map_of_mem_unitary (Unitary.map_mem L₂ V.prop), ← hsq]
    exact hP.norm_one_sub_le_norm_one_sub_sq x
  · intro x y
    change ‖L₂ (V : Matrix (n × m) (n × m) ℂ) x - y‖ ≤
      ‖L₂ E x - y‖ + ‖L₂ Eᴴ y - x‖
    simpa only [← hpolar] using
      norm_unitary_sub_le_add_residuals_of_mul_posSemidef V hP x y

end Matrix
