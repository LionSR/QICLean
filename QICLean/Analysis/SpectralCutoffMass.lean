/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ShiftedDensityTruncation

/-!
# Spectral cutoff mass from the first moment

For a positive semidefinite operator `D`, let `P_b` be its actual spectral
projection onto eigenvalues at most `b`. The operator inequality
`b (I - P_b) ≤ D` bounds the mass of a unit vector above a positive threshold
by its expectation of `D` divided by that threshold.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 421–438, `comparator:defect-mass`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The actual replica defect count and its gap inequality are separate results.

Independently formalized; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:defect-mass.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
/-- For the actual closed spectral cutoff, the first moment bounds the mass above
its threshold. OpenAI area-law manuscript, `07-comparators.tex`, lines 421–438,
`comparator:defect-mass`; this is the generic operator inequality used there. -/
theorem PosSemidef.smul_one_sub_spectralCutoff_le (hA : A.PosSemidef) (b : ℝ) :
    b • (1 - cfc (fun t : ℝ ↦ if t ≤ b then 1 else 0) A) ≤ A := by
  let f : ℝ → ℝ := fun t ↦ if t ≤ b then 1 else 0
  have hcont (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ A) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have horder : cfc (fun t : ℝ ↦ b * (1 - f t)) A ≤ cfc (id : ℝ → ℝ) A := by
    apply (cfc_le_iff (fun t : ℝ ↦ b * (1 - f t)) (id : ℝ → ℝ) A
      (hf := hcont _) (ha := hA.isHermitian)).mpr
    intro t ht
    dsimp [f]
    split_ifs with htb
    · simpa using spectrum_nonneg_of_nonneg hA.nonneg ht
    · simpa using (le_of_not_ge htb)
  have hcalc : cfc (fun t : ℝ ↦ b * (1 - f t)) A = b • (1 - cfc f A) := by
    rw [show (fun t : ℝ ↦ b * (1 - f t)) = (fun t : ℝ ↦ b • (1 - f t)) from rfl,
      cfc_smul b (fun t : ℝ ↦ 1 - f t) A (hf := hcont _),
      cfc_sub (fun _ : ℝ ↦ 1) f A (hg := hcont _),
      cfc_const_one (p := IsSelfAdjoint) ℝ A hA.isHermitian]
  rw [hcalc, cfc_id (p := IsSelfAdjoint) ℝ A hA.isHermitian] at horder
  exact horder

/-- The actual closed spectral projection has mass at least one minus the first
moment divided by a positive threshold. OpenAI area-law manuscript,
`07-comparators.tex`, lines 421–438, `comparator:defect-mass`.
The replica operator and its energy bound are separate consequences. -/
theorem PosSemidef.spectralCutoff_mass_ge (hA : A.PosSemidef) {b : ℝ} (hb : 0 < b)
    (v : EuclideanSpace ℂ n) (hv : ‖v‖ = 1) :
    1 - (star v ⬝ᵥ (A *ᵥ v)).re / b ≤
      (star v ⬝ᵥ (cfc (fun t : ℝ ↦ if t ≤ b then 1 else 0) A *ᵥ v)).re := by
  have hpos := (Matrix.le_iff.mp
    (hA.smul_one_sub_spectralCutoff_le b)).dotProduct_mulVec_nonneg v
  have hreal := (Complex.nonneg_iff.mp hpos).1
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    one_mulVec, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hreal
  have hn : (star v ⬝ᵥ v).re = 1 := by
    have hnorm : (star v ⬝ᵥ v).re = ‖v‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct_comm]
      rfl
    simpa only [hv, one_pow] using hnorm
  rw [hn] at hreal
  have htail : 1 - (star v ⬝ᵥ
      (cfc (fun t : ℝ ↦ if t ≤ b then 1 else 0) A *ᵥ v)).re ≤
      (star v ⬝ᵥ (A *ᵥ v)).re / b := (le_div_iff₀ hb).mpr (by nlinarith)
  linarith

end Matrix
