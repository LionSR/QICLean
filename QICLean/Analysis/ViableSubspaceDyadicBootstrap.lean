/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceMinimum
import QICLean.Analysis.ViableSubspaceNestedCountSampling
import QICLean.Analysis.ViableSubspaceDimension
import QICLean.Analysis.PolynomialFilterDyadicGrowth

/-!
# A strict dimension comparison for nested viable targets

Actual minimizing spaces and a finite first count comparison reduce the
low-density argument to the calibrated nested-target sample. The previous
minimum determines the sample size; the next optimal space is the space
in which the sample is drawn. Its actual improving image has dimension
strictly smaller than the previous minimum, giving a contradiction.

This is an auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. The nested improving families,
count comparisons and a finite count cap are explicit premises here.
Their derivation from a physical Hamiltonian is a separate theorem.

**Local fix (strict dimension decrease):** The actual sample size is
`p / (2 * D^2)`, with `p` the previous minimum, rather than the
dimension of the next optimal space. Its image has dimension below `p`.
See `docs/paper-gaps/alvv16_low_density_sampling.tex`.
-/

open scoped TensorProduct InnerProductSpace

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- Nested actual improving families give a viable subspace at the initial
count. The proof selects actual natural minima and invokes the literal
calibrated Haar sample at the first bad-to-good pair. Auxiliary to ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_isViable_finrank_le_of_dyadic_families
    (T : ℕ → Submodule ℂ (M ⊗[ℂ] F)) (D : ℕ → ℕ) (r : ℕ)
    (hT : ∀ j, T j ≤ T (j + 1)) (hr : 1 ≤ r)
    (htarget : ∀ j, Module.finrank ℂ (T j) ≤ r)
    (hlogD : ∀ j, 100 ≤ Real.log (D j : ℝ))
    (hcount : ∀ j, Real.log (D (j + 1) : ℝ) ≤ (13 / 6) * Real.log (D j : ℝ))
    (hcap : ∃ j, Module.finrank ℂ M ≤ r * D j ^ 3)
    (hfamily : ∀ j,
      ∃ (A : Fin (D j ^ 2) → M →L[ℂ] M)
        (Tlo Thi : Submodule ℂ (M ⊗[ℂ] F)) (Delta : ℝ),
        IsCloseTo (1 / 200) (T (j + 1)) Thi ∧
        IsCloseTo (1 / 200) Tlo (T j) ∧ 0 ≤ Delta ∧
        (D j : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
        ∀ delta < 1, ∀ S : Submodule ℂ M, IsViable delta S Thi →
          IsViable (Delta / (1 - delta) ^ 2)
            (⨆ i, S.map (A i : M →ₗ[ℂ] M)) Tlo) :
    ∃ W : Submodule ℂ M,
      Module.finrank ℂ W ≤ r * D 0 ^ 3 ∧ IsViable (3 / 200) W (T 0) := by
  classical
  obtain ⟨p, W, hW⟩ := exists_isViable_minimal_sequence (3 / 200) (by norm_num) T hT
  have hex : ∃ j, p j ≤ r * D j ^ 3 := by
    obtain ⟨j, hj⟩ := hcap
    exact ⟨j, (hW j).2.2.2.1.trans hj⟩
  obtain ⟨j, hgood, hfirst⟩ : ∃ j, p j ≤ r * D j ^ 3 ∧
      ∀ i < j, r * D i ^ 3 < p i :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ hi ↦ lt_of_not_ge (Nat.find_min hex hi)⟩
  cases j with
  | zero =>
    refine ⟨W 0, ?_, (hW 0).2.1⟩
    simpa only [(hW 0).1] using hgood
  | succ j =>
    obtain ⟨A, Tlo, Thi, Delta, hupper, hlower, hDelta, htrade, himprove⟩ := hfamily j
    have hpW : p j ≤ Module.finrank ℂ (W (j + 1)) := by
      simpa only [(hW (j + 1)).1] using (hW j).2.2.2.2
    have hupperDim : Module.finrank ℂ (W (j + 1)) ≤ r * D (j + 1) ^ 3 := by
      simpa only [(hW (j + 1)).1] using hgood
    have hThi : Module.finrank ℂ Thi ≤ r :=
      (hupper.finrank_le (by norm_num)).trans (htarget (j + 1))
    obtain ⟨U, _hs1, _halpha, _hsample, _hdims, _hsv, _hhalf, hlt, _hraw, hfinal⟩ :=
      exists_isViable_nested_sample_of_count_comparison hupper hlower A himprove
        hDelta (hlogD j) hr hThi (hcount j) (hfirst j (Nat.lt_succ_self j))
        ((hW (j + 1)).2.1) hpW hupperDim htrade
    exact False.elim (not_lt_of_ge ((hW j).2.2.1 _ hfinal) hlt)

/-- For the actual natural ceiling counts, both the finite count cap and
the logarithmic comparisons follow from their definitions. Only the
nested improving families and target inclusions remain premises.
Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_isViable_finrank_le_of_dyadic_filter_families
    (C v : ℝ) (m r : ℕ) (hC : 100 ≤ C) (hv : 0 < v) (hm : 2 ≤ m)
    (hlogm : 100 ≤ Real.log (m : ℝ))
    (T : ℕ → Submodule ℂ (M ⊗[ℂ] F))
    (hT : ∀ j, T j ≤ T (j + 1)) (hr : 1 ≤ r)
    (htarget : ∀ j, Module.finrank ℂ (T j) ≤ r) :
    let w := fun j : ℕ ↦ v / (6 * (2 : ℝ) ^ j)
    let g := fun j ↦ min (w j) 1
    let u := fun j ↦ 1 + Real.log (m : ℝ) + Real.log (1 / g j)
    let ell := fun j ↦ ⌈C * u j ^ 2 / g j⌉₊
    let D := fun j ↦ (m * ell j ^ 2) ^ (22 * ell j)
    (∀ j, ∃ (A : Fin (D j ^ 2) → M →L[ℂ] M)
      (Tlo Thi : Submodule ℂ (M ⊗[ℂ] F)) (Delta : ℝ),
      IsCloseTo (1 / 200) (T (j + 1)) Thi ∧
      IsCloseTo (1 / 200) Tlo (T j) ∧ 0 ≤ Delta ∧
      (D j : ℝ) ^ 12 * Delta ≤ 1 / 100000 ∧
      ∀ delta < 1, ∀ S : Submodule ℂ M, IsViable delta S Thi →
        IsViable (Delta / (1 - delta) ^ 2)
          (⨆ i, S.map (A i : M →ₗ[ℂ] M)) Tlo) →
    ∃ W : Submodule ℂ M,
      Module.finrank ℂ W ≤ r * D 0 ^ 3 ∧ IsViable (3 / 200) W (T 0) := by
  intro w g u ell D hfamily
  have hw (j : ℕ) : 0 < w j := by dsimp only [w]; positivity
  have hhalf (j : ℕ) : w (j + 1) = w j / 2 := by
    dsimp only [w]
    rw [pow_succ]
    ring
  have hg (j : ℕ) : 0 < g j := lt_min (hw j) zero_lt_one
  have hratio (j : ℕ) : g j ≤ 2 * g (j + 1) := by
    by_cases hh : w (j + 1) ≤ 1
    · rw [show g (j + 1) = w (j + 1) from min_eq_left hh]
      calc
        g j ≤ w j := min_le_left _ _
        _ = 2 * w (j + 1) := by rw [hhalf]; ring
    · rw [show g (j + 1) = 1 from min_eq_right (le_of_not_ge hh)]
      exact (min_le_right _ _).trans (by norm_num)
  have hcounts (j : ℕ) : 100 ≤ Real.log (D j : ℝ) ∧
      Real.log (D (j + 1) : ℝ) ≤ (13 / 6) * Real.log (D j : ℝ) :=
    Real.log_polynomial_filter_count_half_step C m (g j) (g (j + 1)) hC hlogm
      (hg j) (min_le_right _ _) (hg (j + 1)) (min_le_right _ _) (hratio j)
  have hcap : ∃ j, Module.finrank ℂ M ≤ r * D j ^ 3 := by
    obtain ⟨j, _hell, hD⟩ := Real.exists_dyadic_polynomial_filter_count_ge C v m
      (Module.finrank ℂ M) ((by norm_num : (1 : ℝ) ≤ 100).trans hC) hv hm
    refine ⟨j, hD.trans ?_⟩
    exact (Nat.le_self_pow (by decide : 3 ≠ 0) (D j)).trans
      (by simpa only [one_mul] using Nat.mul_le_mul_right (D j ^ 3) hr)
  exact exists_isViable_finrank_le_of_dyadic_families T D r hT hr htarget
    (fun j ↦ (hcounts j).1) (fun j ↦ (hcounts j).2) hcap hfamily

end Submodule
