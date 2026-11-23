/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Gap.WeightedPositiveKernel
import QICLean.Spectral.Gap.EigenvalueGap

/-!
# Gap transfer through two-sided positive comparisons

Two positive operators which bound one another up to strictly positive
constants have the same kernel. Consequently a gap above the kernel, every
eigenvalue other than `0` being at least `γ`, transfers through the lower
comparison. A one-sided comparison `κ P ≤ m Q` transfers the gap as well once
the two kernels are known to agree
(`LinearMap.IsPositive.forall_hasEigenvalue_of_scaled_comparison`).

The kernel comparisons are moved from TNLean,
`TNLean/MPS/ParentHamiltonian/Martingale/PositiveComparisonGap.lean` at commit `414a18fb88`,
with no change to the statements. The gap transfer through a one-sided comparison is moved from
TNLean, `TNLean/MPS/ParentHamiltonian/Gap/Comparison/OpenRangeComparison.lean` at commit
`600676ccac`, without its unused hypothesis `0 < γ`.
-/

open scoped InnerProductSpace ComplexOrder

namespace LinearMap.IsPositive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Order between positive operators reverses the inclusion of their kernels. -/
theorem ker_le_of_le {P Q : E →ₗ[ℂ] E} (hP : P.IsPositive) (hPQ : P ≤ Q) :
    LinearMap.ker Q ≤ LinearMap.ker P := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  apply hP.apply_eq_zero_of_re_inner_eq_zero
  have h := hPQ.re_inner_nonneg_left v
  have hv' := LinearMap.mem_ker.mp hv
  have hnonneg := hP.re_inner_nonneg_left v
  have hnonpos : RCLike.re ⟪P v, v⟫_ℂ ≤ 0 := by
    simpa only [LinearMap.sub_apply, hv', zero_sub, inner_neg_left, map_neg,
      neg_nonneg] using h
  exact le_antisymm hnonpos hnonneg

/-- Two-sided bounds by strictly positive multiples give equal kernels. -/
theorem ker_eq_of_smul_le_of_le_smul {P Q : E →ₗ[ℂ] E}
    (hP : P.IsPositive) (hQ : Q.IsPositive) {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hLower : (a : ℂ) • P ≤ (b : ℂ) • Q)
    (hUpper : (b : ℂ) • Q ≤ (c : ℂ) • P) :
    LinearMap.ker P = LinearMap.ker Q := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  apply le_antisymm
  · simpa only [LinearMap.ker_smul _ _ hc', LinearMap.ker_smul _ _ hb'] using
      (hQ.smul_of_nonneg (by exact_mod_cast hb.le)).ker_le_of_le hUpper
  · simpa only [LinearMap.ker_smul _ _ hb', LinearMap.ker_smul _ _ ha'] using
      (hP.smul_of_nonneg (by exact_mod_cast ha.le)).ker_le_of_le hLower

/-- **A gap transfers through a one-sided comparison.** A comparison `κ P ≤ m Q` of a positive
operator `P` with an operator `Q` of the same kernel transfers a gap `γ` above the kernel of
`P`, every eigenvalue of `P` other than `0` being at least `γ`, to the gap `κ γ / m` above the
kernel of `Q`. The positivity of `Q` follows from the comparison. -/
theorem forall_hasEigenvalue_of_scaled_comparison [FiniteDimensional ℂ E]
    {P Q : E →ₗ[ℂ] E} (hP : P.IsPositive) {κ γ m : ℝ} (hκ : 0 < κ) (hm : 0 < m)
    (hOrder : (κ : ℂ) • P ≤ (m : ℂ) • Q) (hKer : LinearMap.ker P = LinearMap.ker Q)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue P μ → μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue Q μ → μ = 0 ∨ ((κ * γ / m : ℝ) : ℂ) ≤ μ := by
  have hmQ : ((m : ℂ) • Q).IsPositive := by
    simpa only [add_sub_cancel] using
      (hP.smul_of_nonneg (Complex.zero_le_real.mpr hκ.le)).add hOrder
  have hQ : Q.IsPositive := by
    simpa only [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne', Complex.ofReal_one,
      one_smul] using hmQ.smul_of_nonneg (Complex.zero_le_real.mpr (inv_pos.mpr hm).le)
  refine hQ.isSymmetric.forall_hasEigenvalue_of_re_inner fun v hv ↦ ?_
  have hPv := hP.isSymmetric.mul_norm_sq_le_re_inner_of_forall_hasEigenvalue hGap
    (by rwa [hKer])
  have hOv := hOrder.re_inner_nonneg_right v
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, inner_sub_right, inner_smul_right,
    map_sub, RCLike.re_to_complex, Complex.re_ofReal_mul, sub_nonneg] at hOv
  rw [div_mul_eq_mul_div, div_le_iff₀ hm]
  nlinarith [mul_le_mul_of_nonneg_left hPv hκ.le]

/-- **A gap transfers through a two-sided positive comparison, eigenvalue form.** If
`a P ≤ b Q ≤ c P` for positive operators with `a, b, c > 0` and every eigenvalue of `P` other
than `0` is at least `γ > 0`, then every eigenvalue of `Q` other than `0` is at least
`a γ / b`. -/
theorem forall_hasEigenvalue_of_smul_le_of_le_smul [FiniteDimensional ℂ E]
    {P Q : E →ₗ[ℂ] E} (hP : P.IsPositive) (hQ : Q.IsPositive)
    {a b c γ : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (_hγ : 0 < γ)
    (hLower : (a : ℂ) • P ≤ (b : ℂ) • Q) (hUpper : (b : ℂ) • Q ≤ (c : ℂ) • P)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue P μ → μ = 0 ∨ (γ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue Q μ → μ = 0 ∨ ((a * γ / b : ℝ) : ℂ) ≤ μ :=
  hP.forall_hasEigenvalue_of_scaled_comparison ha hb hLower
    (hP.ker_eq_of_smul_le_of_le_smul hQ ha hb hc hLower hUpper) hGap

end LinearMap.IsPositive
