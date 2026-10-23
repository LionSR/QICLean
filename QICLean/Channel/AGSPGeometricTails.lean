/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ProductOverlapBootstrap

/-!
# Geometric Schmidt tails from a fixed invariant vector

Let `K` fix a unit bipartite vector `Γ` and preserve its orthogonal complement.
Suppose that `K` shrinks squared norms on that complement by at most `δ`, has
operator-Schmidt rank at most `D`, and satisfies `D * δ ≤ 1 / 2`. The descending
Schmidt probabilities of the original `Γ` then have geometric tails after
two initial powers, with rate `1 / (2 * D)` and rank cutoffs `D ^ (2 + i)`.

The proof chooses an actual product vector with nonzero overlap, applies
powers of the same operator, and uses a homogeneous maximal-overlap bound.
The parameter `δ` is real and has no sign assumption. The fact that `D ≥ 1`
follows from the fixed unit vector. A cutoff beyond the first-factor dimension
has an empty tail. These are fixed-vector hypotheses; the entropy summation
is a separate result.

## Main results

* `Matrix.sum_eigenvalues_geometric_tail_of_operatorSchmidtRank`: geometric
  tails of the reduced density matrix of the original fixed unit vector.

## References

* AKLV, arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`) and Corollary 2.4
  (`col:half`), lines 296–324 and 350–361. The rank-tail entropy argument
  from approximants is at lines 1059–1075.
-/

open scoped BigOperators InnerProductSpace Matrix ComplexOrder

namespace LinearMap

/-- Powers preserve an invariant orthogonal subspace and iterate its squared-norm
bound. This is the elementary iteration for the fixed-vector hypotheses of AKLV,
arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`) and Corollary 2.4 (`col:half`). -/
private theorem inner_pow_eq_zero_and_norm_sq_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : Module.End ℂ E) (Γ : E) {θ : ℝ} (hθ : 0 ≤ θ)
    (hperp : ∀ v : E, ⟪Γ, v⟫_ℂ = 0 →
      ⟪Γ, A v⟫_ℂ = 0 ∧ ‖A v‖ ^ 2 ≤ θ * ‖v‖ ^ 2)
    (v : E) (hv : ⟪Γ, v⟫_ℂ = 0) (r : ℕ) :
    ⟪Γ, (A ^ r) v⟫_ℂ = 0 ∧ ‖(A ^ r) v‖ ^ 2 ≤ θ ^ r * ‖v‖ ^ 2 := by
  induction r with
  | zero =>
    simpa only [pow_zero, Module.End.one_apply, one_mul] using
      And.intro hv (le_rfl : ‖v‖ ^ 2 ≤ ‖v‖ ^ 2)
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    refine ⟨(hperp _ ih.1).1, (hperp _ ih.1).2.trans ?_⟩
    simpa only [pow_succ', mul_assoc] using mul_le_mul_of_nonneg_left ih.2 hθ

end LinearMap

namespace Matrix

open Classical in
/-- A rank-bounded approximation with a nonzero component along a unit vector
bounds the uncaptured Schmidt probability. This is the variational step in the
rank-tail entropy argument of AKLV, arXiv:1301.1162v1, lines 1059–1075. -/
private theorem one_sub_kyFanNorm_le_of_orthogonal_decomposition
    {m n : Type*} [Fintype m] [Fintype n]
    (Γ χ v : EuclideanSpace ℂ (m × n)) (a : ℂ)
    (hΓ : ‖Γ‖ = 1) (ha : a ≠ 0) (hv : ⟪Γ, v⟫_ℂ = 0)
    (hχ : χ = a • Γ + v) {k : ℕ} (hk : k < Fintype.card m)
    (hrank : schmidtRank (WithLp.ofLp χ) ≤ k) :
    1 - (posSemidef_self_mul_conjTranspose
      (schmidtCoeffMatrix (WithLp.ofLp Γ))).isHermitian.kyFanNorm k ≤
      ‖v‖ ^ 2 / ‖a‖ ^ 2 := by
  classical
  have hΓinner : ⟪Γ, Γ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hΓ]
    norm_num
  have hoverlap : ⟪Γ, χ⟫_ℂ = a := by
    simp only [hχ, inner_add_right, inner_smul_right, hΓinner, hv, mul_one, add_zero]
  have hnorm : ‖χ‖ ^ 2 = ‖a‖ ^ 2 + ‖v‖ ^ 2 := by
    simpa only [hχ, norm_smul, hΓ, mul_one, pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ) (a • Γ) v
        (by simp only [inner_smul_left, hv, mul_zero])
  let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
  have htrace : ((C * Cᴴ).trace).re = 1 := by
    simpa only [Complex.one_re] using
      congrArg Complex.re (trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Γ hΓ)
  let hρ := posSemidef_self_mul_conjTranspose C
  have hFle : hρ.isHermitian.kyFanNorm k ≤ 1 := by
    calc
      _ ≤ hρ.isHermitian.kyFanNorm (Fintype.card m) := hρ.kyFanNorm_mono hk.le
      _ = 1 := by rw [IsHermitian.kyFanNorm_card_eq_trace_re, htrace]
  have hbound : ‖a‖ ^ 2 ≤ hρ.isHermitian.kyFanNorm k * (‖a‖ ^ 2 + ‖v‖ ^ 2) := by
    simpa only [hoverlap, hnorm] using normSq_inner_le_kyFanNorm_mul_normSq Γ χ hk hrank
  apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr ha) 2)).2
  have hlast := mul_le_mul_of_nonneg_right hFle (sq_nonneg ‖v‖)
  nlinarith only [hbound, hlast]

open Classical in
/-- The descending Schmidt probabilities of the original fixed unit vector have
geometric tails after two initial powers. This quantitative auxiliary supports
the favorable-tradeoff argument of AKLV, arXiv:1301.1162v1, Corollary 2.4
(`col:half`), under the fixed-vector form of Definition 2.1 (`def:AGSP`).
The rank-tail entropy argument from approximants is at source lines 1059–1075.

The shrinking parameter is arbitrary real and is weakened internally to
`1 / (2D)`. A cutoff beyond the first-factor dimension has an empty tail.
No optimizing vector or supplied approximation is assumed. -/
theorem sum_eigenvalues_geometric_tail_of_operatorSchmidtRank
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {D : ℕ} {δ : ℝ}
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ D)
    (htradeoff : (D : ℝ) * δ ≤ 1 / 2) (i : ℕ) :
    let C := Matrix.schmidtCoeffMatrix (WithLp.ofLp Γ)
    let hρ := Matrix.posSemidef_self_mul_conjTranspose C
    (∑ b ∈ Finset.univ.filter
      (fun b : Fin (Fintype.card m) ↦ D ^ (2 + i) ≤ b.val),
        hρ.isHermitian.eigenvalues₀ b) ≤
      (1 / (2 * (D : ℝ))) ^ (i + 1) := by
  classical
  have hΓne : Γ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hΓ]
    exact one_ne_zero
  have hKne : K ≠ 0 := by
    intro hz
    have hΓzero : Γ = 0 := by
      simpa only [hz, map_zero, LinearMap.zero_apply] using hfix.symm
    exact hΓne hΓzero
  have hD : 1 ≤ D := Nat.succ_le_of_lt
    ((operatorSchmidtRank_pos_of_ne_zero K hKne).trans_le hrank)
  have hDreal : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  let θ : ℝ := 1 / (2 * (D : ℝ))
  have hθpos : 0 < θ := by dsimp [θ]; positivity
  have hδ : δ ≤ θ := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * (D : ℝ))).2
    nlinarith only [htradeoff]
  have hperpθ : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ θ := by
    intro ψ hψ horth
    exact ⟨(hperp ψ hψ horth).1, (hperp ψ hψ horth).2.trans hδ⟩
  obtain ⟨u, w, hφ, hφoverlap⟩ :=
    exists_unit_product_overlap_ge_of_operatorSchmidtRank K Γ hΓ hfix hperp hrank htradeoff
  let φ : EuclideanSpace ℂ (m × n) :=
    WithLp.toLp 2 (fun p ↦ u p.1 * w p.2)
  have hφunit : ‖φ‖ = 1 := hφ
  let a : ℂ := ⟪Γ, φ⟫_ℂ
  have hsq : (1 / Real.sqrt (2 * (D : ℝ))) ^ 2 ≤ ‖a‖ ^ 2 :=
    pow_le_pow_left₀ (by positivity) hφoverlap 2
  have hxlower : θ ≤ ‖a‖ ^ 2 := by
    simpa only [div_pow, one_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (D : ℝ))] using hsq
  have hane : a ≠ 0 := by
    intro hz
    simpa [hz] using (hθpos.trans_le hxlower)
  let v : EuclideanSpace ℂ (m × n) := φ - a • Γ
  have hv : ⟪Γ, v⟫_ℂ = 0 := by
    simp [v, a, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hΓ]
  have hdecomp : φ = a • Γ + v := by
    dsimp only [v]
    rw [add_comm (a • Γ), sub_add_cancel]
  have hvnorm : ‖v‖ ^ 2 ≤ 1 := by
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (𝕜 := ℂ) (a • Γ) v (by simp only [inner_smul_left, hv, mul_zero])
    have hn : 1 = ‖a • Γ‖ ^ 2 + ‖v‖ ^ 2 := by
      simpa only [← hdecomp, hφunit, one_pow, pow_two, one_mul] using hpyth
    nlinarith only [hn, sq_nonneg ‖a • Γ‖]
  let A : Module.End ℂ (EuclideanSpace ℂ (m × n)) := toEuclideanLin K
  let r : ℕ := 2 + i
  let χ := (A ^ r) φ
  let z := (A ^ r) v
  obtain ⟨hzorth, hznorm⟩ := LinearMap.inner_pow_eq_zero_and_norm_sq_le A Γ hθpos.le
    (perpendicular_shrinking_homogeneous A Γ θ hperpθ) v hv r
  have hfixpow : (A ^ r) Γ = Γ := by
    simpa only [Module.End.pow_apply] using Function.iterate_fixed hfix r
  have hχdecomp : χ = a • Γ + z := by
    dsimp only [χ, z]
    rw [hdecomp, map_add, map_smul, hfixpow]
  have hzbound : ‖z‖ ^ 2 ≤ θ ^ r :=
    hznorm.trans (by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hvnorm (pow_nonneg hθpos.le r))
  have hφrank : schmidtRank (WithLp.ofLp φ) ≤ 1 := by
    simpa only [φ, WithLp.ofLp_toLp] using schmidtRank_product_le_one u w
  let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
  let hρ := posSemidef_self_mul_conjTranspose C
  change (∑ b ∈ Finset.univ.filter
    (fun b : Fin (Fintype.card m) ↦ D ^ (2 + i) ≤ b.val),
      hρ.isHermitian.eigenvalues₀ b) ≤ θ ^ (i + 1)
  have hχrank : schmidtRank (WithLp.ofLp χ) ≤ D ^ r := by
    change schmidtRank (WithLp.ofLp ((toEuclideanLin K ^ r) φ)) ≤ D ^ r
    have hpow := congrArg
      (fun A : Module.End ℂ (EuclideanSpace ℂ (m × n)) ↦ A φ)
      (toLpLin_pow 2 K r)
    rw [← hpow]
    simpa only [toLpLin_apply, WithLp.ofLp_toLp, Nat.mul_one] using
      (schmidtRank_pow_mulVec_le K (WithLp.ofLp φ) hrank r).trans
        (Nat.mul_le_mul_left (D ^ r) hφrank)
  have htrace : ((C * Cᴴ).trace).re = 1 := by
    simpa only [Complex.one_re] using
      congrArg Complex.re (trace_schmidtCoeffMatrix_mul_conjTranspose_of_norm_one Γ hΓ)
  by_cases hk : D ^ (2 + i) < Fintype.card m
  · have htail := one_sub_kyFanNorm_le_of_orthogonal_decomposition
      Γ χ z a hΓ hane hzorth hχdecomp hk hχrank
    rw [hρ.isHermitian.sum_eigenvalues₀_filter_le, htrace]
    calc
      _ ≤ ‖z‖ ^ 2 / ‖a‖ ^ 2 := htail
      _ ≤ θ ^ r / ‖a‖ ^ 2 := div_le_div_of_nonneg_right hzbound (sq_nonneg _)
      _ ≤ θ ^ r / θ := div_le_div_of_nonneg_left (pow_nonneg hθpos.le r) hθpos hxlower
      _ = θ ^ (i + 1) := by
        rw [show r = (i + 1) + 1 by dsimp only [r]; omega,
          pow_succ, mul_div_cancel_right₀ _ hθpos.ne']
  · have he : Finset.univ.filter
        (fun b : Fin (Fintype.card m) ↦ D ^ (2 + i) ≤ b.val) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro b _hb
      exact not_le_of_gt (b.isLt.trans_le (Nat.le_of_not_gt hk))
    simpa only [he, Finset.sum_empty] using pow_nonneg hθpos.le (i + 1)

end Matrix
