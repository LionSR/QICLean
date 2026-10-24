/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.SchmidtRankAction
import QICLean.Channel.MaximalOverlap
import Mathlib.Algebra.BigOperators.Fin

/-!
# Product overlap from an invariant unit vector

Let K fix a unit bipartite vector Γ and preserve its orthogonal complement.
If K contracts squared norms on that complement by at most δ, has
operator-Schmidt rank at most D, and Dδ ≤ 1/2, then a unit product vector
has overlap with Γ at least 1/√(2D). The parameter δ is an arbitrary real
number; no sign, nonempty-factor or optimizing-vector premise is imposed.

A maximizing product vector is obtained from the existing maximal-overlap
principle. Applying K to that vector gives the scalar overlap inequality;
the operator-to-vector Schmidt-rank bound supplies its rank estimate.

## References

AKLV, arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`) and Lemma 2.2
(`lem:mu1`), `1dfrustrated34.tex`, lines 296–337. The fixed-vector
assumptions are those used in the unique-ground-state settings of Sections 4
and 6.1, lines 534–537 and 879–883. In those settings the ground-space
complement is precisely Γ-perpendicular. This module proves the fixed-vector
auxiliary; it does not identify that complement for a degenerate ground
space or assert an entropy bound.
-/

open scoped BigOperators Matrix InnerProductSpace ComplexOrder

namespace Matrix

private theorem euclidean_inner_eq_raw
    {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℂ = star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact dotProduct_comm _ _

private theorem raw_unit_of_norm_one
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) (hx : ‖x‖ = 1) :
    star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp x = 1 := by
  rw [← euclidean_inner_eq_raw, inner_self_eq_norm_sq_to_K, hx]
  norm_num

private theorem norm_one_of_raw_unit
    {ι : Type*} [Fintype ι] (x : ι → ℂ) (hx : star x ⬝ᵥ x = 1) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = 1 := by
  have hs := Matrix.re_star_dotProduct_self_eq_norm_sq x
  rw [hx] at hs
  change (1 : ℝ) = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 at hs
  apply (sq_eq_sq₀ (norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ ι))
    zero_le_one).mp
  simpa only [one_pow] using hs.symm


/-- A nonzero vector is a positive real multiple of an actual unit vector. -/
private theorem exists_unit_rescaling
    {ι : Type*} [Fintype ι] (x : EuclideanSpace ℂ ι) (hx : x ≠ 0) :
    ∃ y : EuclideanSpace ℂ ι, ‖y‖ = 1 ∧ x = (‖x‖ : ℂ) • y := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : EuclideanSpace ℂ ι := ((‖x‖ : ℂ)⁻¹) • x
  refine ⟨y, ?_, ?_⟩
  · simp only [y, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hn]
    exact inv_mul_cancel₀ hn.ne'
  · dsimp only [y]
    rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]

/-- Rank at most one gives actual product factors, including the zero vector. -/
private theorem exists_product_of_schmidtRank_le_one
    {m n : Type*} [Fintype n] (φ : m × n → ℂ)
    (hφ : schmidtRank φ ≤ 1) :
    ∃ (u : m → ℂ) (v : n → ℂ), φ = fun p ↦ u p.1 * v p.2 := by
  obtain ⟨P, Q, hPQ⟩ := exists_mul_eq_of_rank_le (schmidtCoeffMatrix φ) hφ
  refine ⟨fun i ↦ P i 0, fun j ↦ Q 0 j, ?_⟩
  funext p
  have hp := congrFun (congrFun hPQ p.1) p.2
  simpa only [Matrix.mul_apply, Fin.sum_univ_one, schmidtCoeffMatrix_apply] using hp.symm

/-- Multiplication by a nonzero complex scalar preserves Schmidt rank. -/
theorem schmidtRank_smul_eq_of_ne_zero
    {m n : Type*} [Fintype n] (c : ℂ) (hc : c ≠ 0) (φ : m × n → ℂ) :
    schmidtRank (c • φ) = schmidtRank φ := by
  have hcoeff : schmidtCoeffMatrix (c • φ) = c • schmidtCoeffMatrix φ := by
    ext i j
    rfl
  rw [schmidtRank, hcoeff]
  exact rank_smul_of_mem_nonZeroDivisors (schmidtCoeffMatrix φ)
    (mem_nonZeroDivisors_of_ne_zero hc)

open Classical in
/-- Padded descending eigenvalues are all bounded by the first one. -/
private theorem kyFanNorm_le_mul_one
    {m : Type*} [Fintype m] (ρ : Matrix m m ℂ) (hρ : ρ.PosSemidef) (k : ℕ) :
    hρ.isHermitian.kyFanNorm k ≤ (k : ℝ) * hρ.isHermitian.kyFanNorm 1 := by
  have htop : hρ.isHermitian.kyFanNorm 1 = hρ.isHermitian.descEigenvalue 0 := by
    simp only [IsHermitian.kyFanNorm, Finset.sum_range_one]
  have hentry (i : ℕ) :
      hρ.isHermitian.descEigenvalue i ≤ hρ.isHermitian.descEigenvalue 0 := by
    by_cases hi : i < Fintype.card m
    · have h0 : 0 < Fintype.card m := Nat.zero_lt_of_lt hi
      rw [IsHermitian.descEigenvalue, IsHermitian.descEigenvalue,
        dite_eq_left hi, dite_eq_left h0]
      exact hρ.isHermitian.eigenvalues₀_antitone (by simp)
    · rw [IsHermitian.descEigenvalue, dite_eq_right hi]
      exact hρ.descEigenvalue_nonneg 0
  rw [htop, IsHermitian.kyFanNorm]
  calc
    (∑ i ∈ Finset.range k, hρ.isHermitian.descEigenvalue i) ≤
        ∑ _i ∈ Finset.range k, hρ.isHermitian.descEigenvalue 0 :=
      Finset.sum_le_sum fun i _ ↦ hentry i
    _ = (k : ℝ) * hρ.isHermitian.descEigenvalue 0 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

open Classical in
/-- Both the strict-index and full-index maximum principles are used. -/
private theorem unit_overlap_le_rank_mul_top
    {m n : Type*} [Fintype m] [Fintype n]
    (Γ χ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1) (hχ : ‖χ‖ = 1)
    {D : ℕ} (hD : 1 ≤ D) (hrank : schmidtRank (WithLp.ofLp χ) ≤ D) :
    ‖⟪Γ, χ⟫_ℂ‖ ^ 2 ≤ (D : ℝ) *
      (posSemidef_self_mul_conjTranspose
        (schmidtCoeffMatrix (WithLp.ofLp Γ))).isHermitian.kyFanNorm 1 := by
  let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
  have hρ := posSemidef_self_mul_conjTranspose C
  have hΓraw := raw_unit_of_norm_one Γ hΓ
  have hχraw := raw_unit_of_norm_one χ hχ
  rw [euclidean_inner_eq_raw]
  by_cases hsmall : D < Fintype.card m
  · have hb := (maximalSchmidtOverlap_eq_kyFanNorm
      (WithLp.ofLp Γ) hΓraw hD hsmall).2
      ⟨WithLp.ofLp χ, hχraw, hrank, rfl⟩
    exact hb.trans (kyFanNorm_le_mul_one (C * Cᴴ) hρ D)
  · have hcard : Fintype.card m ≤ D := Nat.le_of_not_gt hsmall
    have hb := (maximalSchmidtOverlap_eq_kyFanNorm_top (WithLp.ofLp Γ) hΓraw).2
      ⟨WithLp.ofLp χ, hχraw, schmidtRank_le_left (WithLp.ofLp χ), rfl⟩
    refine hb.trans ((kyFanNorm_le_mul_one (C * Cᴴ) hρ (Fintype.card m)).trans ?_)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hρ.kyFanNorm_nonneg 1)

open Classical in
/-- The rank-overlap estimate is homogeneous and includes a zero output. -/
private theorem overlap_le_rank_mul_top
    {m n : Type*} [Fintype m] [Fintype n]
    (Γ χ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    {D : ℕ} (hD : 1 ≤ D) (hrank : schmidtRank (WithLp.ofLp χ) ≤ D) :
    ‖⟪Γ, χ⟫_ℂ‖ ^ 2 ≤ (D : ℝ) *
      (posSemidef_self_mul_conjTranspose
        (schmidtCoeffMatrix (WithLp.ofLp Γ))).isHermitian.kyFanNorm 1 * ‖χ‖ ^ 2 := by
  by_cases hχ : χ = 0
  · simp only [hχ, inner_zero_right, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, le_refl]
  · obtain ⟨y, hy, hscale⟩ := exists_unit_rescaling χ hχ
    have hn : 0 < ‖χ‖ := norm_pos_iff.mpr hχ
    have heq : schmidtRank (WithLp.ofLp χ) = schmidtRank (WithLp.ofLp y) := by
      rw [hscale, WithLp.ofLp_smul]
      exact schmidtRank_smul_eq_of_ne_zero (‖χ‖ : ℂ)
        (by exact_mod_cast hn.ne') (WithLp.ofLp y)
    have hyrank : schmidtRank (WithLp.ofLp y) ≤ D := heq ▸ hrank
    have hb := unit_overlap_le_rank_mul_top Γ y hΓ hy hD hyrank
    calc
      ‖⟪Γ, χ⟫_ℂ‖ ^ 2 = ‖(‖χ‖ : ℂ) * ⟪Γ, y⟫_ℂ‖ ^ 2 := by
        conv_lhs => rw [hscale, inner_smul_right]
      _ = ‖χ‖ ^ 2 * ‖⟪Γ, y⟫_ℂ‖ ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, mul_pow]
      _ ≤ ‖χ‖ ^ 2 * ((D : ℝ) *
          (posSemidef_self_mul_conjTranspose
            (schmidtCoeffMatrix (WithLp.ofLp Γ))).isHermitian.kyFanNorm 1) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = (D : ℝ) *
          (posSemidef_self_mul_conjTranspose
            (schmidtCoeffMatrix (WithLp.ofLp Γ))).isHermitian.kyFanNorm 1 * ‖χ‖ ^ 2 := by
        ring

open Classical in
/-- An actual normalized rank-one maximizer exists, even in left dimension one. -/
private theorem exists_unit_rank_one_top
    {m n : Type*} [Fintype m] [Fintype n]
    (Γ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1) :
    ∃ φ : EuclideanSpace ℂ (m × n), ‖φ‖ = 1 ∧
      schmidtRank (WithLp.ofLp φ) ≤ 1 ∧
      ‖⟪Γ, φ⟫_ℂ‖ ^ 2 =
        (posSemidef_self_mul_conjTranspose
          (schmidtCoeffMatrix (WithLp.ofLp Γ))).isHermitian.kyFanNorm 1 ∧
      0 < ‖⟪Γ, φ⟫_ℂ‖ ^ 2 := by
  have hΓne : Γ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hΓ]
    exact one_ne_zero
  have hrawne : WithLp.ofLp Γ ≠ 0 := fun hz ↦ hΓne ((WithLp.ofLp_eq_zero (p := 2)).mp hz)
  obtain ⟨p, _⟩ := Function.ne_iff.mp hrawne
  have hcard : 0 < Fintype.card m := Fintype.card_pos_iff.mpr ⟨p.1⟩
  let C := schmidtCoeffMatrix (WithLp.ofLp Γ)
  have hρ := posSemidef_self_mul_conjTranspose C
  have hΓraw := raw_unit_of_norm_one Γ hΓ
  have htrace : ((C * Cᴴ).trace).re = 1 := by
    rw [trace_mul_comm, ← star_dotProduct_self_eq_trace_conjTranspose_mul]
    rw [hΓraw, Complex.one_re]
  have hpos : 0 < hρ.isHermitian.kyFanNorm 1 :=
    hρ.zero_lt_kyFanNorm_one hcard (by rw [htrace]; norm_num)
  have hgreat : IsGreatest
      {r : ℝ | ∃ ψ : m × n → ℂ, star ψ ⬝ᵥ ψ = 1 ∧
        HasSchmidtRankLE 1 ψ ∧ ‖star (WithLp.ofLp Γ) ⬝ᵥ ψ‖ ^ 2 = r}
      (hρ.isHermitian.kyFanNorm 1) := by
    by_cases hdim : 1 < Fintype.card m
    · exact maximalSchmidtOverlap_eq_kyFanNorm (WithLp.ofLp Γ) hΓraw le_rfl hdim
    · have heq : Fintype.card m = 1 := by omega
      simpa only [heq] using maximalSchmidtOverlap_eq_kyFanNorm_top
        (WithLp.ofLp Γ) hΓraw
  obtain ⟨ψ, hψ, hrank, heq⟩ := hgreat.1
  refine ⟨WithLp.toLp 2 ψ, norm_one_of_raw_unit ψ hψ, hrank, ?_, ?_⟩
  · simpa only [euclidean_inner_eq_raw, WithLp.ofLp_toLp] using heq
  · simpa only [euclidean_inner_eq_raw, WithLp.ofLp_toLp, heq] using hpos

/-- A contraction bound on unit perpendicular vectors extends homogeneously,
without any sign assumption on the squared-norm bound. -/
theorem perpendicular_shrinking_homogeneous
    {ι : Type*} [Fintype ι]
    (A : EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ ι)
    (Γ : EuclideanSpace ℂ ι) (δ : ℝ)
    (hperp : ∀ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
      ⟪Γ, A ψ⟫_ℂ = 0 ∧ ‖A ψ‖ ^ 2 ≤ δ)
    (v : EuclideanSpace ℂ ι) (hv : ⟪Γ, v⟫_ℂ = 0) :
    ⟪Γ, A v⟫_ℂ = 0 ∧ ‖A v‖ ^ 2 ≤ δ * ‖v‖ ^ 2 := by
  by_cases hz : v = 0
  · simp only [hz, map_zero, inner_zero_right, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0), mul_zero, le_refl, and_self]
  · obtain ⟨y, hy, hscale⟩ := exists_unit_rescaling v hz
    have hn : 0 < ‖v‖ := norm_pos_iff.mpr hz
    have hyorth : ⟪Γ, y⟫_ℂ = 0 := by
      have hh : (‖v‖ : ℂ) * ⟪Γ, y⟫_ℂ = 0 := by
        have hh := hv
        rw [hscale, inner_smul_right] at hh
        exact hh
      exact (mul_eq_zero.mp hh).resolve_left (by exact_mod_cast hn.ne')
    obtain ⟨hortho, hnorm⟩ := hperp y hy hyorth
    have hAv : A v = (‖v‖ : ℂ) • A y := by
      conv_lhs => rw [hscale, map_smul]
    constructor
    · rw [hAv, inner_smul_right, hortho, mul_zero]
    · calc
        ‖A v‖ ^ 2 = ‖v‖ ^ 2 * ‖A y‖ ^ 2 := by
          rw [hAv, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hn, mul_pow]
        _ ≤ ‖v‖ ^ 2 * δ := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
        _ = δ * ‖v‖ ^ 2 := mul_comm _ _

/-- The sharper rational bound and the source constant both allow real δ. -/
private theorem overlap_scalar_bootstrap
    {D : ℕ} {δ x : ℝ} (hD : 1 ≤ D) (htradeoff : (D : ℝ) * δ ≤ 1 / 2)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (hbootstrap : 1 ≤ (D : ℝ) * (x + δ * (1 - x))) :
    (1 - (D : ℝ) * δ) / ((D : ℝ) * (1 - δ)) ≤ x ∧
      1 / (2 * (D : ℝ)) ≤ x := by
  have hDreal : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < (D : ℝ) := lt_of_lt_of_le zero_lt_one hDreal
  have hδ : δ < 1 := by
    by_contra hh
    have hδ1 : 1 ≤ δ := le_of_not_gt hh
    have hm : (D : ℝ) ≤ (D : ℝ) * δ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1 hDpos.le
    have hbad : (1 : ℝ) ≤ 1 / 2 := hDreal.trans (hm.trans htradeoff)
    norm_num at hbad
  have hden : 0 < (D : ℝ) * (1 - δ) := mul_pos hDpos (sub_pos.mpr hδ)
  constructor
  · apply (div_le_iff₀ hden).2
    nlinarith only [hbootstrap]
  · have hmul : (D : ℝ) * δ * (1 - x) ≤ (1 / 2 : ℝ) * (1 - x) :=
      mul_le_mul_of_nonneg_right htradeoff (sub_nonneg.mpr hx1)
    have hh : (1 / 2 : ℝ) ≤ (D : ℝ) * x := by
      nlinarith only [hbootstrap, hmul, hx0]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (D : ℝ))).2
    nlinarith only [hh]

open Classical in
/-- The maximizing product vector satisfies the sharp overlap inequality before any
tradeoff restriction is imposed. AKLV, arXiv:1301.1162v1, proof of Lemma 2.2
(`lem:mu1`), `1dfrustrated34.tex`, lines 331–337. -/
private theorem exists_unit_rank_one_overlap_bootstrap
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {D : ℕ} {δ : ℝ}
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ D) :
    ∃ φ : EuclideanSpace ℂ (m × n), 1 ≤ D ∧ ‖φ‖ = 1 ∧
      schmidtRank (WithLp.ofLp φ) ≤ 1 ∧
      0 < ‖⟪Γ, φ⟫_ℂ‖ ^ 2 ∧ ‖⟪Γ, φ⟫_ℂ‖ ^ 2 ≤ 1 ∧
      ‖φ - ⟪Γ, φ⟫_ℂ • Γ‖ ^ 2 = 1 - ‖⟪Γ, φ⟫_ℂ‖ ^ 2 ∧
      1 ≤ (D : ℝ) * (‖⟪Γ, φ⟫_ℂ‖ ^ 2 + δ * (1 - ‖⟪Γ, φ⟫_ℂ‖ ^ 2)) := by
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
  obtain ⟨φ, hφ, hφrank, hφtop, hxpos⟩ := exists_unit_rank_one_top Γ hΓ
  let a : ℂ := ⟪Γ, φ⟫_ℂ
  let v : EuclideanSpace ℂ (m × n) := φ - a • Γ
  let x : ℝ := ‖a‖ ^ 2
  have hx0 : 0 < x := hxpos
  have hx1 : x ≤ 1 := by
    have hcs : ‖a‖ ≤ 1 := by simpa only [a, hΓ, hφ, mul_one] using norm_inner_le_norm Γ φ
    dsimp only [x]
    calc
      ‖a‖ ^ 2 ≤ (1 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg a) hcs 2
      _ = 1 := one_pow 2
  have hΓinner : ⟪Γ, Γ⟫_ℂ = 1 := by
    rw [euclidean_inner_eq_raw]
    exact raw_unit_of_norm_one Γ hΓ
  have hv : ⟪Γ, v⟫_ℂ = 0 := by
    simp only [v, inner_sub_right, inner_smul_right, hΓinner, mul_one, a, sub_self]
  have hdecomp : φ = a • Γ + v := by
    dsimp only [v]
    rw [add_comm (a • Γ), sub_add_cancel]
  have hnorma : ‖a • Γ‖ = ‖a‖ := by rw [norm_smul, hΓ, mul_one]
  have hnormv : ‖v‖ ^ 2 = 1 - x := by
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (𝕜 := ℂ) (a • Γ) v (by simp only [inner_smul_left, hv, mul_zero])
    have hsquare : ‖φ‖ ^ 2 = ‖a‖ ^ 2 + ‖v‖ ^ 2 := by
      simpa only [← hdecomp, hnorma, pow_two] using hpyth
    rw [hφ, one_pow] at hsquare
    change 1 = x + ‖v‖ ^ 2 at hsquare
    linarith only [hsquare]
  obtain ⟨hKvorth, hKvnorm⟩ := perpendicular_shrinking_homogeneous
    (Matrix.toEuclideanLin K) Γ δ hperp v hv
  have hKdecomp : Matrix.toEuclideanLin K φ = a • Γ + Matrix.toEuclideanLin K v := by
    rw [hdecomp, map_add, map_smul, hfix]
  have hpreserve : ⟪Γ, Matrix.toEuclideanLin K φ⟫_ℂ = a := by
    rw [hKdecomp, inner_add_right, inner_smul_right, hKvorth, hΓinner,
      mul_one, add_zero]
  have hnormK : ‖Matrix.toEuclideanLin K φ‖ ^ 2 ≤ x + δ * (1 - x) := by
    have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (𝕜 := ℂ) (a • Γ) (Matrix.toEuclideanLin K v)
      (by simp only [inner_smul_left, hKvorth, mul_zero])
    have hidentity : ‖Matrix.toEuclideanLin K φ‖ ^ 2 = x +
        ‖Matrix.toEuclideanLin K v‖ ^ 2 := by
      simpa only [← hKdecomp, hnorma, x, pow_two] using hpyth
    rw [hidentity]
    exact add_le_add (le_refl x) (by simpa only [hnormv] using hKvnorm)
  have houtput : schmidtRank (WithLp.ofLp (Matrix.toEuclideanLin K φ)) ≤ D := by
    change schmidtRank (K *ᵥ WithLp.ofLp φ) ≤ D
    calc
      schmidtRank (K *ᵥ WithLp.ofLp φ) ≤
          operatorSchmidtRank K * schmidtRank (WithLp.ofLp φ) :=
        schmidtRank_mulVec_le K (WithLp.ofLp φ)
      _ ≤ D * 1 := Nat.mul_le_mul hrank hφrank
      _ = D := Nat.mul_one D
  have hoverlap := overlap_le_rank_mul_top Γ (Matrix.toEuclideanLin K φ) hΓ hD houtput
  rw [← hφtop, hpreserve] at hoverlap
  change x ≤ (D : ℝ) * x * ‖Matrix.toEuclideanLin K φ‖ ^ 2 at hoverlap
  have hbound : x ≤ (D : ℝ) * x * (x + δ * (1 - x)) :=
    hoverlap.trans (mul_le_mul_of_nonneg_left hnormK
      (mul_nonneg (Nat.cast_nonneg D) hx0.le))
  have hbootstrap : 1 ≤ (D : ℝ) * (x + δ * (1 - x)) := by
    have hscaled : x * 1 ≤ x * ((D : ℝ) * (x + δ * (1 - x))) := by
      calc
        x * 1 = x := mul_one x
        _ ≤ (D : ℝ) * x * (x + δ * (1 - x)) := hbound
        _ = x * ((D : ℝ) * (x + δ * (1 - x))) := by ring
    exact le_of_mul_le_mul_left hscaled hx0
  exact ⟨φ, hD, hφ, hφrank, hx0, hx1, hnormv, hbootstrap⟩

open Classical in
/-- A fixed unit vector preserved by a bipartite operator has a unit product
vector of overlap at least 1/√(2D) under the stated rank and shrinking tradeoff.

AKLV, arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`), Lemma 2.2 (`lem:mu1`),
and the unique-ground-state applications in Sections 4 and 6.1;
`1dfrustrated34.tex`, lines 296–337, 534–537 and 879–883.
The shrinking parameter may be any real number. -/
theorem exists_unit_product_overlap_ge_of_operatorSchmidtRank
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ : EuclideanSpace ℂ (m × n))
    (hΓ : ‖Γ‖ = 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {D : ℕ} {δ : ℝ}
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ D)
    (htradeoff : (D : ℝ) * δ ≤ 1 / 2) :
    ∃ (u : m → ℂ) (v : n → ℂ),
      let φ : EuclideanSpace ℂ (m × n) :=
        WithLp.toLp 2 (fun p ↦ u p.1 * v p.2)
      ‖φ‖ = 1 ∧
        1 / Real.sqrt (2 * (D : ℝ)) ≤ ‖⟪Γ, φ⟫_ℂ‖ := by
  classical
  obtain ⟨φ, hD, hφ, hφrank, hx0, hx1, _, hbootstrap⟩ :=
    exists_unit_rank_one_overlap_bootstrap K Γ hΓ hfix hperp hrank
  let a : ℂ := ⟪Γ, φ⟫_ℂ
  have hxlower := (overlap_scalar_bootstrap hD htradeoff hx0 hx1 hbootstrap).2
  have hroot : 1 / Real.sqrt (2 * (D : ℝ)) ≤ ‖a‖ := by
    have hs : Real.sqrt (1 / (2 * (D : ℝ))) ≤ ‖a‖ := by
      calc
        Real.sqrt (1 / (2 * (D : ℝ))) ≤ Real.sqrt (‖a‖ ^ 2) := Real.sqrt_le_sqrt hxlower
        _ = ‖a‖ := Real.sqrt_sq (norm_nonneg a)
    simpa only [one_div, Real.sqrt_inv] using hs
  obtain ⟨u, w, huw⟩ := exists_product_of_schmidtRank_le_one (WithLp.ofLp φ) hφrank
  have hproduct : (WithLp.toLp 2 (fun p ↦ u p.1 * w p.2) :
      EuclideanSpace ℂ (m × n)) = φ := by
    rw [← huw, WithLp.toLp_ofLp]
  refine ⟨u, w, ?_⟩
  dsimp only
  rw [hproduct]
  exact ⟨hφ, hroot⟩

open Classical in
/-- A fixed unit vector is a product vector if an operator of operator-Schmidt rank
at most one preserves its orthogonal complement and contracts squared norms there
by a real factor strictly less than one. This is the rank-one endpoint of the
maximizing-vector argument in AKLV, arXiv:1301.1162v1, Definition 2.1 (`def:AGSP`)
and Lemma 2.2 (`lem:mu1`), `1dfrustrated34.tex`, lines 296–337.
No nonnegativity premise on the shrinking factor is required. -/
theorem schmidtRank_le_one_of_operatorSchmidtRank_le_one
    {m n : Type*} [Fintype m] [Fintype n]
    (K : Matrix (m × n) (m × n) ℂ)
    (Γ : EuclideanSpace ℂ (m × n)) (hΓ : ‖Γ‖ = 1)
    (hfix : Matrix.toEuclideanLin K Γ = Γ)
    {δ : ℝ}
    (hperp : ∀ ψ : EuclideanSpace ℂ (m × n),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ δ)
    (hrank : Matrix.operatorSchmidtRank K ≤ 1) (hδ : δ < 1) :
    schmidtRank (WithLp.ofLp Γ) ≤ 1 := by
  classical
  obtain ⟨φ, _, _, hφrank, hxpos, _, hnormv, hbootstrap⟩ :=
    exists_unit_rank_one_overlap_bootstrap K Γ hΓ hfix hperp hrank
  simp only [Nat.cast_one, one_mul] at hbootstrap
  have hfactor : (1 - δ) * (1 - ‖⟪Γ, φ⟫_ℂ‖ ^ 2) ≤ (1 - δ) * 0 := by
    nlinarith only [hbootstrap]
  have hxge : 1 ≤ ‖⟪Γ, φ⟫_ℂ‖ ^ 2 :=
    sub_nonpos.mp (le_of_mul_le_mul_left hfactor (sub_pos.mpr hδ))
  have hres : ‖φ - ⟪Γ, φ⟫_ℂ • Γ‖ ^ 2 = 0 :=
    le_antisymm (hnormv.trans_le (sub_nonpos.mpr hxge)) (sq_nonneg _)
  have hscale : φ = ⟪Γ, φ⟫_ℂ • Γ :=
    sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hres))
  have ha : ⟪Γ, φ⟫_ℂ ≠ 0 := fun hz ↦ by simp [hz] at hxpos
  have hscaled : schmidtRank (WithLp.ofLp (⟪Γ, φ⟫_ℂ • Γ)) ≤ 1 :=
    (congrArg (fun ψ : EuclideanSpace ℂ (m × n) ↦
      schmidtRank (WithLp.ofLp ψ)) hscale) ▸ hφrank
  simpa only [WithLp.ofLp_smul, schmidtRank_smul_eq_of_ne_zero _ ha] using hscaled

end Matrix
