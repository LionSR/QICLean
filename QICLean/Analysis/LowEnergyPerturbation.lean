/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import QICLean.Analysis.ViableSubspace

/-!
# Closeness of low-energy subspaces under a perturbation on the low spectrum

Let `H` and `H'` be diagonal in orthonormal bases `b` and `b'` with eigenvalues `a` and `a'`,
and let `T(c)` and `T'(c)` be the spans of the basis vectors with eigenvalue at most `c`.
Suppose `H` and `H'` differ by at most `ξ` on `T(c)`: `‖(H - H') φ‖ ≤ ξ ‖φ‖` for `φ ∈ T(c)`,
and every eigenvalue of `H` is at least `m`. Split the spectrum of `H` above `m` into windows
of width `2 h`. On a window centred at `μ` a vector `ψ` satisfies `‖(H' - μ) ψ‖ ≤ (ξ + h) ‖ψ‖`,
so by Chebyshev's inequality its mass on the eigenvalues of `H'` above `c'` is at most
`(ξ + h) / (c' - c - h)` times its norm. Summing over the `N` windows that meet `[m, c]` with
the Cauchy–Schwarz inequality, `T'(c')` is `δ`-close to `T(c)` as soon as
`N (ξ + h) ^ 2 ≤ δ (c' - c - h) ^ 2`.

This is the argument of Arad, Landau, Vazirani and Vidick (arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, proof of Lemma `lem:hard-trunc`, second item, lines 959–969), with
the perturbation bound of Proposition `prop:truncation` (lines 894–921) as a hypothesis.

**Local fix (window count and Chebyshev gap):** the source counts the windows as
`⌈(η - ε₀) / (2 h)⌉` and divides by `η' - η`. The windows of width `2 h` covering the closed
interval `[m, c]` number `⌊(c - m) / (2 h)⌋ + 1`, and the centre of the top window can lie up
to `h` above `c`, so the Chebyshev gap is `c' - c - h`. The conclusion of the source is
unchanged. Documented in `docs/paper-gaps/alvv16_hard_truncation_windows.tex`.

## Main statements

* `Submodule.spectralSpanLE`: the span `T(c)`.
* `Submodule.mul_norm_starProjection_orthogonal_le`: Chebyshev's inequality.
* `Submodule.isCloseTo_spectralSpanLE_of_perturbation`: the closeness.
-/

open scoped InnerProductSpace
open Module

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {n : Type*} [Fintype n]

/-- The span of the basis vectors whose eigenvalue is at most `c`. -/
def spectralSpanLE (b : OrthonormalBasis n 𝕜 E) (a : n → ℝ) (c : ℝ) : Submodule 𝕜 E :=
  span 𝕜 (b '' {j | a j ≤ c})

omit [FiniteDimensional 𝕜 E] in
theorem mem_spectralSpanLE_iff (b : OrthonormalBasis n 𝕜 E) (a : n → ℝ) (c : ℝ) (x : E) :
    x ∈ spectralSpanLE b a c ↔ ∀ j, c < a j → b.repr x j = 0 := by
  have hT : spectralSpanLE b a c = span 𝕜 (b.toBasis '' {j | a j ≤ c}) := by
    rw [OrthonormalBasis.coe_toBasis]; rfl
  rw [hT, Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff,
    OrthonormalBasis.coe_toBasis_repr_apply, Set.mem_ofPred_eq]
  exact ⟨fun h' j hj => by_contra fun hne => (h' j hne).not_gt hj,
    fun h' j hne => by_contra fun hj => hne (h' j (not_le.mp hj))⟩

omit [FiniteDimensional 𝕜 E] in
/-- Parseval's identity for a vector given by its coefficients. -/
theorem norm_sq_repr_symm (b : OrthonormalBasis n 𝕜 E) (f : n → 𝕜) :
    ‖b.repr.symm (WithLp.toLp 2 f)‖ ^ 2 = ∑ j, ‖f j‖ ^ 2 := by
  rw [LinearIsometryEquiv.norm_map, EuclideanSpace.norm_sq_eq]

omit [FiniteDimensional 𝕜 E] in
/-- The coefficients of `H x` for `H` diagonal in `b`. -/
theorem repr_apply_of_eigen (b : OrthonormalBasis n 𝕜 E) (a : n → ℝ) {H : E →ₗ[𝕜] E}
    (hH : ∀ j, H (b j) = (a j : 𝕜) • b j) (x : E) (j : n) :
    b.repr (H x) j = (a j : 𝕜) * b.repr x j := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, hH, smul_smul, OrthonormalBasis.repr_self,
    PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

/-- The projection onto the complement of `T(c)` keeps the coordinates above `c`. -/
theorem starProjection_orthogonal_spectralSpanLE (b : OrthonormalBasis n 𝕜 E) (a : n → ℝ)
    (c : ℝ) (x : E) [DecidablePred fun j => c < a j] :
    (spectralSpanLE b a c)ᗮ.starProjection x =
      b.repr.symm (WithLp.toLp 2 fun j => if c < a j then b.repr x j else 0) := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set y := b.repr.symm (WithLp.toLp 2 fun j => if a j ≤ c then b.repr x j else 0)
  have hy : y ∈ spectralSpanLE b a c := by
    rw [mem_spectralSpanLE_iff]
    intro j hj
    simp [y, not_le.mpr hj]
  have hxy : x - y ∈ (spectralSpanLE b a c)ᗮ := by
    refine (mem_orthogonal' _ _).mpr fun w hw => ?_
    rw [mem_spectralSpanLE_iff] at hw
    rw [← b.sum_inner_mul_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : a j ≤ c
    · have : ⟪b j, x - y⟫_𝕜 = 0 := by
        rw [← b.repr_apply_apply, map_sub]
        simp [y, hj]
      rw [← inner_conj_symm, this, map_zero, zero_mul]
    · rw [← b.repr_apply_apply, hw j (not_le.mp hj), mul_zero]
  have hP : (spectralSpanLE b a c)ᗮ.starProjection x = x - y := by
    rw [starProjection_orthogonal_val,
      ← eq_starProjection_of_mem_of_inner_eq_zero hy fun w hw => (mem_orthogonal' _ _).mp hxy w hw]
  rw [hP]
  apply b.repr.injective
  ext j
  simp only [map_sub, LinearIsometryEquiv.apply_symm_apply, y, PiLp.sub_apply]
  by_cases hj : c < a j
  · simp [hj, not_le.mpr hj]
  · simp [hj, not_lt.mp hj]

/-- The squared mass of `x` above `c` is the sum of the squared coordinates above `c`. -/
theorem norm_sq_starProjection_orthogonal_spectralSpanLE (b : OrthonormalBasis n 𝕜 E)
    (a : n → ℝ) (c : ℝ) (x : E) :
    ‖(spectralSpanLE b a c)ᗮ.starProjection x‖ ^ 2 =
      ∑ j, if c < a j then ‖b.repr x j‖ ^ 2 else 0 := by
  classical
  rw [starProjection_orthogonal_spectralSpanLE, norm_sq_repr_symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- **Chebyshev's inequality.** If every eigenvalue of `H` above `c` is at distance at least
`D` from `μ`, the mass of `x` above `c` is at most `‖(H - μ) x‖ / D`. -/
theorem mul_norm_starProjection_orthogonal_le (b : OrthonormalBasis n 𝕜 E) (a : n → ℝ)
    {H : E →ₗ[𝕜] E} (hH : ∀ j, H (b j) = (a j : 𝕜) • b j) {c μ D : ℝ} (hD : 0 ≤ D)
    (hgap : ∀ j, c < a j → D ≤ |a j - μ|) (x : E) :
    D * ‖(spectralSpanLE b a c)ᗮ.starProjection x‖ ≤ ‖H x - (μ : 𝕜) • x‖ := by
  classical
  refine le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) ?_
  have hrepr : H x - (μ : 𝕜) • x =
      b.repr.symm (WithLp.toLp 2 fun j => ((a j - μ : ℝ) : 𝕜) * b.repr x j) := by
    apply b.repr.injective
    ext j
    simp [repr_apply_of_eigen b a hH, sub_mul, Algebra.smul_def, RCLike.algebraMap_eq_ofReal]
  rw [mul_pow, norm_sq_starProjection_orthogonal_spectralSpanLE, hrepr, norm_sq_repr_symm,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, mul_pow, RCLike.norm_ofReal]
  split_ifs with hj
  · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD (hgap j hj) 2) (by positivity)
  · rw [mul_zero]; positivity

/-- **One window.** A vector of `T(c)` whose coefficients sit at eigenvalues of `H` within `h`
of `μ` has mass at most `(ξ + h) / (c' - c - h)` above `c'` for `H'`. -/
theorem mul_norm_starProjection_orthogonal_le_of_window (b b' : OrthonormalBasis n 𝕜 E)
    (a a' : n → ℝ) {H H' : E →ₗ[𝕜] E} (hH : ∀ j, H (b j) = (a j : 𝕜) • b j)
    (hH' : ∀ j, H' (b' j) = (a' j : 𝕜) • b' j) {c c' ξ h μ : ℝ}
    (hpert : ∀ φ ∈ spectralSpanLE b a c, ‖H φ - H' φ‖ ≤ ξ * ‖φ‖) (hc' : c + h ≤ c')
    {ψ : E} (hψ : ψ ∈ spectralSpanLE b a c) (hsupp : ∀ j, b.repr ψ j ≠ 0 → |a j - μ| ≤ h) :
    (c' - c - h) * ‖(spectralSpanLE b' a' c')ᗮ.starProjection ψ‖ ≤ (ξ + h) * ‖ψ‖ := by
  classical
  by_cases h0 : ψ = 0
  · simp [h0]
  obtain ⟨j, hj⟩ : ∃ j, b.repr ψ j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact h0 (b.repr.injective (by ext j; simp [hall j]))
  have hμ : μ ≤ c + h := by
    have h1 := hsupp j hj
    have h2 : a j ≤ c := not_lt.mp fun hlt => hj ((mem_spectralSpanLE_iff _ _ _ _).mp hψ j hlt)
    linarith [neg_abs_le (a j - μ)]
  have hcheb := mul_norm_starProjection_orthogonal_le b' a' hH' (c := c') (μ := μ) (D := c' - c - h)
    (by linarith) (fun k hk => by rw [abs_of_pos (by linarith)]; linarith) ψ
  have hwin : ‖H ψ - (μ : 𝕜) • ψ‖ ≤ h * ‖ψ‖ := by
    have hh : 0 ≤ h := (abs_nonneg _).trans (hsupp j hj)
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    have hrepr : H ψ - (μ : 𝕜) • ψ =
        b.repr.symm (WithLp.toLp 2 fun j => ((a j - μ : ℝ) : 𝕜) * b.repr ψ j) := by
      apply b.repr.injective
      ext j
      simp [repr_apply_of_eigen b a hH, sub_mul, Algebra.smul_def, RCLike.algebraMap_eq_ofReal]
    have hψn : ‖ψ‖ ^ 2 = ∑ j, ‖b.repr ψ j‖ ^ 2 := by
      rw [← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    rw [hrepr, norm_sq_repr_symm, mul_pow, hψn, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, mul_pow, RCLike.norm_ofReal]
    by_cases hk : b.repr ψ k = 0
    · simp [hk]
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hsupp k hk) 2)
        (by positivity)
  calc (c' - c - h) * ‖(spectralSpanLE b' a' c')ᗮ.starProjection ψ‖
      ≤ ‖H' ψ - (μ : 𝕜) • ψ‖ := hcheb
    _ ≤ ‖H' ψ - H ψ‖ + ‖H ψ - (μ : 𝕜) • ψ‖ := by
        rw [show H' ψ - (μ : 𝕜) • ψ = (H' ψ - H ψ) + (H ψ - (μ : 𝕜) • ψ) by abel]
        exact norm_add_le _ _
    _ ≤ ξ * ‖ψ‖ + h * ‖ψ‖ := by
        rw [norm_sub_rev]
        exact add_le_add (hpert ψ hψ) hwin
    _ = (ξ + h) * ‖ψ‖ := by ring

/-- **The closeness of the low-energy subspaces.** If `H` and `H'` differ by at most `ξ` on
`T(c)`, every eigenvalue of `H` is at least `m`, `h > 0`, `c + h < c'`, and the number
`N = ⌊(c - m) / (2 h)⌋ + 1` of windows of width `2 h` meeting `[m, c]` satisfies
`N (ξ + h) ^ 2 ≤ δ (c' - c - h) ^ 2`, then `T'(c')` is `δ`-close to `T(c)`. Arad, Landau,
Vazirani and Vidick, arXiv:1602.08828v2, proof of Lemma `lem:hard-trunc`, second item
(lines 959–969). -/
theorem isCloseTo_spectralSpanLE_of_perturbation (b b' : OrthonormalBasis n 𝕜 E)
    (a a' : n → ℝ) {H H' : E →ₗ[𝕜] E} (hH : ∀ j, H (b j) = (a j : 𝕜) • b j)
    (hH' : ∀ j, H' (b' j) = (a' j : 𝕜) • b' j) {c c' ξ h m δ : ℝ}
    (hpert : ∀ φ ∈ spectralSpanLE b a c, ‖H φ - H' φ‖ ≤ ξ * ‖φ‖) (hh : 0 < h)
    (hm : ∀ j, m ≤ a j) (hc' : c + h < c')
    (hδ : ((⌊(c - m) / (2 * h)⌋₊ + 1 : ℕ) : ℝ) * (ξ + h) ^ 2 ≤ δ * (c' - c - h) ^ 2) :
    IsCloseTo δ (spectralSpanLE b' a' c') (spectralSpanLE b a c) := by
  classical
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  set N := ⌊(c - m) / (2 * h)⌋₊ + 1
  set w : n → ℕ := fun j => ⌊(a j - m) / (2 * h)⌋₊
  set D := c' - c - h
  have hD : 0 < D := by simp only [D]; linarith
  rw [isCloseTo_iff]
  intro φ hφ
  -- the pieces of `φ` on the windows
  set ψ : ℕ → E := fun v => b.repr.symm (WithLp.toLp 2 fun j => if w j = v then b.repr φ j else 0)
  have hψrepr (v : ℕ) (j : n) : b.repr (ψ v) j = if w j = v then b.repr φ j else 0 := by
    simp [ψ]
  have hψmem (v : ℕ) : ψ v ∈ spectralSpanLE b a c := by
    rw [mem_spectralSpanLE_iff]
    intro j hj
    rw [hψrepr]
    split_ifs
    · exact (mem_spectralSpanLE_iff _ _ _ _).mp hφ j hj
    · rfl
  have hsupp (v : ℕ) (j : n) (hj : b.repr (ψ v) j ≠ 0) :
      |a j - (m + (2 * v + 1) * h)| ≤ h := by
    rw [hψrepr] at hj
    split_ifs at hj with hv
    · have h2h : 0 < 2 * h := by linarith
      have hnn : 0 ≤ (a j - m) / (2 * h) := div_nonneg (by linarith [hm j]) h2h.le
      have hlo := Nat.floor_le hnn
      have hhi := Nat.lt_floor_add_one ((a j - m) / (2 * h))
      simp only [w] at hv
      rw [hv] at hlo hhi
      rw [le_div_iff₀ h2h] at hlo
      rw [div_lt_iff₀ h2h] at hhi
      rw [abs_le]
      constructor <;> nlinarith
    · exact absurd rfl hj
  have hsum : φ = ∑ v ∈ Finset.range N, ψ v := by
    apply b.repr.injective
    ext j
    simp only [map_sum, WithLp.ofLp_sum, Finset.sum_apply, hψrepr]
    rw [Finset.sum_ite_eq]
    split_ifs with hjN
    · rfl
    · by_contra hne
      have hjc : a j ≤ c :=
        not_lt.mp fun hlt => hne ((mem_spectralSpanLE_iff _ _ _ _).mp hφ j hlt)
      apply hjN
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (by gcongr))
  have hwin (v : ℕ) : D * ‖(spectralSpanLE b' a' c')ᗮ.starProjection (ψ v)‖ ≤
      (ξ + h) * ‖ψ v‖ :=
    mul_norm_starProjection_orthogonal_le_of_window b b' a a' hH hH' hpert hc'.le (hψmem v)
      (hsupp v)
  have hnorm : ∑ v ∈ Finset.range N, ‖ψ v‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    have hψn (v : ℕ) : ‖ψ v‖ ^ 2 = ∑ j, if w j = v then ‖b.repr φ j‖ ^ 2 else 0 := by
      simp only [ψ]
      rw [norm_sq_repr_symm]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> simp
    simp_rw [hψn]
    rw [Finset.sum_comm, ← b.repr.norm_map, EuclideanSpace.norm_sq_eq]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.sum_ite_eq]
    split_ifs
    · rfl
    · positivity
  -- Chebyshev on each window, then the Cauchy–Schwarz inequality over the windows
  have hmass : D * ‖(spectralSpanLE b' a' c')ᗮ.starProjection φ‖ ≤
      (ξ + h) * ∑ v ∈ Finset.range N, ‖ψ v‖ := by
    conv_lhs => rw [hsum, map_sum]
    calc D * ‖∑ v ∈ Finset.range N, (spectralSpanLE b' a' c')ᗮ.starProjection (ψ v)‖
        ≤ D * ∑ v ∈ Finset.range N, ‖(spectralSpanLE b' a' c')ᗮ.starProjection (ψ v)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) hD.le
      _ = ∑ v ∈ Finset.range N, D * ‖(spectralSpanLE b' a' c')ᗮ.starProjection (ψ v)‖ :=
          Finset.mul_sum _ _ _
      _ ≤ ∑ v ∈ Finset.range N, (ξ + h) * ‖ψ v‖ := Finset.sum_le_sum fun v _ => hwin v
      _ = (ξ + h) * ∑ v ∈ Finset.range N, ‖ψ v‖ := (Finset.mul_sum _ _ _).symm
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := fun v => ‖ψ v‖)
  rw [Finset.card_range] at hcs
  have hsq : D ^ 2 * ‖(spectralSpanLE b' a' c')ᗮ.starProjection φ‖ ^ 2 ≤
      D ^ 2 * (δ * ‖φ‖ ^ 2) := by
    calc D ^ 2 * ‖(spectralSpanLE b' a' c')ᗮ.starProjection φ‖ ^ 2
        = (D * ‖(spectralSpanLE b' a' c')ᗮ.starProjection φ‖) ^ 2 := by ring
      _ ≤ ((ξ + h) * ∑ v ∈ Finset.range N, ‖ψ v‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hmass 2
      _ = (ξ + h) ^ 2 * (∑ v ∈ Finset.range N, ‖ψ v‖) ^ 2 := by ring
      _ ≤ (ξ + h) ^ 2 * (N * ‖φ‖ ^ 2) := by
          gcongr
          exact hcs.trans (mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg _))
      _ = (N * (ξ + h) ^ 2) * ‖φ‖ ^ 2 := by ring
      _ ≤ (δ * D ^ 2) * ‖φ‖ ^ 2 := by gcongr
      _ = D ^ 2 * (δ * ‖φ‖ ^ 2) := by ring
  have hperp := le_of_mul_le_mul_left hsq (by positivity)
  have hpy := norm_sq_eq_add_norm_sq_starProjection φ (spectralSpanLE b' a' c')
  linarith

end Submodule
