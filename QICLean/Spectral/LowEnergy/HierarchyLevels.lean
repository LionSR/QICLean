/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.LowEnergy.HierarchicalProjection

/-!
# All levels of Hastings' hierarchical projection and the energy of its final state

Section II of Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 668–707, builds projections level by level. The level-`m` projection of a
block of `2^m` sites is the spectral window, centred at `c = ⟨Ψ_a, M Ψ_a⟩`, of the pair operator
`M` joining its two halves, taken inside the range of the product `Q` of the two level-`(m - 1)`
projections of those halves. The source compares the level-`m` projection with the normalized
vector `Ψ^{m-1}_a` of the level below and records the recursion
`b_m = (ε + 2 b_{m-1})^{1 - 1/h}` (lines 696–704).

This file carries out the bookkeeping over all `h` levels. Every deficiency is measured against
`Ψ_a` itself. The normalized image `u = Q Ψ_a / ‖Q Ψ_a‖` enters only through the residual of
the window: it lies in the range of `Q`, at distance at most `2 D` from `Ψ_a` when each half
moves `Ψ_a` by at most `D`, so the window moves it by at most `(ε + ‖M - c‖ 2 D) / x`. The
nested-projection bound then gives the deficiency of the new level against `Ψ_a`:
`D_{m+1}² ≤ 2 D_m² + ((ε + ‖M - c‖ 2 D_m) / x_m)²`. With the source's window radii this yields
`D_m ≤ (3^m - 1) e^{s^m}`, where `ε = K e` and `‖M - c‖ ≤ K`.

**Local fix (deficiency against the ground state):** the source's `b_m` is the deficiency of
the level-`m` projection on the intermediate vector `Ψ^{m-1}_a` (lines 696–704), while the
window stays centred at the expectation in `Ψ_a` (line 681). Comparing every level with `Ψ_a`
instead replaces the printed recurrence by `D_{m+1}² ≤ 2 D_m² + (e + 2 D_m)^{2s}` and its
coefficient `2^m - 1` by `3^m - 1`, which is still polynomial in the number `N = 2^h` of
supersites. Documented in `docs/paper-gaps/hastings05_hierarchical_projection.tex`.

The blocks of one level act on disjoint sets of supersites, so their projections commute. Here
that commutation is a hypothesis; it follows from the supersite grouping of lines 609–628,
which is not formalized here.

## The energy of the final state

At the end of the construction (lines 705–720) the source states that once the deficiency
`b_h` of the last level is small, "there is at least one state `α^h`, and one may show" eq.
`hchy`: `⟨α^h, ∑_i M_i α^h⟩ ≤ ⟨Ψ_a, ∑_i M_i Ψ_a⟩ + N J O(exp[−l_proj/(log₂(N) l_fac)])`. The
source gives no argument. Let `Q` be the projection onto the states kept at the last level and
suppose that `Ψ` is moved by `Q` by at most `b < 1` in norm, the form in which the deficiency of
a level is measured here. Then `Q Ψ ≠ 0`, the normalized image `φ = Q Ψ / ‖Q Ψ‖` lies in the
range of `Q` and within `2 b` of `Ψ`, and for every operator `M`,
`|⟨φ, M φ⟩ − ⟨Ψ, M Ψ⟩| ≤ 2 ‖M‖ ‖φ − Ψ‖ ≤ 4 ‖M‖ b`. For `M = ∑_{i<N} M_i` with `‖M_i‖ ≤ J` this
is `⟨φ, M φ⟩ ≤ ⟨Ψ, M Ψ⟩ + 4 N J b`, eq. `hchy` with the explicit constant `4 N J b` in place of
`N J O(·)`.

**Scope restriction (the final state):** the state produced is the normalized image of `Ψ_a`,
a unit vector in the span of the final states `α^h`, rather than one of the `α^h` themselves.
The bound holds for any sum of terms. The deficiency `b` of the last level is a hypothesis.
Documented in `docs/paper-gaps/hastings05_hierarchical_energy.tex`.

## Main statements

* `Matrix.norm_sub_compressedWindowProjection_mul_sq_le`: one level against the ground state.
* `Matrix.isStarProjection_hierarchy`: every projection of the hierarchy is an orthogonal
  projection.
* `Real.hierarchyDeficiency`, `Matrix.norm_sub_hierarchy_le`: all levels for given window
  radii.
* `Real.hierarchyMajorant`, `Real.hierarchyDeficiency_le_hierarchyMajorant`: the source's
  window radii.
* `Real.hierarchyMajorant_le`, `Real.hierarchyMajorant_le_rpow_quarter`:
  `D_m ≤ (3^m - 1) e^{s^m}`, and `(3^h - 1) e^{1/4}` for the source's exponent.
* `Matrix.abs_re_inner_sub_re_inner_le`: `|⟨φ, M φ⟩ − ⟨ψ, M ψ⟩| ≤ 2 ‖M‖ ‖φ − ψ‖` for unit
  vectors.
* `Matrix.norm_inv_norm_smul_toEuclideanLin_sub_le_two_mul`: the normalized image under one
  projection is within `2 b` of the vector.
* `Matrix.exists_mem_range_re_inner_le_add`: a unit vector in the range of `Q` with energy at
  most `⟨Ψ, M Ψ⟩ + 4 ‖M‖ b`.
* `Matrix.exists_mem_range_re_inner_sum_le_add`: eq. `hchy`, with `4 N J b` for `N` terms of
  norm at most `J`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace Real

/-- The deficiency bound of level `m` for window radii `x`: `D₀ = 0` and
`D_{m+1} = √(2 D_m² + ((ε + K 2 D_m) / x_m)²)`. -/
noncomputable def hierarchyDeficiency (ε K : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => √(2 * hierarchyDeficiency ε K x m ^ 2 +
      ((ε + K * (2 * hierarchyDeficiency ε K x m)) / x m) ^ 2)

theorem hierarchyDeficiency_zero (ε K : ℝ) (x : ℕ → ℝ) : hierarchyDeficiency ε K x 0 = 0 := rfl

theorem hierarchyDeficiency_succ (ε K : ℝ) (x : ℕ → ℝ) (m : ℕ) :
    hierarchyDeficiency ε K x (m + 1) = √(2 * hierarchyDeficiency ε K x m ^ 2 +
      ((ε + K * (2 * hierarchyDeficiency ε K x m)) / x m) ^ 2) := rfl

/-- The deficiency majorant for the source's window radii: `β₀ = 0` and
`β_{m+1} = √(2 β_m² + ((e + 2 β_m)^s)²)`. Here `e = ε / K` is the residual in units of the
coupling bound `K`, as in arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 676–681, where
`K = J l_proj` and `s = 1 - 1/h`. -/
noncomputable def hierarchyMajorant (e s : ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => √(2 * hierarchyMajorant e s m ^ 2 + ((e + 2 * hierarchyMajorant e s m) ^ s) ^ 2)

theorem hierarchyMajorant_zero (e s : ℝ) : hierarchyMajorant e s 0 = 0 := rfl

theorem hierarchyMajorant_succ (e s : ℝ) (m : ℕ) :
    hierarchyMajorant e s (m + 1) =
      √(2 * hierarchyMajorant e s m ^ 2 + ((e + 2 * hierarchyMajorant e s m) ^ s) ^ 2) := rfl

theorem hierarchyMajorant_nonneg (e s : ℝ) (m : ℕ) : 0 ≤ hierarchyMajorant e s m := by
  cases m with
  | zero => exact le_rfl
  | succ m => exact Real.sqrt_nonneg _

/-- **The source's window radii.** With `ε = K e`, `K > 0`, `e > 0` and the radius
`x_m = K (e + 2 β_m)^{1 - s}` of arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 676–681,
the deficiency bound of every level is at most `β_m`. -/
theorem hierarchyDeficiency_le_hierarchyMajorant {K e : ℝ} (hK : 0 < K) (he : 0 < e) (s : ℝ)
    (m : ℕ) :
    hierarchyDeficiency (K * e) K
        (fun j => K * (e + 2 * hierarchyMajorant e s j) ^ (1 - s)) m ≤
      hierarchyMajorant e s m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    set D := hierarchyDeficiency (K * e) K
      (fun j => K * (e + 2 * hierarchyMajorant e s j) ^ (1 - s)) m
    set β := hierarchyMajorant e s m
    have hβ := hierarchyMajorant_nonneg e s m
    have hD : 0 ≤ D := by
      cases m with
      | zero => exact le_rfl
      | succ m => exact Real.sqrt_nonneg _
    have hpos : 0 < e + 2 * β := by positivity
    have hsplit : (e + 2 * β) ^ s * (K * (e + 2 * β) ^ (1 - s)) = K * (e + 2 * β) := by
      rw [mul_left_comm, ← Real.rpow_add hpos, add_sub_cancel, Real.rpow_one]
    have hterm : (K * e + K * (2 * D)) / (K * (e + 2 * β) ^ (1 - s)) ≤ (e + 2 * β) ^ s := by
      rw [div_le_iff₀ (by positivity), hsplit]
      have := mul_le_mul_of_nonneg_left ih hK.le
      linarith
    have hnn : 0 ≤ (K * e + K * (2 * D)) / (K * (e + 2 * β) ^ (1 - s)) := by positivity
    rw [hierarchyDeficiency_succ, hierarchyMajorant_succ]
    refine Real.sqrt_le_sqrt ?_
    have h1 := pow_le_pow_left₀ hD ih 2
    have h2 := pow_le_pow_left₀ hnn hterm 2
    linarith

/-- **The closed form.** For `0 < e ≤ 1` and `0 ≤ s ≤ 1`, `β_m ≤ (3^m - 1) e^{s^m}`. The
source's case `s = 1 - 1/h`, `m = h` is `hierarchyMajorant_le_rpow_quarter`. Each step uses
`e ≤ e^{s^m}`, `e^{s^m} ≤ e^{s^{m+1}}` and `C^s ≤ C` for `C ≥ 1`. -/
theorem hierarchyMajorant_le {e s : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (m : ℕ) :
    hierarchyMajorant e s m ≤ ((3 : ℝ) ^ m - 1) * e ^ (s ^ m) := by
  induction m with
  | zero => simp [hierarchyMajorant_zero]
  | succ m ih =>
    set β := hierarchyMajorant e s m
    set C : ℝ := (3 : ℝ) ^ m - 1
    set t : ℝ := e ^ (s ^ m)
    have hβ := hierarchyMajorant_nonneg e s m
    have hC : 0 ≤ C := by
      have : (1 : ℝ) ≤ 3 ^ m := one_le_pow₀ (by norm_num)
      linarith
    have hsm0 : 0 ≤ s ^ m := pow_nonneg hs0 m
    have hsm1 : s ^ m ≤ 1 := pow_le_one₀ hs0 hs1
    have ht0 : 0 < t := Real.rpow_pos_of_pos he0 _
    -- `e ≤ e^{s^m}` and `e^{s^m} ≤ e^{s^{m+1}}`, since the exponents decrease towards zero.
    have het : e ≤ t := by
      simpa using Real.rpow_le_rpow_of_exponent_ge he0 he1 hsm1
    have ht' : t ^ s = e ^ (s ^ (m + 1)) := by
      rw [← Real.rpow_mul he0.le, pow_succ]
    have hss : s ^ (m + 1) ≤ s ^ m := by
      rw [pow_succ]
      exact mul_le_of_le_one_right hsm0 hs1
    have htt' : t ≤ e ^ (s ^ (m + 1)) := Real.rpow_le_rpow_of_exponent_ge he0 he1 hss
    -- `e + 2 β ≤ (1 + 2 C) t`, and `((1 + 2 C) t)^s ≤ (1 + 2 C) t^s`.
    have h1 : e + 2 * β ≤ (1 + 2 * C) * t := by nlinarith
    have h2 : (e + 2 * β) ^ s ≤ (1 + 2 * C) * e ^ (s ^ (m + 1)) := by
      calc (e + 2 * β) ^ s ≤ ((1 + 2 * C) * t) ^ s :=
            Real.rpow_le_rpow (by positivity) h1 hs0
        _ = (1 + 2 * C) ^ s * t ^ s := Real.mul_rpow (by positivity) ht0.le
        _ ≤ (1 + 2 * C) * e ^ (s ^ (m + 1)) := by
            rw [ht']
            gcongr
            exact Real.rpow_le_self_of_one_le (by linarith) hs1
    have h3 : β ≤ C * e ^ (s ^ (m + 1)) := ih.trans (by gcongr)
    have hpow : 0 ≤ (e + 2 * β) ^ s := Real.rpow_nonneg (by positivity) _
    rw [hierarchyMajorant_succ]
    refine Real.sqrt_le_iff.mpr ⟨?_, ?_⟩
    · have : (1 : ℝ) ≤ 3 ^ (m + 1) := one_le_pow₀ (by norm_num)
      have := Real.rpow_pos_of_pos he0 (s ^ (m + 1))
      nlinarith
    · have h3' := pow_le_pow_left₀ hβ h3 2
      have h2' := pow_le_pow_left₀ hpow h2 2
      have e3 : (3 : ℝ) ^ (m + 1) - 1 = 3 * C + 2 := by rw [pow_succ]; ring
      rw [e3]
      have := Real.rpow_pos_of_pos he0 (s ^ (m + 1))
      nlinarith [mul_nonneg hC hC]

/-- **The last level for the source's exponent.** For `0 < e ≤ 1`, `h ≥ 2` and
`s = 1 - 1/h`, the majorant of the last level satisfies `β_h ≤ (3^h - 1) e^{1/4}`, since
`(1 - 1/h)^h ≥ 1/4`. With `N = 2^h` supersites and `e = exp(-l_proj/l_fac)` this is the analogue
of the printed `N exp(-(l_proj/l_fac)(1 - 1/h)^h)` of arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 705–707, with `3^h = N^{log₂ 3}` in place of `N`. -/
theorem hierarchyMajorant_le_rpow_quarter {e : ℝ} (he0 : 0 < e) (he1 : e ≤ 1) {h : ℕ}
    (hh : 2 ≤ h) :
    hierarchyMajorant e (1 - 1 / (h : ℝ)) h ≤ ((3 : ℝ) ^ h - 1) * e ^ (1 / 4 : ℝ) := by
  have hs0 : (0 : ℝ) ≤ 1 - 1 / (h : ℝ) := Nat.one_sub_one_div_cast_nonneg h
  have hs1 : 1 - 1 / (h : ℝ) ≤ 1 := Nat.one_sub_one_div_cast_le_one h
  refine (hierarchyMajorant_le he0 he1 hs0 hs1 h).trans ?_
  have h3 : (1 : ℝ) ≤ 3 ^ h := one_le_pow₀ (by norm_num)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge he0 he1 (quarter_le_one_sub_inv_pow hh)) (by linarith)

end Real

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **One level against the ground state.** Let `P`, `P'` be commuting orthogonal projections
that each move the unit vector `ψ` by at most `D`, and let `R` be the window of `M` at `c` and
`x > 0` inside the range of `P P'`. If `‖(M - c) ψ‖ ≤ ε`, then
`‖ψ - R ψ‖² ≤ 2 D² + ((ε + ‖M - c‖ 2 D) / x)²`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 668–699, with the deficiency measured against `ψ = Ψ_a`. -/
theorem norm_sub_compressedWindowProjection_mul_sq_le {P P' M : Matrix ι ι ℂ}
    (hP : IsStarProjection P) (hP' : IsStarProjection P') (hc : Commute P P')
    (hM : M.IsHermitian) (c : ℝ) {x : ℝ} (hx : 0 < x) {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1)
    {ε D : ℝ} (hres : ‖toEuclideanLin (M - (c : ℂ) • 1) ψ‖ ≤ ε)
    (hD : ‖ψ - toEuclideanLin P ψ‖ ≤ D) (hD' : ‖ψ - toEuclideanLin P' ψ‖ ≤ D) :
    ‖ψ - toEuclideanLin (compressedWindowProjection (P * P') M c x) ψ‖ ^ 2 ≤
      2 * D ^ 2 + ((ε + ‖M - (c : ℂ) • 1‖ * (2 * D)) / x) ^ 2 := by
  have hQ := hP.mul hP' hc
  have h1 := norm_sub_sq_le_of_mul_eq (isStarProjection_compressedWindowProjection hQ hM c x)
    hQ (compressedWindowProjection_mul hQ M c x) hψ
  have h2 := norm_sub_mul_sq_le_of_isStarProjection hP P' ψ
  have h3 := pow_le_pow_left₀ (norm_nonneg _) hD 2
  have h4 := pow_le_pow_left₀ (norm_nonneg _) hD' 2
  set v := toEuclideanLin (P * P') ψ
  have hu : toEuclideanLin (P * P') (((‖v‖⁻¹ : ℝ) : ℂ) • v) = ((‖v‖⁻¹ : ℝ) : ℂ) • v := by
    rw [map_smul, ← toEuclideanLin_mul_apply, hQ.isIdempotentElem.eq]
  have h5 := norm_sub_compressedWindowProjection_le_of_norm_sub_le hQ hM c hx hu hres
    (norm_inv_norm_smul_toEuclideanLin_mul_sub_le_two_mul hP hP' hc hψ hD hD')
  have h6 := pow_le_pow_left₀ (norm_nonneg _) h5 2
  linarith

/-- Every projection of the hierarchy is an orthogonal projection, when the halves of each block
commute. -/
theorem isStarProjection_hierarchy (P M : ℕ → ℕ → Matrix ι ι ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hcomm : ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)))
    (hM : ∀ m k, (M m k).IsHermitian) : ∀ m k, IsStarProjection (P m k) := by
  intro m
  induction m with
  | zero => intro k; rw [hP0]; exact IsStarProjection.one _
  | succ m ih =>
    intro k
    rw [hstep]
    exact isStarProjection_compressedWindowProjection
      ((ih (2 * k)).mul (ih (2 * k + 1)) (hcomm m k)) (hM m k) _ _

/-- **All levels.** Let `P m k` be the level-`m` projection of block `k`, with `P 0 k = 1` on
single supersites and `P (m + 1) k` the window of `M m k` at `c m k` and `x m` inside the range
of `P m (2k) P m (2k + 1)`. If the two halves of each block commute, every residual
`‖(M m k - c m k) ψ‖` is at most `ε` and every `‖M m k - c m k‖` at most `K`, then each
level-`m` projection moves the unit vector `ψ` by at most `Real.hierarchyDeficiency ε K x m`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 668–707, where `ψ = Ψ_a` and
`c m k = ⟨Ψ_a, M m k Ψ_a⟩`. -/
theorem norm_sub_hierarchy_le (P M : ℕ → ℕ → Matrix ι ι ℂ) (c : ℕ → ℕ → ℝ) (x : ℕ → ℝ)
    (hP0 : ∀ k, P 0 k = 1)
    (hstep : ∀ m k, P (m + 1) k =
      compressedWindowProjection (P m (2 * k) * P m (2 * k + 1)) (M m k) (c m k) (x m))
    (hcomm : ∀ m k, Commute (P m (2 * k)) (P m (2 * k + 1)))
    (hM : ∀ m k, (M m k).IsHermitian) (hx : ∀ m, 0 < x m) {ψ : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) {ε K : ℝ}
    (hres : ∀ m k, ‖toEuclideanLin (M m k - (c m k : ℂ) • 1) ψ‖ ≤ ε)
    (hK : ∀ m k, ‖M m k - (c m k : ℂ) • 1‖ ≤ K) :
    ∀ m k, IsStarProjection (P m k) ∧
      ‖ψ - toEuclideanLin (P m k) ψ‖ ≤ Real.hierarchyDeficiency ε K x m := by
  have hproj := isStarProjection_hierarchy P M c x hP0 hstep hcomm hM
  suffices hbound : ∀ m k, ‖ψ - toEuclideanLin (P m k) ψ‖ ≤ Real.hierarchyDeficiency ε K x m from
    fun m k ↦ ⟨hproj m k, hbound m k⟩
  intro m
  induction m with
  | zero =>
    intro k
    rw [hP0, Real.hierarchyDeficiency_zero, toEuclideanLin_one_apply, sub_self, norm_zero]
  | succ m ih =>
    intro k
    have hP := hproj m (2 * k)
    have hP' := hproj m (2 * k + 1)
    have hD := ih (2 * k)
    have hD' := ih (2 * k + 1)
    rw [hstep]
    have hD0 : 0 ≤ Real.hierarchyDeficiency ε K x m := (norm_nonneg _).trans hD
    have h := norm_sub_compressedWindowProjection_mul_sq_le hP hP' (hcomm m k) (hM m k)
      (c m k) (hx m) hψ (hres m k) hD hD'
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hres m k)
    have hmono : (ε + ‖M m k - (c m k : ℂ) • 1‖ * (2 * Real.hierarchyDeficiency ε K x m)) / x m ≤
        (ε + K * (2 * Real.hierarchyDeficiency ε K x m)) / x m :=
      div_le_div_of_nonneg_right (by nlinarith [hK m k]) (hx m).le
    have hnn : 0 ≤ (ε + ‖M m k - (c m k : ℂ) • 1‖ * (2 * Real.hierarchyDeficiency ε K x m)) / x m :=
      div_nonneg (by positivity) (hx m).le
    rw [Real.hierarchyDeficiency_succ]
    refine Real.le_sqrt_of_sq_le (h.trans ?_)
    have := pow_le_pow_left₀ hnn hmono 2
    linarith

/-- **Energies of nearby unit vectors.** For unit vectors `φ`, `ψ` and every operator `M`,
`|re⟨φ, M φ⟩ − re⟨ψ, M ψ⟩| ≤ 2 ‖M‖ ‖φ − ψ‖`. -/
theorem abs_re_inner_sub_re_inner_le (M : Matrix ι ι ℂ) {φ ψ : EuclideanSpace ℂ ι}
    (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1) :
    |(⟪φ, toEuclideanLin M φ⟫_ℂ).re - (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re| ≤
      2 * ‖M‖ * ‖φ - ψ‖ := by
  have e : ⟪φ, toEuclideanLin M φ⟫_ℂ - ⟪ψ, toEuclideanLin M ψ⟫_ℂ =
      ⟪φ - ψ, toEuclideanLin M φ⟫_ℂ + ⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]; ring
  have h1 : ‖⟪φ - ψ, toEuclideanLin M φ⟫_ℂ‖ ≤ ‖M‖ * ‖φ - ψ‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    have := Entropy.norm_toEuclideanLin_le M φ
    rw [hφ, mul_one] at this
    nlinarith [norm_nonneg (φ - ψ)]
  have h2 : ‖⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ‖ ≤ ‖M‖ * ‖φ - ψ‖ := by
    refine (norm_inner_le_norm _ _).trans ?_
    rw [hψ, one_mul]
    exact Entropy.norm_toEuclideanLin_le M _
  rw [← Complex.sub_re, e]
  calc |(⟪φ - ψ, toEuclideanLin M φ⟫_ℂ + ⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ).re|
      ≤ ‖⟪φ - ψ, toEuclideanLin M φ⟫_ℂ + ⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ‖ :=
        Complex.abs_re_le_norm _
    _ ≤ ‖⟪φ - ψ, toEuclideanLin M φ⟫_ℂ‖ + ‖⟪ψ, toEuclideanLin M (φ - ψ)⟫_ℂ‖ := norm_add_le _ _
    _ ≤ 2 * ‖M‖ * ‖φ - ψ‖ := by linarith

/-- **Normalizing the image under one projection.** If the orthogonal projection `Q` moves the
unit vector `ψ` by at most `b`, the normalized image `Q ψ / ‖Q ψ‖` is within `2 b` of `ψ`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 686–689, for one projection. -/
theorem norm_inv_norm_smul_toEuclideanLin_sub_le_two_mul {Q : Matrix ι ι ℂ}
    {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) {b : ℝ} (h : ‖ψ - toEuclideanLin Q ψ‖ ≤ b) :
    ‖((‖toEuclideanLin Q ψ‖⁻¹ : ℝ) : ℂ) • toEuclideanLin Q ψ - ψ‖ ≤ 2 * b := by
  refine (norm_inv_norm_smul_sub_le hψ).trans ?_
  rw [norm_sub_rev]
  linarith

/-- **A state of the final level with nearly the ground-state energy.** Let `Q` be an orthogonal
projection that moves the unit vector `Ψ` by at most `b < 1`. Then some unit vector `φ` with
`Q φ = φ` satisfies `re⟨φ, M φ⟩ ≤ re⟨Ψ, M Ψ⟩ + 4 ‖M‖ b` for every operator `M`; it is the
normalized image `Q Ψ / ‖Q Ψ‖`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 709–720, eq. `hchy`, with the restriction of the module docstring. -/
theorem exists_mem_range_re_inner_le_add {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    {Ψ : EuclideanSpace ℂ ι} (hΨ : ‖Ψ‖ = 1) {b : ℝ} (h : ‖Ψ - toEuclideanLin Q Ψ‖ ≤ b)
    (hb : b < 1) :
    ∃ φ : EuclideanSpace ℂ ι, ‖φ‖ = 1 ∧ toEuclideanLin Q φ = φ ∧ ‖φ - Ψ‖ ≤ 2 * b ∧
      ∀ M : Matrix ι ι ℂ,
        (⟪φ, toEuclideanLin M φ⟫_ℂ).re ≤ (⟪Ψ, toEuclideanLin M Ψ⟫_ℂ).re + 4 * ‖M‖ * b := by
  set v := toEuclideanLin Q Ψ with hv
  have hv0 : 0 < ‖v‖ := by
    have := norm_sub_norm_le Ψ (Ψ - v)
    rw [sub_sub_cancel, hΨ] at this
    linarith
  set φ : EuclideanSpace ℂ ι := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hφdef
  have hφ : ‖φ‖ = 1 := by
    rw [hφdef, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hv0.ne']
  have hQφ : toEuclideanLin Q φ = φ := by
    have hQQ : toEuclideanLin Q (toEuclideanLin Q Ψ) = toEuclideanLin Q Ψ := by
      rw [← toEuclideanLin_mul_apply, hQ.isIdempotentElem.eq]
    rw [hφdef, map_smul, hv, hQQ]
  have hd : ‖φ - Ψ‖ ≤ 2 * b := norm_inv_norm_smul_toEuclideanLin_sub_le_two_mul hΨ h
  refine ⟨φ, hφ, hQφ, hd, fun M ↦ ?_⟩
  have hE := abs_re_inner_sub_re_inner_le M hφ hΨ
  have hM := norm_nonneg M
  have : 2 * ‖M‖ * ‖φ - Ψ‖ ≤ 4 * ‖M‖ * b := by nlinarith
  linarith [le_abs_self ((⟪φ, toEuclideanLin M φ⟫_ℂ).re - (⟪Ψ, toEuclideanLin M Ψ⟫_ℂ).re)]

/-- **Eq. `hchy`.** Let `Q` be an orthogonal projection that moves the unit vector `Ψ` by at most
`b < 1`, and let `M = ∑_{i<N} M_i` with `‖M_i‖ ≤ J`. Then some unit vector `φ` with `Q φ = φ`
has `re⟨φ, M φ⟩ ≤ re⟨Ψ, M Ψ⟩ + 4 N J b`. With `Q` the projection onto the final states and
`b = b_h`, this is eq. `hchy` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 709–720, with the explicit constant `4 N J b_h` and the restriction of the module
docstring. -/
theorem exists_mem_range_re_inner_sum_le_add {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    {Ψ : EuclideanSpace ℂ ι} (hΨ : ‖Ψ‖ = 1) {b : ℝ} (h : ‖Ψ - toEuclideanLin Q Ψ‖ ≤ b)
    (hb : b < 1) {N : ℕ} (Mi : Fin N → Matrix ι ι ℂ) {J : ℝ} (hJ : ∀ i, ‖Mi i‖ ≤ J) :
    ∃ φ : EuclideanSpace ℂ ι, ‖φ‖ = 1 ∧ toEuclideanLin Q φ = φ ∧
      (⟪φ, toEuclideanLin (∑ i, Mi i) φ⟫_ℂ).re ≤
        (⟪Ψ, toEuclideanLin (∑ i, Mi i) Ψ⟫_ℂ).re + 4 * N * J * b := by
  obtain ⟨φ, hφ, hQφ, -, hE⟩ := exists_mem_range_re_inner_le_add hQ hΨ h hb
  refine ⟨φ, hφ, hQφ, (hE _).trans ?_⟩
  have hb0 : 0 ≤ b := (norm_nonneg _).trans h
  have hsum : ‖∑ i, Mi i‖ ≤ N * J := by
    refine (norm_sum_le _ _).trans ?_
    simpa using Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ hJ i
  have : 4 * ‖∑ i, Mi i‖ * b ≤ 4 * (N * J) * b := by
    have := mul_le_mul_of_nonneg_right hsum hb0
    nlinarith
  linarith

end Matrix
