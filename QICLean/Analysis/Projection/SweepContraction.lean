/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Projection.DetectabilityLemma

/-!
# Contraction of one sweep of projections

Let `h_0, …, h_{m-1}` be orthogonal projections on a complete inner product space, each failing
to commute with at most `d` of the others, and let `Ω` be a vector annihilated by all of them:
the terms of a frustration-free Hamiltonian with ground vector `Ω`. Suppose that `∑ h_k ≥ γ` on
the orthogonal complement of `Ω`. The sweep `D = (1 - h_{m-1}) ⋯ (1 - h_0)` fixes `Ω`, maps the
complement of `Ω` to itself, and contracts it by the factor

`θ = (1 + γ / (d + 1)²)^{-1/2}`,

so that `‖D^t v‖ ≤ θ^t ‖v‖` for every `v ⟂ Ω`. This is the spectral gap amplification of Anshu,
Arad and Vidick, derived from the detectability lemma
`ContinuousLinearMap.re_inner_sum_complementProd_le`.

Every hypothesis on the projections is required only at the indices `k < m` that the sweep
uses, as in the source, which speaks of a finite family `h_0, …, h_{m-1}`.

## Main statements

* `ContinuousLinearMap.complementProd_apply_of_forall_apply_eq_zero`: the sweep fixes `Ω`.
* `ContinuousLinearMap.inner_complementProd_of_forall_apply_eq_zero`: the sweep preserves the
  overlap with `Ω`.
* `ContinuousLinearMap.norm_sq_complementProd_le_of_gap`: one sweep,
  `((d + 1)² + γ) ‖D v‖² ≤ (d + 1)² ‖v‖²` for `v ⟂ Ω`.
* `ContinuousLinearMap.norm_pow_complementProd_le_of_gap`: `‖D^t v‖ ≤ θ^t ‖v‖` for `v ⟂ Ω`.

## References

* A. Anshu, I. Arad and T. Vidick, *Simple proof of the detectability lemma and spectral gap
  amplification*, Phys. Rev. B 93, 205142 (2016).
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] {h : ℕ → E →L[𝕜] E} {Ω : E}

omit [CompleteSpace E] in
/-- A sweep `(1 - h_{n-1}) ⋯ (1 - h_0)` depends only on its first `n` factors. -/
theorem complementProd_congr {h' : ℕ → E →L[𝕜] E} {n : ℕ} (hh' : ∀ k < n, h k = h' k) :
    complementProd h n = complementProd h' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [complementProd_succ, complementProd_succ, hh' n n.lt_succ_self,
      ih fun k hk ↦ hh' k (Nat.lt_succ_of_lt hk)]

omit [CompleteSpace E] in
/-- A sweep fixes every vector annihilated by its projections. -/
theorem complementProd_apply_of_forall_apply_eq_zero {n : ℕ} (hΩ : ∀ k < n, h k Ω = 0) :
    complementProd h n Ω = Ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [complementProd_succ_apply, ih fun k hk ↦ hΩ k (Nat.lt_succ_of_lt hk),
      hΩ n n.lt_succ_self, sub_zero]

/-- A sweep of projections annihilating `Ω` preserves the overlap with `Ω`. -/
theorem inner_complementProd_of_forall_apply_eq_zero {n : ℕ}
    (hh : ∀ k < n, IsStarProjection (h k)) (hΩ : ∀ k < n, h k Ω = 0) (v : E) :
    ⟪Ω, complementProd h n v⟫_𝕜 = ⟪Ω, v⟫_𝕜 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [complementProd_succ_apply, inner_sub_right,
      ← IsStarProjection.inner_apply_left (hh n n.lt_succ_self), hΩ n n.lt_succ_self,
      inner_zero_left, sub_zero,
      ih (fun k hk ↦ hh k (Nat.lt_succ_of_lt hk)) fun k hk ↦ hΩ k (Nat.lt_succ_of_lt hk)]

open scoped Classical in
/-- **One sweep contracts the complement of the ground vector.** Let `h_0, …, h_{m-1}` be
projections annihilating `Ω`, each failing to commute with at most `d` of the others, with
`γ ‖v‖² ≤ ⟨v, ∑ h_k v⟩` for every `v ⟂ Ω`. Then `((d + 1)² + γ) ‖D v‖² ≤ (d + 1)² ‖v‖²` for
every `v ⟂ Ω`, where `D = (1 - h_{m-1}) ⋯ (1 - h_0)`. Anshu, Arad and Vidick, Phys. Rev. B 93,
205142 (2016), spectral gap amplification. -/
theorem norm_sq_complementProd_le_of_gap {m d : ℕ} (hh : ∀ k < m, IsStarProjection (h k))
    (hΩ : ∀ k < m, h k Ω = 0)
    (hd : ∀ i < m, ((Finset.range m).filter (fun j ↦ j ≠ i ∧ ¬Commute (h i) (h j))).card ≤ d)
    {γ : ℝ} (hgap : ∀ v : E, ⟪Ω, v⟫_𝕜 = 0 →
      γ * ‖v‖ ^ 2 ≤ RCLike.re ⟪v, (∑ i ∈ Finset.range m, h i) v⟫_𝕜)
    {v : E} (hv : ⟪Ω, v⟫_𝕜 = 0) :
    (((d : ℝ) + 1) ^ 2 + γ) * ‖complementProd h m v‖ ^ 2 ≤ ((d : ℝ) + 1) ^ 2 * ‖v‖ ^ 2 := by
  -- The sweep only sees `h 0, …, h (m - 1)`; replace the other entries by `0`.
  set h' : ℕ → E →L[𝕜] E := fun k ↦ if k < m then h k else 0
  have hagree : ∀ k < m, h k = h' k := fun k hk ↦ by simp [h', hk]
  have hh' : ∀ k, IsStarProjection (h' k) := fun k ↦ by
    by_cases hk : k < m
    · simpa [h', hk] using hh k hk
    · simp [h', hk, IsStarProjection.zero]
  have hd' : ∀ i < m,
      ((Finset.range m).filter (fun j ↦ j ≠ i ∧ ¬Commute (h' i) (h' j))).card ≤ d := by
    intro i hi
    refine le_of_eq_of_le (congrArg Finset.card (Finset.filter_congr fun j hj ↦ ?_)) (hd i hi)
    rw [← hagree i hi, ← hagree j (Finset.mem_range.mp hj)]
  have hD : complementProd h m = complementProd h' m := complementProd_congr hagree
  have hsum : ∑ i ∈ Finset.range m, h i = ∑ i ∈ Finset.range m, h' i :=
    Finset.sum_congr rfl fun i hi ↦ hagree i (Finset.mem_range.mp hi)
  have hDL := re_inner_sum_complementProd_le hh' hd' v
  rw [← hD, ← hsum] at hDL
  have hlow := hgap _ ((inner_complementProd_of_forall_apply_eq_zero hh hΩ v).trans hv)
  have hmass : ‖complementProd h m v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    have := sum_norm_sq_apply_complementProd hh' v m
    have : 0 ≤ ∑ k ∈ Finset.range m, ‖h' k (complementProd h' k v)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    rw [hD]
    linarith
  have hd0 : (0 : ℝ) ≤ 2 * d + 1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmass hd0]

open scoped Classical in
/-- **Repeated sweeps contract geometrically.** Under the hypotheses of
`norm_sq_complementProd_le_of_gap` with `0 ≤ γ`, every `v ⟂ Ω` satisfies
`‖D^t v‖ ≤ θ^t ‖v‖` with `θ = (1 + γ / (d + 1)²)^{-1/2}`. Anshu, Arad and Vidick,
Phys. Rev. B 93, 205142 (2016). -/
theorem norm_pow_complementProd_le_of_gap {m d : ℕ} (hh : ∀ k < m, IsStarProjection (h k))
    (hΩ : ∀ k < m, h k Ω = 0)
    (hd : ∀ i < m, ((Finset.range m).filter (fun j ↦ j ≠ i ∧ ¬Commute (h i) (h j))).card ≤ d)
    {γ : ℝ} (hγ : 0 ≤ γ) (hgap : ∀ v : E, ⟪Ω, v⟫_𝕜 = 0 →
      γ * ‖v‖ ^ 2 ≤ RCLike.re ⟪v, (∑ i ∈ Finset.range m, h i) v⟫_𝕜)
    (t : ℕ) {v : E} (hv : ⟪Ω, v⟫_𝕜 = 0) :
    ‖(complementProd h m ^ t) v‖ ≤ (√(1 + γ / ((d : ℝ) + 1) ^ 2))⁻¹ ^ t * ‖v‖ := by
  set D := complementProd h m
  set θ := (√(1 + γ / ((d : ℝ) + 1) ^ 2))⁻¹ with hθ
  have hd1 : (0 : ℝ) < ((d : ℝ) + 1) ^ 2 := by positivity
  have hs : (0 : ℝ) < √(1 + γ / ((d : ℝ) + 1) ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  have hθ0 : 0 ≤ θ := inv_nonneg.mpr hs.le
  have hone : ∀ w : E, ⟪Ω, w⟫_𝕜 = 0 → ‖D w‖ ≤ θ * ‖w‖ := by
    intro w hw
    have key := norm_sq_complementProd_le_of_gap hh hΩ hd hgap hw
    have hsq : (√(1 + γ / ((d : ℝ) + 1) ^ 2)) ^ 2 = 1 + γ / ((d : ℝ) + 1) ^ 2 :=
      Real.sq_sqrt (by positivity)
    have h2 : (√(1 + γ / ((d : ℝ) + 1) ^ 2) * ‖D w‖) ^ 2 ≤ ‖w‖ ^ 2 := by
      rw [mul_pow, hsq]
      have : (1 + γ / ((d : ℝ) + 1) ^ 2) * ‖D w‖ ^ 2 =
          ((((d : ℝ) + 1) ^ 2 + γ) * ‖D w‖ ^ 2) / ((d : ℝ) + 1) ^ 2 := by
        field_simp
      rw [this, div_le_iff₀ hd1]
      linarith
    have h3 : √(1 + γ / ((d : ℝ) + 1) ^ 2) * ‖D w‖ ≤ ‖w‖ :=
      (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg w) two_ne_zero).mp h2
    rw [hθ, inv_mul_eq_div, le_div_iff₀ hs, mul_comm]
    exact h3
  have horth : ∀ n : ℕ, ⟪Ω, (D ^ n) v⟫_𝕜 = 0 := by
    intro n
    induction n with
    | zero => simpa using hv
    | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, inner_complementProd_of_forall_apply_eq_zero hh hΩ, ih]
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_apply_eq_comp, pow_succ', mul_assoc]
    exact (hone _ (horth t)).trans (mul_le_mul_of_nonneg_left ih hθ0)

end ContinuousLinearMap
