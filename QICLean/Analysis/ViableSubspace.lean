/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Closeness of subspaces

Arad, Landau, Vazirani and Vidick, *Rigorous RG algorithms and area laws for low energy
eigenstates in 1D* (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Section `s:vs`), measure how
well a subspace approximates another through projections. A subspace `T` is `δ`-close to `T'`
when `P_{T'} P_T P_{T'} ≥ (1 - δ) P_{T'}` (Definition `d:close`, lines 469–474); a subspace `S`
of one factor is `δ`-viable for `T` when `S ⊗ H_B` is `δ`-close to `T` (Definition `d:vs`,
lines 433–440).

The operator inequality says that every vector of `T'` keeps at least the fraction `1 - δ` of its
squared norm when projected onto `T` (`isCloseTo_iff`). Two consequences are used throughout the
source's procedures:

* if `S` is `δ`-close to `T` with `δ < 1`, every `t ∈ T` is the projection `P_T s` of some
  `s ∈ S` with `‖s‖ ≤ ‖t‖ / (1 - δ)` (Lemma `l:2`, lines 449–465);
* closeness is approximately transitive: `δ` and `δ'` give `2 (δ + δ')` (Lemma `l:close`,
  lines 484–489).

The proof of `l:close` in the source (line 488) mixes the names `ν`, `δ'` and `P_{S_ext}`; the
argument is the one written out here.

## Main statements

* `Submodule.IsCloseTo`, `Submodule.isCloseTo_iff`: closeness and its vector form.
* `Submodule.IsCloseTo.exists_mem_starProjection_eq`: Lemma `l:2`.
* `Submodule.IsCloseTo.trans`: Lemma `l:close`.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The subspace `T` is `δ`-close to `T'`: `P_{T'} P_T P_{T'} ≥ (1 - δ) P_{T'}` in the Loewner
order. Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Definition `d:close`
(lines 469–474). For `T = S ⊗ H_B` this is `δ`-viability of `S` for `T'` (Definition `d:vs`,
lines 433–440). -/
def IsCloseTo (δ : ℝ) (T T' : Submodule 𝕜 E) : Prop :=
  ((1 - δ : ℝ) : 𝕜) • T'.starProjection ≤ T'.starProjection * T.starProjection * T'.starProjection

/-- **Closeness as a statement about vectors.** `T` is `δ`-close to `T'` exactly when every
`t ∈ T'` satisfies `(1 - δ) ‖t‖² ≤ ‖P_T t‖²`. Arad, Landau, Vazirani and Vidick,
arXiv:1602.08828v2, the reformulation at the start of the proof of Lemma `l:close` (line 488). -/
theorem isCloseTo_iff {δ : ℝ} {T T' : Submodule 𝕜 E} :
    IsCloseTo δ T T' ↔ ∀ t ∈ T', (1 - δ) * ‖t‖ ^ 2 ≤ ‖T.starProjection t‖ ^ 2 := by
  -- the two quadratic forms, evaluated at any `x`
  have hquad (x : E) :
      RCLike.re ⟪(T'.starProjection * T.starProjection * T'.starProjection -
          ((1 - δ : ℝ) : 𝕜) • T'.starProjection) x, x⟫_𝕜 =
        ‖T.starProjection (T'.starProjection x)‖ ^ 2 -
          (1 - δ) * ‖T'.starProjection x‖ ^ 2 := by
    have e1 : RCLike.re ⟪T'.starProjection (T.starProjection (T'.starProjection x)), x⟫_𝕜 =
        ‖T.starProjection (T'.starProjection x)‖ ^ 2 := by
      rw [T'.inner_starProjection_left_eq_right, T.re_inner_starProjection_eq_normSq,
        ← Submodule.norm_coe, ← T.starProjection_apply]
    have e2 : RCLike.re ⟪((1 - δ : ℝ) : 𝕜) • T'.starProjection x, x⟫_𝕜 =
        (1 - δ) * ‖T'.starProjection x‖ ^ 2 := by
      rw [inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul,
        T'.re_inner_starProjection_eq_normSq, ← Submodule.norm_coe, ← T'.starProjection_apply]
    have e3 : (T'.starProjection * T.starProjection * T'.starProjection -
        ((1 - δ : ℝ) : 𝕜) • T'.starProjection) x =
        T'.starProjection (T.starProjection (T'.starProjection x)) -
          ((1 - δ : ℝ) : 𝕜) • T'.starProjection x := rfl
    rw [e3, inner_sub_left, map_sub, e1, e2]
  constructor
  · intro h t ht
    have hpos := (ContinuousLinearMap.le_def.mp h).re_inner_nonneg_left t
    rw [hquad, T'.starProjection_eq_self_iff.mpr ht] at hpos
    linarith
  · intro h
    have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
    refine ContinuousLinearMap.le_def.mpr ?_
    refine ContinuousLinearMap.isPositive_def'.mpr ⟨?_, fun x => ?_⟩
    · have h1 : IsSelfAdjoint (T'.starProjection * T.starProjection * T'.starProjection) :=
        (isSelfAdjoint_starProjection T).conjugate_self (isSelfAdjoint_starProjection T')
      have hc : IsSelfAdjoint ((1 - δ : ℝ) : 𝕜) := by
        rw [isSelfAdjoint_iff, RCLike.star_def, RCLike.conj_ofReal]
      have h2 : IsSelfAdjoint (((1 - δ : ℝ) : 𝕜) • T'.starProjection) :=
        IsSelfAdjoint.smul hc (isSelfAdjoint_starProjection T')
      exact h1.sub h2
    · rw [ContinuousLinearMap.reApplyInnerSelf_apply, hquad]
      linarith [h _ (T'.starProjection_apply_mem x)]

/-- **Lemma `l:2`.** If `S` is `δ`-close to `T` with `δ < 1`, then every `t ∈ T` is the
projection `P_T s` of some `s ∈ S` with `‖s‖ ≤ ‖t‖ / (1 - δ)`. For `S ⊗ H_B` in place of `S`
this is Lemma `l:2` of Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2 (lines 449–465):
every unit `t` of `T` is `P_T s` with `s ∈ S ⊗ H_B` and `‖s‖ ≤ 1 / (1 - δ)`. -/
theorem IsCloseTo.exists_mem_starProjection_eq {δ : ℝ} {S T : Submodule 𝕜 E}
    (h : IsCloseTo δ S T) (hδ : δ < 1) {t : E} (ht : t ∈ T) :
    ∃ s ∈ S, T.starProjection s = t ∧ ‖s‖ ≤ ‖t‖ / (1 - δ) := by
  have hv := isCloseTo_iff.mp h
  have hc : 0 < 1 - δ := by linarith
  -- the compression `r ↦ P_T P_S r` of `T` into itself
  let f : T →ₗ[𝕜] T :=
    (T.starProjection.toLinearMap ∘ₗ S.starProjection.toLinearMap ∘ₗ T.subtype).codRestrict T
      fun r => T.starProjection_apply_mem _
  have hform (r : T) : RCLike.re ⟪(f r : E), (r : E)⟫_𝕜 = ‖S.starProjection r‖ ^ 2 := by
    change RCLike.re ⟪T.starProjection (S.starProjection r), (r : E)⟫_𝕜 = _
    rw [T.inner_starProjection_left_eq_right, T.starProjection_eq_self_iff.mpr r.2,
      S.re_inner_starProjection_eq_normSq, ← Submodule.norm_coe, ← S.starProjection_apply]
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 := hv r r.2
    have h2 := hform r
    rw [hr, ZeroMemClass.coe_zero, inner_zero_left, map_zero] at h2
    have : ‖(r : E)‖ ^ 2 ≤ 0 := by nlinarith
    exact Subtype.ext (by simpa using this)
  obtain ⟨r, hr⟩ := (LinearMap.injective_iff_surjective.mp hinj) ⟨t, ht⟩
  have hrt : T.starProjection (S.starProjection r) = t := congrArg Subtype.val hr
  refine ⟨S.starProjection r, S.starProjection_apply_mem _, hrt, ?_⟩
  -- `(1 - δ) ‖r‖² ≤ ‖P_S r‖² = re ⟪t, r⟫ ≤ ‖t‖ ‖r‖`
  have h1 := hv r r.2
  have h2 : ‖S.starProjection r‖ ^ 2 ≤ ‖t‖ * ‖(r : E)‖ := by
    rw [← hform r]
    refine (RCLike.re_le_norm _).trans ?_
    rw [show (f r : E) = t from hrt]
    exact norm_inner_le_norm _ _
  have hsr : ‖S.starProjection r‖ ≤ ‖(r : E)‖ := S.norm_starProjection_apply_le _
  rw [le_div_iff₀ hc]
  rcases eq_or_lt_of_le (norm_nonneg (r : E)) with h0 | hpos
  · rw [← h0] at hsr
    have : ‖S.starProjection r‖ = 0 := le_antisymm hsr (norm_nonneg _)
    rw [this, zero_mul]
    exact norm_nonneg _
  · have : (1 - δ) * ‖(r : E)‖ ≤ ‖t‖ := by
      have : (1 - δ) * ‖(r : E)‖ ^ 2 ≤ ‖t‖ * ‖(r : E)‖ := h1.trans h2
      nlinarith
    calc ‖S.starProjection r‖ * (1 - δ) ≤ ‖(r : E)‖ * (1 - δ) := by gcongr
      _ = (1 - δ) * ‖(r : E)‖ := mul_comm _ _
      _ ≤ ‖t‖ := this

/-- **Lemma `l:close`.** If `T` is `δ`-close to `T'` and `T'` is `δ'`-close to `T''`, with
`δ ≥ 0`, then `T` is `2 (δ + δ')`-close to `T''`. With `T = S ⊗ H_B` this is also the
second statement: a `δ`-viable `S` for `T'` is `2 (δ + δ')`-viable for `T''`. Arad, Landau,
Vazirani and Vidick, arXiv:1602.08828v2, lines 484–489. -/
theorem IsCloseTo.trans {δ δ' : ℝ} {T T' T'' : Submodule 𝕜 E} (h : IsCloseTo δ T T')
    (h' : IsCloseTo δ' T' T'') (hδ : 0 ≤ δ) :
    IsCloseTo (2 * (δ + δ')) T T'' := by
  rw [isCloseTo_iff] at h h' ⊢
  intro a ha
  set b := T'.starProjection a
  set c := T.starProjection b
  -- Pythagoras for the two projections
  have hab : ‖a - b‖ ^ 2 ≤ δ' * ‖a‖ ^ 2 := by
    have hpy := norm_sq_eq_add_norm_sq_starProjection a T'
    rw [starProjection_orthogonal_val] at hpy
    have := h' a ha
    nlinarith
  have hbc : ‖b - c‖ ^ 2 ≤ δ * ‖a‖ ^ 2 := by
    have hpy := norm_sq_eq_add_norm_sq_starProjection b T
    rw [starProjection_orthogonal_val] at hpy
    have h1 := h b (T'.starProjection_apply_mem a)
    have hb : ‖b‖ ≤ ‖a‖ := T'.norm_starProjection_apply_le a
    have : ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 := by gcongr
    nlinarith
  -- `P_T a` is at least as close to `a` as `c ∈ T`: `a - c = (a - P_T a) + (P_T a - c)`
  have hmin : ‖a - T.starProjection a‖ ^ 2 ≤ ‖a - c‖ ^ 2 := by
    have hmem : T.starProjection a - c ∈ T :=
      T.sub_mem (T.starProjection_apply_mem a) (T.starProjection_apply_mem b)
    have horth : ⟪a - T.starProjection a, T.starProjection a - c⟫_𝕜 = 0 :=
      T.starProjection_inner_eq_zero a _ hmem
    have hsplit : a - c = (a - T.starProjection a) + (T.starProjection a - c) := by abel
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    rw [← hsplit] at this
    nlinarith [sq_nonneg ‖T.starProjection a - c‖]
  have hac : ‖a - c‖ ^ 2 ≤ 2 * (δ + δ') * ‖a‖ ^ 2 := by
    have htri : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := norm_sub_le_norm_sub_add_norm_sub a b c
    have : ‖a - c‖ ^ 2 ≤ 2 * (‖a - b‖ ^ 2 + ‖b - c‖ ^ 2) := by
      nlinarith [norm_nonneg (a - c), norm_nonneg (a - b), norm_nonneg (b - c),
        sq_nonneg (‖a - b‖ - ‖b - c‖)]
    linarith
  have hpy := norm_sq_eq_add_norm_sq_starProjection a T
  rw [starProjection_orthogonal_val] at hpy
  nlinarith

end Submodule
