/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

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
* `Submodule.starProjection_inf_of_commute`, `Submodule.IsCloseTo.inf_of_commute`: the operator
  step of Lemma `l:t`.
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

/-- A projection preimage with both the source norm bound and the sharper squared-norm
bound. The compression inverse used in ALVV, arXiv:1602.08828v2, Lemma `l:2`,
lines 449–465, also gives the second estimate by its quadratic form. This auxiliary
retains the same witness in both inequalities. -/
theorem IsCloseTo.exists_mem_starProjection_eq_and_norm_sq_le
    {δ : ℝ} {S T : Submodule 𝕜 E} (h : IsCloseTo δ S T) (hδ : δ < 1)
    {t : E} (ht : t ∈ T) :
    ∃ s ∈ S, T.starProjection s = t ∧ ‖s‖ ≤ ‖t‖ / (1 - δ) ∧
      ‖s‖ ^ 2 ≤ ‖t‖ ^ 2 / (1 - δ) := by
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
  -- `(1 - δ) ‖r‖² ≤ ‖P_S r‖² = re ⟪t, r⟫ ≤ ‖t‖ ‖r‖`
  have h1 := hv r r.2
  have h2 : ‖S.starProjection r‖ ^ 2 ≤ ‖t‖ * ‖(r : E)‖ := by
    rw [← hform r]
    refine (RCLike.re_le_norm _).trans ?_
    rw [show (f r : E) = t from hrt]
    exact norm_inner_le_norm _ _
  have hr_bound : ‖(r : E)‖ ≤ ‖t‖ / (1 - δ) := by
    rw [le_div_iff₀ hc]
    rcases eq_or_lt_of_le (norm_nonneg (r : E)) with hzero | hpos
    · rw [← hzero, zero_mul]
      exact norm_nonneg _
    · have hb : (1 - δ) * ‖(r : E)‖ ^ 2 ≤ ‖t‖ * ‖(r : E)‖ := h1.trans h2
      nlinarith
  refine ⟨S.starProjection r, S.starProjection_apply_mem _, hrt,
    (S.norm_starProjection_apply_le _).trans hr_bound, ?_⟩
  calc
    ‖S.starProjection r‖ ^ 2 ≤ ‖t‖ * ‖(r : E)‖ := h2
    _ ≤ ‖t‖ * (‖t‖ / (1 - δ)) :=
      mul_le_mul_of_nonneg_left hr_bound (norm_nonneg _)
    _ = ‖t‖ ^ 2 / (1 - δ) := by ring

/-- **Lemma `l:2`.** If `S` is `δ`-close to `T` with `δ < 1`, then every `t ∈ T` is the
projection `P_T s` of some `s ∈ S` with `‖s‖ ≤ ‖t‖ / (1 - δ)`. For `S ⊗ H_B` in place of `S`
this is Lemma `l:2` of Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2 (lines 449–465):
every unit `t` of `T` is `P_T s` with `s ∈ S ⊗ H_B` and `‖s‖ ≤ 1 / (1 - δ)`. -/
theorem IsCloseTo.exists_mem_starProjection_eq {δ : ℝ} {S T : Submodule 𝕜 E}
    (h : IsCloseTo δ S T) (hδ : δ < 1) {t : E} (ht : t ∈ T) :
    ∃ s ∈ S, T.starProjection s = t ∧ ‖s‖ ≤ ‖t‖ / (1 - δ) := by
  obtain ⟨u, hu, hproj, hnorm, _⟩ := h.exists_mem_starProjection_eq_and_norm_sq_le hδ ht
  exact ⟨u, hu, hproj, hnorm⟩

/-- Weighted composition of closeness. The free positive parameter keeps the coefficient
of the first error arbitrarily close to one. This refines the projection argument in
ALVV, arXiv:1602.08828v2, Lemma `l:close`, lines 484–489. -/
theorem IsCloseTo.trans_weighted {δ δ' θ : ℝ} {T T' T'' : Submodule 𝕜 E} (h : IsCloseTo δ T T')
    (h' : IsCloseTo δ' T' T'') (hδ : 0 ≤ δ) (hθ : 0 < θ) :
    IsCloseTo ((1 + θ) * δ + (1 + 1 / θ) * δ') T T'' := by
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
  have hac : ‖a - c‖ ^ 2 ≤ ((1 + θ) * δ + (1 + 1 / θ) * δ') * ‖a‖ ^ 2 := by
    have htri : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := norm_sub_le_norm_sub_add_norm_sub a b c
    have hyoung : 2 * ‖a - b‖ * ‖b - c‖ ≤
        θ * ‖b - c‖ ^ 2 + ‖a - b‖ ^ 2 / θ := by
      apply (mul_le_mul_iff_right₀ hθ).mp
      field_simp
      nlinarith [sq_nonneg (θ * ‖b - c‖ - ‖a - b‖)]
    have hsq : ‖a - c‖ ^ 2 ≤
        (1 + θ) * ‖b - c‖ ^ 2 + (1 + 1 / θ) * ‖a - b‖ ^ 2 := by
      simp only [div_eq_mul_inv] at hyoung ⊢
      nlinarith [norm_nonneg (a - c), norm_nonneg (a - b), norm_nonneg (b - c)]
    calc
      ‖a - c‖ ^ 2 ≤ _ := hsq
      _ ≤ (1 + θ) * (δ * ‖a‖ ^ 2) + (1 + 1 / θ) * (δ' * ‖a‖ ^ 2) := by
        gcongr
      _ = _ := by ring
  have hpy := norm_sq_eq_add_norm_sq_starProjection a T
  rw [starProjection_orthogonal_val] at hpy
  nlinarith

/-- **Composition of closeness.** This is the factor-two specialization of weighted
composition used in ALVV, arXiv:1602.08828v2, Lemma `l:close`, lines 484–489. -/
theorem IsCloseTo.trans {δ δ' : ℝ} {T T' T'' : Submodule 𝕜 E} (h : IsCloseTo δ T T')
    (h' : IsCloseTo δ' T' T'') (hδ : 0 ≤ δ) :
    IsCloseTo (2 * (δ + δ')) T T'' := by
  simpa only [div_one, one_add_one_eq_two, mul_add] using
    h.trans_weighted h' hδ (show (0 : ℝ) < 1 by norm_num)

/-- **The projection onto an intersection.** If the projections onto `U₁` and `U₂` commute, the
projection onto `U₁ ⊓ U₂` is their product. -/
theorem starProjection_inf_of_commute {U₁ U₂ : Submodule 𝕜 E}
    (h : Commute U₁.starProjection U₂.starProjection) :
    (U₁ ⊓ U₂).starProjection = U₁.starProjection * U₂.starProjection := by
  ext x
  have hcomm : U₁.starProjection (U₂.starProjection x) = U₂.starProjection (U₁.starProjection x) :=
    congrArg (fun A : E →L[𝕜] E => A x) h.eq
  refine (U₁ ⊓ U₂).eq_starProjection_of_mem_of_inner_eq_zero ⟨U₁.starProjection_apply_mem _, ?_⟩
    fun w hw => ?_
  · change U₁.starProjection (U₂.starProjection x) ∈ U₂
    rw [hcomm]
    exact U₂.starProjection_apply_mem _
  · change ⟪x - U₁.starProjection (U₂.starProjection x), w⟫_𝕜 = 0
    rw [inner_sub_left, U₁.inner_starProjection_left_eq_right,
      U₁.starProjection_eq_self_iff.mpr hw.1, U₂.inner_starProjection_left_eq_right,
      U₂.starProjection_eq_self_iff.mpr hw.2, sub_self]

/-- **The operator step of Lemma `l:t` (tensoring).** If `U₁` is `δ₁`-close and `U₂` is
`δ₂`-close to `T`, and the projections onto `U₁` and `U₂` commute, then `U₁ ⊓ U₂` is
`(δ₁ + δ₂)`-close to `T`. For viable sets `S₁`, `S₂` on disjoint subsystems,
`U_k = S_k ⊗ H_{rest}` have commuting projections and
`U₁ ⊓ U₂ = (S₁ ⊗ S₂) ⊗ H_{rest}`, so `S₁ ⊗ S₂` is `(δ₁ + δ₂)`-viable. Arad, Landau, Vazirani
and Vidick, arXiv:1602.08828v2, proof of Lemma `l:t` (lines 506–523); the tensor-product
statement itself is not formalized here. -/
theorem IsCloseTo.inf_of_commute {δ₁ δ₂ : ℝ} {U₁ U₂ T : Submodule 𝕜 E}
    (h₁ : IsCloseTo δ₁ U₁ T) (h₂ : IsCloseTo δ₂ U₂ T)
    (hc : Commute U₁.starProjection U₂.starProjection) :
    IsCloseTo (δ₁ + δ₂) (U₁ ⊓ U₂) T := by
  rw [isCloseTo_iff] at h₁ h₂ ⊢
  intro t ht
  rw [starProjection_inf_of_commute hc]
  set P₁ := U₁.starProjection
  set P₂ := U₂.starProjection
  -- `P₁ t = P₁ P₂ t + P₁ (t - P₂ t)`, an orthogonal sum
  have hsplit : P₁ t = P₁ (P₂ t) + P₁ (t - P₂ t) := by rw [← map_add, add_sub_cancel]
  have horth : ⟪P₁ (P₂ t), P₁ (t - P₂ t)⟫_𝕜 = 0 := by
    have hcomm : P₁ (P₂ t) = P₂ (P₁ t) := congrArg (fun A : E →L[𝕜] E => A t) hc.eq
    rw [← U₁.inner_starProjection_left_eq_right,
      U₁.starProjection_eq_self_iff.mpr (U₁.starProjection_apply_mem _), hcomm,
      U₂.inner_starProjection_left_eq_right, map_sub,
      U₂.starProjection_eq_self_iff.mpr (U₂.starProjection_apply_mem _), sub_self, inner_zero_right]
  have hpy : ‖P₁ t‖ ^ 2 = ‖P₁ (P₂ t)‖ ^ 2 + ‖P₁ (t - P₂ t)‖ ^ 2 := by
    rw [hsplit, sq, sq, sq]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hc₁ : ‖P₁ (t - P₂ t)‖ ≤ ‖t - P₂ t‖ := U₁.norm_starProjection_apply_le _
  have hc₂ : ‖t - P₂ t‖ ^ 2 = ‖t‖ ^ 2 - ‖P₂ t‖ ^ 2 := by
    have := norm_sq_eq_add_norm_sq_starProjection t U₂
    rw [starProjection_orthogonal_val] at this
    linarith
  have e1 := h₁ t ht
  have e2 := h₂ t ht
  have : ‖P₁ (t - P₂ t)‖ ^ 2 ≤ ‖t - P₂ t‖ ^ 2 := by gcongr
  change _ ≤ ‖P₁ (P₂ t)‖ ^ 2
  linarith

end Submodule

section ViableProjectionNonzero

/-!
# Nonzero projections from a close target

A closeness loss below one makes the orthogonal projection injective on
its target. In particular, projecting a nonzero target vector gives a
nonzero candidate vector. This is a finite-dimensional consequence of
ALVV, arXiv:1602.08828v2, the vector characterization of closeness at
line 488, used for the trial vectors in lines 1631 and 1807.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Loss below one preserves nonzero vectors under the actual projection.
Auxiliary to ALVV, arXiv:1602.08828v2, the vector characterization of
closeness at line 488 and the trial-vector step at line 1807. -/
theorem IsCloseTo.starProjection_ne_zero {delta : ℝ} {U T : Submodule 𝕜 E}
    (h : IsCloseTo delta U T) (hdelta : delta < 1) {t : E}
    (ht : t ∈ T) (htne : t ≠ 0) : U.starProjection t ≠ 0 := by
  intro hz
  have hh := (isCloseTo_iff.mp h) t ht
  rw [hz, norm_zero, zero_pow two_ne_zero] at hh
  have hp : 0 < (1 - delta) * ‖t‖ ^ 2 :=
    mul_pos (sub_pos.mpr hdelta) (sq_pos_of_pos (norm_pos_iff.mpr htne))
  exact (not_lt_of_ge hh) hp

end Submodule

end ViableProjectionNonzero

section ViableSubspaceDimension

/-!
# Dimensions of mutually approximating subspaces

If one subspace approximates another with squared projection loss below one,
the approximating subspace has at least the dimension of the other. Thus two
nested subspaces that approximate a third in opposite directions coincide.
Every intermediate subspace retains both approximation estimates.

These finite-dimensional consequences of ALVV, arXiv:1602.08828v2, Lemma `l:2`,
lines 449–465, give the dimension comparison used in the proof of Theorem
`t:ais`, line 1020. They impose no one-dimensional or nonzero-space condition.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A subspace approximated with error below one has no larger dimension than
its approximating subspace. This is a finite-dimensional consequence of ALVV,
arXiv:1602.08828v2, Lemma `l:2`, lines 449–465. -/
theorem IsCloseTo.finrank_le {δ : ℝ} {U T : Submodule 𝕜 E}
    (h : IsCloseTo δ U T) (hδ : δ < 1) :
    Module.finrank 𝕜 T ≤ Module.finrank 𝕜 U := by
  let f : U →ₗ[𝕜] T := T.orthogonalProjectionOnto.toLinearMap.comp U.subtype
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨u, hu, hut, _⟩ := h.exists_mem_starProjection_eq hδ t.property
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    change T.starProjection u = (t : E)
    exact hut
  exact LinearMap.finrank_le_finrank_of_surjective hf

/-- If two nested subspaces approximate a third in opposite directions with
errors below one, then they coincide. Every intermediate subspace is the same
space and retains both approximation bounds. This supplies the dimension step
for the hard-truncation argument in ALVV, arXiv:1602.08828v2, proof of
Theorem `t:ais`, line 1020; no Hamiltonian conclusion is asserted here. -/
theorem eq_and_isCloseTo_of_le {δ δ' : ℝ} {U V G : Submodule 𝕜 E}
    (hUV : U ≤ V) (hUG : IsCloseTo δ U G) (hGV : IsCloseTo δ' G V)
    (hδ : δ < 1) (hδ' : δ' < 1) :
    U = V ∧ ∀ W : Submodule 𝕜 E, U ≤ W → W ≤ V →
      W = U ∧ IsCloseTo δ W G ∧ IsCloseTo δ' G W := by
  have hdim : Module.finrank 𝕜 V ≤ Module.finrank 𝕜 U :=
    (hGV.finrank_le hδ').trans (hUG.finrank_le hδ)
  have hEq : U = V := Submodule.eq_of_le_of_finrank_le hUV hdim
  refine ⟨hEq, ?_⟩
  intro W hUW hWV
  have hWU : W = U := le_antisymm (hWV.trans (le_of_eq hEq.symm)) hUW
  refine ⟨hWU, ?_, ?_⟩
  · simpa only [hWU] using hUG
  · simpa only [hWU, hEq] using hGV

end Submodule

end ViableSubspaceDimension

section ViableSubspaceOrder

/-!
# Closeness from inclusion of subspaces

A subspace containing a target has zero projection loss on that target.
It is therefore close to the target at every nonnegative error parameter.
This includes self-closeness as the equality case. Closeness is also
monotone in its error parameter. These are supporting
projection identities for ALVV, arXiv:1602.08828v2, Lemma `l:close`,
lines 484–489, and the short-region alternatives to Theorems `t:ais`
and `t:aisgapless`, lines 1010–1041.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Closeness is monotone in the parameter: a `δ`-close subspace is `δ'`-close for `δ ≤ δ'`. -/
theorem IsCloseTo.of_le {δ δ' : ℝ} {U T : Submodule 𝕜 E} (h : IsCloseTo δ U T) (hδ : δ ≤ δ') :
    IsCloseTo δ' U T := by
  rw [isCloseTo_iff] at h ⊢
  intro t ht
  refine le_trans ?_ (h t ht)
  nlinarith [sq_nonneg ‖t‖]

/-- Inclusion gives closeness at every nonnegative error parameter.
In particular a target is close to itself. Auxiliary to ALVV,
arXiv:1602.08828v2, Lemma `l:close`, lines 484–489. -/
theorem isCloseTo_of_le {delta : ℝ} {U T : Submodule 𝕜 E}
    (hdelta : 0 ≤ delta) (hTU : T ≤ U) : IsCloseTo delta U T := by
  apply isCloseTo_iff.mpr
  intro x hx
  rw [U.starProjection_eq_self_iff.mpr (hTU hx)]
  exact mul_le_of_le_one_left (sq_nonneg _) (by linarith only [hdelta])

end Submodule

end ViableSubspaceOrder

section ViableSubspaceSymmetry

/-!
# Symmetry of closeness in equal dimension

For two finite-dimensional subspaces of the same dimension, the squared
projection loss is the same in both directions. This is the geometric
symmetry used when comparing the Ritz space and the original ground space
in ALVV, arXiv:1602.08828v2, Definition `d:close`, lines 469–474, and the
last step of `t:alg1`, lines 1811–1817. No Hamiltonian conclusion is assumed.
-/

open scoped InnerProductSpace

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Closeness is symmetric for subspaces of equal dimension, with the same
squared error. This supports the equal-dimension ground-space comparison
in ALVV, arXiv:1602.08828v2, Definition `d:close` and `t:alg1`, lines 1811–1817.
Zero subspaces and arbitrary real error parameters are included. -/
theorem IsCloseTo.symm_of_finrank_eq {δ : ℝ} {U T : Submodule 𝕜 E}
    (h : IsCloseTo δ U T) (hdim : Module.finrank 𝕜 U = Module.finrank 𝕜 T) :
    IsCloseTo δ T U := by
  by_cases hδ : δ < 1
  · have hc : 0 < 1 - δ := sub_pos.mpr hδ
    have hvec := isCloseTo_iff.mp h
    let f : T →ₗ[𝕜] U := U.orthogonalProjectionOnto.toLinearMap.comp T.subtype
    have hfinj : Function.Injective f := by
      apply LinearMap.ker_eq_bot.mp
      apply eq_bot_iff.mpr
      intro t ht
      have hzero : U.starProjection (t : E) = 0 := by
        have heq := congrArg Subtype.val (LinearMap.mem_ker.mp ht)
        exact heq
      have hsq : ‖(t : E)‖ ^ 2 ≤ 0 := by
        apply _root_.le_of_mul_le_mul_left ?_ hc
        simpa only [hzero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] using
          hvec t t.property
      have htzero : (t : E) = 0 := by
        apply norm_eq_zero.mp
        nlinarith only [hsq, norm_nonneg (t : E)]
      simpa only [Submodule.mem_bot] using (Subtype.ext htzero : t = 0)
    have hfsurj : Function.Surjective f :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim.symm).mp hfinj
    apply isCloseTo_iff.mpr
    intro u hu
    by_cases hu0 : u = 0
    · simp only [hu0, map_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero,
        le_refl]
    obtain ⟨t, ht⟩ := hfsurj ⟨u, hu⟩
    have hproj : U.starProjection (t : E) = u := congrArg Subtype.val ht
    have htnorm : (1 - δ) * ‖(t : E)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      simpa only [hproj] using hvec t t.property
    have hpair : ⟪(t : E), u⟫_𝕜 = ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
      calc
        ⟪(t : E), u⟫_𝕜 = ⟪U.starProjection (t : E), u⟫_𝕜 := by
          rw [U.inner_starProjection_left_eq_right, U.starProjection_eq_self_iff.mpr hu]
        _ = ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
          rw [hproj, inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]
    have hpairT : ⟪(t : E), T.starProjection u⟫_𝕜 = ((‖u‖ ^ 2 : ℝ) : 𝕜) := by
      rw [← T.inner_starProjection_left_eq_right,
        T.starProjection_eq_self_iff.mpr t.property]
      exact hpair
    have hCS : ‖u‖ ^ 2 ≤ ‖(t : E)‖ * ‖T.starProjection u‖ := by
      have hbound := re_inner_le_norm (𝕜 := 𝕜) (t : E) (T.starProjection u)
      rwa [hpairT, RCLike.ofReal_re] at hbound
    have hsq : (‖u‖ ^ 2) ^ 2 ≤ ‖(t : E)‖ ^ 2 * ‖T.starProjection u‖ ^ 2 := by
      simpa only [mul_pow] using pow_le_pow_left₀ (sq_nonneg ‖u‖) hCS 2
    have hprod : ((1 - δ) * ‖u‖ ^ 2) * ‖u‖ ^ 2 ≤
        ‖T.starProjection u‖ ^ 2 * ‖u‖ ^ 2 := by
      calc
        _ = (1 - δ) * (‖u‖ ^ 2) ^ 2 := by simp only [pow_two, mul_assoc]
        _ ≤ (1 - δ) * (‖(t : E)‖ ^ 2 * ‖T.starProjection u‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq hc.le
        _ = ((1 - δ) * ‖(t : E)‖ ^ 2) * ‖T.starProjection u‖ ^ 2 :=
          (mul_assoc _ _ _).symm
        _ ≤ ‖u‖ ^ 2 * ‖T.starProjection u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right htnorm (sq_nonneg _)
        _ = ‖T.starProjection u‖ ^ 2 * ‖u‖ ^ 2 := mul_comm _ _
    exact _root_.le_of_mul_le_mul_right hprod (sq_pos_of_pos (norm_pos_iff.mpr hu0))
  · apply isCloseTo_iff.mpr
    intro u _hu
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hδ))
      (sq_nonneg ‖u‖)).trans (sq_nonneg _)

end Submodule

end ViableSubspaceSymmetry

section ViableSubspaceUnitApproximation

/-!
# Normalized projections from close subspaces

For a unit vector in the target of a close subspace, its orthogonal projection
is nonzero. Normalizing that projection preserves the squared-overlap bound
and fixes the phase: the inner product with the original vector is a
nonnegative real number. The squared distance is at most twice the closeness
error. These are vector consequences of ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474.
-/

open scoped InnerProductSpace ComplexOrder

namespace Submodule

/-- A unit target vector admits its normalized orthogonal projection in the
approximating subspace. The projection has squared overlap at least `1 - δ`,
its phase is aligned with the target, and its squared distance is at most
`2 * δ`. This is the vector interpretation of ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474. -/
theorem IsCloseTo.exists_unit_mem_norm_inner_sq_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {δ : ℝ} {S T : Submodule ℂ E}
    (h : IsCloseTo δ S T) (hδ : δ < 1) {ψ : E} (hψT : ψ ∈ T) (hψ : ‖ψ‖ = 1) :
    ∃ φ : E, φ ∈ S ∧ ‖φ‖ = 1 ∧ 1 - δ ≤ ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ∧
      ⟪φ, ψ⟫_ℂ = ((‖S.starProjection ψ‖ : ℝ) : ℂ) ∧
      ‖φ - ψ‖ ^ 2 ≤ 2 * δ ∧
      φ = ((‖S.starProjection ψ‖⁻¹ : ℝ) : ℂ) • S.starProjection ψ := by
  let p := S.starProjection ψ
  have hproj : 1 - δ ≤ ‖p‖ ^ 2 := by
    simpa only [hψ, one_pow, mul_one] using isCloseTo_iff.mp h ψ hψT
  have hp : 0 < ‖p‖ := by nlinarith [norm_nonneg p]
  have hpp : ⟪p, ψ⟫_ℂ = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
    have he : S.starProjection p = p :=
      S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem ψ)
    have hinner : ⟪p, ψ⟫_ℂ = ⟪p, p⟫_ℂ := by
      calc
        ⟪p, ψ⟫_ℂ = ⟪S.starProjection p, ψ⟫_ℂ := by rw [he]
        _ = ⟪p, S.starProjection ψ⟫_ℂ := S.inner_starProjection_left_eq_right _ _
    rw [hinner, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  let φ := ((‖p‖⁻¹ : ℝ) : ℂ) • p
  have hφ : ‖φ‖ = 1 := by
    dsimp only [φ]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hp,
      inv_mul_cancel₀ hp.ne']
  have hinner : ⟪φ, ψ⟫_ℂ = ((‖p‖ : ℝ) : ℂ) := by
    dsimp only [φ]
    rw [inner_smul_left, hpp, Complex.conj_ofReal, ← Complex.ofReal_mul]
    congr 1
    rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
  have hoverlap : ‖⟪φ, ψ⟫_ℂ‖ = ‖p‖ := by
    rw [hinner, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  refine ⟨φ, S.smul_mem _ (S.starProjection_apply_mem ψ), hφ,
    by simpa only [hoverlap] using hproj, hinner, ?_, rfl⟩
  have hple : ‖p‖ ≤ 1 := by simpa only [hψ] using S.norm_starProjection_apply_le ψ
  have hsq : ‖p‖ ^ 2 ≤ ‖p‖ := by nlinarith [norm_nonneg p]
  rw [norm_sub_sq (𝕜 := ℂ), hφ, hψ, hinner]
  change 1 ^ 2 - 2 * ‖p‖ + 1 ^ 2 ≤ 2 * δ
  nlinarith

end Submodule

end ViableSubspaceUnitApproximation
