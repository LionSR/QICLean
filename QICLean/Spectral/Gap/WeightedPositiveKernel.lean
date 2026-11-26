/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import QICLean.Spectral.Gap.EigenvalueGap

/-!
# Weighted sums of positive operators

Kernel equality and Loewner comparison for strictly positively weighted
finite sums of positive operators.  The
statements are the analytic content of the blocked-sum comparison in
Rozmán--Molnár--Schuch, arXiv:2607.19078v1, Lemma `block-obc`
(statement at main.tex lines 607--651, argument at lines 795--811).  That
source expands the blocked parent Hamiltonian as a weighted sum
$\sum_i \gamma_i h_i$ of positive local terms with real coefficients
$0 < \gamma_i \le 1$: strict positivity of the coefficients preserves the
kernel, and the bound $\gamma_i \le 1$ places the weighted sum below the
unweighted sum in Loewner order.  The source tex is not vendored in this
repository, so the citation is by arXiv identifier and lemma label.

## Main results

* `LinearMap.IsPositive.apply_eq_zero_of_re_inner_eq_zero`: a positive
  operator annihilates a vector as soon as its quadratic form vanishes on
  that vector.
* `WeightedPositiveKernel.ker_weighted_sum_eq_sum`: strictly positive real
  weights do not change the kernel of a finite sum of positive operators;
  `WeightedPositiveKernel.ker_weighted_sum_eq_iInf` identifies the common
  kernel with the intersection of the individual kernels.
* `WeightedPositiveKernel.weighted_sum_le_sum`: weights at most one place the
  weighted sum below the unweighted sum in Loewner order.

Moved from TNLean, `TNLean/MPS/ParentHamiltonian/Gap/Spectator/BoundedProjectionDeformation.lean` at
commit `021ba0bd19` (Apache-2.0).
-/

open scoped InnerProductSpace

namespace LinearMap.IsPositive

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A positive operator annihilates a vector on which its quadratic form
vanishes: `Re ⟪T v, v⟫ = 0` forces `T v = 0`.

The proof uses the positivity of the quadratic form along the real affine
line `t ↦ v + t • (T v)`: it is nonnegative for every real `t`, vanishes at
`t = 0`, and its linear coefficient is `2 * ‖T v‖ ^ 2`, which forces
`‖T v‖ = 0`. -/
theorem apply_eq_zero_of_re_inner_eq_zero {T : E →ₗ[𝕜] E} (hT : T.IsPositive)
    {v : E} (hv : RCLike.re (⟪T v, v⟫_𝕜) = 0) : T v = 0 := by
  by_contra hne
  have hsq : (0 : ℝ) < ‖T v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  have hc : (0 : ℝ) ≤ RCLike.re (⟪T (T v), T v⟫_𝕜) := hT.re_inner_nonneg_left (T v)
  -- The quadratic form is nonnegative along the real affine line, with
  -- constant term `0` and linear coefficient `2 * ‖T v‖ ^ 2`.
  have hline : ∀ t : ℝ,
      0 ≤ 2 * t * (‖T v‖ ^ 2) + t ^ 2 * RCLike.re (⟪T (T v), T v⟫_𝕜) := by
    intro t
    have hpos := hT.re_inner_nonneg_left (v + (t : 𝕜) • T v)
    have hexp : RCLike.re (⟪T (v + (t : 𝕜) • T v), v + (t : 𝕜) • T v⟫_𝕜)
        = 2 * t * (‖T v‖ ^ 2) + t ^ 2 * RCLike.re (⟪T (T v), T v⟫_𝕜) := by
      have hTv : T (v + (t : 𝕜) • T v) = T v + (t : 𝕜) • T (T v) := by
        rw [map_add, map_smul]
      have hsymm : ⟪T (T v), v⟫_𝕜 = ⟪T v, T v⟫_𝕜 := hT.isSymmetric (T v) v
      have hself : RCLike.re (⟪T v, T v⟫_𝕜) = ‖T v‖ ^ 2 := inner_self_eq_norm_sq _
      rw [hTv]
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
        RCLike.conj_ofReal, map_add, RCLike.re_ofReal_mul, hsymm, hself, hv]
      ring
    rwa [hexp] at hpos
  -- At negative times, `2 * t * ‖T v‖ ^ 2 ≤ t ^ 2 * re ⟪T (T v), T v⟫`, so
  -- dividing by any positive `t` gives `2 * ‖T v‖ ^ 2 ≤ t * re ⟪T (T v), T v⟫`.
  have hkey : ∀ t : ℝ, 0 < t →
      2 * (‖T v‖ ^ 2) ≤ t * RCLike.re (⟪T (T v), T v⟫_𝕜) := by
    intro t ht
    have h := hline (-t)
    have h2 : (2 * (‖T v‖ ^ 2)) * t
        ≤ (t * RCLike.re (⟪T (T v), T v⟫_𝕜)) * t := by
      nlinarith [mul_nonneg (sq_nonneg t) hc]
    exact le_of_mul_le_mul_right h2 ht
  -- Evaluate at the positive time `‖T v‖ ^ 2 / (re ⟪T (T v), T v⟫ + 1)`.
  have hden : (0 : ℝ) < RCLike.re (⟪T (T v), T v⟫_𝕜) + 1 := by linarith
  have hsmall := hkey ((‖T v‖ ^ 2) / (RCLike.re (⟪T (T v), T v⟫_𝕜) + 1))
    (div_pos hsq hden)
  have hfrac : ((‖T v‖ ^ 2) / (RCLike.re (⟪T (T v), T v⟫_𝕜) + 1))
      * RCLike.re (⟪T (T v), T v⟫_𝕜) ≤ ‖T v‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [sq_nonneg ‖T v‖]
  linarith

end LinearMap.IsPositive

namespace WeightedPositiveKernel

variable {ι 𝕜 E : Type*} [Fintype ι] [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]

/-- The quadratic form of a weighted sum of operators expands into the
weighted sum of the individual quadratic forms. -/
theorem re_inner_weighted_sum_apply (w : ι → ℝ) (P : ι → E →ₗ[𝕜] E) (v : E) :
    RCLike.re (⟪(∑ i, (w i : 𝕜) • P i) v, v⟫_𝕜) =
      ∑ i, w i * RCLike.re (⟪P i v, v⟫_𝕜) := by
  rw [LinearMap.sum_apply, sum_inner, map_sum (RCLike.re : 𝕜 →+ ℝ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, inner_smul_left, RCLike.conj_ofReal, RCLike.re_ofReal_mul]

/-- A strictly positively weighted sum of positive operators annihilates a
vector exactly when every operator in the sum annihilates it.

With strictly positive weights this is the weighted form of the
blocked-sum kernel comparison in Rozmán--Molnár--Schuch, arXiv:2607.19078v1,
Lemma `block-obc`: expanding the real quadratic form of the weighted sum
gives a sum of nonnegative terms, so its vanishing forces each
`Re ⟪P i v, v⟫` to vanish, and positivity of `P i` then forces `P i v = 0`. -/
theorem apply_weighted_sum_eq_zero_iff {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) (v : E) :
    (∑ i, (w i : 𝕜) • P i) v = 0 ↔ ∀ i, P i v = 0 := by
  constructor
  · intro hsum
    have hre : (∑ i, w i * RCLike.re (⟪P i v, v⟫_𝕜)) = 0 := by
      rw [← re_inner_weighted_sum_apply w P v, hsum]
      simp
    have hterms : (fun i => w i * RCLike.re (⟪P i v, v⟫_𝕜)) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun i => mul_nonneg (le_of_lt (hw i)) ((hP i).re_inner_nonneg_left v))).mp hre
    intro i
    have hterm : w i * RCLike.re (⟪P i v, v⟫_𝕜) = 0 := by
      simpa using congrFun hterms i
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h (ne_of_gt (hw i))
    · exact (hP i).apply_eq_zero_of_re_inner_eq_zero h
  · intro h
    rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.smul_apply, h i]
    simp

/-- A finite sum of positive operators annihilates a vector exactly when
every summand annihilates it. -/
theorem apply_sum_eq_zero_iff {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive)
    (v : E) :
    (∑ i, P i) v = 0 ↔ ∀ i, P i v = 0 := by
  have h := apply_weighted_sum_eq_zero_iff (fun _ : ι => one_pos) hP v
  simpa using h

/-- The kernel of a strictly positively weighted sum of positive operators is
the intersection of the individual kernels. -/
theorem ker_weighted_sum_eq_iInf {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    LinearMap.ker (∑ i, (w i : 𝕜) • P i) = ⨅ i, LinearMap.ker (P i) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact apply_weighted_sum_eq_zero_iff hw hP v

/-- The kernel of a finite sum of positive operators is the intersection of
the individual kernels. -/
theorem ker_sum_eq_iInf {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    LinearMap.ker (∑ i, P i) = ⨅ i, LinearMap.ker (P i) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  exact apply_sum_eq_zero_iff hP v

/-- Strictly positive real weights do not change the kernel of a finite sum
of positive operators. -/
theorem ker_weighted_sum_eq_sum {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    LinearMap.ker (∑ i, (w i : 𝕜) • P i) = LinearMap.ker (∑ i, P i) :=
  (ker_weighted_sum_eq_iInf hw hP).trans (ker_sum_eq_iInf hP).symm

/-- A weighted sum of positive operators with nonnegative real weights is
positive. -/
theorem isPositive_weighted_sum {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    (∑ i, (w i : 𝕜) • P i).IsPositive :=
  LinearMap.isPositive_sum Finset.univ fun i _ =>
    (hP i).smul_of_nonneg (RCLike.ofReal_nonneg.mpr (hw i))

/-- Real weights at most one place the weighted sum below the unweighted sum
in Loewner order.

This is the Loewner comparison of the blocked-sum argument in
Rozmán--Molnár--Schuch, arXiv:2607.19078v1, Lemma `block-obc`: the
difference is the weighted sum with weights `1 - w i`, each nonnegative. -/
theorem weighted_sum_le_sum {w : ι → ℝ} (hw : ∀ i, w i ≤ 1)
    {P : ι → E →ₗ[𝕜] E} (hP : ∀ i, (P i).IsPositive) :
    (∑ i, (w i : 𝕜) • P i) ≤ ∑ i, P i := by
  rw [LinearMap.le_def]
  have hsub : (∑ i, P i) - ∑ i, (w i : 𝕜) • P i
      = ∑ i, ((1 - w i : ℝ) : 𝕜) • P i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.ofReal_sub, RCLike.ofReal_one, sub_smul, one_smul]
  rw [hsub]
  exact isPositive_weighted_sum (fun i => sub_nonneg.mpr (hw i)) hP

end WeightedPositiveKernel

section

open scoped BigOperators InnerProductSpace ComplexOrder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

namespace LinearEquiv

/-- The canonical projection constraint whose kernel is the inverse image
of \(\ker P\) under \(e\). -/
noncomputable def deformedConstraintProjection (e : E ≃ₗ[ℂ] F) (P : F →ₗ[ℂ] F) :
    E →ₗ[ℂ] E :=
  ((LinearMap.ker P).comap e.toLinearMap)ᗮ.starProjection.toLinearMap

/-- Deformed constraints are symmetric projections. -/
theorem deformedConstraintProjection_isSymmetricProjection
    (e : E ≃ₗ[ℂ] F) (P : F →ₗ[ℂ] F) :
    (e.deformedConstraintProjection P).IsSymmetricProjection :=
  Submodule.isSymmetricProjection_starProjection _

/-- The deformed projection has exactly the pulled-back kernel. -/
theorem ker_deformedConstraintProjection (e : E ≃ₗ[ℂ] F) (P : F →ₗ[ℂ] F) :
    LinearMap.ker (e.deformedConstraintProjection P) =
      (LinearMap.ker P).comap e.toLinearMap := by
  simp only [deformedConstraintProjection, Submodule.ker_starProjection,
    Submodule.orthogonal_orthogonal]

/-- Congruence distributes over the finite constraint sum. -/
theorem adjoint_congruence_sum {ι : Type*} [Fintype ι]
    (e : E ≃ₗ[ℂ] F) (P : ι → F →ₗ[ℂ] F) :
    e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap =
      ∑ i, e.toLinearMap.adjoint ∘ₗ P i ∘ₗ e.toLinearMap := by
  ext v
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum]

/-- The sum of the deformed constraints has the pulled-back kernel of the
original positive constraint sum. -/
theorem ker_sum_deformedConstraintProjection {ι : Type*} [Fintype ι]
    (e : E ≃ₗ[ℂ] F) (P : ι → F →ₗ[ℂ] F)
    (hP : ∀ i, (P i).IsPositive) :
    LinearMap.ker (∑ i, e.deformedConstraintProjection (P i)) =
      (LinearMap.ker (∑ i, P i)).comap e.toLinearMap := by
  rw [WeightedPositiveKernel.ker_sum_eq_iInf
    (fun i => (e.deformedConstraintProjection_isSymmetricProjection (P i)).isPositive),
    WeightedPositiveKernel.ker_sum_eq_iInf hP, Submodule.comap_iInf]
  simp only [ker_deformedConstraintProjection]

/-- If \(e\) carries \(S\) onto \(T\), deforming the projection onto \(S^\perp\) by
\(e^{-1}\) gives the projection onto \(T^\perp\), and deforming the projection onto
\(T^\perp\) by \(e\) gives back the projection onto \(S^\perp\). -/
theorem deformedConstraintProjection_orthogonal_of_map_eq
    (e : E ≃ₗ[ℂ] F) (S : Submodule ℂ E) (T : Submodule ℂ F)
    (h : S.map e.toLinearMap = T) :
    e.symm.deformedConstraintProjection Sᗮ.starProjection.toLinearMap =
        Tᗮ.starProjection.toLinearMap ∧
      e.deformedConstraintProjection Tᗮ.starProjection.toLinearMap =
        Sᗮ.starProjection.toLinearMap := by
  constructor
  · simp only [deformedConstraintProjection, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal, Submodule.comap_equiv_eq_map_symm, symm_symm, h]
  · have hsymm := (Submodule.map_symm_eq_iff e).mpr h
    simp only [deformedConstraintProjection, Submodule.ker_starProjection,
      Submodule.orthogonal_orthogonal, Submodule.comap_equiv_eq_map_symm, hsymm]

/-- If \(e(S)=T\), then the conjugate \(U^{-1}eU\) carries \(U^{-1}(S)\) onto
\(U^{-1}(T)\). -/
theorem map_conj_map_symm_of_map_eq {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (U : M ≃ₗ[ℂ] N) (e : N ≃ₗ[ℂ] N) (S T : Submodule ℂ N)
    (h : S.map e.toLinearMap = T) :
    (S.map U.symm.toLinearMap).map (U.trans (e.trans U.symm)).toLinearMap =
      T.map U.symm.toLinearMap := by
  rw [← Submodule.map_comp]
  have heq : (U.trans (e.trans U.symm)).toLinearMap.comp U.symm.toLinearMap =
      U.symm.toLinearMap.comp e.toLinearMap := by ext; simp
  rw [heq, Submodule.map_comp, h]

end LinearEquiv

private theorem symmetricProjection_eq_orthogonal_ker_projection
    {P : F →ₗ[ℂ] F} (hP : P.IsSymmetricProjection) :
    P = (LinearMap.ker P)ᗮ.starProjection.toLinearMap := by
  have hrange : LinearMap.range P = (LinearMap.ker P)ᗮ := by
    rw [← hP.isSymmetric.orthogonal_range, Submodule.orthogonal_orthogonal]
  obtain ⟨_, h⟩ := P.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hP
  simpa only [hrange] using h

namespace LinearMap.IsPositive

/-- A bounded inverse loses at most a factor \(C^2\) in the gap above the kernel of a positive
operator under congruence: if every eigenvalue of `P` other than `0` is at least
\(\delta\ge0\), then every eigenvalue of \(e^*Pe\) other than `0` is at least
\(\delta/C^2\). -/
theorem forall_hasEigenvalue_adjoint_congruence_of_inverse_bound
    {P : F →ₗ[ℂ] F} (hP : P.IsPositive) (e : E ≃ₗ[ℂ] F)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 < C)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue P μ → μ = 0 ∨ (δ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap) μ →
      μ = 0 ∨ ((δ / C ^ 2 : ℝ) : ℂ) ≤ μ := by
  let Q := e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap
  refine (hP.adjoint_conj e.toLinearMap).isSymmetric.forall_hasEigenvalue_of_re_inner
    fun v hv ↦ ?_
  let w := (LinearMap.ker P)ᗮ.starProjection (e v)
  let u := e.symm ((LinearMap.ker P).starProjection (e v))
  have hproj : P ((LinearMap.ker P).starProjection (e v)) = 0 :=
    LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ _)
  have hu : u ∈ LinearMap.ker Q := by
    rw [show LinearMap.ker Q = (LinearMap.ker P).comap e.toLinearMap from
      e.ker_adjoint_congruence P]
    change P (e u) = 0
    simpa only [u, e.apply_symm_apply] using hproj
  have horth : ⟪v, u⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hu hv
  have hdecomp : e.symm w = v - u := by
    simp only [w, u, Submodule.starProjection_orthogonal_val, map_sub, e.symm_apply_apply]
  have hnorm : ‖v‖ ≤ C * ‖w‖ := calc
    ‖v‖ ≤ ‖v - u‖ := by
      have hsq : ‖v - u‖ ^ 2 = ‖v‖ ^ 2 + ‖u‖ ^ 2 := by
        simpa only [horth, RCLike.zero_re, mul_zero, sub_zero] using norm_sub_sq (𝕜 := ℂ) v u
      nlinarith [norm_nonneg (v - u), norm_nonneg v, sq_nonneg ‖u‖]
    _ = ‖e.symm w‖ := congrArg norm hdecomp.symm
    _ ≤ C * ‖w‖ := hInverse w
  have hnormSq : ‖v‖ ^ 2 ≤ C ^ 2 * ‖w‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg v) hnorm 2
  have henergy : (⟪v, Q v⟫_ℂ).re = (⟪w, P w⟫_ℂ).re := by
    change (⟪v, e.toLinearMap.adjoint (P (e v))⟫_ℂ).re = _
    rw [LinearMap.adjoint_inner_right]
    change (⟪e v, P (e v)⟫_ℂ).re = (⟪w, P w⟫_ℂ).re
    simp only [w, Submodule.starProjection_orthogonal_val, map_sub, hproj, sub_zero,
      ← hP.isSymmetric _ (e v)]
  calc
    δ / C ^ 2 * ‖v‖ ^ 2 ≤ δ / C ^ 2 * (C ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hnormSq (by positivity)
    _ = δ * ‖w‖ ^ 2 := by field_simp [ne_of_gt hC]
    _ ≤ (⟪w, P w⟫_ℂ).re := hP.isSymmetric.mul_norm_sq_le_re_inner_of_forall_hasEigenvalue hGap
      (Submodule.starProjection_apply_mem _ _)
    _ = (⟪v, Q v⟫_ℂ).re := henergy.symm

end LinearMap.IsPositive

namespace LinearMap.IsSymmetricProjection

/-- A single deformed constraint and the congruence of its original
projection bound one another with constants determined only by \(B,C\). -/
theorem deformedConstraintProjection_comparison
    {P : F →ₗ[ℂ] F} (hP : P.IsSymmetricProjection) (e : E ≃ₗ[ℂ] F)
    {B C : ℝ} (_hB : 0 < B) (hC : 0 < C)
    (hForward : ∀ v : E, ‖e v‖ ≤ B * ‖v‖)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖) :
    ((1 / C ^ 2 : ℝ) : ℂ) • e.deformedConstraintProjection P ≤
        e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap ∧
      e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap ≤
        ((B ^ 2 : ℝ) : ℂ) • e.deformedConstraintProjection P := by
  let G := e.toLinearMap.adjoint ∘ₗ P ∘ₗ e.toLinearMap
  have hG : G.IsPositive := hP.isPositive.adjoint_conj e.toLinearMap
  have hPproj := symmetricProjection_eq_orthogonal_ker_projection hP
  have hcontract (w : F) : ‖P w‖ ≤ ‖w‖ := by
    rw [hPproj]
    exact Submodule.norm_starProjection_apply_le _ _
  have hunitGap : ∀ w ∈ (LinearMap.ker P)ᗮ, (1 : ℝ) * ‖w‖ ≤ ‖P w‖ := by
    intro w hw
    have hfix : P w = w := by
      rw [hPproj]
      exact Submodule.starProjection_eq_self_iff.mpr hw
    simp [hfix]
  have hGproj : (LinearMap.ker G)ᗮ.starProjection.toLinearMap =
      e.deformedConstraintProjection P := by
    rw [show LinearMap.ker G = (LinearMap.ker P).comap e.toLinearMap from
      e.ker_adjoint_congruence P]
    rfl
  constructor
  · have hgap := hP.isPositive.norm_gap_adjoint_congruence_of_inverse_bound
      e (by norm_num : (0 : ℝ) ≤ 1) hC hInverse hunitGap
    simpa only [hGproj] using
      hG.smul_orthogonal_ker_projection_le_of_norm_gap
        (show 0 ≤ (1 : ℝ) / C ^ 2 by positivity) hgap
  · have hbound (w : E) : (⟪G w, w⟫_ℂ).re ≤ B ^ 2 * ‖w‖ ^ 2 := by
      change (⟪e.toLinearMap.adjoint (P (e w)), w⟫_ℂ).re ≤ _
      rw [LinearMap.adjoint_inner_left]
      calc
        _ ≤ ‖P (e w)‖ * ‖e w‖ := re_inner_le_norm (𝕜 := ℂ) _ _
        _ ≤ ‖e w‖ * ‖e w‖ :=
          mul_le_mul_of_nonneg_right (hcontract (e w)) (norm_nonneg _)
        _ ≤ B ^ 2 * ‖w‖ ^ 2 := by
          simpa only [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            mul_self_le_mul_self (norm_nonneg (e w)) (hForward w)
    rw [← hGproj]
    refine ⟨((LinearMap.ker G)ᗮ.starProjection_isSymmetric.smul (by simp)).sub
      hG.isSymmetric, ?_⟩
    intro v
    have hproj : G ((LinearMap.ker G).starProjection v) = 0 :=
      LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem _ _)
    have henergy : ⟪G v, v⟫_ℂ =
        ⟪G ((LinearMap.ker G)ᗮ.starProjection v),
          (LinearMap.ker G)ᗮ.starProjection v⟫_ℂ := by
      simp only [Submodule.starProjection_orthogonal_val, map_sub,
        hG.isSymmetric v, hproj, sub_zero]
    have hnorm : (⟪(LinearMap.ker G)ᗮ.starProjection v, v⟫_ℂ).re =
        ‖(LinearMap.ker G)ᗮ.starProjection v‖ ^ 2 :=
      Submodule.re_inner_starProjection_eq_normSq (𝕜 := ℂ) _ _
    change 0 ≤ (⟪((B ^ 2 : ℝ) : ℂ) • (LinearMap.ker G)ᗮ.starProjection v - G v,
      v⟫_ℂ).re
    simpa only [inner_sub_left, inner_smul_left, Complex.sub_re,
      Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hnorm, henergy, sub_nonneg] using
      hbound ((LinearMap.ker G)ᗮ.starProjection v)

end LinearMap.IsSymmetricProjection

namespace LinearEquiv

/-- Two-sided comparison of the actual finite sums, with constants
independent of the number of constraints. -/
theorem sum_deformedConstraintProjection_comparison {ι : Type*} [Fintype ι]
    (e : E ≃ₗ[ℂ] F) (P : ι → F →ₗ[ℂ] F)
    (hP : ∀ i, (P i).IsSymmetricProjection)
    {B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (hForward : ∀ v : E, ‖e v‖ ≤ B * ‖v‖)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖) :
    ((1 / C ^ 2 : ℝ) : ℂ) • (∑ i, e.deformedConstraintProjection (P i)) ≤
        e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap ∧
      e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap ≤
        ((B ^ 2 : ℝ) : ℂ) • (∑ i, e.deformedConstraintProjection (P i)) := by
  have h := fun i => (hP i).deformedConstraintProjection_comparison
    e hB hC hForward hInverse
  rw [e.adjoint_congruence_sum P]
  constructor
  · simpa only [Finset.smul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h i).1)
  · simpa only [Finset.smul_sum] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => (h i).2)

/-- A uniform forward bound and inverse bound transfer a gap of the
original projection sum to the canonical deformed constraint sum, with
explicit ratio \(\delta/(B^2C^2)\): if every eigenvalue of \(\sum_iP_i\) other than
`0` is at least `δ`, then every eigenvalue of \(\sum_iQ_i\) other than `0` is at least
\(\delta/(B^2C^2)\). -/
theorem forall_hasEigenvalue_sum_deformedConstraintProjection {ι : Type*} [Fintype ι]
    (e : E ≃ₗ[ℂ] F) (P : ι → F →ₗ[ℂ] F)
    (hP : ∀ i, (P i).IsSymmetricProjection)
    {B C δ : ℝ} (hB : 0 < B) (hC : 0 < C) (hδ : 0 < δ)
    (hForward : ∀ v : E, ‖e v‖ ≤ B * ‖v‖)
    (hInverse : ∀ w : F, ‖e.symm w‖ ≤ C * ‖w‖)
    (hGap : ∀ μ : ℂ, Module.End.HasEigenvalue (∑ i, P i) μ → μ = 0 ∨ (δ : ℂ) ≤ μ) :
    ∀ μ : ℂ, Module.End.HasEigenvalue (∑ i, e.deformedConstraintProjection (P i)) μ →
      μ = 0 ∨ ((δ / (B ^ 2 * C ^ 2) : ℝ) : ℂ) ≤ μ := by
  have hsum : (∑ i, P i).IsPositive :=
    LinearMap.isPositive_sum Finset.univ fun i _ => (hP i).isPositive
  have hGGap := hsum.forall_hasEigenvalue_adjoint_congruence_of_inverse_bound
    e hδ.le hC hInverse hGap
  have hker : LinearMap.ker (e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap) =
      LinearMap.ker (∑ i, e.deformedConstraintProjection (P i)) :=
    (e.ker_adjoint_congruence (∑ i, P i)).trans
      (e.ker_sum_deformedConstraintProjection P (fun i => (hP i).isPositive)).symm
  have hUpper : ((1 : ℝ) : ℂ) • (e.toLinearMap.adjoint ∘ₗ (∑ i, P i) ∘ₗ e.toLinearMap) ≤
      ((B ^ 2 : ℝ) : ℂ) • (∑ i, e.deformedConstraintProjection (P i)) := by
    rw [Complex.ofReal_one, one_smul]
    exact (e.sum_deformedConstraintProjection_comparison P hP hB hC hForward hInverse).2
  have h := (hsum.adjoint_conj e.toLinearMap).forall_hasEigenvalue_of_scaled_comparison one_pos
    (sq_pos_of_pos hB) hUpper hker hGGap
  have hratio : 1 * (δ / C ^ 2) / B ^ 2 = δ / (B ^ 2 * C ^ 2) := by
    rw [one_mul, div_div, mul_comm (C ^ 2)]
  rwa [hratio] at h

end LinearEquiv

end
