/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import QICLean.Spectral.Filter.EnergyTruncation
import QICLean.Analysis.Order.LowEnergyPerturbation
import QICLean.Spectral.Gap.SeparatedQuadraticForms
import QICLean.Spectral.Filter.ExponentialWeights
import QICLean.Analysis.Projection.WeightedProjection
import QICLean.Analysis.Norm.MatrixToEuclidean
import QICLean.Spectral.Filter.SoftTruncationHardResidual
import QICLean.Spectral.Filter.ShiftedSoftHardTruncation

/-!
# Regional truncation error from a conjugation bound

Let `A` be Hermitian, let `X` commute with `A` and dominate `u` times its
spectral projection above `r + u`, and let `Y` be any further operator. If
imaginary-time conjugation of `Y` by `exp(s (A - (r + u)))` has norm at most
`C < u - e`, the weighted projection restricted to the spectral span of
`X + Y` at energies at most `e` has norm at most `C / (u - e - C)`. The
discrepancy of clipping `A` at `r + t` is then exponentially small in `t - u`
on that span.

The locality of the interaction enters only through the conjugation bound.

Moved from TNLean, `TNLean/Algebra/WeightedLowRestriction.lean` at commit `e41c3b63`, with
its statements unchanged.

## Main results

* `Matrix.exists_weighted_low_restriction_of_conjugation_le` — the weighted projection
  restricted to the low spectral span.
* `Matrix.norm_truncation_excess_low_le_of_conjugation_le` — the clipping error on that span.
* `Matrix.norm_partially_clipped_truncation_low_le` — the same for one member of a partially
  clipped commuting family.
* `Matrix.norm_soft_truncation_excess_low_le_of_conjugation_le`: soft truncation on a low spectral
  span.

## References

* Arad, Kuwahara and Landau, arXiv:1406.3898, proof of Theorem `thm:lowspec`, `low70.tex`,
  lines 1102–1168.
* Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Proposition 4.4,
  `local_alg_arxiv_v2.tex`, lines 894–921.
-/

section WeightedLowRestriction

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- From a conjugation bound on `Y`, the exponential weight of `A` has a
small restriction from the low spectral span of `X + Y` to the high spectral
range of `A`. AKL14, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168. -/
theorem exists_weighted_low_restriction_of_conjugation_le
    (A X Y : Matrix n n ℂ) (hA : A.IsHermitian) (r u e s C : ℝ) (hs0 : 0 < s)
    (hXA : Commute X A)
    (horder : u • spectralProjectionGE A (r + u) ≤ X)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hEigen : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) (X + Y) (b j) = (a j : ℂ) • b j)
    (hconj : ‖NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ))) * Y *
      NormedSpace.exp (-(s • (A - (r + u) • (1 : Matrix n n ℂ))))‖ ≤ C)
    (hgap : C < u - e) :
    let Q := spectralProjectionGE A (r + u)
    let W := NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ)))
    let T := toEuclideanCLM (n := n) (𝕜 := ℂ)
    let G := Submodule.spectralSpanLE b a e
    let U := (T Q).range
    ∃ Z : G →L[ℂ] U,
      U.subtypeL ∘L Z = (T W * T Q).domRestrict G ∧
      ‖Z‖ ≤ C / (u - e - C) := by
  intro Q W T G U
  let Winv := NormedSpace.exp (-(s • (A - (r + u) •
    (1 : Matrix n n ℂ))))
  let R := G.starProjection
  have hQmat : IsStarProjection Q := hA.isStarProjection_spectralProjectionGE (r + u)
  obtain ⟨hWQ, hXW, hXQ, hInv⟩ := hA.regionalWeight_relations X hXA s (r + u)
  have hWQT : Commute (T W) (T Q) := by
    change T W * T Q = T Q * T W
    simpa only [map_mul] using congrArg T hWQ.eq
  have hXWT : Commute (T X) (T W) := by
    change T X * T W = T W * T X
    simpa only [map_mul] using congrArg T hXW.eq
  have hXQT : Commute (T X) (T Q) := by
    change T X * T Q = T Q * T X
    simpa only [map_mul] using congrArg T hXQ.eq
  have hInvT : T Winv * T W = 1 := by
    simpa only [map_mul, map_one] using congrArg T hInv
  have hQT : IsIdempotentElem (T Q) := by
    change T Q * T Q = T Q
    simpa only [map_mul] using congrArg T hQmat.isIdempotentElem.eq
  have hRT : IsIdempotentElem R := G.isIdempotentElem_starProjection
  have hEigenT : ∀ j, (T X + T Y) (b j) = (a j : ℂ) • b j := by
    intro j
    simpa only [map_add] using hEigen j
  have hRH : Commute R (T X + T Y) :=
    Submodule.commute_starProjection_spectralSpanLE b a (T X + T Y) hEigenT e
  have hOrderT : (u : ℂ) • T Q ≤ T X := by
    have hm : (u : ℂ) • Q ≤ X := by simpa only [Complex.coe_smul] using horder
    have h := Matrix.toEuclideanCLM_le_toEuclideanCLM_iff.mpr hm
    simpa only [map_smul] using h
  let Pkg : Submodule ℂ (EuclideanSpace ℂ (n)) → Prop := fun S ↦
      ∃ (B : S →L[ℂ] S) (XU : U →L[ℂ] U) (Z : S →L[ℂ] U)
          (V : U →L[ℂ] U) (F : S →L[ℂ] U),
        S.subtypeL ∘L B = (T X + T Y).domRestrict S ∧
        U.subtypeL ∘L XU = (T X).domRestrict U ∧
        U.subtypeL ∘L Z = (T W * T Q).domRestrict S ∧
        U.subtypeL ∘L V = (T Q * T W * T Y * T Winv * T Q).domRestrict U ∧
        U.subtypeL ∘L F = (T W * T Q * T Y * (1 - T Q)).domRestrict S ∧
        XU ∘L Z - Z ∘L B = -(V ∘L Z) - F
  have hRrange :
      (R : EuclideanSpace ℂ (n) →ₗ[ℂ]
        EuclideanSpace ℂ (n)).range = G := by
    change G.starProjection.range = G
    exact Submodule.range_starProjection G
  have hrestr0 : Pkg ((R : EuclideanSpace ℂ (n) →ₗ[ℂ]
      EuclideanSpace ℂ (n)).range) :=
    ContinuousLinearMap.exists_restricted_weighted_sylvester
      (T X) (T Y) (T W) (T Winv) (T Q) R hQT hRT
      hWQT hXWT hXQT hRH hInvT
  have hrestr : Pkg G := Eq.mp (congrArg Pkg hRrange) hrestr0
  obtain ⟨B, XU, Z, V, F, hB, hXU, hZ, hV, hF, hEq⟩ := hrestr
  obtain ⟨XU0, hXU0, hLower0⟩ :=
    ContinuousLinearMap.exists_restrict_range_quadratic_lower
      (T Q) (T X) hQT hXQT u hOrderT
  have hLower : ∀ y : U, u * ‖y‖ ^ 2 ≤ (inner ℂ y (XU y)).re := by
    intro y
    have hpoint := congrArg (fun f : U →L[ℂ] EuclideanSpace ℂ (n) ↦ f y)
      (hXU0.trans hXU.symm)
    change (XU0 y : EuclideanSpace ℂ (n)) = (XU y : _) at hpoint
    have hl := hLower0 y
    change u * ‖(y : EuclideanSpace ℂ (n))‖ ^ 2 ≤
      (inner ℂ (y : EuclideanSpace ℂ (n))
        (XU0 y : EuclideanSpace ℂ (n))).re at hl
    change u * ‖(y : EuclideanSpace ℂ (n))‖ ^ 2 ≤
      (inner ℂ (y : EuclideanSpace ℂ (n))
        (XU y : EuclideanSpace ℂ (n))).re
    rw [hpoint] at hl
    exact hl
  have hUpper : ∀ x : G, (inner ℂ x (B x)).re ≤ e * ‖x‖ ^ 2 := by
    intro x
    have hpoint := congrArg (fun f : G →L[ℂ] EuclideanSpace ℂ (n) ↦ f x) hB
    change (B x : EuclideanSpace ℂ (n)) =
      (T X + T Y) (x : EuclideanSpace ℂ (n)) at hpoint
    change (inner ℂ (x : EuclideanSpace ℂ (n))
      (B x : EuclideanSpace ℂ (n))).re ≤
        e * ‖(x : EuclideanSpace ℂ (n))‖ ^ 2
    rw [hpoint]
    have hxG : (x : EuclideanSpace ℂ (n)) ∈
        Submodule.spectralSpanLE b a e := x.property
    exact Submodule.re_inner_apply_le_of_mem_spectralSpanLE
      (E := EuclideanSpace ℂ (n)) (n := n)
      b a (T X + T Y).toLinearMap hEigenT e
      (x := (x : EuclideanSpace ℂ (n))) hxG
  have hlow : ‖W * (1 - Q)‖ ≤ 1 :=
    hA.norm_exp_mul_sub_const_mul_lowProjection_le_one s (r + u) hs0.le
  have hBoundary : ‖Q * W * Y * Winv * Q‖ ≤ C ∧ ‖W * Q * Y * (1 - Q)‖ ≤ C := by
    refine ⟨(norm_projection_conjugated_mul_projection_le Q W Y Winv hQmat).trans hconj, ?_⟩
    calc
      ‖W * Q * Y * (1 - Q)‖ ≤ ‖W * Y * Winv‖ * ‖W * (1 - Q)‖ :=
        norm_weighted_projection_forcing_le Q W Y Winv hQmat hWQ hInv
      _ ≤ C * 1 := mul_le_mul hconj hlow (norm_nonneg _) ((norm_nonneg _).trans hconj)
      _ = C := mul_one _
  have hJnorm : ‖T Q * T W * T Y * T Winv * T Q‖ ≤ C := by
    have h : ‖T (Q * W * Y * Winv * Q)‖ ≤ C := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      exact hBoundary.1
    simpa only [map_mul] using h
  have hLnorm : ‖T W * T Q * T Y * (1 - T Q)‖ ≤ C := by
    have h : ‖T (W * Q * Y * (1 - Q))‖ ≤ C := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
      exact hBoundary.2
    simpa only [map_mul, map_sub, map_one] using h
  have hVnorm : ‖V‖ ≤ C :=
    (ContinuousLinearMap.norm_le_of_subtypeL_comp_eq_domRestrict V
      (T Q * T W * T Y * T Winv * T Q) hV).trans hJnorm
  have hFnorm : ‖F‖ ≤ C :=
    (ContinuousLinearMap.norm_le_of_subtypeL_comp_eq_domRestrict F
      (T W * T Q * T Y * (1 - T Q)) hF).trans hLnorm
  have hFneg : ‖-F‖ ≤ C := (norm_neg F).trans_le hFnorm
  have hEq' : XU ∘L Z - Z ∘L B = (-F) - V ∘L Z := by
    rw [hEq]
    abel
  have hnorm := ContinuousLinearMap.norm_le_div_of_sylvester_perturbation
    XU V B Z (-F) u e C C hLower hUpper hVnorm hFneg hgap hEq'
  exact ⟨Z, hZ, hnorm⟩

/-- From a conjugation bound on `Y`, clipping `A` at `r + t` changes it by at
most `exp(-s (t - u) - 1) / s · C / (u - e - C)` on the low spectral span of
`X + Y`. AKL14, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168. -/
theorem norm_truncation_excess_low_le_of_conjugation_le
    (A X Y : Matrix n n ℂ) (hA : A.IsHermitian) (r u e s t C : ℝ) (hs0 : 0 < s)
    (hut : u ≤ t) (hXA : Commute X A)
    (horder : u • spectralProjectionGE A (r + u) ≤ X)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hEigen : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) (X + Y) (b j) = (a j : ℂ) • b j)
    (hconj : ‖NormedSpace.exp (s • (A - (r + u) • (1 : Matrix n n ℂ))) * Y *
      NormedSpace.exp (-(s • (A - (r + u) • (1 : Matrix n n ℂ))))‖ ≤ C)
    (hgap : C < u - e) :
    ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)
        (A - cfc (fun x : ℝ ↦ min x (r + t)) A)).domRestrict
      (Submodule.spectralSpanLE b a e)‖ ≤
      (Real.exp (-s * (t - u) - 1) / s) * (C / (u - e - C)) := by
  obtain ⟨Z, hZ, hZnorm⟩ := exists_weighted_low_restriction_of_conjugation_le
    A X Y hA r u e s C hs0 hXA horder b a hEigen hconj hgap
  have hcut : r + u ≤ r + t := add_le_add le_rfl hut
  have htail := hA.norm_excess_domRestrict_le_actual_weighted_map
    s (r + t) (r + u) hs0 hcut Z hZ
  have hcoef : 0 ≤ Real.exp (-s * ((r + t) - (r + u)) - 1) / s :=
    div_nonneg (Real.exp_nonneg _) hs0.le
  have hfinal := htail.trans (mul_le_mul_of_nonneg_left hZnorm hcoef)
  have hdiff : (r + t) - (r + u) = t - u := by ring
  simpa only [hdiff] using hfinal

/-- For pairwise commuting Hermitian regional operators with attained lower
bounds, clipping one of them changes the centered partially clipped sum plus `Y`
by an exponentially small amount on its own low spectral span, given a
conjugation bound on `Y`. AKL14, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168; ALVV,
arXiv:1602.08828v2, Proposition 4.4, lines 894–921. -/
theorem norm_partially_clipped_truncation_low_le
    {m : Type*} [Fintype m] [DecidableEq m]
    (A : m → Matrix n n ℂ) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : Pairwise fun i j ↦ Commute (A i) (A j))
    (e : m → ℝ) (he : ∀ i, (e i : ℂ) • (1 : Matrix n n ℂ) ≤ A i)
    (T : Finset m) (j : m) (Y : Matrix n n ℂ) (u ε s t C : ℝ)
    (hs0 : 0 < s) (hu : 0 ≤ u) (hut : u ≤ t)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hEigen : ∀ v, toEuclideanCLM (n := n) (𝕜 := ℂ)
      ((∑ i, ((if i ∈ T then cfc (fun x : ℝ ↦ min x (e i + t)) (A i) else A i) -
        (e i : ℂ) • (1 : Matrix n n ℂ))) + Y) (b v) = (a v : ℂ) • b v)
    (hconj : ‖NormedSpace.exp (s • (A j - (e j + u) • (1 : Matrix n n ℂ))) * Y *
      NormedSpace.exp (-(s • (A j - (e j + u) • (1 : Matrix n n ℂ))))‖ ≤ C)
    (hgap : C < u - ε) :
    ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)
        (A j - cfc (fun x : ℝ ↦ min x (e j + t)) (A j))).domRestrict
      (Submodule.spectralSpanLE b a ε)‖ ≤
      (Real.exp (-s * (t - u) - 1) / s) * (C / (u - ε - C)) :=
  norm_truncation_excess_low_le_of_conjugation_le (A j) _ Y (hA j) (e j) u ε s t C hs0 hut
    (commute_centered_partially_clipped_sum A e t T hcomm j)
    (spectralProjectionGE_le_centered_partially_clipped_sum A e t u T hA he hu hut j)
    b a hEigen hconj hgap

end Matrix

end WeightedLowRestriction

section SoftTruncationLowRestriction

/-!
## Soft truncation on a low spectral span

Let `A` be Hermitian with `A ≥ p`, let `X` commute with `A` and dominate `u Q`, where `Q` is the
spectral projection of `A` onto the energies at least `c`, and let a conjugation bound
`‖e^{s(A - c)} Y e^{-s(A - c)}‖ ≤ C < u - e` hold. On the span `G` of the eigenvectors of
`X + Y` of energy at most `e`, the soft truncation of `A - p` at level `t` and order `m` changes
`A - p` by at most
`exp(-s (p + T - c) - 1)/s · C/(u - e - C) + (t/m) (T/t)^m`
for every `T ≥ 0` with `c ≤ p + T`. The first term is the hard truncation at `p + T` on `G`
(AKL14, Theorem `lowspec`); the second compares the soft and the hard truncations of `A - p`
at `T` (ALVV, `lem:exp-approx`).

The projection floor `u` and the threshold `c` of the projection are independent, and no
upper bound on the norm of `A` is used.

Moved from TNLean, `TNLean/MPS/AreaLaw/RegionalBarrierResidual.lean` at commit `49b78ed821`
(Apache-2.0). Changes: stated for arbitrary matrices `A`, `X`, `Y` with a conjugation bound
`C` on `Y` as a hypothesis, in place of regional sums of the terms of a chain interaction and
the bound `C = 2 |J|` that those terms satisfy.

### Main results

* `Matrix.norm_soft_truncation_excess_low_le_of_conjugation_le` — the soft residual on the low
  spectral span.

### References

* Arad, Kuwahara and Landau, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168.
* Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The soft residual on a low spectral span.** For Hermitian `A ≥ p`, `X` commuting with
`A` with `u Q ≤ X` for the spectral projection `Q` of `A` onto the energies at least `c`, an
eigenbasis of `X + Y`, and `‖e^{s(A - c)} Y e^{-s(A - c)}‖ ≤ C < u - e`, the soft truncation
of `A - p` changes it, on the span of the eigenvectors of `X + Y` of energy at most `e`, by at
most `exp(-s (p + T - c) - 1)/s · C/(u - e - C) + (t/m) (T/t)^m` whenever `0 ≤ T` and
`c ≤ p + T`. AKL14, arXiv:1406.3898, Theorem `lowspec`, lines 1102–1168; ALVV,
arXiv:1602.08828v2, `lem:exp-approx`, lines 1195–1255. -/
theorem norm_soft_truncation_excess_low_le_of_conjugation_le
    (A X Y : Matrix n n ℂ) (hA : A.IsHermitian) (p c u e s t T C : ℝ) (m : ℕ)
    (hp : (p : ℂ) • (1 : Matrix n n ℂ) ≤ A)
    (hs0 : 0 < s) (ht : 0 < t) (hm : 1 ≤ m) (hT : 0 ≤ T) (hcut : c ≤ p + T)
    (hXA : Commute X A) (horder : u • spectralProjectionGE A c ≤ X)
    (b : OrthonormalBasis n ℂ (EuclideanSpace ℂ n)) (a : n → ℝ)
    (hEigen : ∀ j, toEuclideanCLM (n := n) (𝕜 := ℂ) (X + Y) (b j) = (a j : ℂ) • b j)
    (hconj : ‖NormedSpace.exp (s • (A - c • (1 : Matrix n n ℂ))) * Y *
      NormedSpace.exp (-(s • (A - c • (1 : Matrix n n ℂ))))‖ ≤ C)
    (hgap : C < u - e) :
    ‖(toEuclideanCLM (n := n) (𝕜 := ℂ)
        (A - (p : ℂ) • 1 - cfc (Real.softTruncation t m) (A - (p : ℂ) • 1))).domRestrict
      (Submodule.spectralSpanLE b a e)‖ ≤
      (Real.exp (-s * ((p + T) - c) - 1) / s) * (C / (u - e - C)) +
        (t / (m : ℝ)) * (T / t) ^ m := by
  have hc : (c - u) + u = c := sub_add_cancel c u
  have hhard := norm_truncation_excess_low_le_of_conjugation_le A X Y hA (c - u) u e s
    (p + T - (c - u)) C hs0 (by linarith) hXA (by rwa [hc]) b a hEigen (by rwa [hc]) hgap
  rw [show c - u + (p + T - (c - u)) = p + T by ring,
    show p + T - (c - u) - u = p + T - c by ring] at hhard
  have hcmp := (le_iff.mp hp).norm_softTruncation_residual_domRestrict_le t m T ht hm hT
    (Submodule.spectralSpanLE b a e)
  have hclip : A - (p : ℂ) • 1 - energyTruncation (A - (p : ℂ) • 1) T =
      A - cfc (fun x : ℝ ↦ min x (p + T)) A := by
    rw [hA.energyTruncation_sub_smul_one p T, energyTruncation]
    abel
  rw [hclip] at hcmp
  exact hcmp.trans (add_le_add hhard le_rfl)

end Matrix

end SoftTruncationLowRestriction
