/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RelativePinCommute
import QICLean.Entropy.ConditionalMovementRegional

/-!
# The relative coherent pin (Lemma 6.3)

Let `P, x, Y₀, F` partition the sites of `V = ⨂_v ℂ^{n_v}` and let `C_{x,k}` be the relative
metric of moving `x` from the middle part `x Y₀` to `P`. Lemma 6.3 of the area-law paper
(*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`, lines 486–599)
states that, for `a = 2t` small compared with `log(e dim x)` and every unit vector `θ`,

`C_{x,k} ≥ poly(k)^{-1} exp{k a [η_θ - C a^{1/4} log^C(e dim x)]} P_{θ,k}`

with `η_θ = S_θ(x|P) + S_θ(x|Y₀)` and a polynomial uniform in `θ`.

## Proof

By inverse Cauchy–Schwarz it suffices to bound `⟨θ^{⊗k}, C^{-1} θ^{⊗k}⟩ =
‖W_{Px} W_{xY₀} W_P^{-1} W_{Y₀}^{-1} θ^{⊗k}‖²` (`RelativePinAlgebra.lean`). Insert the
compensators `T_R = W_R^{-1} (ρ_R^t)^{⊗k}`, of norm at most a polynomial in `k`
(`RelativePinCompensator.lean`): since `ρ_R^t ρ̂_R^{-t}` is the support projection of `ρ_R`,
`W_P^{-1} W_{Y₀}^{-1} θ^{⊗k} = T_P T_{Y₀} y` with `y = (ρ̂_P^{-t} ρ̂_{Y₀}^{-t} θ)^{⊗k}`, and the
compensators commute with the numerator metrics. Expanding the numerators by the integral
representation (Lemma 6.2) leaves averages of `(σ^t τ^t ρ̂_P^{-t} ρ̂_{Y₀}^{-t} θ)^{⊗k}`, whose
norms are `k`-th powers of the one-copy word of Lemma 5.1.

## Statement form

The polynomial is `K (k + 2)^N`; the exponent of `log(e dim x)` is `2`, and the constant `C` is
twice the constant of Lemma 5.1. The entropy `η_θ` is `Entropy.movementEta` of `θ` in the
coordinates `(x × Y₀) × (P × F)`, which is `S_θ(x|P) + S_θ(x|Y₀)`. The hypothesis `t ≤ 1`
replaces the paper's standing `t < 1/4`.

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `Entropy.frameMarginalP_posSemidef`, `Entropy.trace_frameMarginalP`.
* `TensorPower.relativePin` — **Lemma 6.3**.
-/

open MeasureTheory Matrix PermutationRepresentation Entropy
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {P x Y F : Finset V}

omit [Fintype V] in
theorem frameMarginalP_posSemidef (h : FourPartition P x Y F)
    (θ : EuclideanSpace ℂ (SiteConfig n)) : (frameMarginalP h θ).PosSemidef :=
  (movementMarginalXP_posSemidef _).partialTraceLeft

omit [Fintype V] in
theorem frameMarginalY_posSemidef (h : FourPartition P x Y F)
    (θ : EuclideanSpace ℂ (SiteConfig n)) : (frameMarginalY h θ).PosSemidef :=
  (movementMarginalXU_posSemidef _).partialTraceLeft

theorem trace_vecMulVec_star_eq {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    (vecMulVec u (star u)).trace = ((‖(WithLp.toLp 2 u : EuclideanSpace ℂ ι)‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_vecMulVec, EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.mul_conj]
  rfl

theorem trace_frameMarginalP (h : FourPartition P x Y F) {θ : EuclideanSpace ℂ (SiteConfig n)}
    (hθ : ‖θ‖ = 1) : (frameMarginalP h θ).trace = 1 := by
  rw [frameMarginalP, trace_partialTraceLeft, movementMarginalXP, trace_partialTraceRight,
    trace_vecMulVec_star_eq, norm_toLp_comp_equiv, frameVector, norm_toLp_comp_equiv]
  simp [hθ]

theorem trace_frameMarginalY (h : FourPartition P x Y F) {θ : EuclideanSpace ℂ (SiteConfig n)}
    (hθ : ‖θ‖ = 1) : (frameMarginalY h θ).trace = 1 := by
  rw [frameMarginalY, trace_partialTraceLeft, movementMarginalXU, trace_partialTraceRight,
    trace_vecMulVec_star_eq, frameVector, norm_toLp_comp_equiv]
  simp [hθ]

end Entropy

namespace Matrix

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `ρ^t ρ̂^{-t} = 1 - Π_{ker ρ}` for `ρ ≥ 0` and `t > 0`, with `ρ̂ = ρ + Π_{ker ρ}`. -/
theorem rpow_mul_cfc_kernelCompletion {A : Matrix m m ℂ} (hA : A.PosSemidef) {t : ℝ}
    (ht : 0 < t) :
    A ^ t * cfc (fun s : ℝ => s ^ (-t)) (kernelCompletion A) = 1 - kernelProjection A := by
  have hfin : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f =>
    (finite_real_spectrum (A := A)).continuousOn f
  rw [cfc_rpow_kernelCompletion hA.isHermitian (neg_ne_zero.mpr ht.ne'),
    CFC.rpow_eq_cfc_real hA.nonneg, mul_add, ← cfc_mul _ _ A (hfin _) (hfin _), kernelProjection,
    ← cfc_mul _ _ A (hfin _) (hfin _), ← cfc_add (a := A) _ _ (hfin _) (hfin _),
    ← cfc_const_one ℝ A (ha := hA.isHermitian.isSelfAdjoint),
    ← cfc_sub (a := A) (fun _ : ℝ => (1 : ℝ)) (fun s : ℝ => if s = 0 then (1 : ℝ) else 0)
      (hfin _) (hfin _)]
  refine cfc_congr fun s hs => ?_
  have hs0 : 0 ≤ s := spectrum_nonneg_of_nonneg hA.nonneg hs
  rcases hs0.lt_or_eq with hpos | rfl
  · simp [hpos.ne', ← Real.rpow_add hpos]
  · simp [Real.zero_rpow ht.ne']

end Matrix

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {D : Finset V}

theorem localLift_sub (K K' : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    localLift D (K - K') = localLift D K - localLift D K' := by
  rw [eq_sub_iff_add_eq, ← localLift_add, sub_add_cancel]

/-- If `L_D(Π) θ = 0` then `L_D(ρ^t ρ̂^{-t}) θ = θ`. -/
theorem localLift_rpow_mul_mulVec {ρ : Matrix (RegionConfig n D) (RegionConfig n D) ℂ}
    (hρ : ρ.PosSemidef) {t : ℝ} (ht : 0 < t) {θ : SiteConfig n → ℂ}
    (hker : localLift D (kernelProjection ρ) *ᵥ θ = 0) :
    localLift D (ρ ^ t) *ᵥ (localLift D (cfc (fun s : ℝ => s ^ (-t)) (kernelCompletion ρ)) *ᵥ θ) =
      θ := by
  rw [mulVec_mulVec, ← localLift_mul, rpow_mul_cfc_kernelCompletion hρ ht, localLift_sub,
    localLift_one, sub_mulVec, hker, one_mulVec, sub_zero]

end Entropy

namespace TensorPower

universe u

theorem _root_.Entropy.FourPartition.moveParts {V : Type*} {P x Y F : Finset V}
    (h : Entropy.FourPartition P x Y F) : MoveParts P x Y F :=
  ⟨h.Px, h.PY, h.PF, h.xY, h.xF, h.YF⟩

/-- **Lemma 6.3, the relative coherent pin** (`05-replicas.tex`, equation
`replicas:relative-pin`, lines 486–509). Let `P, x, Y₀, F` partition the sites, `0 < t ≤ 1`,
`a = 2t` with `a log(e dim x) ≤ c`. There is a polynomial `K (k + 2)^N`, uniform in `θ`, such
that for every unit vector `θ` and every `w`,
`exp{k a [η_θ - C a^{1/4} log²(e dim x)]} |⟨θ^{⊗k}, w⟩|² ≤ K (k + 2)^N ⟨w, C_{x,k} w⟩`, that is,
`C_{x,k} ≥ (K (k + 2)^N)^{-1} exp{k a [η_θ - C a^{1/4} log²(e dim x)]} P_{θ,k}`, with
`η_θ = S_θ(x|P) + S_θ(x|Y₀)`. The constants `C` and `c` are universal. -/
theorem relativePin :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]
        {P x Y F : Finset V} (h : FourPartition P x Y F) {t : ℝ}, 0 < t → t ≤ 1 →
        2 * t * Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ≤ c →
        ∃ K N : ℝ, 0 < K ∧ ∀ (k : ℕ) (θ : EuclideanSpace ℂ (SiteConfig n)), ‖θ‖ = 1 →
          ∀ w : Config k (fun v => Fin (n v)) → ℂ,
            ‖star (tensorVec k θ.ofLp) ⬝ᵥ w‖ ^ 2 *
              Real.exp (k * (2 * t) * (movementEta (frameVector h θ) -
                C * (2 * t) ^ (1 / 4 : ℝ) *
                  Real.log (Real.exp 1 * Fintype.card (RegionConfig n x)) ^ 2)) ≤
            K * ((k : ℝ) + 2) ^ N * (star w ⬝ᵥ (relativeMetric n t k P x Y F *ᵥ w)).re := by
  obtain ⟨C₀, c, hC₀, hc, Hmove⟩ := regionalMovement_norm_le.{u}
  refine ⟨2 * C₀, c, by positivity, hc, ?_⟩
  intro V _ _ n _ P x Y F h t ht0 ht1 hsmall
  have σ₀ : SiteConfig n := fun v => ⟨0, Nat.pos_of_ne_zero (NeZero.ne (n v))⟩
  obtain ⟨Cc, hCc0, Hcomp⟩ := exists_l2_opNorm_compensator_le (n := n) ht0
  obtain ⟨Ω₁, _, P₁, hP₁, σ, hσ, hint₁, heq₁⟩ :=
    exists_replicaMetric_integral_localLift (n := n) ht0 ht1 (P ∪ x)
  obtain ⟨Ω₂, _, P₂, hP₂, τ, hτ, hint₂, heq₂⟩ :=
    exists_replicaMetric_integral_localLift (n := n) ht0 ht1 (x ∪ Y)
  refine ⟨1, 4 * Cc, one_pos, fun k θ hθ w => ?_⟩
  set ℓ := Real.log (Real.exp 1 * Fintype.card (RegionConfig n x))
  set η := movementEta (frameVector h θ)
  set z := tensorVec k θ.ofLp
  set ρP := frameMarginalP h θ
  set ρY := frameMarginalY h θ
  have hρP := frameMarginalP_posSemidef h θ
  have hρY := frameMarginalY_posSemidef h θ
  set DP := cfc (fun s : ℝ => s ^ (-t)) (kernelCompletion ρP)
  set DY := cfc (fun s : ℝ => s ^ (-t)) (kernelCompletion ρY)
  set v := localLift P DP *ᵥ (localLift Y DY *ᵥ θ.ofLp)
  set y := tensorVec k v
  set Wa := replicaMetric (fun v => Fin (n v)) t k (P ∪ x)
  set Wb := replicaMetric (fun v => Fin (n v)) t k (x ∪ Y)
  set Wp := replicaMetric (fun v => Fin (n v)) t k P
  set Wy := replicaMetric (fun v => Fin (n v)) t k Y
  set tP := tensorPow (k := k) (localLift P (ρP ^ t))
  set tY := tensorPow (k := k) (localLift Y (ρY ^ t))
  set E := Real.exp (k * (-t * η + C₀ * (2 * t) ^ (5 / 4 : ℝ) * ℓ ^ 2))
  -- the support identity: `z = tP tY y`
  have hz : z = tP *ᵥ (tY *ᵥ y) := by
    have hPY : Disjoint P Y := h.PY
    have hcomm : localLift Y (ρY ^ t) * localLift P DP = localLift P DP * localLift Y (ρY ^ t) :=
      commute_of_isSupportedOn_disjoint (isSupportedOn_localLift _) (isSupportedOn_localLift _)
        hPY σ₀
    have h1 : localLift Y (ρY ^ t) *ᵥ v = localLift P DP *ᵥ θ.ofLp := by
      simp only [v]
      rw [mulVec_mulVec, hcomm, ← mulVec_mulVec,
        localLift_rpow_mul_mulVec hρY ht0 (localLift_kernelProjection_Y_mulVec h θ)]
    have h2 : localLift P (ρP ^ t) *ᵥ (localLift P DP *ᵥ θ.ofLp) = θ.ofLp :=
      localLift_rpow_mul_mulVec hρP ht0 (localLift_kernelProjection_P_mulVec h θ)
    simp only [z, y, tP, tY, tensorPow_mulVec_tensorVec, h1, h2]
  -- moving the compensators
  have hM : moveWord n t k P x Y *ᵥ z = (Wp⁻¹ * tP) *ᵥ ((Wy⁻¹ * tY) *ᵥ (Wa *ᵥ (Wb *ᵥ y))) := by
    have hPx : P ⊆ P ∪ x := Finset.subset_union_left
    have hYx : Y ⊆ x ∪ Y := Finset.subset_union_right
    have hPxY : Disjoint P (x ∪ Y) := Finset.disjoint_union_right.mpr ⟨h.Px, h.PY⟩
    have hYPx : Disjoint Y (P ∪ x) := Finset.disjoint_union_right.mpr ⟨h.PY.symm, h.xY.symm⟩
    have hWp := replicaMetric_inv_eq (n := n) ht0.le k P
    have hWy := replicaMetric_inv_eq (n := n) ht0.le k Y
    have LWa := isLabelFunctionOn_replicaMetric (ι := fun v => Fin (n v)) (k := k) t (P ∪ x)
    have LWb := isLabelFunctionOn_replicaMetric (ι := fun v => Fin (n v)) (k := k) t (x ∪ Y)
    have LWp := isLabelFunctionOn_replicaMetric_inv (ι := fun v => Fin (n v)) (k := k) ht0.le P
    have LWy := isLabelFunctionOn_replicaMetric_inv (ι := fun v => Fin (n v)) (k := k) ht0.le Y
    have c1 : Commute Wy⁻¹ tP := by
      rw [hWy]; exact commute_labelObservable_tensorPow_of_disjoint h.PY σ₀ _ _
    have cap : Commute Wa (Wp⁻¹ * tP) :=
      ((LWp.commute_of_subset LWa hPx).symm).mul_right
        (commute_labelObservable_tensorPow_of_subset hPx σ₀ _ _)
    have cbp : Commute Wb (Wp⁻¹ * tP) :=
      ((LWp.commute_of_disjoint LWb hPxY).symm).mul_right
        (commute_labelObservable_tensorPow_of_disjoint hPxY σ₀ _ _)
    have cay : Commute Wa (Wy⁻¹ * tY) :=
      ((LWy.commute_of_disjoint LWa hYPx).symm).mul_right
        (commute_labelObservable_tensorPow_of_disjoint hYPx σ₀ _ _)
    have cby : Commute Wb (Wy⁻¹ * tY) :=
      ((LWy.commute_of_subset LWb hYx).symm).mul_right
        (commute_labelObservable_tensorPow_of_subset hYx σ₀ _ _)
    have hmat : moveWord n t k P x Y * tP * tY = (Wp⁻¹ * tP) * (Wy⁻¹ * tY) * (Wa * Wb) := by
      have e1 : moveWord n t k P x Y * tP * tY = Wa * Wb * ((Wp⁻¹ * tP) * (Wy⁻¹ * tY)) := by
        simp only [moveWord, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Wy⁻¹ tP tY, c1.eq, Matrix.mul_assoc]
      rw [e1, ((cap.mul_left cbp).mul_right (cay.mul_left cby)).eq]
    rw [hz, mulVec_mulVec, mulVec_mulVec, hmat]
    simp only [mulVec_mulVec, Matrix.mul_assoc]
  -- the averaged numerators
  have hWW : ‖(EuclideanSpace.equiv _ ℂ).symm (Wa *ᵥ (Wb *ᵥ y))‖ ≤ E := by
    sorry
  have hTP : ‖Wp⁻¹ * tP‖ ≤ ((k : ℝ) + 2) ^ Cc :=
    Hcomp k P ρP hρP (trace_frameMarginalP h hθ)
  have hTY : ‖Wy⁻¹ * tY‖ ≤ ((k : ℝ) + 2) ^ Cc :=
    Hcomp k Y ρY hρY (trace_frameMarginalY h hθ)
  have hMz : ‖(EuclideanSpace.equiv _ ℂ).symm (moveWord n t k P x Y *ᵥ z)‖ ≤
      ((k : ℝ) + 2) ^ Cc * (((k : ℝ) + 2) ^ Cc * E) := by
    rw [hM]
    refine (norm_mulVec_le _ _).trans ?_
    refine mul_le_mul hTP ?_ (norm_nonneg _) (by positivity)
    refine (norm_mulVec_le _ _).trans ?_
    exact mul_le_mul hTY hWW (norm_nonneg _) (by positivity)
  have key := norm_star_dotProduct_sq_le_moveWord ht0.le k h.moveParts z w (n := n) (F := F)
  have hre : 0 ≤ (star w ⬝ᵥ (relativeMetric n t k P x Y F *ᵥ w)).re :=
    (posDef_relativeMetric_and_inv ht0.le k h.moveParts (n := n)).1.posSemidef.re_dotProduct_nonneg w
  set X := Real.exp (k * (2 * t) * (η - 2 * C₀ * (2 * t) ^ (1 / 4 : ℝ) * ℓ ^ 2))
  have hX : 0 ≤ X := (Real.exp_pos _).le
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have hE2 : E ^ 2 * X = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, Real.exp_eq_one_iff]
    rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add h2t, Real.rpow_one]
    ring
  have hpow : (((k : ℝ) + 2) ^ Cc * (((k : ℝ) + 2) ^ Cc * E)) ^ 2 =
      ((k : ℝ) + 2) ^ (4 * Cc) * E ^ 2 := by
    rw [show (4 * Cc) = Cc * ((4 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul_natCast hk.le]
    ring
  calc ‖star z ⬝ᵥ w‖ ^ 2 * X
      ≤ (‖(EuclideanSpace.equiv _ ℂ).symm (moveWord n t k P x Y *ᵥ z)‖ ^ 2 *
          (star w ⬝ᵥ (relativeMetric n t k P x Y F *ᵥ w)).re) * X :=
        mul_le_mul_of_nonneg_right key hX
    _ ≤ ((((k : ℝ) + 2) ^ Cc * (((k : ℝ) + 2) ^ Cc * E)) ^ 2 *
          (star w ⬝ᵥ (relativeMetric n t k P x Y F *ᵥ w)).re) * X := by
        gcongr
    _ = 1 * ((k : ℝ) + 2) ^ (4 * Cc) *
          (star w ⬝ᵥ (relativeMetric n t k P x Y F *ᵥ w)).re := by
        rw [hpow]
        linear_combination (((k : ℝ) + 2) ^ (4 * Cc) *
          (star w ⬝ᵥ (relativeMetric n t k P x Y F *ᵥ w)).re) * hE2

end TensorPower
