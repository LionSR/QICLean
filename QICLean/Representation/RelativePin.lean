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
