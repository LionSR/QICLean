/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PureStateTraceDistance
import QICLean.Entropy.ControlledContinuity
import QICLean.Entropy.RegionStrongSubadditivity

/-!
# Mutual information near a state without correlations

Let `η` be a unit vector with no mutual information between disjoint regions `X` and `J`.
Continuity of the mutual information in the dimension of `X` alone gives
`I_ψ(X : J) ≤ 8 √‖ψ - η‖ log(e dim X)` for every unit vector `ψ`. A unitary supported away
from `X ∪ J` changes neither reduction, so the same bound holds for `φ` with
`‖U φ - η‖` in place of `‖ψ - η‖`. With `‖U φ - η‖ ≤ C₁ n^(-K/2)` and
`log dim X ≤ C₂ n²` this is at most `8 √C₁ (1 + C₂) n^(-M)` once `K ≥ 4(M + 2)`.

The regions and the local alphabets are arbitrary, so ancillary systems are included by
enlarging the set of sites. The state may be entangled with every other system, and only the
dimension of `X` enters.

Moved from TNLean, `TNLean/Lattice/EntropyComparison.lean` and
`TNLean/Lattice/SupportedUnitaryEntropy.lean` at commit `e41c3b63`. The forms there with a
unitary `1 ⊗ U` on the complement of `X ∪ J` are the special case of a unitary supported on
that complement.

## Main results

* `ManyBody.traceDistance_regionState_le` — reduction does not increase the trace
  distance of pure states.
* `ManyBody.regionMutualInformation_le_of_norm_sub_le` — continuity against a state without
  correlations.
* `ManyBody.regionMutualInformation_le_of_supported_unitary` — the comparison after a unitary
  supported away from both regions.
* `ManyBody.regionMutualInformation_le_inv_pow_of_supported_unitary` — its polynomial scale.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  proof of Proposition 10.2 (`prop:amplification`), `09-amplification.tex`, lines 545–561,
  and Lemma 2.1 (`lem:continuity`), `01-preliminaries.tex`, lines 33–46 and 76–80.
* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, September 24,
  2026, `02-information.tex`, lines 600–630.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The reduced states of two unit vectors on a region are no farther apart in trace distance
than the pure states themselves. Two-dimensional area law, `01-preliminaries.tex`,
lines 76–80. -/
theorem traceDistance_regionState_le (ψ η : EuclideanSpace ℂ ((v : V) → β v))
    (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) (R : Finset V) :
    traceDistance (regionState ψ R) (regionState η R) ≤
      traceDistance (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
        (vecMulVec (WithLp.ofLp η) (star (WithLp.ofLp η))) :=
  (traceDistance_partialTraceRight_le
      ((posSemidef_vecMulVec_self_star _).submatrix (cutEquiv β R).symm).isHermitian
      ((posSemidef_vecMulVec_self_star _).submatrix (cutEquiv β R).symm).isHermitian
      ((trace_partialTraceRight _).symm.trans
        ((trace_regionState_eq_one hψ (D := R)).trans
          ((trace_regionState_eq_one hη (D := R)).symm.trans
              (trace_partialTraceRight _))))).trans_eq
    (traceDistance_submatrix_equiv (cutEquiv β R).symm
      (posSemidef_vecMulVec_self_star _).isHermitian
      (posSemidef_vecMulVec_self_star _).isHermitian)

/-- **Continuity against a state without correlations.** Let `ψ, η` be unit vectors and
`X, J` disjoint regions with `I_η(X : J) = 0`. Then `I_ψ(X : J) ≤ 8 √‖ψ - η‖ log(e dim X)`.
Only the dimension of `X` enters. Two-dimensional area law, Lemma 2.1,
`01-preliminaries.tex`, lines 33–46 and 76–77, as applied in `09-amplification.tex`,
lines 550–555. -/
theorem regionMutualInformation_le_of_norm_sub_le {ψ η : EuclideanSpace ℂ ((v : V) → β v)}
    (hψ : ‖ψ‖ = 1) (hη : ‖η‖ = 1) {X J : Finset V} (hXJ : Disjoint X J)
    (hprod : regionMutualInformation η X J = 0) :
    regionMutualInformation ψ X J ≤
      8 * √‖ψ - η‖ * Real.log (Real.exp 1 * Fintype.card (RegionConfig β X)) := by
  have htr (χ : EuclideanSpace ℂ ((v : V) → β v)) (hχ : ‖χ‖ = 1) :
      (jointMatrix β χ X J hXJ).trace = 1 := by
    unfold jointMatrix
    rw [trace_submatrix_equiv]
    exact trace_regionState_eq_one hχ (D := _)
  have h := Entropy.abs_mutualInformation_sub_le_sqrt_fin
    (jointMatrix_posSemidef β ψ X J hXJ) (jointMatrix_posSemidef β η X J hXJ)
    (htr ψ hψ) (htr η hη)
  have hψI : Entropy.mutualInformation (jointMatrix β ψ X J hXJ)
      (jointMatrix_posSemidef β ψ X J hXJ).isHermitian
          = regionMutualInformation ψ X J :=
    (regionMutualInformation_eq_matrix β ψ X J hXJ).symm
  have hηI : Entropy.mutualInformation (jointMatrix β η X J hXJ)
      (jointMatrix_posSemidef β η X J hXJ).isHermitian
          = regionMutualInformation η X J :=
    (regionMutualInformation_eq_matrix β η X J hXJ).symm
  rw [hψI, hηI, hprod, sub_zero] at h
  have hdist : traceDistance (jointMatrix β ψ X J hXJ) (jointMatrix β η X J hXJ) ≤
      ‖ψ - η‖ := by
    unfold jointMatrix
    rw [traceDistance_submatrix_equiv _ (regionState_posSemidef _ ψ).isHermitian
      (regionState_posSemidef _ η).isHermitian]
    exact (traceDistance_regionState_le β ψ η hψ hη _).trans
      (traceDistance_vecMulVec_le_norm_sub hψ hη)
  have hlog : 0 ≤ Real.log (Real.exp 1 * Fintype.card (RegionConfig β X)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_exp zero_le_one)
      (Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr
        (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one
          (trace_regionState_eq_one hψ (D := X))))))
  calc regionMutualInformation ψ X J
      ≤ |regionMutualInformation ψ X J| := le_abs_self _
    _ ≤ _ := h
    _ ≤ _ := by gcongr

/-- **The comparison after a unitary supported away from both regions.** Let `U` be a unitary
supported on a region `S` disjoint from `X ∪ J`, and let `η` be a unit vector with
`I_η(X : J) = 0`. Every unit vector `φ` then satisfies
`I_φ(X : J) ≤ 8 √‖U φ - η‖ log(e dim X)`: the unitary changes neither the reduction to `X`,
nor to `J`, nor to `X ∪ J`. Two-dimensional area law, `09-amplification.tex`,
lines 547–555; polynomial PEPS approximation, `02-information.tex`, lines 600–630. -/
theorem regionMutualInformation_le_of_supported_unitary {φ η : EuclideanSpace ℂ ((v : V) → β v)}
    (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1) {X J S : Finset V} (hXJ : Disjoint X J)
    (hS : Disjoint S (X ∪ J)) {U : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    (hU : U ∈ supportedOperators β S) (hUu : Uᴴ * U = 1)
    (hprod : regionMutualInformation η X J = 0) :
    regionMutualInformation φ X J ≤
      8 * √‖toEuclideanLin U φ - η‖ *
        Real.log (Real.exp 1 * Fintype.card (RegionConfig β X)) := by
  have hstate (R : Finset V) (hR : R ⊆ X ∪ J) :=
    regionState_toEuclideanLin_of_mem_supportedOperators
      (hS.mono_right hR) hU hUu φ
  have hent (R : Finset V) (hR : R ⊆ X ∪ J) :
      regionEntropy (toEuclideanLin U φ) R = regionEntropy φ R := by
    exact vonNeumannEntropy_congr (hstate R hR) _ _
  have hψ : ‖toEuclideanLin U φ‖ = 1 := by
    have h := congrArg Matrix.trace (hstate _ subset_rfl)
    rw [trace_regionState, trace_regionState, hφ] at h
    have h' : ‖toEuclideanLin U φ‖ ^ 2 = 1 ^ 2 := by exact_mod_cast h
    nlinarith [norm_nonneg (toEuclideanLin U φ), sq_nonneg (‖toEuclideanLin U φ‖ - 1)]
  have hMI : regionMutualInformation φ X J = regionMutualInformation
      (toEuclideanLin U φ) X J := by
    simp only [regionMutualInformation, hent X Finset.subset_union_left,
      hent J Finset.subset_union_right, hent _ subset_rfl]
  rw [hMI]
  exact regionMutualInformation_le_of_norm_sub_le β hψ hη hXJ hprod

omit [∀ v, DecidableEq (β v)] in
private theorem one_le_card_configuration {φ : EuclideanSpace ℂ ((v : V) → β v)}
    (hφ : ‖φ‖ = 1) (X : Finset V) : (1 : ℝ) ≤ Fintype.card (RegionConfig β X) := by
  classical
  exact Nat.one_le_cast.mpr (Fintype.card_pos_iff.mpr
    (Entropy.Matrix.PosSemidef.nonempty_of_trace_eq_one
        (trace_regionState_eq_one hφ (D := X))))

/-- The scale `8 √C₁ (1 + C₂) n^(2-K/4)` of the comparison, from `‖U φ - η‖ ≤ C₁ n^(-K/2)`
and `log dim X ≤ C₂ n²`. Two-dimensional area law, `09-amplification.tex`, lines 545 and
550–557. -/
private theorem mutualInformation_le_rpow_of_supported_unitary
    {φ η : EuclideanSpace ℂ ((v : V) → β v)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {X J S : Finset V} (hXJ : Disjoint X J) (hS : Disjoint S (X ∪ J))
    {U : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    (hU : U ∈ supportedOperators β S) (hUu : Uᴴ * U = 1)
    (hprod : regionMutualInformation η X J = 0) {C₁ C₂ K : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hδ : ‖toEuclideanLin U φ - η‖ ≤ C₁ * (n : ℝ) ^ (-K / 2))
    (hdim : Real.log (Fintype.card (RegionConfig β X)) ≤ C₂ * (n : ℝ) ^ 2) :
    regionMutualInformation φ X J ≤ 8 * √C₁ * (1 + C₂) * (n : ℝ) ^ (2 - K / 4) := by
  have hbase := regionMutualInformation_le_of_supported_unitary β hφ hη hXJ hS hU hUu hprod
  set δ := ‖toEuclideanLin U φ - η‖
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard := one_le_card_configuration β hφ X
  have hlog : Real.log (Real.exp 1 * Fintype.card (RegionConfig β X)) =
      1 + Real.log (Fintype.card (RegionConfig β X)) := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : Real.log (Real.exp 1 * Fintype.card (RegionConfig β X)) ≤
      (1 + C₂) * (n : ℝ) ^ (2 : ℝ) := by
    rw [hlog, Real.rpow_two]
    nlinarith
  have hsqrt : √δ ≤ √C₁ * (n : ℝ) ^ (-K / 4) := by
    calc √δ ≤ √(C₁ * (n : ℝ) ^ (-K / 2)) := Real.sqrt_le_sqrt hδ
      _ = √C₁ * (n : ℝ) ^ (-K / 4) := by
        rw [Real.sqrt_mul' _ (by positivity), Real.sqrt_eq_rpow ((n : ℝ) ^ (-K / 2)),
          ← Real.rpow_mul hn0.le]
        ring_nf
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * Fintype.card (RegionConfig β X)) := by
    rw [hlog]
    linarith [Real.log_nonneg hcard]
  calc regionMutualInformation φ X J
      ≤ 8 * √δ * Real.log (Real.exp 1 * Fintype.card (RegionConfig β X)) := hbase
    _ ≤ 8 * (√C₁ * (n : ℝ) ^ (-K / 4)) * ((1 + C₂) * (n : ℝ) ^ (2 : ℝ)) := by
        gcongr
    _ = 8 * √C₁ * (1 + C₂) * (n : ℝ) ^ (2 - K / 4) := by
        rw [show (2 : ℝ) - K / 4 = -K / 4 + 2 by ring, Real.rpow_add hn0]
        ring

/-- **The polynomial scale of the comparison** (`eq:amplification-output`). In the setting of
`ManyBody.regionMutualInformation_le_of_supported_unitary`, let `‖U φ - η‖ ≤ C₁ n^(-K/2)` with
`K ≥ 4(M + 2)` and `log dim X ≤ C₂ n²`. Then every part `X'` of `X` has
`I_φ(X' : J) ≤ 8 √C₁ (1 + C₂) n^(-M)`. The source fixes `K ≥ 4(M + 3)`, which satisfies this
hypothesis. Two-dimensional area law, `09-amplification.tex`, lines 545 and 550–561. -/
theorem regionMutualInformation_le_inv_pow_of_supported_unitary
    {φ η : EuclideanSpace ℂ ((v : V) → β v)} (hφ : ‖φ‖ = 1) (hη : ‖η‖ = 1)
    {X J S : Finset V} (hXJ : Disjoint X J) (hS : Disjoint S (X ∪ J))
    {U : Matrix ((v : V) → β v) ((v : V) → β v) ℂ}
    (hU : U ∈ supportedOperators β S) (hUu : Uᴴ * U = 1)
    (hprod : regionMutualInformation η X J = 0) {C₁ C₂ : ℝ} {n M K : ℕ} (hn : 1 ≤ n)
    (hK : 4 * (M + 2) ≤ K) (hδ : ‖toEuclideanLin U φ - η‖ ≤ C₁ * (n : ℝ) ^ (-(K : ℝ) / 2))
    (hdim : Real.log (Fintype.card (RegionConfig β X)) ≤ C₂ * (n : ℝ) ^ 2) :
    ∀ X' ⊆ X, regionMutualInformation φ X' J ≤ 8 * √C₁ * (1 + C₂) * ((n : ℝ) ^ M)⁻¹ := by
  intro X' hX'
  refine (regionMutualInformation_mono_left β φ X' X J hX' hXJ).trans ?_
  have h := mutualInformation_le_rpow_of_supported_unitary β hφ hη hXJ hS hU hUu hprod hn hδ
    hdim
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hC₂ : 0 ≤ C₂ := by
    have h0 := (Real.log_nonneg (one_le_card_configuration β hφ X)).trans hdim
    have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    nlinarith
  have hKr : (4 * ((M : ℝ) + 2)) ≤ K := by exact_mod_cast hK
  have hpow : (n : ℝ) ^ (2 - (K : ℝ) / 4) ≤ ((n : ℝ) ^ M)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  exact h.trans (by gcongr)

end ManyBody
