/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ChoiTypeMap.HaNegativePairing
import QICLean.Channel.ChoiTypeMap.YamagamiPositivity
import QICLean.Channel.DecomposablePPT

/-!
# Indecomposability of Choi-type positive maps

Wolf's Example 3.1, Equation (3.20), holds throughout `d ≥ 3`,
`1 ≤ n ≤ d - 2`. Ha's Theorem 2.1 (pp. 593--595) supplies the witness
`A_γ`; we use its factor swap with `γ = 1/2`. Both the witness and its
first-factor partial transpose have Schmidt number at most two, hence are
positive semidefinite. The negative normalized-Ω quadratic form contradicts
positivity of the ampliation of any decomposable map.

The detector is first proved in the `Fin d` basis, then transported back to
Wolf's cyclic basis. The factor `d` in the quadratic form is retained.
Only indecomposability, rather than Ha's stronger atomicity, is asserted.

## References

* [M. Wolf, *Quantum Channels & Operations*, Example 3.1, Equation (3.20)]
  [Wolf2012QChannels]
* [K.-C. Ha, *Atomic Positive Linear Maps in Matrix Algebras*,
  Theorem 2.1, pp. 593--595][Ha1998AtomicPositiveMaps]
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {d : ℕ} [NeZero d]

/-- **Ha, Theorem 2.1, pp. 593--595.** The factor-swapped PPT witness
rules out decomposability in the standard-coordinate realization. -/
theorem choiTypeMapFin_not_isDecomposablePositiveMap
    (hd : 3 ≤ d) {n : ℕ} (hn₁ : 1 ≤ n) (hn₂ : n ≤ d - 2) :
    ¬ IsDecomposablePositiveMap (choiTypeMapFin d n) := by
  have hγ₀ : (0 : ℝ) < 1 / 2 := by norm_num
  have hγ₁ : (1 / 2 : ℝ) < 1 := by norm_num
  refine not_isDecomposablePositiveMap_of_isPPT_not_tensorMapId_posSemidef
    (tensorFactorSwap_haAGamma_hasSchmidtNumberLE_two (d := d) (1 / 2)).posSemidef
    (partialTransposeLeft_tensorFactorSwap_haAGamma_hasSchmidtNumberLE_two
      hd hγ₀).posSemidef ?_
  intro hPSD
  have hq := hPSD.dotProduct_mulVec_nonneg (omegaVec d)
  have hscaled : 0 ≤ (d : ℂ) *
      (star (omegaVec d) ⬝ᵥ
        (tensorMapId (choiTypeMapFin d n) (tensorFactorSwap (haAGamma d (1 / 2))) *ᵥ
          omegaVec d)) := mul_nonneg (by positivity) hq
  exact (not_lt_of_ge (Complex.nonneg_iff.mp hscaled).1)
    (choiTypeMapFin_haAGamma_omegaVec_quadraticForm_re_neg hd hn₁ hn₂ hγ₀ hγ₁)

private theorem isKrausCP_reindex {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) {E : Matrix J J ℂ →ₗ[ℂ] Matrix J J ℂ} (hE : IsKrausCP E) :
    IsKrausCP ((reindexLinearEquiv ℂ ℂ e e).symm.toLinearMap ∘ₗ E ∘ₗ
      (reindexLinearEquiv ℂ ℂ e e).toLinearMap) := by
  obtain ⟨r, K, hK⟩ := hE
  refine ⟨r, fun i ↦ reindex e.symm e.symm (K i), fun X ↦ ?_⟩
  change reindex e.symm e.symm (E (reindex e e X)) = _
  rw [hK]
  change (reindexLinearEquiv ℂ ℂ e.symm e.symm)
    (∑ i, K i * reindex e e X * (K i)ᴴ) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (reindexRingEquiv ℂ e.symm) (K i * reindex e e X * (K i)ᴴ) = _
  rw [map_mul, map_mul]
  change reindex e.symm e.symm (K i) * reindex e.symm e.symm (reindex e e X) *
    reindex e.symm e.symm (K i)ᴴ = _
  rw [← conjTranspose_reindex]
  have hX : reindex e.symm e.symm (reindex e e X) = X := by
    ext a b
    simp [reindex_apply]
  rw [hX]

/-- **Wolf, Example 3.1, Equation (3.20); Ha, Theorem 2.1.**
The Choi-type map is not decomposable for every source parameter.
Reindexing a hypothetical CP plus completely copositive decomposition
would give one for the standard-coordinate map detected above. -/
theorem choiTypeMap_not_isDecomposablePositiveMap
    (hd : 3 ≤ d) {n : ℕ} (hn₁ : 1 ≤ n) (hn₂ : n ≤ d - 2) :
    ¬ IsDecomposablePositiveMap (choiTypeMap d n) := by
  intro h
  obtain ⟨Ecp, Eccp, hcp, hccp, hsum⟩ := h
  let e : Fin d ≃ ZMod d := ZMod.finEquiv d
  let R := reindexLinearEquiv ℂ ℂ e e
  apply choiTypeMapFin_not_isDecomposablePositiveMap hd hn₁ hn₂
  refine ⟨R.symm.toLinearMap ∘ₗ Ecp ∘ₗ R.toLinearMap,
    R.symm.toLinearMap ∘ₗ Eccp ∘ₗ R.toLinearMap,
    isKrausCP_reindex e hcp, ?_, ?_⟩
  · have hcomm : (R.symm.toLinearMap ∘ₗ Eccp ∘ₗ R.toLinearMap).comp
        (transposeLinearMapComplex (Fin d)) =
        R.symm.toLinearMap ∘ₗ (Eccp.comp (transposeLinearMapComplex (ZMod d))) ∘ₗ
          R.toLinearMap := by
      ext X i j
      rfl
    change IsKrausCP _
    rw [hcomm]
    exact isKrausCP_reindex e hccp
  · ext X i j
    simp [choiTypeMapFin, hsum, R, e]

/-- **Wolf, Example 3.1, Equation (3.20).** For `d ≥ 3` and
`1 ≤ n ≤ d - 2`, the Choi-type map is positive and indecomposable. -/
theorem choiTypeMap_isIndecomposable
    (hd : 3 ≤ d) {n : ℕ} (hn₁ : 1 ≤ n) (hn₂ : n ≤ d - 2) :
    IsIndecomposablePositiveMap (choiTypeMap d n) :=
  ⟨choiTypeMap_isPositiveMap hd hn₁ hn₂,
    choiTypeMap_not_isDecomposablePositiveMap hd hn₁ hn₂⟩

end Matrix
