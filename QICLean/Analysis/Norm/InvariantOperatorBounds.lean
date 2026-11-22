/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Bounds on an invariant subspace and its orthogonal complement

Minimum gain on a target and squared contraction on its orthogonal
complement pass to powers and unitary coordinate identifications.
These are generic operator estimates supporting ALVV,
arXiv:1602.08828v2, Definition spectral-AGSP and Lemma l:er,
lines 570–622. No scalar action or positivity on the target is assumed.
-/

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Powers preserve the target and its complement, retain minimum gain
one on the target, and raise squared contraction to the same power.
Supporting ALVV, arXiv:1602.08828v2, spectral-AGSP, lines 570–581. -/
theorem invariant_subspace_bounds_pow
    (K : E →L[𝕜] E) (T : Submodule 𝕜 E) (Delta : ℝ) (hDelta : 0 ≤ Delta)
    (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ z ∈ Tᗮ, K z ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ z ∈ Tᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) (r : ℕ) :
    (∀ t ∈ T, (K ^ r) t ∈ T) ∧ (∀ z ∈ Tᗮ, (K ^ r) z ∈ Tᗮ) ∧
    (∀ t ∈ T, ‖t‖ ≤ ‖(K ^ r) t‖) ∧
    (∀ z ∈ Tᗮ, ‖(K ^ r) z‖ ^ 2 ≤ Delta ^ r * ‖z‖ ^ 2) := by
  induction r with
  | zero => simp
  | succ r ih =>
    obtain ⟨hT, hTo, hL, hH⟩ := ih
    have heq (x : E) : (K ^ (r + 1)) x = K ((K ^ r) x) := by
      rw [pow_succ', mul_apply_eq_comp]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [heq]
      exact hKT _ (hT t ht)
    · intro z hz
      rw [heq]
      exact hKTo _ (hTo z hz)
    · intro t ht
      rw [heq]
      exact (hL t ht).trans (hlow _ (hT t ht))
    · intro z hz
      rw [heq]
      calc
        ‖K ((K ^ r) z)‖ ^ 2 ≤ Delta * ‖(K ^ r) z‖ ^ 2 := hhigh _ (hTo z hz)
        _ ≤ Delta * (Delta ^ r * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left (hH z hz) hDelta
        _ = Delta ^ (r + 1) * ‖z‖ ^ 2 := by rw [pow_succ' Delta r, mul_assoc]

/-- Unitary identification preserves the target/complement bounds for the
same operator, without requiring a scalar action on its target.
Supporting ALVV, arXiv:1602.08828v2, spectral-AGSP and error reduction,
lines 570–622. -/
theorem invariant_subspace_bounds_conj
    (I : E ≃ₗᵢ[𝕜] F) (K : E →L[𝕜] E) (T : Submodule 𝕜 E) (Delta : ℝ)
    (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ z ∈ Tᗮ, K z ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ z ∈ Tᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) :
    let K' := I.toContinuousLinearEquiv.conjContinuousAlgEquiv K
    let T' := T.map I.toLinearMap
    (∀ t ∈ T', K' t ∈ T') ∧ (∀ z ∈ T'ᗮ, K' z ∈ T'ᗮ) ∧
    (∀ t ∈ T', ‖t‖ ≤ ‖K' t‖) ∧
    (∀ z ∈ T'ᗮ, ‖K' z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2) := by
  intro K' T'
  have heq (x : E) : K' (I x) = I (K x) := by
    change I (K (I.symm (I x))) = I (K x)
    rw [I.symm_apply_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := ht
    change K' (I x) ∈ T'
    rw [heq]
    exact Submodule.mem_map_of_mem (hKT x hx)
  · intro z hz
    change z ∈ (T.map I.toLinearMap)ᗮ at hz
    rw [← T.map_orthogonal_equiv I] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    change K' (I x) ∈ (T.map I.toLinearMap)ᗮ
    rw [heq, ← T.map_orthogonal_equiv I]
    exact Submodule.mem_map_of_mem (hKTo x hx)
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := ht
    change ‖I x‖ ≤ ‖K' (I x)‖
    simpa only [heq, I.norm_map] using hlow x hx
  · intro z hz
    change z ∈ (T.map I.toLinearMap)ᗮ at hz
    rw [← T.map_orthogonal_equiv I] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    change ‖K' (I x)‖ ^ 2 ≤ Delta * ‖I x‖ ^ 2
    simpa only [heq, I.norm_map] using hhigh x hx

end ContinuousLinearMap
