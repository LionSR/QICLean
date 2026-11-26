/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Word.WordMultiplicity
import QICLean.Analysis.FunctionalCalculus.ViableSubspaceSpectralProjector
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Actual operator words in powers of a tensor decomposition

A finite decomposition of an improving operator gives its actual powered
family by taking ordered products of the retained factors. The same order
is used in the environment factors. No commutativity of the summands is
required. The low spectral target is fixed before the power and the viable
input space. This supports ALVV, arXiv:1602.08828v2, `def:spectral-AGSP`,
lines 570–581, and `l:er`, lines 597–622.

It also contains the following results.

* `ContinuousLinearMap.invariant_subspace_bounds_pow`,
  `ContinuousLinearMap.invariant_subspace_bounds_conj`: bounds on an invariant subspace and its
  orthogonal complement.
* `Submodule.IsViable.word_power_of_tensor_decomposition`: actual operator words from
  invariant-subspace bounds.
-/

section OperatorPower

open scoped BigOperators TensorProduct

namespace TensorProduct

variable {𝕜 M R : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R]

/-- Ordered simultaneous products of the two factors give the actual
product of tensor operators. Supporting ALVV, arXiv:1602.08828v2,
`def:spectral-AGSP`, lines 570–581. -/
lemma prod_mapL_ofFn {ι : Type*} (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (r : ℕ) (w : Fin r → ι) :
    (List.ofFn (fun j ↦ mapL (A (w j)) (B (w j)))).prod =
      mapL (List.ofFn (fun j ↦ A (w j))).prod (List.ofFn (fun j ↦ B (w j))).prod := by
  induction r with
  | zero => simp [← ContinuousLinearMap.coe_inj]
  | succ r ih =>
    simp only [List.ofFn_succ, List.prod_cons, ih, mapL_mul]

/-- The actual power of a finite tensor sum is decomposed by its ordered
operator words. Empty alphabets and exponent zero are included. Supporting
ALVV, arXiv:1602.08828v2, `def:spectral-AGSP`, lines 570–581,
and `l:er`, lines 597–622. -/
lemma pow_sum_mapL_eq_sum_words {ι : Type*} [Fintype ι]
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R) (r : ℕ) :
    (∑ i, mapL (A i) (B i)) ^ r =
      ∑ w : Fin r → ι,
        mapL (List.ofFn (fun j ↦ A (w j))).prod (List.ofFn (fun j ↦ B (w j))).prod := by
  rw [Fintype.sum_pow_eq_sum_ordered_words]
  exact Finset.sum_congr rfl fun w _ ↦ prod_mapL_ofFn A B r w

end TensorProduct

namespace Submodule

variable {𝕜 M R ι n : Type*} [RCLike 𝕜]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]
  [Fintype ι] [Fintype n]

/-- The actual finite operator-word family improves viability for the same
fixed low spectral target, with cardinality raised to the power and squared
suppression `Delta ^ r`. Supporting ALVV, arXiv:1602.08828v2,
`def:spectral-AGSP`, lines 570–581, and `l:er`, lines 597–622. -/
lemma IsSpectralProjector.viability_word_power
    {K H : M ⊗[𝕜] R →L[𝕜] M ⊗[𝕜] R}
    {b : OrthonormalBasis n 𝕜 (M ⊗[𝕜] R)} {h k : n → ℝ}
    {eta0 eta1 Delta : ℝ}
    (hK : IsSpectralProjector K H b h k eta0 eta1 Delta)
    (hgap : ∀ j, h j ≤ eta0 ∨ eta1 ≤ h j) (hDelta : 0 ≤ Delta)
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (hdec : K = ∑ i, TensorProduct.mapL (A i) (B i)) (r : ℕ) :
    let T := span 𝕜 (b '' {j | h j ≤ eta0})
    ∀ (S : Submodule 𝕜 M) (delta : ℝ), IsViable delta S T → delta < 1 →
      let grow := ⨆ w : Fin r → ι,
        S.map ((List.ofFn (fun j ↦ A (w j))).prod : M →ₗ[𝕜] M)
      Module.finrank 𝕜 grow ≤ Fintype.card ι ^ r * Module.finrank 𝕜 S ∧
        IsViable (Delta ^ r / (1 - delta) ^ 2) grow T := by
  intro T S delta hS hdelta grow
  have hpower : K ^ r = ∑ w : Fin r → ι,
      TensorProduct.mapL (List.ofFn (fun j ↦ A (w j))).prod
        (List.ofFn (fun j ↦ B (w j))).prod := by
    rw [hdec, TensorProduct.pow_sum_mapL_eq_sum_words]
  obtain ⟨hKT, hKTo, hlow, hhigh⟩ := (hK.pow r).contract hgap
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    hS.map_of_tensor_decomposition
      (fun w : Fin r → ι ↦ (List.ofFn (fun j ↦ A (w j))).prod)
      (fun w : Fin r → ι ↦ (List.ofFn (fun j ↦ B (w j))).prod)
      hpower hdelta (pow_nonneg hDelta r) hKT hKTo hlow hhigh

end Submodule

end OperatorPower

section InvariantOperatorBounds

/-!
## Bounds on an invariant subspace and its orthogonal complement

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

end InvariantOperatorBounds

section InvariantTensorWordPower

/-!
## Actual operator words from invariant-subspace bounds

A fixed tensor decomposition and target/complement bounds imply every
ordered-word error-reduction estimate for the same operator and target.
No common spectral eigenbasis, positivity or scalar action on the target
is required. This supports ALVV, arXiv:1602.08828v2,
Lemma l:er, lines 597–622, under a change of regional coordinates.
-/

open scoped BigOperators TensorProduct

namespace Submodule
variable {𝕜 M R ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [FiniteDimensional 𝕜 M]
  [NormedAddCommGroup R] [InnerProductSpace 𝕜 R] [FiniteDimensional 𝕜 R]

/-- The actual ordered words of one tensor decomposition improve viability
for every power and every viable input. The same operator supplies all
bounds; no spectral-projector or polynomial premise is added.
Supporting ALVV, arXiv:1602.08828v2, Lemma l:er, lines 597–622. -/
theorem IsViable.word_power_of_tensor_decomposition
    {T : Submodule 𝕜 (M ⊗[𝕜] R)} {Delta : ℝ}
    (K : M ⊗[𝕜] R →L[𝕜] M ⊗[𝕜] R)
    (A : ι → M →L[𝕜] M) (B : ι → R →L[𝕜] R)
    (hdec : K = ∑ i, TensorProduct.mapL (A i) (B i))
    (hDelta : 0 ≤ Delta)
    (hKT : ∀ t ∈ T, K t ∈ T) (hKTo : ∀ z ∈ Tᗮ, K z ∈ Tᗮ)
    (hlow : ∀ t ∈ T, ‖t‖ ≤ ‖K t‖)
    (hhigh : ∀ z ∈ Tᗮ, ‖K z‖ ^ 2 ≤ Delta * ‖z‖ ^ 2)
    (r : ℕ) (S : Submodule 𝕜 M) (delta : ℝ)
    (hS : IsViable delta S T) (hdelta : delta < 1) :
    let grow := ⨆ w : Fin r → ι,
      S.map ((List.ofFn (fun j ↦ A (w j))).prod : M →ₗ[𝕜] M)
    Module.finrank 𝕜 grow ≤ Fintype.card ι ^ r * Module.finrank 𝕜 S ∧
      IsViable (Delta ^ r / (1 - delta) ^ 2) grow T := by
  have hpower : K ^ r = ∑ w : Fin r → ι,
      TensorProduct.mapL (List.ofFn (fun j ↦ A (w j))).prod
        (List.ofFn (fun j ↦ B (w j))).prod := by
    rw [hdec, TensorProduct.pow_sum_mapL_eq_sum_words]
  obtain ⟨hT, hTo, hL, hH⟩ :=
    K.invariant_subspace_bounds_pow T Delta hDelta hKT hKTo hlow hhigh r
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    hS.map_of_tensor_decomposition
      (fun w : Fin r → ι ↦ (List.ofFn (fun j ↦ A (w j))).prod)
      (fun w : Fin r → ι ↦ (List.ofFn (fun j ↦ B (w j))).prod)
      hpower hdelta (pow_nonneg hDelta r) hT hTo hL hH

end Submodule

end InvariantTensorWordPower
