/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.AGSPRegionalEntropy

/-!
# Regional entropy of an explicit two-qubit product vector

The projection onto |00⟩ fixes that unit vector and annihilates its
orthogonal complement. Across every site region it has operator-Schmidt
rank at most one. The regional favorable-tradeoff theorem is applied to
the empty region and to the first site, using the same original vector
and operator in both cases.
-/

set_option autoImplicit false

open scoped Matrix InnerProductSpace ComplexOrder

/-- info:
'Entropy.regionEntropy_le_four_log_of_cutOperatorSchmidtRank' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.regionEntropy_le_four_log_of_cutOperatorSchmidtRank

namespace AGSPRegionalEntropyTest

private abbrev Config := Fin 2 → Fin 2

private def zeroConfig : Config := fun _ ↦ 0

private noncomputable def Ω : EuclideanSpace ℂ Config :=
  EuclideanSpace.single zeroConfig 1

private noncomputable def K : Matrix Config Config ℂ :=
  Matrix.single zeroConfig zeroConfig 1

/-- Concrete fixed-vector, shrinking and cut-rank facts for the same |00⟩ projector. -/
private theorem projector_data (A : Finset (Fin 2)) :
    ‖Ω‖ = 1 ∧ Matrix.toEuclideanLin K Ω = Ω ∧
      (∀ ψ : EuclideanSpace ℂ Config,
        ‖ψ‖ = 1 → ⟪Ω, ψ⟫_ℂ = 0 →
          ⟪Ω, Matrix.toEuclideanLin K ψ⟫_ℂ = 0 ∧
            ‖Matrix.toEuclideanLin K ψ‖ ^ 2 ≤ (0 : ℝ)) ∧
      Matrix.operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin 2 ↦ 2) A K) ≤ 1 := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Ω, PiLp.norm_single, norm_one]
  · change WithLp.toLp 2 (K *ᵥ Pi.single zeroConfig (1 : ℂ)) =
      WithLp.toLp 2 (Pi.single zeroConfig (1 : ℂ))
    simp only [K, Matrix.single_mulVec_eq, Pi.single_eq_same, one_mul, one_smul]
  · intro ψ _ horth
    have hψ : WithLp.ofLp ψ zeroConfig = 0 := by
      simpa [Ω, EuclideanSpace.inner_single_left] using horth
    have hzero : Matrix.toEuclideanLin K ψ = 0 := by
      change WithLp.toLp 2 (K *ᵥ WithLp.ofLp ψ) = 0
      simp only [K, Matrix.single_mulVec_eq, one_mul, hψ,
        zero_smul, WithLp.toLp_zero]
    simp [hzero]
  · let e := Entropy.cutEquiv (fun _ : Fin 2 ↦ 2) A
    have hcut : Entropy.cutOperator (n := fun _ : Fin 2 ↦ 2) A K =
        Matrix.single (e zeroConfig) (e zeroConfig) (1 : ℂ) := by
      simp only [Entropy.cutOperator, Matrix.reindex_apply, K,
        Matrix.submatrix_single_equiv, Equiv.symm_symm, e]
    rw [hcut]
    apply Matrix.operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    refine ⟨fun _ : Fin 1 ↦ Matrix.single (e zeroConfig).1 (e zeroConfig).1 (1 : ℂ),
      fun _ : Fin 1 ↦ Matrix.single (e zeroConfig).2 (e zeroConfig).2 (1 : ℂ), ?_⟩
    simp only [Fin.sum_univ_one, Matrix.single_kronecker_single, one_mul, Prod.mk.eta]

/-- The favorable-tradeoff estimate applies to the empty region. -/
example : Entropy.regionEntropy (n := fun _ : Fin 2 ↦ 2) ∅ Ω ≤ 0 := by
  obtain ⟨hΩ, hfix, hperp, hrank⟩ := projector_data ∅
  have result := Entropy.regionEntropy_le_four_log_of_cutOperatorSchmidtRank
    (n := fun _ : Fin 2 ↦ 2) ∅ K Ω hΩ hfix (D := 1) (δ := 0)
    hperp hrank (by norm_num)
  simpa only [Nat.cast_one, Real.log_one, mul_zero] using result

/-- The first site is a nonempty proper region with a two-dimensional local space. -/
example : Entropy.regionEntropy (n := fun _ : Fin 2 ↦ 2) {0} Ω ≤ 0 := by
  obtain ⟨hΩ, hfix, hperp, hrank⟩ := projector_data {0}
  have result := Entropy.regionEntropy_le_four_log_of_cutOperatorSchmidtRank
    (n := fun _ : Fin 2 ↦ 2) {0} K Ω hΩ hfix (D := 1) (δ := 0)
    hperp hrank (by norm_num)
  simpa only [Nat.cast_one, Real.log_one, mul_zero] using result

end AGSPRegionalEntropyTest
