/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.AGSPFavorableEntropy

/-!
# Axiom check and boundary applications of the favorable entropy estimate

The entropy theorem is applied to the identity on a one-dimensional space
with shrinking parameter -1, and to the projection onto |00⟩ on two qubits
with shrinking parameter 0. The unit vector, fixed-vector equation,
orthogonal-complement condition and operator-Schmidt-rank bound are proved
from the same explicit data as in ProductOverlapBootstrapAxioms.
-/

set_option autoImplicit false

open scoped Matrix InnerProductSpace ComplexOrder

/-- info:
'Matrix.vonNeumannEntropy_reduced_le_four_log_of_operatorSchmidtRank' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.vonNeumannEntropy_reduced_le_four_log_of_operatorSchmidtRank

namespace Matrix

private theorem euclidean_inner_eq_raw
    {ι : Type*} [Fintype ι] (x y : EuclideanSpace ℂ ι) :
    ⟪x, y⟫_ℂ = star (WithLp.ofLp x) ⬝ᵥ WithLp.ofLp y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  exact dotProduct_comm _ _

private theorem norm_one_of_raw_unit
    {ι : Type*} [Fintype ι] (x : ι → ℂ) (hx : star x ⬝ᵥ x = 1) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ = 1 := by
  have hs := Matrix.re_star_dotProduct_self_eq_norm_sq x
  rw [hx] at hs
  change (1 : ℝ) = ‖(WithLp.toLp 2 x : EuclideanSpace ℂ ι)‖ ^ 2 at hs
  apply (sq_eq_sq₀ (norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℂ ι))
    zero_le_one).mp
  simpa only [one_pow] using hs.symm


/-- The identity on the one-dimensional bipartite space satisfies the
shrinking condition with δ=-1: no unit vector is perpendicular to its fixed
unit vector. The favorable entropy theorem is applied to these actual data. -/
private theorem negative_shrinking_fin_one_pair_entropy_boundary :
    let C := schmidtCoeffMatrix (fun _ : Fin 1 × Fin 1 ↦ (1 : ℂ))
    vonNeumannEntropy (C * Cᴴ) (posSemidef_self_mul_conjTranspose C).isHermitian ≤ 0 := by
  classical
  let Γ : EuclideanSpace ℂ (Fin 1 × Fin 1) :=
    WithLp.toLp 2 (fun _ ↦ (1 : ℂ))
  have hΓ : ‖Γ‖ = 1 := by
    apply norm_one_of_raw_unit
    norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_one]
  have hfix : toEuclideanLin
      (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) Γ = Γ := by
    change WithLp.toLp 2 ((1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) *ᵥ
      WithLp.ofLp Γ) = Γ
    rw [Matrix.one_mulVec, WithLp.toLp_ofLp]
  have hperp : ∀ ψ : EuclideanSpace ℂ (Fin 1 × Fin 1),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, toEuclideanLin
          (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) ψ⟫_ℂ = 0 ∧
          ‖toEuclideanLin
            (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) ψ‖ ^ 2 ≤ (-1 : ℝ) := by
    intro ψ hψ horth
    have hp : WithLp.ofLp ψ (0, 0) = 0 := by
      simpa [Γ, euclidean_inner_eq_raw, dotProduct,
        Fintype.sum_prod_type, Fin.sum_univ_one] using horth
    have hzero : ψ = 0 := by
      ext p
      have hcoord : p = ((0 : Fin 1), (0 : Fin 1)) := Subsingleton.elim _ _
      simpa only [hcoord, WithLp.ofLp_zero, Pi.zero_apply] using hp
    have hbad : (0 : ℝ) = 1 := by
      simpa only [hzero, norm_zero] using hψ
    exact False.elim (zero_ne_one hbad)
  have hrank : operatorSchmidtRank
      (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) ≤ 1 := by
    apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    refine ⟨fun _ : Fin 1 ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ),
      fun _ : Fin 1 ↦ (1 : Matrix (Fin 1) (Fin 1) ℂ), ?_⟩
    simp only [Fin.sum_univ_one, one_kronecker_one]
  have result := vonNeumannEntropy_reduced_le_four_log_of_operatorSchmidtRank
    (D := 1) (δ := (-1 : ℝ))
    (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)
    Γ hΓ hfix hperp hrank (by norm_num)
  simpa only [Nat.cast_one, Real.log_one, mul_zero, Γ, WithLp.ofLp_toLp] using result


/-- The |00⟩ projection on two qubits annihilates its three-dimensional
orthogonal complement. The favorable entropy theorem is applied with D=1
and δ=0, using the original |00⟩ vector and its actual coefficient matrix. -/
private theorem zero_shrinking_fin_two_projection_entropy_boundary :
    let C := schmidtCoeffMatrix (Pi.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ))
    vonNeumannEntropy (C * Cᴴ) (posSemidef_self_mul_conjTranspose C).isHermitian ≤ 0 := by
  classical
  let Γ : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
    WithLp.toLp 2 (Pi.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ))
  let K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    Matrix.single (0, 0) (0, 0) 1
  have hΓ : ‖Γ‖ = 1 := by
    apply norm_one_of_raw_unit
    norm_num [dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.single_apply]
  have hinner (ψ : EuclideanSpace ℂ (Fin 2 × Fin 2)) :
      ⟪Γ, ψ⟫_ℂ = WithLp.ofLp ψ (0, 0) := by
    rw [euclidean_inner_eq_raw]
    simp [Γ, dotProduct, Pi.single_apply]
  have hfix : toEuclideanLin K Γ = Γ := by
    change WithLp.toLp 2
      (K *ᵥ Pi.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ)) =
        WithLp.toLp 2 (Pi.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ))
    simp only [K, Matrix.single_mulVec_eq, Pi.single_eq_same, one_mul, one_smul]
  have hperp : ∀ ψ : EuclideanSpace ℂ (Fin 2 × Fin 2),
      ‖ψ‖ = 1 → ⟪Γ, ψ⟫_ℂ = 0 →
        ⟪Γ, toEuclideanLin K ψ⟫_ℂ = 0 ∧
          ‖toEuclideanLin K ψ‖ ^ 2 ≤ (0 : ℝ) := by
    intro ψ _ horth
    have hψ00 : WithLp.ofLp ψ (0, 0) = 0 := (hinner ψ).symm.trans horth
    have hzero : toEuclideanLin K ψ = 0 := by
      change WithLp.toLp 2 (K *ᵥ WithLp.ofLp ψ) = 0
      simp only [K, Matrix.single_mulVec_eq, one_mul, hψ00,
        zero_smul, WithLp.toLp_zero]
    simp only [hzero, inner_zero_right, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0), le_refl, and_self]
  have hrank : operatorSchmidtRank K ≤ 1 := by
    apply operatorSchmidtRank_le_of_hasOperatorSchmidtDecomposition
    refine ⟨fun _ : Fin 1 ↦ (Matrix.single (0 : Fin 2) 0 (1 : ℂ)),
      fun _ : Fin 1 ↦ (Matrix.single (0 : Fin 2) 0 (1 : ℂ)), ?_⟩
    simp only [Fin.sum_univ_one, Matrix.single_kronecker_single, one_mul, K]
  have result := vonNeumannEntropy_reduced_le_four_log_of_operatorSchmidtRank
    (D := 1) (δ := (0 : ℝ)) K Γ hΓ hfix hperp hrank (by norm_num)
  simpa only [Nat.cast_one, Real.log_one, mul_zero, Γ, WithLp.ofLp_toLp] using result

end Matrix
