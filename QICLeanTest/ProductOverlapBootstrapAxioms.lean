/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ProductOverlapBootstrap

/-!
# Axiom check and applications of the product-overlap estimate

The applications include an identity on a one-dimensional space with negative
shrinking parameter, the projection onto |00⟩ on two qubits with zero shrinking
parameter, and either tensor factor being empty. The projection has a
three-dimensional orthogonal complement.
-/

set_option autoImplicit false
set_option linter.hashCommand false

open scoped Matrix InnerProductSpace

/-- info:
'Matrix.exists_unit_product_overlap_ge_of_operatorSchmidtRank' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_unit_product_overlap_ge_of_operatorSchmidtRank

/-- info:
'Matrix.schmidtRank_le_one_of_operatorSchmidtRank_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.schmidtRank_le_one_of_operatorSchmidtRank_le_one

/-- info:
'Matrix.schmidtRank_smul_eq_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.schmidtRank_smul_eq_of_ne_zero

/-- info:
'Matrix.perpendicular_shrinking_homogeneous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.perpendicular_shrinking_homogeneous

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

end Matrix

namespace Matrix

/-- In a one-dimensional Hilbert space, the identity permits δ=-1 because
there is no unit vector orthogonal to its given unit vector. Both the overlap
bound and exact Schmidt-rank endpoint are applied to these same concrete data. -/
private theorem negative_shrinking_fin_one_pair_boundary :
    (∃ (u : Fin 1 → ℂ) (v : Fin 1 → ℂ),
      let φ : EuclideanSpace ℂ (Fin 1 × Fin 1) :=
        WithLp.toLp 2 (fun p ↦ u p.1 * v p.2)
      ‖φ‖ = 1 ∧
        1 / Real.sqrt 2 ≤
          ‖⟪(WithLp.toLp 2 (fun _ : Fin 1 × Fin 1 ↦ (1 : ℂ)) :
            EuclideanSpace ℂ (Fin 1 × Fin 1)), φ⟫_ℂ‖) ∧
      schmidtRank (fun _ : Fin 1 × Fin 1 ↦ (1 : ℂ)) ≤ 1 := by
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
  have result := exists_unit_product_overlap_ge_of_operatorSchmidtRank
    (D := 1) (δ := (-1 : ℝ))
    (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)
    Γ hΓ hfix hperp hrank (by norm_num)
  constructor
  · simpa only [Nat.cast_one, mul_one, Γ] using result
  · exact schmidtRank_le_one_of_operatorSchmidtRank_le_one
      (δ := (-1 : ℝ))
      (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ)
      Γ hΓ hfix hperp hrank (by norm_num)

/-- An empty left factor cannot satisfy the unit-vector premise. -/
example {n : Type*} [Fintype n]
    (Γ : EuclideanSpace ℂ (Empty × n)) : ‖Γ‖ ≠ 1 := by
  have hzero : Γ = 0 := by
    ext p
    exact Empty.elim p.1
  simpa only [hzero, norm_zero] using (zero_ne_one : (0 : ℝ) ≠ 1)

/-- An empty right factor likewise cannot satisfy the unit-vector premise. -/
example {m : Type*} [Fintype m]
    (Γ : EuclideanSpace ℂ (m × Empty)) : ‖Γ‖ ≠ 1 := by
  have hzero : Γ = 0 := by
    ext p
    exact Empty.elim p.2
  simpa only [hzero, norm_zero] using (zero_ne_one : (0 : ℝ) ≠ 1)

end Matrix


namespace Matrix

/-- The projection onto |00⟩ in a two-qubit space kills its three-dimensional
orthogonal complement. The full overlap theorem is applied with D=1 and δ=0. -/
private theorem zero_shrinking_fin_two_projection_boundary :
    (∃ (u : Fin 2 → ℂ) (v : Fin 2 → ℂ),
      let φ : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
        WithLp.toLp 2 (fun p ↦ u p.1 * v p.2)
      ‖φ‖ = 1 ∧
        1 / Real.sqrt 2 ≤
          ‖⟪(WithLp.toLp 2
            (Pi.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ)) :
              EuclideanSpace ℂ (Fin 2 × Fin 2)), φ⟫_ℂ‖) ∧
      schmidtRank (Pi.single ((0 : Fin 2), (0 : Fin 2)) (1 : ℂ)) ≤ 1 := by
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
  have result := exists_unit_product_overlap_ge_of_operatorSchmidtRank
    (D := 1) (δ := (0 : ℝ)) K Γ hΓ hfix hperp hrank (by norm_num)
  constructor
  · simpa only [Nat.cast_one, mul_one, Γ] using result
  · exact schmidtRank_le_one_of_operatorSchmidtRank_le_one
      (δ := (3 / 4 : ℝ)) K Γ hΓ hfix
      (fun ψ hψ horth ↦ ⟨(hperp ψ hψ horth).1,
        (hperp ψ hψ horth).2.trans (by norm_num)⟩)
      hrank (by norm_num)

end Matrix
