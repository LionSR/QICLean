/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RestoringOperators
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Abel

/-!
# Column and adjoint identities for restoring operators

The physical index is `(X × Y) × Z`; the enlarged index is
`((X × X) × (X × Y)) × Z`, in `s,e,X,Y,Z` order. All Hilbert-space
norms below are the Euclidean (`L²`) norms, including the blank norms.

The copied vector is defined by relabeling the original `X` coordinate as `e`
and inserting the `s` and `X` blanks. In particular, its equality with the
source's Schmidt expression is a direct substitution, not an additional
hypothesis. The vector identities hold for every physical vector, without
normalization or a prescribed marginal spectrum. Positivity is required only
on the selected coordinates in the inverse-weight cancellation.

## References

* Two-dimensional area-law manuscript (September 24, 2026),
  `09-amplification.tex`, lines 324–415, especially
  `eq:amplification-column-identity`, `eq:amplification-adjoint-identity`, and
  `eq:amplification-adjoint-error`.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix Finset
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

namespace Entropy

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Fintype Z]

/-- Reassociation separating both ancillas from the physical system.
Source: `09-amplification.tex`, lines 399–408. -/
def restoringPhysicalGrouping :
    (((X × X) × (X × Y)) × Z) ≃ ((X × X) × ((X × Y) × Z)) :=
  Equiv.prodAssoc (X × X) (X × Y) Z

/-- The relabeling and blank insertion `ℛ_X`, including the untouched `Z`.
Source: `eq:amplification-swapped-state`, lines 334–339. -/
noncomputable def restoringCopy (sBlank xBlank : X → ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    EuclideanSpace ℂ (((X × X) × (X × Y)) × Z) :=
  WithLp.toLp 2 fun i ↦ sBlank i.1.1.1 * xBlank i.1.2.1 * Ω ((i.1.1.2, i.1.2.2), i.2)

/-- The original physical vector with the two ancillary blanks inserted.
Source: `eq:amplification-column-identity`, lines 368–371. -/
noncomputable def restoringInitial (sBlank eBlank : X → ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    EuclideanSpace ℂ (((X × X) × (X × Y)) × Z) :=
  WithLp.toLp 2 fun i ↦ sBlank i.1.1.1 * eBlank i.1.1.2 * Ω (i.1.2, i.2)

/-- The physical vector tensored with `∑ x, √p_x |x,x⟩` on the ancillas.
When `p` is nonnegative, zero-probability coordinates contribute zero.
Source: `eq:amplification-restored-state`, lines 338–341. -/
noncomputable def restoringRestored (p : X → ℝ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    EuclideanSpace ℂ (((X × X) × (X × Y)) × Z) :=
  WithLp.toLp 2 fun i ↦
    (if i.1.1.1 = i.1.1.2 then (Real.sqrt (p i.1.1.1) : ℂ) else 0) * Ω (i.1.2, i.2)

/-- The selected orthogonal coordinate projection, including all selected
coordinates and no unselected coordinates. Source: lines 303–309 and 400–402. -/
noncomputable def restoringSelectedProjection (E : Finset X) : Matrix X X ℂ :=
  diagonal fun x ↦ if x ∈ E then 1 else 0

omit [Fintype X] in
/-- The selected coordinate projection is Hermitian.
Source: `09-amplification.tex`, lines 303–309 and 403. -/
theorem restoringSelectedProjection_isHermitian (E : Finset X) :
    (restoringSelectedProjection E).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.2
  intro x
  by_cases hx : x ∈ E <;> simp [hx]

/-- The selected coordinate projection is idempotent.
Source: `09-amplification.tex`, lines 303–309 and 403. -/
theorem restoringSelectedProjection_mul_self (E : Finset X) :
    restoringSelectedProjection E * restoringSelectedProjection E =
      restoringSelectedProjection E := by
  simp [restoringSelectedProjection, diagonal_mul_diagonal, mul_ite]

/-- The actual restoring operator with both spectator systems explicit.
Source: `09-amplification.tex`, lines 355–358. -/
noncomputable def restoringGlobal [DecidableEq Z] (E : Finset X) (p : X → ℝ)
    (sBlank xBlank : X → ℂ) (Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) :
    Matrix (((X × X) × (X × Y)) × Z) (((X × X) × (X × Y)) × Z) ℂ :=
  restoringOperatorWithAncilla E p sBlank xBlank Q T ⊗ₖ (1 : Matrix Z Z ℂ)

/-- The full-basis column operator with the remote spectator explicit.
Source: `eq:amplification-column-operator`, lines 361–368. -/
noncomputable def restoringColumnGlobal [DecidableEq Z] (E : Finset X) (p : X → ℝ)
    (sBlank eBlank : X → ℂ) (Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) :
    Matrix (((X × X) × (X × Y)) × Z) (((X × X) × (X × Y)) × Z) ℂ :=
  columnOperator E p sBlank eBlank Q T ⊗ₖ (1 : Matrix Z Z ℂ)

/-- A physical operator acts on `((X,Y),Z)` and fixes both ancillas.
Source: `eq:amplification-adjoint-identity`, lines 402–408. -/
noncomputable def restoringPhysicalLift
    (L : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ) :
    Matrix (((X × X) × (X × Y)) × Z) (((X × X) × (X × Y)) × Z) ℂ :=
  ((1 : Matrix (X × X) (X × X) ℂ) ⊗ₖ L).submatrix
    restoringPhysicalGrouping restoringPhysicalGrouping

omit [DecidableEq X] in
private theorem blank_sum_eq_one (b : X → ℂ)
    (hb : ‖WithLp.toLp 2 b‖ = 1) : ∑ i, star (b i) * b i = 1 := by
  calc
    _ = inner ℂ (WithLp.toLp 2 b) (WithLp.toLp 2 b) := by
      simp only [EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply, mul_comm]
    _ = (‖WithLp.toLp 2 b‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K _
    _ = 1 := by rw [hb]; simp

private theorem kronecker_one_mulVec_apply {A : Type*} [Fintype A] [DecidableEq Z]
    (M : Matrix A A ℂ) (v : A × Z → ℂ) (a : A) (z : Z) :
    ((M ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ v) (a, z) = ∑ b, M a b * v (b, z) := by
  simp [mulVec, dotProduct, kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul]

private theorem physical_block_apply (Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) (b : X → ℂ) (a : X × Y) (t x : X) (y : Y) :
    (Q * (basisColumn t b ⊗ₖ T)) a (x, y) =
      star (b x) * ∑ k, Q a (t, k) * T k y := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, kroneckerMap_apply,
    basisColumn, vecMulVec_apply, Pi.star_apply, Pi.single_apply]
  simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem restoring_with_ancilla_apply (E : Finset X) (p : X → ℝ)
    (sBlank xBlank : X → ℂ) (Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) (s e s' e' : X) (a : X × Y) (x : X) (y : Y) :
    restoringOperatorWithAncilla E p sBlank xBlank Q T ((s, e), a) ((s', e'), (x, y)) =
      (if s ∈ E then restoringWeight (p s) else 0) * star (sBlank s') *
        star (xBlank x) * (∑ k, Q a (s, k) * T k y) *
          (if e = e' then 1 else 0) := by
  simp only [restoringOperatorWithAncilla, Matrix.submatrix_apply,
    restoringAncillaGrouping, Equiv.coe_fn_mk, kroneckerMap_apply,
    restoringOperator, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]
  simp_rw [physical_block_apply]
  simp only [basisColumn, vecMulVec_apply, Pi.star_apply, Pi.single_apply]
  simp only [ite_mul, zero_mul, one_mul, mul_ite, mul_zero]
  split_ifs <;> simp_all
  ring

private theorem column_operator_apply (E : Finset X) (p : X → ℝ)
    (sBlank eBlank : X → ℂ) (Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) (s e s' e' : X) (a : X × Y) (x : X) (y : Y) :
    columnOperator E p sBlank eBlank Q T ((s, e), a) ((s', e'), (x, y)) =
      (if s ∈ E then restoringWeight (p s) else 0) * star (sBlank s') *
        star (eBlank e') * (∑ k, Q a (s, k) * T k y) *
          (if e = x then 1 else 0) := by
  have hsingle (t u : X) : single t u (1 : ℂ) = basisColumn t (Pi.single u 1) := by
    ext i j
    by_cases hi : i = t <;> by_cases hj : j = u <;>
      simp_all [basisColumn, vecMulVec_apply, Matrix.single_apply] <;> aesop
  simp only [columnOperator, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    kroneckerMap_apply, hsingle]
  simp_rw [physical_block_apply]
  simp only [basisColumn, vecMulVec_apply, Pi.star_apply, Pi.single_apply]
  simp only [apply_ite, star_one, star_zero, ite_mul, zero_mul, one_mul,
    mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  split_ifs <;> simp_all
  ring

/-- Direct substitution into the actual column operator. Only the `X` and `e`
blanks need to be unit vectors; the `s` blank and the physical vector can be
arbitrary, and no positivity, projector, or Schmidt assumption is used.
Source: `eq:amplification-column-identity`, lines 368–371. -/
theorem restoringGlobal_mulVec_copy [DecidableEq Z] (E : Finset X) (p : X → ℝ)
    (sBlank xBlank eBlank : X → ℂ)
    (hx : ‖WithLp.toLp 2 xBlank‖ = 1) (he : ‖WithLp.toLp 2 eBlank‖ = 1)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    restoringGlobal E p sBlank xBlank Q T *ᵥ (restoringCopy sBlank xBlank Ω).ofLp =
      restoringColumnGlobal E p sBlank eBlank Q T *ᵥ
        (restoringInitial sBlank eBlank Ω).ofLp := by
  have hx' := blank_sum_eq_one xBlank hx
  have he' := blank_sum_eq_one eBlank he
  ext ⟨⟨⟨s, e⟩, x, y⟩, z⟩
  simp only [restoringGlobal, restoringColumnGlobal, kronecker_one_mulVec_apply,
    Fintype.sum_prod_type, restoring_with_ancilla_apply, column_operator_apply,
    restoringCopy, restoringInitial, WithLp.ofLp_toLp]
  by_cases hse : s ∈ E
  · simp only [hse, ite_true, mul_ite, ite_mul, mul_zero, zero_mul, mul_one,
      Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro s' _
    have hcontract (b : X → ℂ) :
        (∑ a : X, ∑ j : Y, restoringWeight (p s) * star (sBlank s') *
          star (b a) * (∑ k, Q (x, y) (s, k) * T k j) *
            (sBlank s' * b a * Ω ((e, j), z))) =
          (∑ a, star (b a) * b a) *
            (∑ j : Y, restoringWeight (p s) * star (sBlank s') *
              (∑ k, Q (x, y) (s, k) * T k j) * sBlank s' * Ω ((e, j), z)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hcontract xBlank, hcontract eBlank, hx', he']
  · simp [hse]

/-- Physical lifting commutes with insertion of the fixed ancillary pair.
This holds for arbitrary coefficients `p` and arbitrary physical operators.
Source: `09-amplification.tex`, lines 402–408. -/
theorem restoringPhysicalLift_mulVec_restored
    (L : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ) (p : X → ℝ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    restoringPhysicalLift L *ᵥ (restoringRestored p Ω).ofLp =
      (restoringRestored p (WithLp.toLp 2 (L *ᵥ Ω.ofLp))).ofLp := by
  ext ⟨⟨⟨s, e⟩, x, y⟩, z⟩
  simp only [restoringPhysicalLift, Matrix.submatrix_apply, restoringPhysicalGrouping,
    Equiv.prodAssoc, Equiv.coe_fn_mk, kroneckerMap_apply, mulVec, dotProduct,
    Fintype.sum_prod_type, restoringRestored, WithLp.ofLp_toLp, Matrix.one_apply,
    Prod.mk.injEq]
  simp only [ite_mul, mul_ite, zero_mul, one_mul, mul_zero,
    Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases hse : s = e
  · subst e
    simp [Finset.mul_sum, mul_left_comm]
  · have hne (a : X) : ¬(s = a ∧ e = a) := fun h ↦ hse (h.1.trans h.2.symm)
    simp [hse, hne]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Adjoint commutes with the explicitly reassociated physical lift.
Source: `eq:amplification-adjoint-identity`, lines 402–408. -/
theorem restoringPhysicalLift_conjTranspose
    (L : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ) :
    (restoringPhysicalLift L)ᴴ = restoringPhysicalLift Lᴴ := by
  simp [restoringPhysicalLift, conjTranspose_submatrix, conjTranspose_kronecker]

private theorem restoringWeight_mul_sqrt {p : ℝ} (hp : 0 < p) :
    star (restoringWeight p) * (Real.sqrt p : ℂ) = 1 := by
  have hs : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hp)
  have hsc : (Real.sqrt p : ℂ) ≠ 0 := by exact_mod_cast hs
  simp [restoringWeight, hsc]

/-- Inverse square roots cancel against the ancillary Schmidt coefficients.
The selected spectrum may be singular off the selection. No normalization,
idempotence, commutation, or operator norm estimate is assumed.
Source: `eq:amplification-adjoint-identity`, lines 402–408. -/
theorem restoringGlobal_adjoint_restored [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank : X → ℂ)
    {Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : Q.IsHermitian) (hT : T.IsHermitian)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    (restoringGlobal E p sBlank xBlank Q T)ᴴ *ᵥ (restoringRestored p Ω).ofLp =
      (restoringCopy sBlank xBlank
        (WithLp.toLp 2 ((((restoringSelectedProjection E ⊗ₖ T) * Q) ⊗ₖ
          (1 : Matrix Z Z ℂ)) *ᵥ Ω.ofLp))).ofLp := by
  have hQ' (a b : X × Y) : star (Q a b) = Q b a :=
    congrFun (congrFun hQ.eq b) a
  have hT' (a b : Y) : star (T a b) = T b a :=
    congrFun (congrFun hT.eq b) a
  ext ⟨⟨⟨s, e⟩, x, y⟩, z⟩
  simp only [restoringGlobal, conjTranspose_kronecker, conjTranspose_one,
    kronecker_one_mulVec_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    restoring_with_ancilla_apply, restoringRestored, restoringCopy,
    WithLp.ofLp_toLp, Matrix.mul_apply, restoringSelectedProjection,
    kroneckerMap_apply, Matrix.diagonal_apply]
  simp only [star_mul, star_star, star_sum, apply_ite, star_zero,
    hQ', hT', ite_mul, zero_mul, mul_zero, one_mul, mul_one,
    Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases he : e ∈ E
  · simp only [he, ite_true]
    have hc := restoringWeight_mul_sqrt (hp e he)
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    calc
      _ = (star (restoringWeight (p e)) * (Real.sqrt (p e) : ℂ)) *
          (sBlank s * xBlank x * T y c * Q (e, c) (a, b) * Ω ((a, b), z)) := by ring
      _ = _ := by rw [hc]; ring
  · simp [he]

/-- The actual adjoint identity for an arbitrary physical operator. The physical
lift fixes both ancillas, and the rightmost identity fixes the remote factor.
Source: `eq:amplification-adjoint-identity`, lines 402–408. -/
theorem restoringGlobal_adjoint_identity [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank : X → ℂ)
    {Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : Q.IsHermitian) (hT : T.IsHermitian)
    (L : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    (restoringGlobal E p sBlank xBlank Q T)ᴴ *ᵥ
        ((restoringPhysicalLift L)ᴴ *ᵥ (restoringRestored p Ω).ofLp) =
      (restoringCopy sBlank xBlank
        (WithLp.toLp 2 ((((restoringSelectedProjection E ⊗ₖ T) * Q) ⊗ₖ
          (1 : Matrix Z Z ℂ)) *ᵥ (Lᴴ *ᵥ Ω.ofLp)))).ofLp := by
  rw [restoringPhysicalLift_conjTranspose, restoringPhysicalLift_mulVec_restored]
  exact restoringGlobal_adjoint_restored E p hp sBlank xBlank hQ hT _

omit [DecidableEq X] in
/-- Copying and blank insertion preserve the Hilbert norm for unit blanks.
Source: `09-amplification.tex`, lines 399–401. -/
theorem restoringCopy_norm (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    ‖restoringCopy sBlank xBlank Ω‖ = ‖Ω‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  have hs' : ∑ s, ‖sBlank s‖ ^ 2 = 1 := by
    simpa [hs] using (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 sBlank)).symm
  have hx' : ∑ x, ‖xBlank x‖ ^ 2 = 1 := by
    simpa [hx] using (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 xBlank)).symm
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [restoringCopy, PiLp.toLp_apply, Fintype.sum_prod_type, norm_mul, mul_pow]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [← Finset.sum_mul, hx', one_mul]
  simp [hs']

omit [DecidableEq X] in
/-- Copying is an isometry on the Euclidean physical Hilbert space.
Source: `09-amplification.tex`, lines 399–401. -/
theorem restoringCopy_isometry (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1) :
    Isometry (restoringCopy (Y := Y) (Z := Z) sBlank xBlank) := by
  apply Isometry.of_dist_eq
  intro u v
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : restoringCopy sBlank xBlank u - restoringCopy sBlank xBlank v =
      restoringCopy sBlank xBlank (u - v) := by
    ext i
    simp [restoringCopy, mul_sub]
  rw [hsub, restoringCopy_norm sBlank xBlank hs hx]

/-- Exact adjoint error equality. Thus no factor involving the possibly large
norm of the restoring operator is introduced in the adjoint error estimate.
Source: `eq:amplification-adjoint-error`, lines 409–415. -/
theorem restoringGlobal_adjoint_error_eq [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    {Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : Q.IsHermitian) (hT : T.IsHermitian)
    (L : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) :
    ‖WithLp.toLp 2 ((restoringGlobal E p sBlank xBlank Q T)ᴴ *ᵥ
        ((restoringPhysicalLift L)ᴴ *ᵥ (restoringRestored p Ω).ofLp)) -
          restoringCopy sBlank xBlank Ω‖ =
      ‖WithLp.toLp 2 ((((restoringSelectedProjection E ⊗ₖ T) * Q) ⊗ₖ
        (1 : Matrix Z Z ℂ)) *ᵥ (Lᴴ *ᵥ Ω.ofLp)) - Ω‖ := by
  rw [restoringGlobal_adjoint_identity E p hp sBlank xBlank hQ hT L Ω,
    WithLp.toLp_ofLp]
  simpa only [dist_eq_norm] using
    (restoringCopy_isometry (Y := Y) (Z := Z) sBlank xBlank hs hx).dist_eq _ _


private theorem kronecker_isStarProjection {A B : Type*} [Fintype A] [Fintype B]
    {P : Matrix A A ℂ} {Q : Matrix B B ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : IsStarProjection (P ⊗ₖ Q) where
  isIdempotentElem := by
    change (P ⊗ₖ Q) * (P ⊗ₖ Q) = P ⊗ₖ Q
    rw [← mul_kronecker_mul, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  isSelfAdjoint := by
    change (P ⊗ₖ Q)ᴴ = P ⊗ₖ Q
    rw [conjTranspose_kronecker, show Pᴴ = P from hP.isSelfAdjoint,
      show Qᴴ = Q from hQ.isSelfAdjoint]

private theorem projection_norm_apply_le {A : Type*} [Fintype A] [DecidableEq A]
    (P : Matrix A A ℂ) (hP : IsStarProjection P) (v : EuclideanSpace ℂ A) :
    ‖Matrix.toEuclideanCLM (n := A) (𝕜 := ℂ) P v‖ ≤ ‖v‖ := by
  calc
    _ ≤ ‖P‖ * ‖v‖ := P.l2_opNorm_mulVec v
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right (IsStarProjection.norm_le P hP) (norm_nonneg v)
    _ = ‖v‖ := one_mul _

private theorem three_contractions_error {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (A B C : H →ₗ[ℂ] H)
    (hA : ∀ v, ‖A v‖ ≤ ‖v‖) (hB : ∀ v, ‖B v‖ ≤ ‖v‖)
    (hC : ∀ v, ‖C v‖ ≤ ‖v‖) (u v : H) (ε : ℝ)
    (hAu : ‖A u - u‖ ≤ ε) (hBu : ‖B u - u‖ ≤ ε) (hCu : ‖C u - u‖ ≤ ε) :
    ‖A (B (C v)) - u‖ ≤ 3 * ε + ‖v - u‖ := by
  have hsplit : A (B (C v)) - u =
      A (B (C (v - u))) + A (B (C u - u)) + A (B u - u) + (A u - u) := by
    simp only [map_sub]
    abel
  rw [hsplit]
  calc
    _ ≤ ‖A (B (C (v - u)))‖ + ‖A (B (C u - u))‖ +
        ‖A (B u - u)‖ + ‖A u - u‖ := norm_add₄_le
    _ ≤ ‖v - u‖ + ε + ε + ε := add_le_add
      (add_le_add (add_le_add ((hA _).trans ((hB _).trans (hC _)))
        ((hA _).trans ((hB _).trans hCu))) ((hA _).trans hBu)) hAu
    _ = 3 * ε + ‖v - u‖ := by ring

/-- Telescoping the three actual projection errors gives the source's adjoint
estimate without a restoring-operator norm factor. The physical projections
need not commute. The individual disturbance bounds are hypotheses; existence
of suitable typical projections is not asserted.
Source: `eq:amplification-adjoint-error`, lines 409–415. -/
theorem restoringGlobal_adjoint_error_le [DecidableEq Y] [DecidableEq Z]
    (E : Finset X) (p : X → ℝ) (hp : ∀ x ∈ E, 0 < p x)
    (sBlank xBlank : X → ℂ)
    (hs : ‖WithLp.toLp 2 sBlank‖ = 1) (hx : ‖WithLp.toLp 2 xBlank‖ = 1)
    {Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : IsStarProjection Q) (hT : IsStarProjection T)
    (L : Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ)
    (Ω : EuclideanSpace ℂ ((X × Y) × Z)) (ε : ℝ)
    (hXε : ‖WithLp.toLp 2 (((restoringSelectedProjection E ⊗ₖ
      (1 : Matrix Y Y ℂ)) ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ Ω.ofLp) - Ω‖ ≤ ε)
    (hYε : ‖WithLp.toLp 2 ((((1 : Matrix X X ℂ) ⊗ₖ T) ⊗ₖ
      (1 : Matrix Z Z ℂ)) *ᵥ Ω.ofLp) - Ω‖ ≤ ε)
    (hQε : ‖WithLp.toLp 2 ((Q ⊗ₖ (1 : Matrix Z Z ℂ)) *ᵥ Ω.ofLp) - Ω‖ ≤ ε) :
    ‖WithLp.toLp 2 ((restoringGlobal E p sBlank xBlank Q T)ᴴ *ᵥ
        ((restoringPhysicalLift L)ᴴ *ᵥ (restoringRestored p Ω).ofLp)) -
          restoringCopy sBlank xBlank Ω‖ ≤
      3 * ε + ‖WithLp.toLp 2 (Lᴴ *ᵥ Ω.ofLp) - Ω‖ := by
  rw [restoringGlobal_adjoint_error_eq E p hp sBlank xBlank hs hx
    hQ.isSelfAdjoint hT.isSelfAdjoint L Ω]
  let A := (restoringSelectedProjection E ⊗ₖ (1 : Matrix Y Y ℂ)) ⊗ₖ
    (1 : Matrix Z Z ℂ)
  let B := ((1 : Matrix X X ℂ) ⊗ₖ T) ⊗ₖ (1 : Matrix Z Z ℂ)
  let C := Q ⊗ₖ (1 : Matrix Z Z ℂ)
  have hP : IsStarProjection (restoringSelectedProjection E) :=
    ⟨restoringSelectedProjection_mul_self E, restoringSelectedProjection_isHermitian E⟩
  have hA : IsStarProjection A := kronecker_isStarProjection
    (kronecker_isStarProjection hP (.one _)) (.one _)
  have hB : IsStarProjection B := kronecker_isStarProjection
    (kronecker_isStarProjection (.one _) hT) (.one _)
  have hC : IsStarProjection C := kronecker_isStarProjection hQ (.one _)
  have hABC : A * B * C = ((restoringSelectedProjection E ⊗ₖ T) * Q) ⊗ₖ
      (1 : Matrix Z Z ℂ) := by
    simp only [A, B, C, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  rw [← hABC]
  have h := three_contractions_error
    (Matrix.toEuclideanCLM (n := (X × Y) × Z) (𝕜 := ℂ) A).toLinearMap
    (Matrix.toEuclideanCLM (n := (X × Y) × Z) (𝕜 := ℂ) B).toLinearMap
    (Matrix.toEuclideanCLM (n := (X × Y) × Z) (𝕜 := ℂ) C).toLinearMap
    (projection_norm_apply_le A hA) (projection_norm_apply_le B hB)
    (projection_norm_apply_le C hC) Ω (WithLp.toLp 2 (Lᴴ *ᵥ Ω.ofLp)) ε hXε hYε hQε
  simpa only [ContinuousLinearMap.coe_coe, Matrix.toEuclideanCLM_toLp,
    ← Matrix.mulVec_mulVec] using h

end Entropy
