/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Finite-matrix restoring and column operators

The physical coordinate order is `X × Y`. The restoring operator uses
`s × (X × Y)`, represented by `X × (X × Y)`. The column operator uses
`(s × e) × (X × Y)`, represented by `(X × X) × (X × Y)`.

The full orthonormal eigenbasis is identified with the coordinate basis on `X`;
`restoringBasisCoordinates` specifies the conjugation making this identification.
The blank vectors are arbitrary vectors, and need not be eigenvectors. The Gram
identities hold even before imposing their unit-norm conditions. Only the selected
probabilities must be positive. The column operator sums over every coordinate
of its second ancillary system, including coordinates with zero probability.

## References

* Two-dimensional area-law manuscript (September 24, 2026),
  `09-amplification.tex`, lines 324–392, in particular
  `eq:amplification-restoring-operator` and `eq:amplification-column-operator`.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

open Matrix Finset
open scoped BigOperators Kronecker ComplexOrder

namespace Entropy

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- Coordinate identification on `X ⊗ Y`: if the columns of the unitary `U`
are the chosen full eigenbasis on `X`, this is the matrix in that basis.
Source: `09-amplification.tex`, lines 324–327. -/
noncomputable def restoringBasisCoordinates (U : Matrix.unitaryGroup X ℂ)
    (Q : Matrix (X × Y) (X × Y) ℂ) : Matrix (X × Y) (X × Y) ℂ :=
  ((U : Matrix X X ℂ)ᴴ ⊗ₖ (1 : Matrix Y Y ℂ)) * Q *
    ((U : Matrix X X ℂ) ⊗ₖ (1 : Matrix Y Y ℂ))

/-- The rank-one matrix `|b⟩⟨b|`. The blank vectors in the source are unit vectors.
Source: `09-amplification.tex`, lines 331–332 and 378–381. -/
noncomputable def blankProjection (b : X → ℂ) : Matrix X X ℂ :=
  vecMulVec b (star b)

/-- The matrix `|x⟩⟨b|` in the chosen full orthonormal coordinate basis.
Source: `eq:amplification-restoring-operator`. -/
noncomputable def basisColumn (x : X) (b : X → ℂ) : Matrix X X ℂ :=
  vecMulVec (Pi.single x 1) (star b)

/-- The tensor product of two ancillary blank vectors, in `(s,e)` order.
Source: `eq:amplification-column-operator`. -/
noncomputable def pairedBlank (s e : X → ℂ) : X × X → ℂ :=
  fun i ↦ s i.1 * e i.2

/-- Reassociation from `(s,e,X,Y)` grouped as `((s,e),(X,Y))` to
`s,(e,(X,Y))`. No factors are permuted or conjugated.
Source: `eq:amplification-column-operator`. -/
def columnGrouping : ((X × X) × (X × Y)) ≃ (X × (X × (X × Y))) :=
  Equiv.prodAssoc X X (X × Y)

/-- The selected inverse square-root coefficient. No inverse is required on
unselected eigenvalues, which may vanish.
Source: `eq:amplification-restoring-operator`. -/
noncomputable def restoringWeight (p : ℝ) : ℂ :=
  ((Real.sqrt p)⁻¹ : ℝ)

/-- The physical block `⟨x|Q|x⟩` on `Y` in the selected eigenbasis.
Source: `09-amplification.tex`, lines 372–376. -/
noncomputable def restoringBlock (Q : Matrix (X × Y) (X × Y) ℂ) (x : X) :
    Matrix Y Y ℂ :=
  Q.submatrix (fun y ↦ (x, y)) (fun y ↦ (x, y))

/-- The actual restoring operator `R₀` on `s ⊗ (X ⊗ Y)`.
Source: `eq:amplification-restoring-operator`, lines 350–355. -/
noncomputable def restoringOperator (E : Finset X) (p : X → ℝ)
    (sBlank xBlank : X → ℂ) (Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) : Matrix (X × (X × Y)) (X × (X × Y)) ℂ :=
  ∑ x ∈ E, restoringWeight (p x) •
    (basisColumn x sBlank ⊗ₖ (Q * (basisColumn x xBlank ⊗ₖ T)))

/-- The actual column operator `B₀` on `(s ⊗ e) ⊗ (X ⊗ Y)`. The second
sum is over the full basis, without a positivity restriction on `p y`.
Source: `eq:amplification-column-operator`, lines 361–368. -/
noncomputable def columnOperator (E : Finset X) (p : X → ℝ)
    (sBlank eBlank : X → ℂ) (Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) :
    Matrix ((X × X) × (X × Y)) ((X × X) × (X × Y)) ℂ :=
  ∑ x ∈ E, ∑ y : X, restoringWeight (p x) •
    ((basisColumn x sBlank ⊗ₖ basisColumn y eBlank) ⊗ₖ
      (Q * (single x y 1 ⊗ₖ T)))

/-- The positive matrix `B_Y` controlling both Gram matrices.
Source: `09-amplification.tex`, lines 372–381. -/
noncomputable def restoringGram (E : Finset X) (p : X → ℝ)
    (Q : Matrix (X × Y) (X × Y) ℂ) (T : Matrix Y Y ℂ) : Matrix Y Y ℂ :=
  ∑ x ∈ E, ((p x)⁻¹ : ℝ) • (T * restoringBlock Q x * T)

private theorem basisColumn_gram (x z : X) (b : X → ℂ) :
    (basisColumn x b)ᴴ * basisColumn z b =
      if x = z then blankProjection b else 0 := by
  ext i j
  simp [basisColumn, blankProjection, Matrix.mul_apply, Matrix.conjTranspose_apply,
    vecMulVec_apply, Pi.single_apply, ite_mul, mul_ite, eq_comm]

private theorem basisColumn_single (x y : X) :
    basisColumn x (Pi.single y 1) = single x y (1 : ℂ) := by
  ext i j
  simp [basisColumn, vecMulVec_apply, Pi.single_apply, Matrix.single_apply, eq_comm]

private theorem basisColumn_pair (x y : X) (s e : X → ℂ) :
    basisColumn (x, y) (pairedBlank s e) =
      basisColumn x s ⊗ₖ basisColumn y e := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [basisColumn, pairedBlank, vecMulVec_apply, Pi.single_apply,
    kroneckerMap_apply, Prod.mk.injEq, ite_and, mul_assoc, mul_left_comm, mul_comm]

private theorem blankProjection_pair (s e : X → ℂ) :
    blankProjection (pairedBlank s e) = blankProjection s ⊗ₖ blankProjection e := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [blankProjection, pairedBlank, vecMulVec_apply, kroneckerMap_apply]
  ring

private theorem sum_basisColumn_gram {K N : Type*}
    [Fintype K] [DecidableEq K] [Fintype N]
    (E : Finset K) (b : K → ℂ) (A : K → Matrix N N ℂ) :
    (∑ x ∈ E, basisColumn x b ⊗ₖ A x)ᴴ *
        (∑ x ∈ E, basisColumn x b ⊗ₖ A x) =
      blankProjection b ⊗ₖ (∑ x ∈ E, (A x)ᴴ * A x) := by
  classical
  have hpair (x z : K) :
      (basisColumn x b ⊗ₖ A x)ᴴ * (basisColumn z b ⊗ₖ A z) =
        if x = z then blankProjection b ⊗ₖ ((A x)ᴴ * A x) else 0 := by
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, basisColumn_gram]
    split_ifs with h
    · subst z
      rfl
    · exact zero_kronecker _
  rw [conjTranspose_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum, hpair]
  calc
    _ = ∑ x ∈ E, blankProjection b ⊗ₖ ((A x)ᴴ * A x) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx]
    _ = _ := by
      ext i j
      simp [Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]

private theorem basisColumn_sandwich (Q : Matrix (X × Y) (X × Y) ℂ)
    (T : Matrix Y Y ℂ) (x : X) (b : X → ℂ) :
    (basisColumn x b ⊗ₖ T)ᴴ * Q * (basisColumn x b ⊗ₖ T) =
      blankProjection b ⊗ₖ (Tᴴ * restoringBlock Q x * T) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, kroneckerMap_apply,
    basisColumn, blankProjection, vecMulVec_apply, Pi.star_apply,
    restoringBlock, submatrix_apply, Fintype.sum_prod_type]
  simp only [Pi.single_apply, star_mul, star_star, star_ite, star_one, star_zero,
    ite_mul, mul_ite, zero_mul, mul_zero, one_mul, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

private theorem restoringWeight_gram {p : ℝ} (hp : 0 ≤ p) :
    star (restoringWeight p) * restoringWeight p = ((p⁻¹ : ℝ) : ℂ) := by
  have h := congrArg (fun r : ℝ ↦ ((r⁻¹ : ℝ) : ℂ)) (Real.mul_self_sqrt hp)
  simpa [restoringWeight, mul_inv] using h

private theorem weighted_physical_gram {Q : Matrix (X × Y) (X × Y) ℂ}
    {T : Matrix Y Y ℂ} (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hT : T.IsHermitian) (x : X) (b : X → ℂ) {p : ℝ} (hp : 0 ≤ p) :
    (restoringWeight p • (Q * (basisColumn x b ⊗ₖ T)))ᴴ *
        (restoringWeight p • (Q * (basisColumn x b ⊗ₖ T))) =
      blankProjection b ⊗ₖ ((p⁻¹ : ℝ) • (T * restoringBlock Q x * T)) := by
  rw [conjTranspose_smul, smul_mul, mul_smul, smul_smul, restoringWeight_gram hp]
  have hprod :
      (Q * (basisColumn x b ⊗ₖ T))ᴴ * (Q * (basisColumn x b ⊗ₖ T)) =
        blankProjection b ⊗ₖ (T * restoringBlock Q x * T) := by
    rw [conjTranspose_mul, hQ.eq]
    calc
      (basisColumn x b ⊗ₖ T)ᴴ * Q * (Q * (basisColumn x b ⊗ₖ T)) =
          (basisColumn x b ⊗ₖ T)ᴴ * (Q * Q) * (basisColumn x b ⊗ₖ T) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hQQ, basisColumn_sandwich, hT.eq]
  rw [hprod]
  ext i j
  simp [Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul, mul_assoc, mul_left_comm]

/-- The actual restoring operator has Gram matrix
`|0⟩⟨0|_s ⊗ (|0⟩⟨0|_X ⊗ B_Y)`. Only orthogonality and idempotence of `Q`
and Hermiticity of `T` are needed; `Q` and `I ⊗ T` need not commute.
Source: `09-amplification.tex`, lines 372–379. -/
theorem restoringOperator_gram (E : Finset X) (p : X → ℝ)
    (hp : ∀ x ∈ E, 0 < p x) (sBlank xBlank : X → ℂ)
    {Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) (hT : T.IsHermitian) :
    (restoringOperator E p sBlank xBlank Q T)ᴴ *
        restoringOperator E p sBlank xBlank Q T =
      blankProjection sBlank ⊗ₖ (blankProjection xBlank ⊗ₖ restoringGram E p Q T) := by
  unfold restoringOperator
  simp_rw [← kronecker_smul]
  rw [sum_basisColumn_gram]
  have hsum :
      (∑ x ∈ E, (restoringWeight (p x) • (Q * (basisColumn x xBlank ⊗ₖ T)))ᴴ *
        (restoringWeight (p x) • (Q * (basisColumn x xBlank ⊗ₖ T)))) =
      blankProjection xBlank ⊗ₖ restoringGram E p Q T := by
    calc
      _ = ∑ x ∈ E, blankProjection xBlank ⊗ₖ
          (((p x)⁻¹ : ℝ) • (T * restoringBlock Q x * T)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact weighted_physical_gram hQ hQQ hT x xBlank (le_of_lt (hp x hx))
      _ = _ := by
        ext i j
        simp [restoringGram, Matrix.sum_apply, kroneckerMap_apply, Finset.mul_sum]
  rw [hsum]

/-- The full-basis column operator has Gram matrix
`(|0⟩⟨0|_s ⊗ |0⟩⟨0|_e) ⊗ (I_X ⊗ B_Y)`. The identity on `X` comes from
summing over the full basis, including zero-probability coordinates.
Source: `09-amplification.tex`, lines 379–381. -/
theorem columnOperator_gram (E : Finset X) (p : X → ℝ)
    (hp : ∀ x ∈ E, 0 < p x) (sBlank eBlank : X → ℂ)
    {Q : Matrix (X × Y) (X × Y) ℂ} {T : Matrix Y Y ℂ}
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q) (hT : T.IsHermitian) :
    (columnOperator E p sBlank eBlank Q T)ᴴ *
        columnOperator E p sBlank eBlank Q T =
      (blankProjection sBlank ⊗ₖ blankProjection eBlank) ⊗ₖ
        ((1 : Matrix X X ℂ) ⊗ₖ restoringGram E p Q T) := by
  have hop : columnOperator E p sBlank eBlank Q T =
      ∑ xy ∈ E ×ˢ (Finset.univ : Finset X),
        basisColumn xy (pairedBlank sBlank eBlank) ⊗ₖ
          (restoringWeight (p xy.1) • (Q * (basisColumn xy.1 (Pi.single xy.2 1) ⊗ₖ T))) := by
    simp [columnOperator, Finset.sum_product, basisColumn_pair, basisColumn_single,
      kronecker_smul]
  rw [hop, sum_basisColumn_gram, blankProjection_pair]
  congr 1
  rw [Finset.sum_product]
  calc
    _ = ∑ x ∈ E, ∑ y : X, blankProjection (Pi.single y 1) ⊗ₖ
        (((p x)⁻¹ : ℝ) • (T * restoringBlock Q x * T)) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y _
          exact weighted_physical_gram hQ hQQ hT x (Pi.single y 1) (le_of_lt (hp x hx))
    _ = (1 : Matrix X X ℂ) ⊗ₖ restoringGram E p Q T := by
      ext ⟨i, j⟩ ⟨k, l⟩
      simp [blankProjection, restoringGram, Matrix.sum_apply, kroneckerMap_apply,
        vecMulVec_apply, Pi.single_apply, Matrix.one_apply, ite_mul, mul_ite,
        Finset.mul_sum, Finset.sum_mul, eq_comm]

/-- Positivity of the matrix controlling the restoring and column operators.
Source: `09-amplification.tex`, lines 372–376. -/
theorem restoringGram_posSemidef (E : Finset X) (p : X → ℝ)
    (hp : ∀ x ∈ E, 0 < p x) {Q : Matrix (X × Y) (X × Y) ℂ}
    {T : Matrix Y Y ℂ} (hQ : Q.PosSemidef) (hT : T.IsHermitian) :
    (restoringGram E p Q T).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro x hx
  have hblock : (restoringBlock Q x).PosSemidef := hQ.submatrix _
  have hconj := hblock.conjTranspose_mul_mul_same T
  rw [hT.eq] at hconj
  exact hconj.smul (inv_nonneg.mpr (le_of_lt (hp x hx)))

end Entropy
