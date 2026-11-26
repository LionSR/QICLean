/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceNorm.TraceNormAbs
import QICLean.Channel.Basic
import QICLean.Channel.Schwarz.PositiveMapProperties
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Foundational positive-on-abelian matrix lemmas

This file contains the basic finite-dimensional matrix definitions used in the
positive-on-abelian Schwarz argument, together with the diagonal-family
Schwarz inequality that treats commuting families after simultaneous
diagonalization has reduced them to a scalar problem.

## Main definitions

* `BlockPositive` — block-matrix positivity phrased through quadratic forms.
* `PairwiseCommuteImages` — pairwise commutativity of the block images of a
  linear map.
* `blockQuadraticForm` — the quadratic form obtained after applying a linear
  map blockwise.
* `IsPositiveOnCommuting` — positivity on commuting block families.

## Main statements

* `diagonal_family_schwarz_le` — the diagonal / finite-spectrum Schwarz
  inequality for a positive family with $\sum_i B_i \le 1$.
* `PositiveOnAbelian.map_conjTranspose_mul_map_le_of_normal_of_subunital`: normal-input consequences
  of positivity on abelian subalgebras.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.6 and
  Proposition 5.1][Wolf2012QChannels]

## Tags

positive map, commuting family, Schwarz inequality, normal operator
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex Module.End

namespace PositiveOnAbelian

section Basic

variable {D : ℕ}

namespace Internal

/-- Multiplicativity of `Matrix.toEuclideanLin`: lifting matrix multiplication to
the Euclidean linear map level. -/
lemma toEuclideanLin_mul (A B : Matrix (Fin D) (Fin D) ℂ) :
    (Matrix.toEuclideanLin A : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D)) *
      Matrix.toEuclideanLin B = Matrix.toEuclideanLin (A * B) := by
  simpa only [Module.End.mul_eq_comp] using (Matrix.toEuclideanLin_mul A B).symm

end Internal

/-- Quadratic-form positivity for a block matrix with matrix entries.

This is the concrete finite-dimensional formulation of positivity used in the
current file: for every block vector `ψ`, the quadratic form of the block matrix
is nonnegative. -/
def BlockPositive {n D : ℕ}
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)) : Prop :=
  ∀ ψ : Fin n → Fin D → ℂ,
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (a i j).mulVec (ψ j)

/-- The block images of `a` under `T` commute pairwise. -/
def PairwiseCommuteImages {n D : ℕ}
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)) : Prop :=
  ∀ i j k l, Commute (T (a i j)) (T (a k l))

/-- The quadratic form obtained after applying a linear map `T` blockwise. -/
noncomputable def blockQuadraticForm {n D : ℕ}
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ))
    (ψ : Fin n → Fin D → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (T (a i j)).mulVec (ψ j)

/-- A map is **positive on commuting block families** if it preserves
block-quadratic-form positivity whenever the image family is pairwise commuting.

This formulation records the exact condition used by the normal-input Schwarz
argument: after applying the map to each block, the resulting family commutes
pairwise, and positivity of the original block quadratic form remains
positivity of the transformed form. -/
def IsPositiveOnCommuting
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ {n : ℕ} (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)),
    BlockPositive a →
    PairwiseCommuteImages T a →
    ∀ ψ : Fin n → Fin D → ℂ, 0 ≤ blockQuadraticForm T a ψ

section DiagonalFamily

/-- A rectangular Kraus-type map `X ↦ ∑ᵢ Kᵢ X Kᵢ†`. -/
private noncomputable def rectKrausMap {ι m n : Type*}
    [Fintype ι] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (K : ι → Matrix m n ℂ) (X : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ i : ι, K i * X * (K i)ᴴ

/-- Kadison--Schwarz for a unital rectangular Kraus family. -/
private lemma rect_kadison_schwarz_le
    {ι m n : Type*} [Fintype ι] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (K : ι → Matrix m n ℂ)
    (h_unital : ∑ i : ι, K i * (K i)ᴴ = (1 : Matrix m m ℂ))
    (X : Matrix n n ℂ) :
    (rectKrausMap K X)ᴴ * rectKrausMap K X ≤ rectKrausMap K (Xᴴ * X) := by
  classical
  let P : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
    Matrix.fromBlocks (Xᴴ * X) Xᴴ X 1
  have hP : P.PosSemidef := by
    let A : Matrix (n ⊕ n) (n ⊕ Fin 0) ℂ :=
      Matrix.fromBlocks Xᴴ 0 1 0
    simpa only [A, P, Matrix.fromBlocks_conjTranspose, conjTranspose_conjTranspose,
      conjTranspose_one, conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.mul_zero,
      add_zero, mul_one, one_mul] using Matrix.posSemidef_self_mul_conjTranspose A
  let K₂ : ι → Matrix (m ⊕ m) (n ⊕ n) ℂ :=
    fun i => Matrix.fromBlocks (K i) 0 0 (K i)
  have h_term (i : ι) :
      K₂ i * P * (K₂ i)ᴴ =
        Matrix.fromBlocks (K i * (Xᴴ * X) * (K i)ᴴ) (K i * Xᴴ * (K i)ᴴ)
          (K i * X * (K i)ᴴ) (K i * (K i)ᴴ) := by
    simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, add_zero, Matrix.mul_one, zero_add,
      Matrix.fromBlocks_conjTranspose, conjTranspose_zero, Matrix.mul_assoc, Matrix.mul_zero, K₂,
      P]
  have h_sum_psd : (∑ i : ι, K₂ i * P * (K₂ i)ᴴ).PosSemidef :=
    Matrix.posSemidef_sum (s := Finset.univ) (x := fun i => K₂ i * P * (K₂ i)ᴴ)
      (fun i _ => hP.mul_mul_conjTranspose_same (B := K₂ i))
  -- Key identity: the block sum equals the expected block matrix.
  have h_sfb :
      ∀ (A' B' C' D' : ι → Matrix m m ℂ),
        (∑ i : ι, Matrix.fromBlocks (A' i) (B' i) (C' i) (D' i)) =
          Matrix.fromBlocks (∑ i : ι, A' i) (∑ i : ι, B' i)
            (∑ i : ι, C' i) (∑ i : ι, D' i) := by
    intros A' B' C' D'
    ext i j
    rcases i with i' | i' <;> rcases j with j' | j' <;>
      simp only [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  have h_block_eq :
      (∑ i : ι, K₂ i * P * (K₂ i)ᴴ) =
        Matrix.fromBlocks (rectKrausMap K (Xᴴ * X)) ((rectKrausMap K X)ᴴ)
          ((rectKrausMap K X)ᴴᴴ) (1 : Matrix m m ℂ) := by
    simp_rw [h_term]
    rw [h_sfb]
    exact Matrix.fromBlocks_inj.mpr
      ⟨by simp only [rectKrausMap],
       by calc
           (∑ i : ι, K i * Xᴴ * (K i)ᴴ) = rectKrausMap K Xᴴ := by
             simp only [rectKrausMap]
           _ = (rectKrausMap K X)ᴴ := by
               simp only [rectKrausMap, Matrix.mul_assoc, Matrix.conjTranspose_sum,
                 Matrix.conjTranspose_mul, conjTranspose_conjTranspose],
       by simp only [rectKrausMap, conjTranspose_conjTranspose],
       by simpa only using h_unital⟩
  have h_block_psd :
      (Matrix.fromBlocks (rectKrausMap K (Xᴴ * X)) ((rectKrausMap K X)ᴴ)
        ((rectKrausMap K X)ᴴᴴ) (1 : Matrix m m ℂ)).PosSemidef := by
    simpa only [conjTranspose_conjTranspose, h_block_eq] using h_sum_psd
  have : Invertible (1 : Matrix m m ℂ) := invertibleOne
  rw [Matrix.le_iff]
  simpa only [inv_one, mul_one, conjTranspose_conjTranspose] using
    (Matrix.PosDef.fromBlocks₂₂ (A := rectKrausMap K (Xᴴ * X))
      (B := (rectKrausMap K X)ᴴ) (D := (1 : Matrix m m ℂ)) Matrix.PosDef.one).1 h_block_psd

/-- The single-column Kraus operators used to form a finite positive family into a
unital rectangular Kraus map after adjoining one zero coordinate. -/
private noncomputable def familyMainKraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin D) (Fin D) ℂ) (ip : ι × Fin D) :
    Matrix (Fin D) (Option ι) ℂ :=
  fun r o => if o = some ip.1 then C ip.1 r ip.2 else 0

/-- The defect Kraus operators supported on the adjoined zero coordinate. -/
private noncomputable def familyDefectKraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix (Fin D) (Fin D) ℂ) (p : Fin D) : Matrix (Fin D) (Option ι) ℂ :=
  fun r o => if o = none then S r p else 0

/-- The full unital Kraus family attached to a finite PSD family and its defect. -/
private noncomputable def familyKraus {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin D) (Fin D) ℂ) (S : Matrix (Fin D) (Fin D) ℂ) :
    ((ι × Fin D) ⊕ Fin D) → Matrix (Fin D) (Option ι) ℂ
  | Sum.inl ip => familyMainKraus C ip
  | Sum.inr p => familyDefectKraus S p

private lemma familyMain_term_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin D) (Fin D) ℂ) (z : ι → ℂ) (i : ι) (p : Fin D) :
    rectKrausMap (fun _ : Unit => familyMainKraus C (i, p))
      (Matrix.diagonal (fun o : Option ι => o.elim 0 z))
      = z i • (familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) := by
  ext r s
  simp only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
    Matrix.smul_apply, Matrix.mul_apply, familyMainKraus, diagonal_apply, mul_ite, ite_mul,
    zero_mul, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, conjTranspose_apply,
    RCLike.star_def,
    Option.elim_some, one_smul]
  ring_nf

private lemma familyMain_outer_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → Matrix (Fin D) (Fin D) ℂ) (i : ι) :
    (∑ p : Fin D, familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) = C i * (C i)ᴴ := by
  ext r s
  have hL :
      (∑ p : Fin D, familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) r s =
        ∑ p : Fin D, C i r p * (starRingEnd ℂ) (C i s p) := by
    simp only [Matrix.sum_apply, Matrix.mul_apply, familyMainKraus, conjTranspose_apply,
      RCLike.star_def, ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hL]
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def]

private lemma familyDefect_outer_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix (Fin D) (Fin D) ℂ) :
    (∑ p : Fin D, familyDefectKraus (ι := ι) S p * (familyDefectKraus (ι := ι) S p)ᴴ) =
      S * Sᴴ := by
  ext r s
  have hL :
      ((∑ p : Fin D,
          familyDefectKraus (ι := ι) S p * (familyDefectKraus (ι := ι) S p)ᴴ)) r s =
        ∑ p : Fin D, S r p * (starRingEnd ℂ) (S s p) := by
    simp only [Matrix.sum_apply, Matrix.mul_apply, familyDefectKraus, conjTranspose_apply,
      RCLike.star_def, ite_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [hL]
  simp only [Matrix.mul_apply, conjTranspose_apply, RCLike.star_def]

private lemma familyDefect_term_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix (Fin D) (Fin D) ℂ) (z : ι → ℂ) (p : Fin D) :
    rectKrausMap (fun _ : Unit => familyDefectKraus (ι := ι) S p)
      (Matrix.diagonal (fun o : Option ι => o.elim 0 z)) = 0 := by
  ext r s
  simp only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
    Matrix.smul_apply, Matrix.mul_apply, familyDefectKraus, Matrix.diagonal_apply, mul_ite, ite_mul,
    zero_mul, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte, conjTranspose_apply, RCLike.star_def,
    Option.elim_none, nsmul_zero, Matrix.zero_apply]

/-- The diagonal / finite-spectrum Schwarz inequality for a positive family
`{Bᵢ}` with `∑ᵢ Bᵢ ≤ 1`. This is the direct diagonal case needed for the
normal-input Schwarz inequality. -/
theorem diagonal_family_schwarz_le
    {ι : Type*} [Fintype ι]
    (B : ι → Matrix (Fin D) (Fin D) ℂ)
    (hB : ∀ i, (B i).PosSemidef)
    (hsub : ∑ i, B i ≤ (1 : Matrix (Fin D) (Fin D) ℂ))
    (z : ι → ℂ) :
    (∑ i, (starRingEnd ℂ (z i)) • B i) * (∑ i, z i • B i)
      ≤ ∑ i, ((starRingEnd ℂ (z i)) * z i) • B i := by
  classical
  have hBfac : ∀ i, ∃ C : Matrix (Fin D) (Fin D) ℂ, B i = C * Cᴴ := by
    intro i
    exact CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
      ((Matrix.nonneg_iff_posSemidef).mpr (hB i))
  choose C hC using hBfac
  have hdef_psd : (1 - ∑ i, B i).PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact sub_nonneg.mpr hsub
  obtain ⟨S, hS⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp
    ((Matrix.nonneg_iff_posSemidef).mpr hdef_psd)
  let K : ((ι × Fin D) ⊕ Fin D) → Matrix (Fin D) (Option ι) ℂ := familyKraus C S
  let X : Matrix (Option ι) (Option ι) ℂ := Matrix.diagonal (fun o : Option ι => o.elim 0 z)
  have hK_unital : ∑ a, K a * (K a)ᴴ = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    calc
      (∑ x, ∑ x_1, K (Sum.inl (x, x_1)) * (K (Sum.inl (x, x_1)))ᴴ) +
          ∑ x, K (Sum.inr x) * (K (Sum.inr x))ᴴ = (∑ x, C x * (C x)ᴴ) + S * Sᴴ := by
              simp only [familyKraus, familyMain_outer_sum, familyDefect_outer_sum, K]
      _ = (∑ x, B x) + (1 - ∑ i, B i) := by
            have hS' : S * Sᴴ = 1 - ∑ i, B i := by
              simpa only [Matrix.star_eq_conjTranspose] using hS.symm
            simp only [hS', hC, add_sub_cancel]
      _ = 1 := by simp only [sub_eq_add_neg, add_comm, add_neg_cancel_left]
  have hMainTerm (i : ι) (p : Fin D) :
      familyMainKraus C (i, p) * X * (familyMainKraus C (i, p))ᴴ =
        z i • (familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) := by
    simpa only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
      one_smul] using familyMain_term_eq (C := C) (z := z) i p
  have hDefTerm (p : Fin D) :
      familyDefectKraus (ι := ι) S p * X * (familyDefectKraus (ι := ι) S p)ᴴ = 0 := by
    simpa only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
      one_smul] using familyDefect_term_zero (ι := ι) (S := S) (z := z) p
  have hmap : rectKrausMap K X = ∑ i, z i • B i := by
    rw [rectKrausMap, Fintype.sum_sum_type, Fintype.sum_prod_type]
    calc
      (∑ x, ∑ x_1, K (Sum.inl (x, x_1)) * X * (K (Sum.inl (x, x_1)))ᴴ) +
          ∑ x, K (Sum.inr x) * X * (K (Sum.inr x))ᴴ =
            (∑ x, z x • ∑ x_1, familyMainKraus C (x, x_1) * (familyMainKraus C (x, x_1))ᴴ) +
              ∑ x : Fin D, 0 := by
              simp only [familyKraus, hMainTerm, hDefTerm, sum_const_zero, add_zero, smul_sum,
                K]
      _ = ∑ x, z x • (C x * (C x)ᴴ) := by
        simp only [familyMain_outer_sum, sum_const_zero, add_zero]
      _ = ∑ x, z x • B x := by simp only [hC]
  let zsq : ι → ℂ := fun i => (starRingEnd ℂ (z i)) * z i
  have hXsq_fun :
      (fun i : Option ι => (starRingEnd ℂ) (i.elim 0 z) * i.elim 0 z) =
        (fun i : Option ι => i.elim 0 zsq) := by
    funext i
    cases i <;> simp only [Option.elim_none, map_zero, mul_zero, Option.elim_some, zsq]
  have hXsq : Xᴴ * X = Matrix.diagonal (fun o : Option ι => o.elim 0 zsq) := by
    simp only [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Pi.star_apply,
      RCLike.star_def, hXsq_fun, X]
  have hMainTermSq (i : ι) (p : Fin D) :
      familyMainKraus C (i, p) * (Xᴴ * X) * (familyMainKraus C (i, p))ᴴ =
        zsq i • (familyMainKraus C (i, p) * (familyMainKraus C (i, p))ᴴ) := by
    rw [hXsq]
    simpa only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
      one_smul] using familyMain_term_eq (C := C) (z := zsq) i p
  have hDefTermSq (p : Fin D) :
      familyDefectKraus (ι := ι) S p * (Xᴴ * X) *
        (familyDefectKraus (ι := ι) S p)ᴴ = 0 := by
    rw [hXsq]
    simpa only [rectKrausMap, univ_unique, PUnit.default_eq_unit, sum_const, card_singleton,
      one_smul] using familyDefect_term_zero (ι := ι) (S := S) (z := zsq) p
  have hmap_star : rectKrausMap K (Xᴴ * X) = ∑ i, zsq i • B i := by
    rw [rectKrausMap, Fintype.sum_sum_type, Fintype.sum_prod_type]
    calc
      (∑ x, ∑ x_1, K (Sum.inl (x, x_1)) * (Xᴴ * X) * (K (Sum.inl (x, x_1)))ᴴ) +
          ∑ x, K (Sum.inr x) * (Xᴴ * X) * (K (Sum.inr x))ᴴ =
            (∑ x, zsq x •
              ∑ x_1, familyMainKraus C (x, x_1) * (familyMainKraus C (x, x_1))ᴴ) +
              ∑ x : Fin D, 0 := by
              simp only [familyKraus, hMainTermSq, hDefTermSq, sum_const_zero, add_zero,
                smul_sum, K]
      _ = ∑ x, zsq x • (C x * (C x)ᴴ) := by
        simp only [familyMain_outer_sum, sum_const_zero, add_zero]
      _ = ∑ x, zsq x • B x := by simp only [hC]
  have hks := rect_kadison_schwarz_le (K := K) hK_unital X
  have hBherm : ∀ i, (B i)ᴴ = B i := fun i => (hB i).isHermitian.eq
  simpa only [ge_iff_le, hmap, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    RCLike.star_def, hBherm, hmap_star] using hks

end DiagonalFamily

end Basic

section Consequences

/-!
## Normal-input consequences of positivity on abelian subalgebras

This file derives the normal-input Schwarz inequality from the positive-on-
abelian theory. The main step is a spectral decomposition of a normal
matrix into rank-one positive pieces, after which the diagonal-family Schwarz
inequality applies termwise.

### Main statements

* `map_conjTranspose_mul_map_le_of_normal_of_subunital` — the normal-input
  Kadison--Schwarz inequality for positive subunital maps.

### References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.6 and
  Proposition 5.1][Wolf2012QChannels]

### Tags

positive map, normal operator, Kadison--Schwarz inequality
-/

variable {D : ℕ}

section NormalDiagonalization

local notation "E" => EuclideanSpace ℂ (Fin D)
local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

private lemma linearMap_eq_sum_rankOne_of_orthonormalBasis
    {s : Type*} [Fintype s]
    (b : OrthonormalBasis s ℂ E)
    (L : E →ₗ[ℂ] E) (μ : s → ℂ)
    (hL : ∀ i, L (b i) = μ i • b i) :
    L = ∑ i, μ i •
      (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
  apply LinearMap.ext
  intro v
  calc
    L v = L (∑ i, inner ℂ (b i) v • b i) := by rw [b.sum_repr' v]
    _ = ∑ i, inner ℂ (b i) v • L (b i) := by simp only [map_sum, map_smul]
    _ = ∑ i, inner ℂ (b i) v • (μ i • b i) := by simp only [hL]
    _ = ∑ i, μ i • (inner ℂ (b i) v • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, smul_smul]
      ring_nf
    _ = (∑ i, μ i •
      (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) :
        E →L[ℂ] E) : E →ₗ[ℂ] E)) v := by
      simp only [smul_smul, LinearMap.coe_sum, LinearMap.coe_smul, ContinuousLinearMap.coe_coe,
        Finset.sum_apply, Pi.smul_apply, InnerProductSpace.rankOne_apply]

private lemma commute_parts_of_normal
    (A : Mat) (hA : Aᴴ * A = A * Aᴴ) :
    Commute ((1 / 2 : ℂ) • (A + Aᴴ)) ((Complex.I / 2 : ℂ) • (Aᴴ - A)) := by
  have hAA : Commute A Aᴴ := (commute_iff_eq A Aᴴ).mpr hA.symm
  -- Commute (A + Aᴴ) with (Aᴴ - A) by combining the individual commutators.
  have hsum_sub : Commute (A + Aᴴ) (Aᴴ - A) :=
    (hAA.add_left (Commute.refl Aᴴ)).sub_right ((Commute.refl A).add_left hAA.symm)
  simpa only [one_div, smul_add, ne_eq, div_eq_zero_iff, Complex.I_ne_zero,
    OfNat.ofNat_ne_zero, or_self, not_false_eq_true, Commute.smul_right_iff₀] using
    (hsum_sub.smul_left (1 / 2 : ℂ)).smul_right (Complex.I / 2 : ℂ)

private lemma exists_diagonal_family_of_normal
    {A : Mat} (hA : Aᴴ * A = A * Aᴴ) :
    ∃ (s : Type) (_ : Fintype s) (_ : DecidableEq s)
      (b : OrthonormalBasis s ℂ E) (eig : s → ℂ),
      let P : s → Mat := fun i =>
        Matrix.toEuclideanLin.symm
          (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) : E →L[ℂ] E))
      A = ∑ i, eig i • P i ∧
      Aᴴ * A = ∑ i, (star (eig i) * eig i) • P i ∧
      (∀ i, (P i).PosSemidef) ∧
      (∑ i, P i = 1) := by
  classical
  let H : Mat := (1 / 2 : ℂ) • (A + Aᴴ)
  let K : Mat := (Complex.I / 2 : ℂ) • (Aᴴ - A)
  have hH : H.IsHermitian := by
    ext i j
    simp only [smul_add, one_div, conjTranspose_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, RCLike.star_def, star_add, star_mul', star_inv₀, star_ofNat,
      RingHomCompTriple.comp_apply, RingHom.id_apply, add_comm, H]
  have hK : K.IsHermitian := by
    ext i j
    simp only [sub_eq_add_neg, smul_add, smul_neg, conjTranspose_apply, Matrix.add_apply,
      Matrix.smul_apply, RCLike.star_def, smul_eq_mul, Matrix.neg_apply, star_add, star_mul',
      star_div₀, conj_I,
      star_ofNat, RingHomCompTriple.comp_apply, RingHom.id_apply, star_neg, K]
    ring_nf
  have hHKmat : Commute H K := by
    simpa only [H, K, smul_add, one_div, Matrix.smul_mul, Matrix.mul_smul, mul_comm,
      mul_left_comm, mul_assoc, ne_eq, div_eq_zero_iff, Complex.I_ne_zero, OfNat.ofNat_ne_zero,
      or_self, not_false_eq_true, Commute.smul_right_iff₀] using
      commute_parts_of_normal (A := A) hA
  let Hlin : E →ₗ[ℂ] E := Matrix.toEuclideanLin H
  let Klin : E →ₗ[ℂ] E := Matrix.toEuclideanLin K
  have hHlin : Hlin.IsSymmetric := by
    simpa only using ((Matrix.isSymmetric_toEuclideanLin_iff (A := H)).mpr hH)
  have hKlin : Klin.IsSymmetric := by
    simpa only using ((Matrix.isSymmetric_toEuclideanLin_iff (A := K)).mpr hK)
  have hEuclMul := Internal.toEuclideanLin_mul (D := D)
  have hHKlin : Commute Hlin Klin :=
    hEuclMul H K |>.trans (congrArg Matrix.toEuclideanLin hHKmat.eq) |>.trans (hEuclMul K H).symm
  -- Factor out the eigenspace-invariance proof for Klin once, then use it for
  -- both the restriction operator and the orthonormal basis construction.
  have hKinv : ∀ (μ : Eigenvalues Hlin),
      ∀ x ∈ Module.End.eigenspace Hlin μ, Klin x ∈ Module.End.eigenspace Hlin μ :=
    fun μ x hx => (Module.End.mem_eigenspace_iff).mpr <|
      (Module.End.mem_genEigenspace_one).mp <|
        (Module.End.mapsTo_genEigenspace_of_comm hHKlin μ 1) hx
  let Krestr : ∀ μ : Eigenvalues Hlin,
      Module.End ℂ (Module.End.eigenspace Hlin μ) :=
    fun μ => Klin.restrict (hKinv μ)
  have hKrestr : ∀ μ : Eigenvalues Hlin,
      @LinearMap.IsSymmetric ℂ (Module.End.eigenspace Hlin μ) _ _ _
        (Klin.restrict (hKinv μ)) :=
    fun μ => hKlin.restrict_invariant (hKinv μ)
  let bFamily : ∀ μ : Eigenvalues Hlin,
      OrthonormalBasis (Fin (Module.finrank ℂ (Module.End.eigenspace Hlin μ))) ℂ
        (Module.End.eigenspace Hlin μ) :=
    fun μ => (hKrestr μ).eigenvectorBasis rfl
  let s := Σ μ : Eigenvalues Hlin,
    Fin (Module.finrank ℂ (Module.End.eigenspace Hlin μ))
  let cBasis : Module.Basis s ℂ E :=
    (hHlin.direct_sum_isInternal).collectedBasis (fun i => (bFamily i).toBasis)
  have hOrthoC : Orthonormal ℂ cBasis :=
    DirectSum.IsInternal.collectedBasis_orthonormal
      (hV := hHlin.orthogonalFamily_eigenspaces')
      (hV_sum := hHlin.direct_sum_isInternal)
      (v_family := fun i => (bFamily i).toBasis)
      (hv_family := fun i => (bFamily i).orthonormal)
  let b : OrthonormalBasis s ℂ E := cBasis.toOrthonormalBasis hOrthoC
  let ν : s → ℂ := fun a => ↑((hKrestr a.1).eigenvalues rfl a.2)
  let eig : s → ℂ := fun a => (a.1 : ℂ) + Complex.I * ν a
  have hb_eq (a : s) : b a = (((bFamily a.1) a.2 : Module.End.eigenspace Hlin a.1) : E) := by
    rw [show b a = cBasis a by
      simp only [b, Module.Basis.coe_toOrthonormalBasis]]
    change cBasis a = (((bFamily a.1).toBasis a.2 : Module.End.eigenspace Hlin a.1) : E)
    exact congrFun
      (hHlin.direct_sum_isInternal.collectedBasis_coe (fun i => (bFamily i).toBasis)) a
  have hHb (a : s) : Hlin (b a) = (a.1 : ℂ) • b a := by
    rw [hb_eq a]
    exact (Module.End.mem_eigenspace_iff).mp ((bFamily a.1 a.2).2)
  have hKb (a : s) : Klin (b a) = ν a • b a := by
    have hv_eq : Krestr a.1 ((bFamily a.1) a.2) =
        (↑((hKrestr a.1).eigenvalues rfl a.2) : ℂ) • (bFamily a.1) a.2 :=
      (Module.End.mem_eigenspace_iff).mp
        (((hKrestr a.1).hasEigenvector_eigenvectorBasis rfl a.2).1)
    have hv' := congrArg (fun x : Module.End.eigenspace Hlin a.1 => (x : E)) hv_eq
    rw [hb_eq a]
    simpa [ν, Krestr] using hv'
  have hA_decomp : A = H + Complex.I • K := by
    ext i j
    simp only [one_div, smul_add, sub_eq_add_neg, smul_neg, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, conjTranspose_apply, RCLike.star_def, Matrix.neg_apply, H, K]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have hA_lin_decomp : Matrix.toEuclideanLin A = Hlin + Complex.I • Klin := by
    simpa only [one_div, smul_add, map_add, map_smul, map_sub] using
      congrArg Matrix.toEuclideanLin hA_decomp
  have hAb (a : s) : Matrix.toEuclideanLin A (b a) = eig a • b a := by
    rw [hA_lin_decomp]
    calc
      (Hlin + Complex.I • Klin) (b a) =
          (a.1 : ℂ) • b a + Complex.I • (ν a • b a) := by
            rw [LinearMap.add_apply, LinearMap.smul_apply, hHb a, hKb a]
      _ = eig a • b a := by
            simp only [smul_smul, add_smul, eig]
  let P : s → Mat := fun i =>
    Matrix.toEuclideanLin.symm
      (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) : E →L[ℂ] E))
  have hA_matrix : A = ∑ i, eig i • P i := by
    apply Matrix.toEuclideanLin.injective
    simpa only [P, map_sum, map_smul, LinearEquiv.apply_symm_apply] using
      (linearMap_eq_sum_rankOne_of_orthonormalBasis (b := b) (L := Matrix.toEuclideanLin A)
        (μ := eig) hAb)
  have hAstar_decomp : Aᴴ = H - Complex.I • K := by
    ext i j
    simp only [one_div, smul_add, sub_eq_add_neg, smul_neg, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, conjTranspose_apply, RCLike.star_def, Matrix.neg_apply, H, K]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  have hAstar_lin_decomp : Matrix.toEuclideanLin Aᴴ = Hlin - Complex.I • Klin := by
    simpa only [one_div, smul_add, map_add, map_smul, map_sub] using
      congrArg Matrix.toEuclideanLin hAstar_decomp
  have hAstarb (a : s) : Matrix.toEuclideanLin Aᴴ (b a) = star (eig a) • b a := by
    rw [hAstar_lin_decomp]
    have hμreal : (starRingEnd ℂ) (a.1 : ℂ) = (a.1 : ℂ) :=
      hHlin.conj_eigenvalue_eq_self a.1.property
    have hνreal : star (ν a) = ν a := by
      simp only [ν, RCLike.star_def, Complex.conj_ofReal]
    calc
      Hlin (b a) - Complex.I • Klin (b a)
          = (a.1 : ℂ) • b a - Complex.I • (ν a • b a) := by
            simp only [hHb, hKb]
      _ = ((a.1 : ℂ) + -(Complex.I * ν a)) • b a := by
          simp only [sub_eq_add_neg, add_smul, smul_smul, neg_smul]
      _ = star (eig a) • b a := by
          simp only [star_add, star_mul', RCLike.star_def, hνreal, hμreal, conj_I, neg_mul, eig]
  have hAb_ofLp (a : s) : A.mulVec (b a).ofLp = eig a • (b a).ofLp := by
    simpa only [Matrix.ofLp_toLpLin (p := 2) (q := 2), Matrix.toLin'_apply,
      WithLp.ofLp_smul]
      using congrArg WithLp.ofLp (hAb a)
  have hAstarb_ofLp (a : s) : Aᴴ.mulVec (b a).ofLp = star (eig a) • (b a).ofLp := by
    simpa only [Matrix.ofLp_toLpLin (p := 2) (q := 2), Matrix.toLin'_apply,
      WithLp.ofLp_smul]
      using congrArg WithLp.ofLp (hAstarb a)
  have hAstarAb (a : s) : Matrix.toEuclideanLin (Aᴴ * A) (b a) =
      (star (eig a) * eig a) • b a := by
    apply (WithLp.ofLp_injective 2)
    change (Aᴴ * A).mulVec (b a).ofLp =
      ((star (eig a) * eig a) • b a).ofLp
    rw [← Matrix.mulVec_mulVec, hAb_ofLp a, Matrix.mulVec_smul, hAstarb_ofLp a]
    rw [WithLp.ofLp_smul, smul_smul, mul_comm]
  have hAstarA_matrix : Aᴴ * A = ∑ i, (star (eig i) * eig i) • P i := by
    apply Matrix.toEuclideanLin.injective
    simpa only [P, map_sum, map_smul, LinearEquiv.apply_symm_apply] using
      (linearMap_eq_sum_rankOne_of_orthonormalBasis
        (b := b) (L := Matrix.toEuclideanLin (Aᴴ * A))
        (μ := fun i => star (eig i) * eig i) hAstarAb)
  have hPpsd : ∀ i, (P i).PosSemidef := by
    intro i
    rw [show P i = Matrix.vecMulVec (b i).ofLp (star (b i).ofLp) by
      simpa only [P] using
        (InnerProductSpace.symm_toEuclideanLin_rankOne (x := b i) (y := b i))]
    simpa only using Matrix.posSemidef_vecMulVec_self_star ((b i).ofLp)
  have hPsum : ∑ i, P i = (1 : Mat) := by
    have hrank := b.sum_rankOne_eq_id
    simpa only [ContinuousLinearMap.toLinearMap_sum, map_sum, ContinuousLinearMap.coe_id,
      Matrix.toLpLin_symm_id] using
      congrArg (fun L : E →L[ℂ] E =>
        Matrix.toEuclideanLin.symm (L : E →ₗ[ℂ] E)) hrank
  refine ⟨s, inferInstance, inferInstance, b, eig, ?_⟩
  dsimp [P]
  exact ⟨hA_matrix, hAstarA_matrix, hPpsd, hPsum⟩

end NormalDiagonalization

/-- Wolf Proposition 1.6 / Proposition 5.1 interface for normal inputs.

This is the concrete normal-operator Schwarz inequality needed later: if `T` is
positive and subunital on the identity, then normal inputs satisfy the usual
Kadison--Schwarz conclusion. -/
theorem map_conjTranspose_mul_map_le_of_normal_of_subunital
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T)
    {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : Aᴴ * A = A * Aᴴ)
    (h_subunital : T 1 ≤ (1 : Matrix (Fin D) (Fin D) ℂ)) :
    T Aᴴ * T A ≤ T (Aᴴ * A) := by
  classical
  obtain ⟨s, _, _, b, eig, hA_decomp, hAstarA_decomp, hPpsd, hPsum⟩ :=
    exists_diagonal_family_of_normal (A := A) hA
  let P : s → Matrix (Fin D) (Fin D) ℂ := fun i =>
    Matrix.toEuclideanLin.symm
      (↑((((InnerProductSpace.rankOne ℂ) (b i)) (b i)) :
        EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D)))
  let B : s → Matrix (Fin D) (Fin D) ℂ := fun i => T (P i)
  have hB : ∀ i, (B i).PosSemidef := fun i => hT (P i) (hPpsd i)
  have hsub : ∑ i, B i ≤ (1 : Matrix (Fin D) (Fin D) ℂ) := by
    calc
      ∑ i, B i = T (∑ i, P i) := by simp only [map_sum, B]
      _ = T 1 := by rw [hPsum]
      _ ≤ 1 := h_subunital
  have hTA : T A = ∑ i, eig i • B i := by
    rw [hA_decomp]
    simp only [map_sum, map_smul, B, P]
  have hTAA : T (Aᴴ * A) = ∑ i, (star (eig i) * eig i) • B i := by
    rw [hAstarA_decomp]
    simp only [RCLike.star_def, map_sum, map_smul, B, P]
  have hBherm : ∀ i, (B i)ᴴ = B i := fun i => (hB i).isHermitian.eq
  have hTAstar : T Aᴴ = ∑ i, star (eig i) • B i := by
    calc
      T Aᴴ = (T A)ᴴ := by simpa only using hT.map_conjTranspose A
      _ = (∑ i, eig i • B i)ᴴ := by rw [hTA]
      _ = ∑ i, star (eig i) • B i := by
          simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
            hBherm]
  simpa only [hTAstar, RCLike.star_def, hTA, hTAA, ge_iff_le] using
    diagonal_family_schwarz_le (B := B) hB hsub eig

end Consequences

end PositiveOnAbelian
