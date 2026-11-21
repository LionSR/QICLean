/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.GroupWithZero.Pi
import QICLean.Algebra.FinSumPermutation

/-!
# Exact factorizations of idempotents, matrix units and representations

An idempotent matrix admits a factorization `P = W * V` with `V * W = 1`, where the inner
dimension is exactly the rank of `P`. The idempotent need not be Hermitian. The construction
chooses coordinates on its range and uses `P` itself to define the coordinate projection.

A system of matrix units acting on a finite-dimensional vector space then has an exact
rectangular factorization, whose multiplicity is the rank of one diagonal matrix unit, and a
multiplicative linear map from a finite product of full matrix algebras to matrices is a sum of
biorthogonal standard blocks. The sum of the block supports is the image of the source identity,
which need not be the ambient identity. Zero-dimensional source factors and zero multiplicities
are allowed. No preservation of adjoints or of the ambient identity is needed, so the results
also apply to non-unital representations, whose support is an idempotent.

This is the finite-dimensional representation decomposition of Garre-Rubio, Lootens and Molnár,
arXiv:2203.12563v3, Appendix A.

Moved from TNLean, `TNLean/Algebra/MatrixIdempotentFactorization.lean`,
`TNLean/Algebra/MatrixUnitFactorization.lean` and `TNLean/Algebra/PiMatrixRepresentation.lean`
at commit `49b78ed821` (Apache-2.0). Changes: the three files are merged.

## Main results

* `Matrix.exists_rankFactorization_of_idempotent`: an idempotent factors through its range.
* `Matrix.exists_matrixUnitFactorization`, `Matrix.exists_matrixUnitBlocks`: exact
  factorization of a system of matrix units.
* `Matrix.exists_multiplicativeLinearMap_blocks`: a multiplicative linear map on a full matrix
  algebra is a sum of biorthogonal standard blocks.
* `Matrix.exists_piMatrix_blocks`: the same for a finite product of full matrix algebras.

## References

* Garre-Rubio, Lootens, Molnár, arXiv:2203.12563v3, Appendix A.
-/

open scoped Matrix

namespace Matrix

/-- An idempotent factors through its range with a left inverse. No adjoint or
self-adjointness assumption is needed, and rank zero is allowed. -/
theorem exists_rankFactorization_of_idempotent
    {K : Type*} [Field K] {n : ℕ}
    (P : Matrix (Fin n) (Fin n) K) (hP : P * P = P) :
    ∃ (W : Matrix (Fin n) (Fin P.rank) K) (V : Matrix (Fin P.rank) (Fin n) K),
      V * W = 1 ∧ W * V = P := by
  classical
  let f := P.mulVecLin
  let e : (Fin P.rank → K) ≃ₗ[K] LinearMap.range f :=
    (Module.finBasisOfFinrankEq K (LinearMap.range f) rfl).equivFun.symm
  let W := LinearMap.toMatrix' ((LinearMap.range f).subtype.comp e.toLinearMap)
  let V := LinearMap.toMatrix' (e.symm.toLinearMap.comp f.rangeRestrict)
  have hW (x : Fin P.rank → K) : W *ᵥ x = (e x : Fin n → K) := by
    simp [W]
  have hV (x : Fin n → K) : e (V *ᵥ x) = f.rangeRestrict x := by
    simp [V]
  have hfix (x : LinearMap.range f) : f (x : Fin n → K) = x := by
    obtain ⟨y, hy⟩ := x.property
    change P *ᵥ (x : Fin n → K) = x
    rw [← hy]
    change P *ᵥ (P *ᵥ y) = P *ᵥ y
    rw [mulVec_mulVec, hP]
  refine ⟨W, V, ?_, ?_⟩
  · apply Matrix.ext_iff_mulVec.2
    intro x
    rw [← mulVec_mulVec, one_mulVec, hW]
    apply e.injective
    rw [hV]
    apply Subtype.ext
    exact hfix (e x)
  · apply Matrix.ext_iff_mulVec.2
    intro x
    rw [← mulVec_mulVec, hW, hV]
    rfl

/-- A matrix-unit system factors through equal-dimensional coordinate spaces.
The factorization is exact even when its support is a proper idempotent. -/
theorem exists_matrixUnitFactorization
    {K : Type*} [Field K] {n : Type*} [DecidableEq n] {D : ℕ}
    (E : n → n → Matrix (Fin D) (Fin D) K)
    (hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0)
    (i₀ : n) :
    ∃ (A : n → Matrix (Fin D) (Fin (E i₀ i₀).rank) K)
      (B : n → Matrix (Fin (E i₀ i₀).rank) (Fin D) K),
      (∀ i j, B i * A j = if i = j then 1 else 0) ∧
      (∀ i j, A i * B j = E i j) := by
  classical
  have hP : E i₀ i₀ * E i₀ i₀ = E i₀ i₀ := by simp [hE]
  obtain ⟨C, H, hHC, hCH⟩ := exists_rankFactorization_of_idempotent (E i₀ i₀) hP
  have hPC : E i₀ i₀ * C = C := by
    calc
      E i₀ i₀ * C = (C * H) * C :=
        congrArg (fun T : Matrix (Fin D) (Fin D) K => T * C) hCH.symm
      _ = C := by rw [Matrix.mul_assoc, hHC, Matrix.mul_one]
  refine ⟨fun i => E i i₀ * C, fun j => H * E i₀ j, ?_, ?_⟩
  · intro i j
    calc
      (H * E i₀ i) * (E j i₀ * C) = H * (E i₀ i * E j i₀) * C := by
        simp only [Matrix.mul_assoc]
      _ = if i = j then 1 else 0 := by
        rw [hE]
        by_cases hij : i = j
        · simp only [hij, ite_true, Matrix.mul_assoc, hPC, hHC]
        · simp [hij]
  · intro i j
    calc
      (E i i₀ * C) * (H * E i₀ j) = (E i i₀ * (C * H)) * E i₀ j := by
        simp only [Matrix.mul_assoc]
      _ = E i j := by simp [hCH, hE]

/-- Reassembling the columns of a rectangular factorization gives the usual
sum over multiplicity blocks. -/
theorem sum_multiplicityBlocks_mul
    {K n m : Type*} [CommSemiring K] [Fintype n] [Fintype m] {D : ℕ}
    (A : n → Matrix (Fin D) m K) (B : n → Matrix m (Fin D) K)
    (M : Matrix n n K) :
    (∑ μ : m, (of fun a i => A i a μ) * M * (of fun j b => B j μ b)) =
      ∑ i : n, ∑ j : n, M i j • (A i * B j) := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, of_apply, Finset.sum_mul,
    Finset.mul_sum, smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr₂ fun i _ j _ ↦ ?_
  apply Finset.sum_congr rfl
  intro μ _
  ring

/-- A system of matrix units is a sum of mutually biorthogonal copies of the
standard representation, with multiplicity equal to a diagonal unit's rank. -/
theorem exists_matrixUnitBlocks
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {D : ℕ}
    (E : n → n → Matrix (Fin D) (Fin D) K)
    (hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0)
    (i₀ : n) :
    ∃ (W : Fin (E i₀ i₀).rank → Matrix (Fin D) n K)
      (V : Fin (E i₀ i₀).rank → Matrix n (Fin D) K),
      (∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) ∧
      (∀ M : Matrix n n K, ∑ μ, W μ * M * V μ =
        ∑ i, ∑ j, M i j • E i j) := by
  classical
  obtain ⟨A, B, hBA, hAB⟩ := exists_matrixUnitFactorization E hE i₀
  let W := fun μ => of fun a i => A i a μ
  let V := fun μ => of fun i a => B i μ a
  refine ⟨W, V, ?_, ?_⟩
  · intro μ ν
    ext i j
    have hentry := congrArg (fun T => T μ ν) (hBA i j)
    change (B i * A j) μ ν = _
    rw [hentry]
    by_cases hij : i = j <;> by_cases hμν : μ = ν <;>
      simp [hij, hμν, Matrix.one_apply]
  · intro M
    rw [sum_multiplicityBlocks_mul]
    simp only [hAB]

/-- A multiplicative linear map on a full matrix algebra is an exact finite
sum of biorthogonal standard blocks. It need not preserve the identity. -/
theorem exists_multiplicativeLinearMap_blocks
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {D : ℕ}
    (ρ : Matrix n n K →ₗ[K] Matrix (Fin D) (Fin D) K)
    (hρ : ∀ M N, ρ (M * N) = ρ M * ρ N) (i₀ : n) :
    ∃ (m : ℕ) (W : Fin m → Matrix (Fin D) n K) (V : Fin m → Matrix n (Fin D) K),
      (∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) ∧
      (∀ M, ρ M = ∑ μ, W μ * M * V μ) := by
  classical
  let E := fun i j => ρ (single i j 1)
  have hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    dsimp [E]
    rw [← hρ]
    by_cases hjk : j = k
    · subst k
      simp
    · simp [hjk]
  obtain ⟨W, V, hVW, hsum⟩ := exists_matrixUnitBlocks E hE i₀
  refine ⟨(E i₀ i₀).rank, W, V, hVW, fun M => ?_⟩
  rw [hsum]
  conv_lhs => rw [matrix_eq_sum_single M]
  simp only [map_sum]
  refine Finset.sum_congr₂ fun i _ j _ ↦ ?_
  change ρ (single i j (M i j)) = M i j • ρ (single i j 1)
  rw [← map_smul]
  congr 1
  simp

/-- The full-matrix representation decomposition also covers an empty matrix
index type, in which case its multiplicity can be chosen to be zero. -/
theorem exists_multiplicativeLinearMap_blocks_of_fintype
    {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n] {D : ℕ}
    (ρ : Matrix n n K →ₗ[K] Matrix (Fin D) (Fin D) K)
    (hρ : ∀ M N, ρ (M * N) = ρ M * ρ N) :
    ∃ (m : ℕ) (W : Fin m → Matrix (Fin D) n K) (V : Fin m → Matrix n (Fin D) K),
      (∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) ∧
      (∀ M, ρ M = ∑ μ, W μ * M * V μ) := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    refine ⟨0, Fin.elim0, Fin.elim0, fun μ => Fin.elim0 μ, fun M => ?_⟩
    have hM : M = 0 := Subsingleton.elim _ _
    simp [hM]
  | inr hn =>
    exact exists_multiplicativeLinearMap_blocks ρ hρ (Classical.choice hn)

/-- Each member of a biorthogonal family is supported on its total
idempotent, on both sides. -/
theorem biorthogonal_sum_support
    {K m n d : Type*} [Semiring K] [Fintype m] [Fintype n] [Fintype d]
    [DecidableEq m] [DecidableEq n]
    (W : m → Matrix d n K) (V : m → Matrix n d K)
    (hVW : ∀ μ ν, V μ * W ν = if μ = ν then 1 else 0) (μ : m) :
    (∑ ν, W ν * V ν) * W μ = W μ ∧
      V μ * (∑ ν, W ν * V ν) = V μ := by
  constructor
  · rw [Matrix.sum_mul, Finset.sum_eq_single μ]
    · rw [Matrix.mul_assoc, hVW, ite_eq_left rfl, Matrix.mul_one]
    · intro ν _ hν
      rw [Matrix.mul_assoc, hVW, ite_eq_right hν, Matrix.mul_zero]
    · simp
  · rw [Matrix.mul_sum, Finset.sum_eq_single μ]
    · rw [← Matrix.mul_assoc, hVW, ite_eq_left rfl, Matrix.one_mul]
    · intro ν _ hν
      rw [← Matrix.mul_assoc, hVW, ite_eq_right (Ne.symm hν), Matrix.zero_mul]
    · simp

/-- Every multiplicative linear representation of a finite product of full
matrix algebras splits exactly into biorthogonal copies of the standard
representations. The total support is the image of the identity, with no
unitality or preservation of adjoints required. -/
theorem exists_piMatrix_blocks
    {K C : Type*} [Field K] [Fintype C]
    (δ : C → ℕ) {D : ℕ}
    (ρ : (∀ c, Matrix (Fin (δ c)) (Fin (δ c)) K) →ₗ[K]
      Matrix (Fin D) (Fin D) K)
    (hρ : ∀ M N, ρ (M * N) = ρ M * ρ N) :
    ∃ (m : C → ℕ)
      (W : ∀ c, Fin (m c) → Matrix (Fin D) (Fin (δ c)) K)
      (V : ∀ c, Fin (m c) → Matrix (Fin (δ c)) (Fin D) K),
      (∀ c μ ν, V c μ * W c ν = if μ = ν then 1 else 0) ∧
      (∀ c d, c ≠ d → ∀ μ ν, V c μ * W d ν = 0) ∧
      (∀ M, ρ M = ∑ c, ∑ μ, W c μ * M c * V c μ) ∧
      ρ 1 = ∑ c, ∑ μ, W c μ * V c μ := by
  classical
  let ρc := fun c => ρ.comp
    (LinearMap.single K (fun c => Matrix (Fin (δ c)) (Fin (δ c)) K) c)
  have hρc (c : C) : ∀ M N, ρc c (M * N) = ρc c M * ρc c N := by
    intro M N
    change ρ (Pi.single c (M * N)) = ρ (Pi.single c M) * ρ (Pi.single c N)
    rw [Pi.single_mul, hρ]
  choose m W V hVW hsum using
    fun c => exists_multiplicativeLinearMap_blocks_of_fintype (ρc c) (hρc c)
  have hsupport (c : C) : ρc c 1 = ∑ μ, W c μ * V c μ := by
    simpa using hsum c 1
  have hleft (c : C) (μ : Fin (m c)) : ρc c 1 * W c μ = W c μ := by
    rw [hsupport]
    exact (biorthogonal_sum_support (W c) (V c) (hVW c) μ).1
  have hright (c : C) (μ : Fin (m c)) : V c μ * ρc c 1 = V c μ := by
    rw [hsupport]
    exact (biorthogonal_sum_support (W c) (V c) (hVW c) μ).2
  have horth (c d : C) (hcd : c ≠ d) : ρc c 1 * ρc d 1 = 0 := by
    change ρ (Pi.single c 1) * ρ (Pi.single d 1) = 0
    rw [← hρ, ← Pi.single_mul_left]
    simp [Pi.single_eq_of_ne hcd]
  have htotal (M : ∀ c, Matrix (Fin (δ c)) (Fin (δ c)) K) :
      ρ M = ∑ c, ∑ μ, W c μ * M c * V c μ := by
    calc
      ρ M = ρ (∑ c, Pi.single c (M c)) := by rw [LinearMap.sum_single_apply]
      _ = ∑ c, ρc c (M c) := by simp [ρc]
      _ = _ := by simp only [hsum]
  refine ⟨m, W, V, hVW, ?_, htotal, ?_⟩
  · intro c d hcd μ ν
    calc
      V c μ * W d ν = (V c μ * ρc c 1) * (ρc d 1 * W d ν) := by
        rw [hright, hleft]
      _ = V c μ * (ρc c 1 * ρc d 1) * W d ν := by
        simp only [Matrix.mul_assoc]
      _ = 0 := by rw [horth c d hcd, Matrix.mul_zero, Matrix.zero_mul]
  · simpa using htotal 1

end Matrix
