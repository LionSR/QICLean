/-
Copyright (c) 2026 Sirui Lu and TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Channel.SchmidtRank
import QICLean.Channel.Schwarz.PositiveOnAbelian.Basic
import QICLean.Channel.Schwarz.TwoPositive
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Choi compression for the rank-one test

This file connects the pure-state ampliation test for `k`-positivity with the
Choi-matrix compression in Wolf Chapter 3, Proposition 3.1, equation (3.4).

For a map $T : M_d(\mathbb{C}) \to M_{d'}(\mathbb{C})$, the Choi matrix acts
on the output-first space $\mathbb{C}^{d'}\otimes\mathbb{C}^d$. With the
`Matrix.omegaVec` normalization, the vector for $X\in M_{d\times k}(\mathbb{C})$
has component $d^{-1/2}X_{a,p}$ at $(a,p)$.

## Main definitions

* `ChoiJamiolkowski.rightCompression`: the right-factor Choi compression,
  written in the index convention of the blockwise ampliation.
* `ChoiJamiolkowski.rightTensorMatrix`: the right tensor factor on the input
  Choi index, defaulting to the equal-dimension specialization.
* `ChoiJamiolkowski.compressedOmegaVector`: the vector with component
  $d^{-1/2}X_{a,p}$ at the pair $(a,p)$.

## Main results

* `ChoiJamiolkowski.nPositiveAmpliation_rankOne_eq_rightCompression`: the
  ampliation of the associated rank-one matrix is exactly that compression.
* `ChoiJamiolkowski.rightTensorMatrix_mul_choiMatrix_mul_conjTranspose_rectangular`: the
  same compression is the sandwich by the right tensor factor.
* `ChoiJamiolkowski.compressedOmegaVector_hasSchmidtRankLE`: the compressed
  maximally entangled vector has Schmidt rank at most the compression dimension.
* `ChoiJamiolkowski.compressedOmegaVector_schmidtRank_eq_rank`: the compressed
  maximally entangled vector has Schmidt rank equal to the rank of the
  right-factor matrix.
* `ChoiJamiolkowski.hasSchmidtRankLE_iff_exists_rank_le_compressedOmegaVector`:
  the square-input parametrization of vectors of bounded Schmidt rank.
* `ChoiJamiolkowski.isNPositiveMap_iff_forall_rightCompression_posSemidef`:
  `k`-positivity is equivalent to positivity of all right-factor compressions.
* `ChoiJamiolkowski.rightTensorMatrix_mul_rightTensorMatrix`: right tensor
  factors multiply by multiplying the corresponding right-factor matrices.
* Fixed-column compression: a square right-factor sandwich controls every
  rectangular compression whose columns it fixes; see
  `rightCompression_posSemidef_of_projection_sandwich_of_mul_eq_self_rectangular`.
* `Matrix.exists_mul_conjTranspose_of_isHermitian_idempotent_rank`: a Hermitian
  idempotent matrix of rank `k` factors as `P = V * Vᴴ`.
* `Matrix.exists_isHermitian_idempotent_rank_mul_eq_self`: every rectangular
  right factor with `k ≤ d` is fixed by a Hermitian idempotent rank-`k` projection.
* `IsNPositiveMap.rightProjection_choiMatrix_sandwich_posSemidef_rectangular`:
  `k`-positivity makes every rank-`k` input-projection Choi sandwich positive.
* `isNPositiveMap_iff_forall_rankProjection_choiMatrix_sandwich_posSemidef_rectangular`:
  Wolf's rank-`k` projection form of the rectangular Choi criterion.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 3,
  Proposition 3.1, equation (3.4)][Wolf2012QChannels]
-/

open scoped Matrix BigOperators ComplexOrder
open Matrix Finset

namespace Matrix

/-- Over finite complex coordinates, nonnegative quadratic forms imply positive
semidefiniteness; the Hermitian part follows from complex polarization. -/
theorem posSemidef_of_dotProduct_mulVec_nonneg_complex
    {n : Type*} [Fintype n] {M : Matrix n n ℂ}
    (hM : ∀ x : n → ℂ, (0 : ℂ) ≤ star x ⬝ᵥ (M *ᵥ x)) : M.PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ hM
  rw [← Matrix.isSymmetric_toEuclideanLin_iff]
  have hpos : (Matrix.toEuclideanLin M).IsPositive := by
    rw [LinearMap.isPositive_iff_complex]
    intro x
    have hx_nonneg : (0 : ℂ) ≤ star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp) := hM x.ofLp
    have hx_real :
        star (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)) =
          star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp) := by
      rw [RCLike.star_def]
      exact RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hx_nonneg).2
    have hinner :
        inner ℂ ((Matrix.toEuclideanLin M) x) x =
          star (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp)) := by
      change inner ℂ (((Matrix.toLpLin 2 2) M) x) x =
        star (star x.ofLp ⬝ᵥ (M *ᵥ x.ofLp))
      rw [Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
      rw [dotProduct_comm]
      simp [dotProduct, mul_comm]
    constructor
    · rw [hinner, hx_real]
      exact RCLike.conj_eq_iff_re.mp (by simpa [RCLike.star_def] using hx_real)
    · rw [hinner, hx_real]
      exact (RCLike.nonneg_iff.mp hx_nonneg).1
  exact hpos.isSymmetric

end Matrix

namespace Submodule

/-- A finite-dimensional subspace of dimension at most `r` lies in one of dimension
exactly `r`, provided `r` is no larger than the ambient dimension. -/
theorem exists_le_finrank_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] (W : Submodule K V) {r : ℕ}
    (hW : Module.finrank K W ≤ r) (hr : r ≤ Module.finrank K V) :
    ∃ U : Submodule K V, W ≤ U ∧ Module.finrank K U = r := by
  classical
  let P : ℕ → Prop := fun n => ∀ W : Submodule K V,
    r - Module.finrank K W = n → Module.finrank K W ≤ r →
      ∃ U : Submodule K V, W ≤ U ∧ Module.finrank K U = r
  have hP : ∀ n, P n := by
    intro n
    induction n with
    | zero =>
        intro W hdiff hWle
        refine ⟨W, le_rfl, ?_⟩
        omega
    | succ n ih =>
        intro W hdiff hWle
        have hlt : Module.finrank K W < r := by omega
        have hWV : Module.finrank K W < Module.finrank K V := lt_of_lt_of_le hlt hr
        obtain ⟨v, hv⟩ := Submodule.exists_of_finrank_lt W hWV
        let W' : Submodule K V := W ⊔ Submodule.span K ({v} : Set V)
        have hWleW' : W ≤ W' := le_sup_left
        have hvnot : v ∉ W := by
          intro hvW
          exact hv 1 one_ne_zero (by simpa using hvW)
        have hfinW' : Module.finrank K W' = Module.finrank K W + 1 := by
          simpa [W'] using
            (Submodule.finrank_sup_span_singleton (K := K) (V := V) (p := W) hvnot)
        have hW'le : Module.finrank K W' ≤ r := by omega
        have hdiff' : r - Module.finrank K W' = n := by omega
        obtain ⟨U, hW'U, hUfin⟩ := ih W' hdiff' hW'le
        exact ⟨U, hWleW'.trans hW'U, hUfin⟩
  exact hP (r - Module.finrank K W) W rfl hW

end Submodule

namespace Matrix

/-- Every finite-dimensional Hermitian idempotent matrix of rank `k` factors as
`P = V * Vᴴ` with `k` columns. The proof identifies `P` with the orthogonal
projection onto its range and uses an orthonormal basis of that range as the
columns of `V`. This is the factorization in Wolf, Proposition 3.1, item 2. -/
theorem exists_mul_conjTranspose_of_isHermitian_idempotent_rank
    {D k : ℕ} (P : Matrix (Fin D) (Fin D) ℂ)
    (hP : P.IsHermitian) (hP_idem : P * P = P) (hrank : P.rank = k) :
    ∃ V : Matrix (Fin D) (Fin k) ℂ, P = V * Vᴴ := by
  let E := EuclideanSpace ℂ (Fin D)
  let p : E →ₗ[ℂ] E := Matrix.toEuclideanLin P
  have hp : p.IsSymmetricProjection := by
    constructor
    · change Matrix.toEuclideanLin P * Matrix.toEuclideanLin P = Matrix.toEuclideanLin P
      rw [PositiveOnAbelian.Internal.toEuclideanLin_mul, hP_idem]
    · exact (Matrix.isSymmetric_toEuclideanLin_iff (A := P)).mpr hP
  obtain ⟨horth, hp_eq⟩ :=
    LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range.mp hp
  let : (LinearMap.range p).HasOrthogonalProjection := horth
  have hrange : Module.finrank ℂ (LinearMap.range p) = k := by
    have hrank_range0 :
        P.rank = Module.finrank ℂ (LinearMap.range
          (Matrix.toEuclideanLin P : E →ₗ[ℂ] E)) := by
      rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
      exact Matrix.rank_eq_finrank_range_toLin P
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    have hrank_range : P.rank = Module.finrank ℂ (LinearMap.range p) := by
      simpa [p, E] using hrank_range0
    exact hrank_range.symm.trans hrank
  let b0 : OrthonormalBasis (Fin (Module.finrank ℂ (LinearMap.range p))) ℂ
      (LinearMap.range p) :=
    stdOrthonormalBasis ℂ (LinearMap.range p)
  let b : OrthonormalBasis (Fin k) ℂ (LinearMap.range p) :=
    b0.reindex (finCongr hrange)
  let V : Matrix (Fin D) (Fin k) ℂ := fun a j => (b j : E) a
  refine ⟨V, ?_⟩
  apply Matrix.toEuclideanLin.injective
  have hVV : V * Vᴴ = ∑ j : Fin k, Matrix.vecMulVec (b j : E) (star (b j : E)) := by
    ext a c
    calc
      (V * Vᴴ) a c = ∑ j, V a j * star (V c j) := by
        rw [Matrix.mul_apply]
        rfl
      _ = (∑ j : Fin k, Matrix.vecMulVec (b j : E) (star (b j : E))) a c := by
        rw [Matrix.sum_apply]
        rfl
  have hsum_rankOne :
      Matrix.toEuclideanLin (V * Vᴴ) =
        ∑ j : Fin k, (InnerProductSpace.rankOne ℂ (b j : E) (b j : E) : E →ₗ[ℂ] E) := by
    rw [hVV]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have h := congrArg Matrix.toEuclideanLin
      (InnerProductSpace.symm_toEuclideanLin_rankOne (𝕜 := ℂ)
        (x := (b j : E)) (y := (b j : E)))
    simpa using h.symm
  have hstar_linear :
      ((LinearMap.range p).starProjection : E →ₗ[ℂ] E) =
        ∑ j : Fin k, (InnerProductSpace.rankOne ℂ (b j : E) (b j : E) : E →ₗ[ℂ] E) := by
    have hstar := OrthonormalBasis.starProjection_eq_sum_rankOne (U := LinearMap.range p) b
    simpa [ContinuousLinearMap.toLinearMap_sum] using
      congrArg (fun L : E →L[ℂ] E => (L : E →ₗ[ℂ] E)) hstar
  calc
    Matrix.toEuclideanLin P = p := rfl
    _ = ((LinearMap.range p).starProjection : E →ₗ[ℂ] E) := hp_eq
    _ = ∑ j : Fin k, (InnerProductSpace.rankOne ℂ (b j : E) (b j : E) : E →ₗ[ℂ] E) :=
      hstar_linear
    _ = Matrix.toEuclideanLin (V * Vᴴ) := hsum_rankOne.symm

/-- The linear map represented by a rectangular product is the composition of
the two represented linear maps. -/
lemma toEuclideanLin_mul_rect {D k : ℕ}
    (P : Matrix (Fin D) (Fin D) ℂ) (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix.toEuclideanLin (P * X) =
      (Matrix.toEuclideanLin P).comp (Matrix.toEuclideanLin X) := by
  change Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin D) ℂ).toBasis (P * X) =
    (Matrix.toLin (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin D) ℂ).toBasis P).comp
      (Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis X)
  exact Matrix.toLin_mul (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    (EuclideanSpace.basisFun (Fin D) ℂ).toBasis P X

/-- If `k ≤ D`, then every rectangular matrix `X : M_{D,k}(ℂ)` is fixed by
some rank-`k` Hermitian idempotent on the left.  The projection is the
orthogonal projection onto a `k`-dimensional subspace containing the column
space of `X`.

This is the geometric converse step in Wolf, Proposition 3.1, item 2. -/
theorem exists_isHermitian_idempotent_rank_mul_eq_self
    {D k : ℕ} (hkD : k ≤ D) (X : Matrix (Fin D) (Fin k) ℂ) :
    ∃ P : Matrix (Fin D) (Fin D) ℂ,
      P.IsHermitian ∧ P * P = P ∧ P.rank = k ∧ P * X = X := by
  classical
  let W : Submodule ℂ (EuclideanSpace ℂ (Fin D)) :=
    LinearMap.range (Matrix.toEuclideanLin X : EuclideanSpace ℂ (Fin k) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin D))
  have hWfin : Module.finrank ℂ W ≤ k := by
    have hrank_range0 : X.rank = Module.finrank ℂ W := by
      change X.rank = Module.finrank ℂ (LinearMap.range
        ((Matrix.toLin (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin D) ℂ).toBasis) X))
      exact Matrix.rank_eq_finrank_range_toLin X
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin k) ℂ).toBasis
    rw [← hrank_range0]
    exact Matrix.rank_le_width X
  have hkE : k ≤ Module.finrank ℂ (EuclideanSpace ℂ (Fin D)) := by
    simpa using hkD
  obtain ⟨U, hWU, hUfin⟩ := Submodule.exists_le_finrank_eq W hWfin hkE
  let : U.HasOrthogonalProjection := inferInstance
  let p : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D) :=
    (U.starProjection : EuclideanSpace ℂ (Fin D) →ₗ[ℂ] EuclideanSpace ℂ (Fin D))
  let P : Matrix (Fin D) (Fin D) ℂ := Matrix.toEuclideanLin.symm p
  refine ⟨P, ?_, ?_, ?_, ?_⟩
  · exact (Matrix.isSymmetric_toEuclideanLin_iff (A := P)).mp
      (by simpa [P, p] using U.starProjection_isSymmetric)
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul_rect]
    have hp : p.IsSymmetricProjection := by
      dsimp [p]
      exact Submodule.isSymmetricProjection_starProjection U
    simpa [P, p, Module.End.mul_eq_comp] using hp.isIdempotentElem.eq
  · have hrank_range0 :
        P.rank = Module.finrank ℂ
          (LinearMap.range (Matrix.toEuclideanLin P : EuclideanSpace ℂ (Fin D) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin D))) := by
      change P.rank = Module.finrank ℂ (LinearMap.range
        ((Matrix.toLin (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
          (EuclideanSpace.basisFun (Fin D) ℂ).toBasis) P))
      exact Matrix.rank_eq_finrank_range_toLin P
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
        (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
    have hrange :
        LinearMap.range (Matrix.toEuclideanLin P : EuclideanSpace ℂ (Fin D) →ₗ[ℂ]
          EuclideanSpace ℂ (Fin D)) = U := by
      calc
        LinearMap.range (Matrix.toEuclideanLin P : EuclideanSpace ℂ (Fin D) →ₗ[ℂ]
            EuclideanSpace ℂ (Fin D))
            = LinearMap.range p := by simp [P]
        _ = U := by simp [p, Submodule.range_starProjection U]
    rw [hrank_range0, hrange, hUfin]
  · apply Matrix.toEuclideanLin.injective
    rw [toEuclideanLin_mul_rect]
    ext v
    have hvW : Matrix.toEuclideanLin X v ∈ W := by
      exact ⟨v, rfl⟩
    have hvU : Matrix.toEuclideanLin X v ∈ U := hWU hvW
    simp [P, p, Submodule.starProjection_eq_self_iff.mpr hvU]

end Matrix

namespace ChoiJamiolkowski

variable {d d' k : ℕ}

/-- The right-factor Choi compression in the blockwise-ampliation convention.
Here `X : Matrix (Fin d) (Fin k) ℂ` carries the input Choi and ampliation indices,
while `i,j : Fin d'` are output indices. The $(i,p),(j,q)$ entry is
$\sum_{a,b} X_{a,p}\,\tau_{(i,a),(j,b)}\,\overline{X_{b,q}}$, where $\tau$ is
the Choi matrix of `T`. -/
noncomputable def rightCompression
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d) (Fin k) ℂ) :
    Matrix (Fin d' × Fin k) (Fin d' × Fin k) ℂ :=
  Matrix.of fun ip jq =>
    ∑ a : Fin d, ∑ b : Fin d,
      X a ip.2 * ChoiRectangular.choiMatrix T (ip.1, a) (jq.1, b) * star (X b jq.2)

/-- The entry formula for the Choi right-factor compression: its $(i,p),(j,q)$ entry is
$\sum_{a,b} X_{a,p}\,\tau_{(i,a),(j,b)}\,\overline{X_{b,q}}$, where $\tau$ is
the Choi matrix of `T`. -/
theorem rightCompression_apply
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d) (Fin k) ℂ) (i j : Fin d') (p q : Fin k) :
    rightCompression T X (i, p) (j, q) =
      ∑ a : Fin d, ∑ b : Fin d,
        X a p * ChoiRectangular.choiMatrix T (i, a) (j, b) * star (X b q) :=
  rfl

/-- The matrix representing the right tensor factor in the Choi-compression
index convention. Its entry from the output-input Choi index `(j,a)` to the
output-ampliation index `(i,p)` is $\delta_{ij}X_{a,p}$. The optional output
dimension defaults to the input dimension. Source: Wolf, Chapter 3,
Proposition 3.1, lines 89--115. -/
noncomputable def rightTensorMatrix (X : Matrix (Fin d) (Fin k) ℂ) (d' : ℕ := d) :
    Matrix (Fin d' × Fin k) (Fin d' × Fin d) ℂ :=
  Matrix.of fun ip ja => if ip.1 = ja.1 then X ja.2 ip.2 else 0

/-- In the Choi-compression convention, the right-tensor matrix for `X * Xᴴ`
factors as `R_Xᴴ * R_X`. -/
theorem rightTensorMatrix_mul_conjTranspose_eq_conjTranspose_mul_self
    (X : Matrix (Fin d) (Fin k) ℂ) :
    rightTensorMatrix (d' := d') (X * Xᴴ) =
      (rightTensorMatrix (d' := d') X)ᴴ * rightTensorMatrix (d' := d') X := by
  classical
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp only [rightTensorMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      ite_true]
    rw [Fintype.sum_prod_type]
    simp [mul_comm]
  · simp only [rightTensorMatrix, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Fintype.sum_prod_type]
    have hji : ¬j = i := fun hji => hij hji.symm
    simp [hij, hji]

/-- Multiplying by a square right tensor factor multiplies the underlying matrices. -/
theorem rightTensorMatrix_mul_rightTensorMatrix
    (X : Matrix (Fin d) (Fin k) ℂ) (P : Matrix (Fin d) (Fin d) ℂ) :
    rightTensorMatrix (d' := d') X * rightTensorMatrix (d' := d') P =
      rightTensorMatrix (d' := d') (P * X) := by
  classical
  ext ⟨i, p⟩ ⟨j, a⟩
  simp only [rightTensorMatrix, Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst j
    simp [mul_comm]
  · simp [hij]

/-- Sandwiching the Choi matrix by the right tensor factor gives exactly the
right-factor compression entries.  In Wolf's notation this is the identity
between $(\mathbf{1}\otimes X)\tau(\mathbf{1}\otimes X)^\dagger$ and the
matrix with entries
$\sum_{a,b} X_{a,p}\tau_{(i,a),(j,b)}\overline{X_{b,q}}$. -/
theorem rightTensorMatrix_mul_choiMatrix_mul_conjTranspose_rectangular
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d) (Fin k) ℂ) :
    rightTensorMatrix (d' := d') X * ChoiRectangular.choiMatrix T *
        (rightTensorMatrix (d' := d') X)ᴴ =
      rightCompression T X := by
  classical
  ext ⟨i, p⟩ ⟨j, q⟩
  simp only [rightTensorMatrix, rightCompression, Matrix.mul_apply, Matrix.of_apply,
    Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · rw [Finset.sum_comm]
    simp [Finset.mul_sum, mul_assoc, mul_comm]
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- A right-factor Choi-sandwich quadratic form is the Choi form on the pullback. -/
theorem rightTensor_choiMatrix_quadraticForm_eq_rectangular
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d) (Fin k) ℂ) (η : Fin d' × Fin k → ℂ) :
    star η ⬝ᵥ
        ((rightTensorMatrix (d' := d') X * ChoiRectangular.choiMatrix T *
            (rightTensorMatrix (d' := d') X)ᴴ) *ᵥ η) =
      star ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η) ⬝ᵥ
        (ChoiRectangular.choiMatrix T *ᵥ
          ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η)) := by
  have hmul :
      ((rightTensorMatrix (d' := d') X * ChoiRectangular.choiMatrix T *
          (rightTensorMatrix (d' := d') X)ᴴ) *ᵥ η) =
        rightTensorMatrix (d' := d') X *ᵥ
          (ChoiRectangular.choiMatrix T *ᵥ
            ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η)) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hstar :
      star ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η) =
        star η ᵥ* rightTensorMatrix (d' := d') X := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hmul, Matrix.dotProduct_mulVec, ← hstar]

/-- A right-compression quadratic form is the Choi form on the adjoint pullback. -/
theorem rightCompression_quadraticForm_eq_choiMatrix_quadraticForm_rectangular
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d) (Fin k) ℂ) (η : Fin d' × Fin k → ℂ) :
    star η ⬝ᵥ (rightCompression T X *ᵥ η) =
      star ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η) ⬝ᵥ
        (ChoiRectangular.choiMatrix T *ᵥ
          ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η)) := by
  rw [← rightTensorMatrix_mul_choiMatrix_mul_conjTranspose_rectangular (T := T) (X := X)]
  exact rightTensor_choiMatrix_quadraticForm_eq_rectangular T X η

/-- The coefficient matrix of an adjoint right-tensor pullback is the compressed
vector's coefficient matrix times the adjoint right-factor matrix. -/
theorem schmidtCoeffMatrix_rightTensorMatrix_conjTranspose_mulVec
    (X : Matrix (Fin d) (Fin k) ℂ) (η : Fin d' × Fin k → ℂ) :
    Matrix.schmidtCoeffMatrix ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η) =
      Matrix.schmidtCoeffMatrix η * Xᴴ := by
  classical
  ext j a
  simp only [Matrix.schmidtCoeffMatrix, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    rightTensorMatrix, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j]
  · simp [mul_comm]
  · intro i _ hij
    simp [hij]
  · simp

/-- An adjoint right-tensor pullback has Schmidt rank at most the compression size. -/
theorem rightTensorMatrix_conjTranspose_mulVec_hasSchmidtRankLE
    (X : Matrix (Fin d) (Fin k) ℂ) (η : Fin d' × Fin k → ℂ) :
    Matrix.HasSchmidtRankLE k ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η) := by
  have hrank :
      (Matrix.schmidtCoeffMatrix
        ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η)).rank ≤ k := by
    rw [schmidtCoeffMatrix_rightTensorMatrix_conjTranspose_mulVec]
    calc
      (Matrix.schmidtCoeffMatrix η * Xᴴ).rank ≤ (Xᴴ).rank :=
        Matrix.rank_mul_le_right (Matrix.schmidtCoeffMatrix η) Xᴴ
      _ = X.rank := Matrix.rank_conjTranspose X
      _ ≤ Fintype.card (Fin k) := Matrix.rank_le_card_width X
      _ = k := by simp
  simpa [Matrix.HasSchmidtRankLE, Matrix.schmidtRank] using hrank

/-- Every vector of Schmidt rank at most `k` in the output-input tensor product
is obtained by pulling back a vector in the output-ampliation tensor product
through the adjoint of a right tensor factor. -/
theorem exists_rightTensorMatrix_conjTranspose_mulVec_of_hasSchmidtRankLE
    {ψ : Fin d' × Fin d → ℂ} (hψ : Matrix.HasSchmidtRankLE k ψ) :
    ∃ X : Matrix (Fin d) (Fin k) ℂ, ∃ η : Fin d' × Fin k → ℂ,
      (rightTensorMatrix (d' := d') X)ᴴ *ᵥ η = ψ := by
  classical
  let A : Matrix (Fin d') (Fin d) ℂ := Matrix.schmidtCoeffMatrix ψ
  have hA : A.rank ≤ k := by
    simpa [A, Matrix.HasSchmidtRankLE, Matrix.schmidtRank] using hψ
  obtain ⟨B, C, hBC⟩ := Matrix.exists_mul_eq_of_rank_le A hA
  let X : Matrix (Fin d) (Fin k) ℂ := Cᴴ
  let η : Fin d' × Fin k → ℂ := fun ip => B ip.1 ip.2
  refine ⟨X, η, ?_⟩
  ext ip
  rcases ip with ⟨j, a⟩
  calc
    ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η) (j, a)
        = Matrix.schmidtCoeffMatrix
          ((rightTensorMatrix (d' := d') X)ᴴ *ᵥ η) j a := rfl
    _ = (B * C) j a := by
        rw [schmidtCoeffMatrix_rightTensorMatrix_conjTranspose_mulVec]
        have hηcoeff : Matrix.schmidtCoeffMatrix η = B := by
          ext i p
          rfl
        rw [hηcoeff]
        simp only [X, Matrix.conjTranspose_conjTranspose]
    _ = A j a := by rw [hBC]
    _ = ψ (j, a) := rfl

/-- Apply `X` on the right factor of the normalized maximally entangled vector. -/
noncomputable def compressedOmegaVector (X : Matrix (Fin D) (Fin k) ℂ) :
    Fin D × Fin k → ℂ :=
  fun ip => ((1 : ℂ) / ((D : ℝ).sqrt : ℂ)) * X ip.1 ip.2

/-- For `D > 0`, the compressed maximally entangled vector has Schmidt rank
equal to the rank of the right-factor matrix. -/
theorem compressedOmegaVector_schmidtRank_eq_rank [NeZero D]
    (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix.schmidtRank (compressedOmegaVector X) = X.rank := by
  let c : ℂ := (1 : ℂ) / ((D : ℝ).sqrt : ℂ)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hsqrt_ne : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hDpos)
  have hc_ne : c ≠ 0 := by
    simp [c, hsqrt_ne]
  have hcoeff :
      Matrix.schmidtCoeffMatrix (compressedOmegaVector X) = c • X := by
    ext i p
    simp [Matrix.schmidtCoeffMatrix, compressedOmegaVector, c]
  rw [Matrix.schmidtRank, hcoeff]
  exact Matrix.rank_smul_of_mem_nonZeroDivisors X
    (mem_nonZeroDivisors_of_ne_zero hc_ne)

/-- Applying a `D × k` right factor to the maximally entangled vector gives
Schmidt rank at most `k`. -/
theorem compressedOmegaVector_hasSchmidtRankLE
    (X : Matrix (Fin D) (Fin k) ℂ) :
    Matrix.HasSchmidtRankLE k (compressedOmegaVector X) := by
  simpa [Matrix.HasSchmidtRankLE, Matrix.schmidtRank, Matrix.schmidtCoeffMatrix,
    compressedOmegaVector] using
    Matrix.rank_le_card_width (Matrix.schmidtCoeffMatrix (compressedOmegaVector X))

/-- A right-factor compression of rank at most `r` gives Schmidt rank at most `r`. -/
theorem compressedOmegaVector_hasSchmidtRankLE_of_rank_le [NeZero D]
    {m k : ℕ} {X : Matrix (Fin D) (Fin m) ℂ} (hX : X.rank ≤ k) :
    Matrix.HasSchmidtRankLE k (compressedOmegaVector X) := by
  simpa [Matrix.HasSchmidtRankLE, compressedOmegaVector_schmidtRank_eq_rank] using hX

/-- For `D > 0`, every vector in $\mathbb{C}^D\otimes\mathbb{C}^k$ is obtained
from the normalized maximally entangled vector by applying a `D × k` right-factor
matrix, and the matrix rank agrees with the Schmidt rank of the vector. This is
the rectangular right-factor parametrization used in the only-if direction of
Wolf, Chapter 3, Proposition 3.4, lines 250--267. -/
theorem exists_compression_of_vector [NeZero D]
    (ψ : Fin D × Fin k → ℂ) :
    ∃ X : Matrix (Fin D) (Fin k) ℂ,
      compressedOmegaVector X = ψ ∧ X.rank = Matrix.schmidtRank ψ := by
  let X : Matrix (Fin D) (Fin k) ℂ :=
    fun a p => (((D : ℝ).sqrt : ℂ)) * ψ (a, p)
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne D)
  have hsqrt_ne : ((D : ℝ).sqrt : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr hDpos)
  have hvec : compressedOmegaVector X = ψ := by
    ext ip
    rcases ip with ⟨i, p⟩
    simp only [compressedOmegaVector, X]
    field_simp [hsqrt_ne]
  refine ⟨X, hvec, ?_⟩
  simpa [hvec] using (compressedOmegaVector_schmidtRank_eq_rank (X := X)).symm

/-- Square specialization of `exists_compression_of_vector`. -/
theorem exists_squareCompression_of_vector [NeZero D]
    (ψ : Fin D × Fin D → ℂ) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      compressedOmegaVector X = ψ ∧ X.rank = Matrix.schmidtRank ψ :=
  exists_compression_of_vector ψ

/-- For `D > 0`, a square bipartite vector with Schmidt rank at most `r` has a
square right-factor matrix representative of rank at most `r`. -/
theorem exists_squareCompression_of_hasSchmidtRankLE [NeZero D]
    {r : ℕ} {ψ : Fin D × Fin D → ℂ} (hψ : Matrix.HasSchmidtRankLE r ψ) :
    ∃ X : Matrix (Fin D) (Fin D) ℂ,
      compressedOmegaVector X = ψ ∧ X.rank ≤ r := by
  obtain ⟨X, hXvec, hXrank⟩ := exists_squareCompression_of_vector (D := D) ψ
  exact ⟨X, hXvec, hXrank.trans_le hψ⟩

/-- Wolf's square-matrix parametrization of bounded Schmidt-rank vectors.
When D is positive, a vector in $\mathbb{C}^D \otimes \mathbb{C}^D$ has Schmidt
rank at most k if and only if it is obtained from the normalized maximally
entangled vector by applying a square matrix of rank at most k on the right
tensor factor. -/
theorem hasSchmidtRankLE_iff_exists_rank_le_compressedOmegaVector [NeZero D]
    {k : ℕ} {ψ : Fin D × Fin D → ℂ} :
    Matrix.HasSchmidtRankLE k ψ ↔
      ∃ X : Matrix (Fin D) (Fin D) ℂ, X.rank ≤ k ∧ compressedOmegaVector X = ψ := by
  constructor
  · intro hψ
    obtain ⟨X, hXvec, hXrank⟩ := exists_squareCompression_of_hasSchmidtRankLE
      (D := D) hψ
    exact ⟨X, hXrank, hXvec⟩
  · rintro ⟨X, hX, rfl⟩
    exact compressedOmegaVector_hasSchmidtRankLE_of_rank_le hX

/-- For the vector `compressedOmegaVector X`, the `k`-fold ampliation of the
rank-one matrix $|\psi\rangle\langle\psi|$ by `T` is the right-factor Choi
compression by `X`. -/
theorem nPositiveAmpliation_rankOne_eq_rightCompression
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (X : Matrix (Fin d) (Fin k) ℂ) :
    nPositiveAmpliation k T
        (Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))) =
      rightCompression T X := by
  classical
  ext ⟨i, p⟩ ⟨j, q⟩
  let c : ℂ := (1 : ℂ) / ((d : ℝ).sqrt : ℂ)
  have hblock :
      (Matrix.of fun a b =>
          Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
            (a, p) (b, q)) =
        ∑ a : Fin d, ∑ b : Fin d,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj d) a b := by
    calc
      (Matrix.of fun a b =>
          Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
            (a, p) (b, q))
          = Matrix.of fun a b => (X a p * star (X b q)) * (c * star c) := by
            ext a b
            simp [compressedOmegaVector, c, Matrix.vecMulVec_apply]
            ring
      _ = ∑ a : Fin d, ∑ b : Fin d,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj d) a b := by
            rw [Matrix.matrix_eq_sum_single
              (Matrix.of fun a b => (X a p * star (X b q)) * (c * star c))]
            simp [ChoiJamiolkowski.omegaSlice_eq_single, c, Matrix.smul_single,
              smul_eq_mul]
  calc
    nPositiveAmpliation k T
        (Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X)))
        (i, p) (j, q)
        = T (Matrix.of fun a b =>
            Matrix.vecMulVec (compressedOmegaVector X) (star (compressedOmegaVector X))
              (a, p) (b, q)) i j := rfl
    _ = T (∑ a : Fin d, ∑ b : Fin d,
          (X a p * star (X b q)) • Matrix.bipartiteSlice (Matrix.omegaProj d) a b) i j := by
        rw [hblock]
    _ = (∑ a : Fin d, ∑ b : Fin d,
          (X a p * star (X b q)) • T (Matrix.bipartiteSlice (Matrix.omegaProj d) a b)) i j := by
        simp [map_sum]
    _ = rightCompression T X (i, p) (j, q) := by
        rw [rightCompression_apply]
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          ChoiRectangular.choiMatrix_apply]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring_nf

/-- Rectangular compression form of Wolf, Proposition 3.1, equation (3.4):
when `d > 0`, `k`-positivity of a map from `M_d(ℂ)` to `M_{d'}(ℂ)` is
equivalent to positivity of every right-factor compression of its Choi matrix
by a matrix in `M_{d,k}(ℂ)`. Source: Wolf, Chapter 3, Proposition 3.1,
lines 89--115. -/
theorem isNPositiveMap_iff_forall_rightCompression_posSemidef [NeZero d]
    (k : ℕ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ) :
    IsNPositiveMap k T ↔
      ∀ X : Matrix (Fin d) (Fin k) ℂ, (rightCompression T X).PosSemidef := by
  constructor
  · intro hT X
    rw [← nPositiveAmpliation_rankOne_eq_rightCompression (T := T) (X := X)]
    exact (isNPositiveMap_iff_forall_ampliation_rank_one_posSemidef k T).mp hT
      (compressedOmegaVector X)
  · intro hX
    rw [isNPositiveMap_iff_forall_ampliation_rank_one_posSemidef]
    intro φ
    let X : Matrix (Fin d) (Fin k) ℂ :=
      fun a p => (((d : ℝ).sqrt : ℂ)) * φ (a, p)
    have hvec : compressedOmegaVector X = φ := by
      have hdpos : 0 < (d : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
      have hsqrt_ne : ((d : ℝ).sqrt : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_ne_zero'.mpr hdpos)
      ext ip
      rcases ip with ⟨i, p⟩
      simp only [compressedOmegaVector, X]
      field_simp [hsqrt_ne]
    rw [← hvec]
    rw [nPositiveAmpliation_rankOne_eq_rightCompression]
    exact hX X

/-- Converse Schmidt-rank test for Wolf's Choi criterion. If all vectors of
Schmidt rank at most `k` in the output-input tensor product have nonnegative
Choi quadratic form, then the map is `k`-positive.
Wolf prints "Schmidt-rank `k`". The exact-rank test is vacuous when `k > d'`,
whereas the standard criterion is the at-most-`k` statement proved here. See
`docs/paper-gaps/wolf_prop3_1_exact_schmidt_rank_scope.tex`.
Source: Wolf, Chapter 3, Proposition 3.1, lines 89--115. -/
theorem isNPositiveMap_of_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg_rectangular
    [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hψ : ∀ ψ : Fin d' × Fin d → ℂ, Matrix.HasSchmidtRankLE k ψ →
      (0 : ℂ) ≤ star ψ ⬝ᵥ (ChoiRectangular.choiMatrix T *ᵥ ψ)) :
    IsNPositiveMap k T := by
  rw [isNPositiveMap_iff_forall_rightCompression_posSemidef]
  intro X
  refine Matrix.posSemidef_of_dotProduct_mulVec_nonneg_complex ?_
  intro η
  rw [rightCompression_quadraticForm_eq_choiMatrix_quadraticForm_rectangular
    (T := T) (X := X) (η := η)]
  exact hψ _ (rightTensorMatrix_conjTranspose_mulVec_hasSchmidtRankLE X η)

/-- A `k`-positive map has positive Choi sandwiches by every right tensor
factor `X : M_{d,k}(\mathbb{C})`. This is the forward implication of the
projection-compression formulation before requiring that `X` comes from a
rank-`k` Hermitian projection. -/
theorem IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_rectangular [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsNPositiveMap k T) (X : Matrix (Fin d) (Fin k) ℂ) :
    (rightTensorMatrix (d' := d') X * ChoiRectangular.choiMatrix T *
      (rightTensorMatrix (d' := d') X)ᴴ).PosSemidef := by
  rw [rightTensorMatrix_mul_choiMatrix_mul_conjTranspose_rectangular]
  exact (isNPositiveMap_iff_forall_rightCompression_posSemidef k T).mp hT X

/-- If a right-factor matrix `P` is presented as `V * Vᴴ`, then its Choi
sandwich is a compression of the rectangular Choi sandwich for `V`. -/
theorem rightTensorMatrix_mul_conjTranspose_choi_sandwich_eq_rectangular
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (V : Matrix (Fin d) (Fin k) ℂ) :
    rightTensorMatrix (d' := d') (V * Vᴴ) * ChoiRectangular.choiMatrix T *
        (rightTensorMatrix (d' := d') (V * Vᴴ))ᴴ =
      (rightTensorMatrix (d' := d') V)ᴴ *
        (rightTensorMatrix (d' := d') V * ChoiRectangular.choiMatrix T *
          (rightTensorMatrix (d' := d') V)ᴴ) *
          rightTensorMatrix (d' := d') V := by
  rw [rightTensorMatrix_mul_conjTranspose_eq_conjTranspose_mul_self]
  simp [Matrix.mul_assoc]

/-- If a right-factor matrix has the form `V * Vᴴ`, then the corresponding
Choi sandwich is positive semidefinite. To recover the full statement of Wolf,
Proposition 3.1, item 2, for an arbitrary rank-`k` orthogonal projection `P`,
one additionally needs a factorization `P = V * Vᴴ`. -/
theorem IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_mul_conjTranspose_rectangular
    [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsNPositiveMap k T) (V : Matrix (Fin d) (Fin k) ℂ) :
    (rightTensorMatrix (d' := d') (V * Vᴴ) * ChoiRectangular.choiMatrix T *
      (rightTensorMatrix (d' := d') (V * Vᴴ))ᴴ).PosSemidef := by
  rw [rightTensorMatrix_mul_conjTranspose_choi_sandwich_eq_rectangular]
  have hV := IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_rectangular hT V
  exact hV.conjTranspose_mul_mul_same (rightTensorMatrix (d' := d') V)

/-- Forward projection-compression consequence in Wolf, Proposition 3.1,
item 2.  If `P = Pᴴ`, `P * P = P`, and `rank(P) = k`, then the right-factor
Choi sandwich by `P` is positive semidefinite under `k`-positivity. -/
theorem IsNPositiveMap.rightProjection_choiMatrix_sandwich_posSemidef_rectangular
    [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsNPositiveMap k T) {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.IsHermitian) (hP_idem : P * P = P) (hrank : P.rank = k) :
    (rightTensorMatrix (d' := d') P * ChoiRectangular.choiMatrix T *
      (rightTensorMatrix (d' := d') P)ᴴ).PosSemidef := by
  obtain ⟨V, rfl⟩ :=
    Matrix.exists_mul_conjTranspose_of_isHermitian_idempotent_rank P hP hP_idem hrank
  exact
    IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_mul_conjTranspose_rectangular
      hT V

/-- If a square right factor `P` fixes the columns of `X`, then
positivity of the Choi sandwich by `P` implies positivity of the rectangular
right compression by `X`.  This is the algebraic half of the converse direction
in Wolf, Proposition 3.1, item 2; the remaining geometric step is to choose a
rank-`k` projection `P` with `P * X = X`. Source: Wolf, Chapter 3,
Proposition 3.1 proof, lines 110--111. -/
theorem rightCompression_posSemidef_of_projection_sandwich_of_mul_eq_self_rectangular
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    {P : Matrix (Fin d) (Fin d) ℂ} {X : Matrix (Fin d) (Fin k) ℂ}
    (hPX : P * X = X)
    (hP : (rightTensorMatrix (d' := d') P * ChoiRectangular.choiMatrix T *
      (rightTensorMatrix (d' := d') P)ᴴ).PosSemidef) :
    (rightCompression T X).PosSemidef := by
  rw [← rightTensorMatrix_mul_choiMatrix_mul_conjTranspose_rectangular]
  have hR :
      rightTensorMatrix (d' := d') X * rightTensorMatrix (d' := d') P =
        rightTensorMatrix (d' := d') X := by
    rw [rightTensorMatrix_mul_rightTensorMatrix, hPX]
  rw [← hR]
  simpa [Matrix.mul_assoc] using
    hP.conjTranspose_mul_mul_same (rightTensorMatrix (d' := d') X)ᴴ

/-- Converse projection-compression implication in Wolf, Proposition 3.1,
item 2. If every rank-`k` Hermitian input projection gives a positive Choi
sandwich and `k ≤ d`, then `T` is `k`-positive. The theorem includes `k = 0`;
normalization requires nonempty input dimension, while the output dimension is
unrestricted. Source: Wolf, Chapter 3, Proposition 3.1, lines 89--115. -/
theorem isNPositiveMap_of_forall_rankProjection_choiMatrix_sandwich_posSemidef_rectangular
    [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hkd : k ≤ d)
    (hP : ∀ P : Matrix (Fin d) (Fin d) ℂ,
      P.IsHermitian → P * P = P → P.rank = k →
        (rightTensorMatrix (d' := d') P * ChoiRectangular.choiMatrix T *
          (rightTensorMatrix (d' := d') P)ᴴ).PosSemidef) :
    IsNPositiveMap k T := by
  rw [isNPositiveMap_iff_forall_rightCompression_posSemidef]
  intro X
  obtain ⟨P, hHerm, hIdem, hrank, hPX⟩ :=
    Matrix.exists_isHermitian_idempotent_rank_mul_eq_self hkd X
  exact
    rightCompression_posSemidef_of_projection_sandwich_of_mul_eq_self_rectangular
    hPX (hP P hHerm hIdem hrank)

/-- Wolf's rank-`k` projection form of the rectangular Choi criterion: under
`d > 0` and `k ≤ d`, `k`-positivity is equivalent to positivity of all Choi
sandwiches by rank-`k` Hermitian idempotent projections on the input factor.
The theorem includes `k = 0`; the output dimension is unrestricted. Source:
Wolf, Chapter 3, Proposition 3.1, lines 89--115. -/
theorem isNPositiveMap_iff_forall_rankProjection_choiMatrix_sandwich_posSemidef_rectangular
    [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ} (hkd : k ≤ d) :
    IsNPositiveMap k T ↔
      ∀ P : Matrix (Fin d) (Fin d) ℂ,
        P.IsHermitian → P * P = P → P.rank = k →
          (rightTensorMatrix (d' := d') P * ChoiRectangular.choiMatrix T *
            (rightTensorMatrix (d' := d') P)ᴴ).PosSemidef := by
  constructor
  · intro hT P hHerm hIdem hrank
    exact
      IsNPositiveMap.rightProjection_choiMatrix_sandwich_posSemidef_rectangular
        hT hHerm hIdem hrank
  · exact
      isNPositiveMap_of_forall_rankProjection_choiMatrix_sandwich_posSemidef_rectangular
        hkd

/-- Forward direction of Wolf's Schmidt-rank expectation criterion. If `T` is
`k`-positive, then the rectangular Choi quadratic form is nonnegative on every
output-input vector of Schmidt rank at most `k`. Source: Wolf, Chapter 3,
Proposition 3.1, lines 89--115, with the exact-rank
wording correction recorded in
`docs/paper-gaps/wolf_prop3_1_exact_schmidt_rank_scope.tex`. -/
theorem IsNPositiveMap.choiMatrix_quadraticForm_nonneg_of_hasSchmidtRankLE_rectangular [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsNPositiveMap k T) {ψ : Fin d' × Fin d → ℂ}
    (hψ : Matrix.HasSchmidtRankLE k ψ) :
    0 ≤ star ψ ⬝ᵥ (ChoiRectangular.choiMatrix T *ᵥ ψ) := by
  obtain ⟨X, η, hη⟩ :=
    exists_rightTensorMatrix_conjTranspose_mulVec_of_hasSchmidtRankLE hψ
  have hcomp : (rightCompression T X).PosSemidef :=
    (isNPositiveMap_iff_forall_rightCompression_posSemidef k T).mp hT X
  have hq := hcomp.dotProduct_mulVec_nonneg η
  rw [rightCompression_quadraticForm_eq_choiMatrix_quadraticForm_rectangular] at hq
  simpa [hη] using hq

/-- Schmidt-rank expectation criterion for Wolf's rectangular Choi matrix:
`k`-positivity is equivalent to nonnegativity of the Choi quadratic form on all
output-input vectors of Schmidt rank at most `k`. The input dimension is
nonempty; `k = 0` and an empty output dimension are permitted.
Wolf's exact-rank wording is not valid under only `k ≤ d`; see
`docs/paper-gaps/wolf_prop3_1_exact_schmidt_rank_scope.tex`.
Source: Wolf, Chapter 3, Proposition 3.1, lines 89--115. -/
theorem isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg_rectangular
    [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ} :
    IsNPositiveMap k T ↔
      ∀ ψ : Fin d' × Fin d → ℂ, Matrix.HasSchmidtRankLE k ψ →
        (0 : ℂ) ≤ star ψ ⬝ᵥ (ChoiRectangular.choiMatrix T *ᵥ ψ) := by
  constructor
  · intro hT ψ hψ
    exact IsNPositiveMap.choiMatrix_quadraticForm_nonneg_of_hasSchmidtRankLE_rectangular hT hψ
  · intro hψ
    exact isNPositiveMap_of_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg_rectangular hψ

/-! ### Equal-dimension specializations -/
variable {D : ℕ}
/-- Equal-dimension specialization of the rectangular right-tensor sandwich. -/
theorem rightTensorMatrix_mul_choiMatrix_mul_conjTranspose
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) :
    rightTensorMatrix X * choiMatrix T * (rightTensorMatrix X)ᴴ =
      rightCompression T X := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (rightTensorMatrix_mul_choiMatrix_mul_conjTranspose_rectangular
      (d' := D) T X)
/-- Equal-dimension specialization of the rectangular Choi-sandwich quadratic form. -/
theorem rightTensor_choiMatrix_quadraticForm_eq
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) (η : Fin D × Fin k → ℂ) :
    star η ⬝ᵥ
        ((rightTensorMatrix X * choiMatrix T * (rightTensorMatrix X)ᴴ) *ᵥ η) =
      star ((rightTensorMatrix X)ᴴ *ᵥ η) ⬝ᵥ
        (choiMatrix T *ᵥ ((rightTensorMatrix X)ᴴ *ᵥ η)) := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (rightTensor_choiMatrix_quadraticForm_eq_rectangular (d' := D) T X η)
/-- Equal-dimension specialization of the rectangular right-compression quadratic form. -/
theorem rightCompression_quadraticForm_eq_choiMatrix_quadraticForm
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D) (Fin k) ℂ) (η : Fin D × Fin k → ℂ) :
    star η ⬝ᵥ (rightCompression T X *ᵥ η) =
      star ((rightTensorMatrix X)ᴴ *ᵥ η) ⬝ᵥ
        (choiMatrix T *ᵥ ((rightTensorMatrix X)ᴴ *ᵥ η)) := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (rightCompression_quadraticForm_eq_choiMatrix_quadraticForm_rectangular
      (d' := D) T X η)
/-- Equal-dimension specialization of the converse bounded-Schmidt-rank Choi test. -/
theorem isNPositiveMap_of_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hψ : ∀ ψ : Fin D × Fin D → ℂ, Matrix.HasSchmidtRankLE k ψ →
      (0 : ℂ) ≤ star ψ ⬝ᵥ (choiMatrix T *ᵥ ψ)) :
    IsNPositiveMap k T := by
  apply
    isNPositiveMap_of_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg_rectangular
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using hψ
/-- Equal-dimension specialization of rectangular Choi-sandwich positivity. -/
theorem IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsNPositiveMap k T) (X : Matrix (Fin D) (Fin k) ℂ) :
    (rightTensorMatrix X * choiMatrix T * (rightTensorMatrix X)ᴴ).PosSemidef := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_rectangular
      (d' := D) hT X)
/-- Equal-dimension specialization of the factorized Choi-sandwich identity. -/
theorem rightTensorMatrix_mul_conjTranspose_choi_sandwich_eq
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (V : Matrix (Fin D) (Fin k) ℂ) :
    rightTensorMatrix (V * Vᴴ) * choiMatrix T * (rightTensorMatrix (V * Vᴴ))ᴴ =
      (rightTensorMatrix V)ᴴ *
        (rightTensorMatrix V * choiMatrix T * (rightTensorMatrix V)ᴴ) *
          rightTensorMatrix V := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (rightTensorMatrix_mul_conjTranspose_choi_sandwich_eq_rectangular
      (d' := D) T V)
/-- Equal-dimension specialization of the factorized-projection Choi sandwich. -/
theorem IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_mul_conjTranspose
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsNPositiveMap k T) (V : Matrix (Fin D) (Fin k) ℂ) :
    (rightTensorMatrix (V * Vᴴ) * choiMatrix T *
      (rightTensorMatrix (V * Vᴴ))ᴴ).PosSemidef := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_mul_conjTranspose_rectangular
      (d' := D) hT V)
/-- Equal-dimension specialization of the forward rank-`k` projection Choi sandwich. -/
theorem IsNPositiveMap.rightTensor_choiMatrix_sandwich_posSemidef_of_isHermitian_idempotent_rank
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsNPositiveMap k T) {P : Matrix (Fin D) (Fin D) ℂ}
    (hP : P.IsHermitian) (hP_idem : P * P = P) (hrank : P.rank = k) :
    (rightTensorMatrix P * choiMatrix T * (rightTensorMatrix P)ᴴ).PosSemidef := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (IsNPositiveMap.rightProjection_choiMatrix_sandwich_posSemidef_rectangular
      (d' := D) hT hP hP_idem hrank)
/-- Equal-dimension specialization of fixed-column compression. -/
theorem rightCompression_posSemidef_of_rightTensorMatrix_sandwich_posSemidef_of_mul_eq_self
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    {P : Matrix (Fin D) (Fin D) ℂ} {X : Matrix (Fin D) (Fin k) ℂ}
    (hPX : P * X = X)
    (hP : (rightTensorMatrix P * choiMatrix T * (rightTensorMatrix P)ᴴ).PosSemidef) :
    (rightCompression T X).PosSemidef := by
  apply
    rightCompression_posSemidef_of_projection_sandwich_of_mul_eq_self_rectangular
      hPX
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using hP
/-- Equal-dimension specialization of the projection-compression converse. -/
theorem isNPositiveMap_of_forall_rankProjection_rightTensor_choiMatrix_sandwich_posSemidef
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hkD : k ≤ D)
    (hP : ∀ P : Matrix (Fin D) (Fin D) ℂ,
      P.IsHermitian → P * P = P → P.rank = k →
        (rightTensorMatrix P * choiMatrix T * (rightTensorMatrix P)ᴴ).PosSemidef) :
    IsNPositiveMap k T := by
  apply
    isNPositiveMap_of_forall_rankProjection_choiMatrix_sandwich_posSemidef_rectangular
      hkD
  intro P hHerm hIdem hrank
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    hP P hHerm hIdem hrank
/-- Equal-dimension specialization of Wolf's rank-`k` projection criterion. -/
theorem isNPositiveMap_iff_forall_rankProjection_rightTensor_choiMatrix_sandwich_posSemidef
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} (hkD : k ≤ D) :
    IsNPositiveMap k T ↔
      ∀ P : Matrix (Fin D) (Fin D) ℂ,
        P.IsHermitian → P * P = P → P.rank = k →
          (rightTensorMatrix P * choiMatrix T * (rightTensorMatrix P)ᴴ).PosSemidef := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (isNPositiveMap_iff_forall_rankProjection_choiMatrix_sandwich_posSemidef_rectangular
      (d' := D) (T := T) hkD)
/-- Equal-dimension specialization of the forward bounded-Schmidt-rank Choi test. -/
theorem IsNPositiveMap.choiMatrix_quadraticForm_nonneg_of_hasSchmidtRankLE
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsNPositiveMap k T) {ψ : Fin D × Fin D → ℂ}
    (hψ : Matrix.HasSchmidtRankLE k ψ) :
    0 ≤ star ψ ⬝ᵥ (choiMatrix T *ᵥ ψ) := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (IsNPositiveMap.choiMatrix_quadraticForm_nonneg_of_hasSchmidtRankLE_rectangular
      (d' := D) hT hψ)
/-- Equal-dimension specialization of the bounded-Schmidt-rank Choi criterion. -/
theorem isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg
    [NeZero D]
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ} :
    IsNPositiveMap k T ↔
      ∀ ψ : Fin D × Fin D → ℂ, Matrix.HasSchmidtRankLE k ψ →
        (0 : ℂ) ≤ star ψ ⬝ᵥ (choiMatrix T *ᵥ ψ) := by
  simpa only [ChoiRectangular.choiMatrix_eq_choiJamiolkowski] using
    (isNPositiveMap_iff_forall_hasSchmidtRankLE_choiMatrix_quadraticForm_nonneg_rectangular
      (d' := D) (T := T))

end ChoiJamiolkowski
