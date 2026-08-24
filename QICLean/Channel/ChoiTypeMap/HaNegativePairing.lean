/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ChoiTypeMap.HaBlockTranspose
import QICLean.Channel.MaximallyEntangled

/-!
# Ha's negative pairing

This module formalizes the remaining algebraic part of Ha's construction on
pp. 595--596.  It first fixes the tensor-factor order in the Eom--Kye pairing
identity, and then evaluates that pairing for Ha's matrix `A_γ` and the
Choi-type map.

The factor swap is essential: the map acts on the first factor of `A_γ^σ`.
The source uses the unnormalized vectorized identity `J_d`, whereas
`omegaVec d` is normalized; consequently the corresponding quadratic form is
multiplied by `d`.

No positivity, indecomposability, or atomicity assertion is made here.

## References

* [K.-C. Ha, *Atomic Positive Linear Maps in Matrix Algebras*,
  pp. 595--596][Ha1998AtomicPositiveMaps]
* [S.-H. Kye and H.-J. Eom, *Duality for positive linear maps in matrix
  algebras*, equations (1) and (13)][EomKye2000Duality]
-/

open scoped Matrix ComplexOrder
open Finset

namespace Matrix

/-! ## Tensor-factor order and the Eom--Kye pairing -/

/-- Exchange the two tensor factors of a bipartite matrix. -/
def tensorFactorSwap {I J : Type*}
    (A : Matrix (I × J) (I × J) ℂ) :
    Matrix (J × I) (J × I) ℂ :=
  A.submatrix Prod.swap Prod.swap

@[simp]
theorem tensorFactorSwap_apply {I J : Type*}
    (A : Matrix (I × J) (I × J) ℂ)
    (p q : J × I) :
    tensorFactorSwap A p q = A (p.2, p.1) (q.2, q.1) :=
  rfl

@[simp]
theorem tensorFactorSwap_tensorFactorSwap {I J : Type*}
    (A : Matrix (I × J) (I × J) ℂ) :
    tensorFactorSwap (tensorFactorSwap A) = A := by
  ext p q
  rfl

/-- Swapping factors converts the source's second-factor partial transpose
into a first-factor partial transpose. -/
theorem partialTransposeLeft_tensorFactorSwap {d d' : ℕ}
    (A : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ) :
    partialTransposeLeft (tensorFactorSwap A) =
      tensorFactorSwap (partialTransposeRight A) := by
  ext p q
  rfl

/-- Tensor-factor exchange preserves an upper bound on Schmidt number. -/
theorem HasSchmidtNumberLE.tensorFactorSwap {d d' n : ℕ}
    {A : Matrix (Fin d × Fin d') (Fin d × Fin d') ℂ}
    (hA : HasSchmidtNumberLE n A) :
    HasSchmidtNumberLE n (tensorFactorSwap A) := by
  classical
  obtain ⟨ι, _, ψ, hψ, rfl⟩ := hA
  refine ⟨ι, inferInstance, fun i ↦ (ψ i) ∘ Prod.swap, fun i ↦ ?_, ?_⟩
  · have hcoeff :
        schmidtCoeffMatrix ((ψ i) ∘ Prod.swap) = (schmidtCoeffMatrix (ψ i))ᵀ := by
      ext a b
      simp [schmidtCoeffMatrix, Function.comp]
    rw [HasSchmidtRankLE, schmidtRank, hcoeff, Matrix.rank_transpose]
    exact hψ i
  · ext p q
    simp only [tensorFactorSwap_apply, Matrix.sum_apply, vecMulVec_apply,
      Pi.star_apply, Function.comp_apply]
    rfl

/-- The coefficient form of the Eom--Kye bilinear pairing.  If
`A = ∑ a_{i,j} ⊗ e_{i,j}`, this is `∑ ⟨T(e_{i,j}), a_{i,j}⟩`, with
`⟨X,Y⟩ = Tr(Y Xᵀ)`. -/
noncomputable def eomKyePairing {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix (J × I) (J × I) ℂ)
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix J J ℂ) : ℂ :=
  ∑ i : I, ∑ j : I, ∑ a : J, ∑ b : J,
    A (a, i) (b, j) * T (Matrix.single i j 1) a b

/-- Pair a bipartite matrix with the unnormalized vectorized identity `J`.
In coordinates this is `∑ i,j X_{(i,i),(j,j)}`. -/
noncomputable def eomKyeJPairing {I : Type*} [Fintype I]
    (X : Matrix (I × I) (I × I) ℂ) : ℂ :=
  ∑ i : I, ∑ j : I, X (i, i) (j, j)

/-- **Eom--Kye, equations (1) and (13).**  The coefficient pairing is
obtained by applying the map to the first tensor factor of the factor-swapped
matrix and then pairing with the vectorized identity. -/
theorem eomKyePairing_eq_JPairing_tensorMapId_factorSwap
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix (I × I) (I × I) ℂ)
    (T : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) :
    eomKyePairing A T = eomKyeJPairing (tensorMapId T (tensorFactorSwap A)) := by
  classical
  have hslice (a b : I) :
      bipartiteSlice (tensorFactorSwap A) a b =
        ∑ i : I, ∑ j : I, A (a, i) (b, j) • Matrix.single i j 1 := by
    rw [Matrix.matrix_eq_sum_single (bipartiteSlice (tensorFactorSwap A) a b)]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp [bipartiteSlice_apply]
  have hreorder (f : I → I → I → I → ℂ) :
      (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) =
        ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
    calc
      (∑ i, ∑ j, ∑ a, ∑ b, f i j a b) =
          ∑ i, ∑ a, ∑ j, ∑ b, f i j a b := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, ∑ i, ∑ j, f i j a b := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ ↦ ?_
        rw [show (∑ i, ∑ j, ∑ b, f i j a b) =
            ∑ i, ∑ b, ∑ j, f i j a b from
          Finset.sum_congr rfl fun i _ ↦ Finset.sum_comm]
        exact Finset.sum_comm
  rw [eomKyePairing, eomKyeJPairing]
  simp only [tensorMapId_apply]
  simp_rw [hslice, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact hreorder fun i j a b ↦ A (a, i) (b, j) * T (Matrix.single i j 1) a b

/-- The source's vectorized identity is unnormalized.  With the repository's
normalized `omegaVec`, its pairing is therefore `d` times the corresponding
quadratic form. -/
theorem eomKyeJPairing_eq_omegaVec_quadraticForm {d : ℕ} (hd : 0 < d)
    (X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    eomKyeJPairing X =
      (d : ℂ) * (star (omegaVec d) ⬝ᵥ (X *ᵥ omegaVec d)) := by
  classical
  have hstar (i j : Fin d) :
      star (if i = j then (1 : ℂ) / ((d : ℝ).sqrt : ℂ) else 0) =
        if i = j then star ((1 : ℂ) / ((d : ℝ).sqrt : ℂ)) else 0 := by
    by_cases hij : i = j <;> simp [hij]
  rw [eomKyeJPairing]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Fintype.sum_prod_type,
    omegaVec_apply]
  simp_rw [mul_ite, mul_zero]
  simp_rw [hstar]
  simp only [one_div, star_inv₀, RCLike.star_def, Complex.conj_ofReal,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, ite_mul, zero_mul]
  let c : ℂ := ((d : ℝ).sqrt : ℂ)⁻¹
  change (∑ i : Fin d, ∑ j : Fin d, X (i, i) (j, j)) =
    (d : ℂ) * ∑ i : Fin d, c * ∑ j : Fin d, X (i, i) (j, j) * c
  have hc : c * c = 1 / (d : ℂ) := by
    dsimp [c]
    simpa [div_eq_mul_inv, Complex.conj_ofReal] using
      (MaximallyEntangled.omegaCoeff_eq_inv hd)
  have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdc : (d : ℂ) * c * c = 1 := by
    rw [mul_assoc, hc]
    field_simp
  symm
  calc
    (d : ℂ) * ∑ i : Fin d, c * ∑ j : Fin d, X (i, i) (j, j) * c =
        ∑ i : Fin d, (d : ℂ) *
          (c * ∑ j : Fin d, X (i, i) (j, j) * c) := by
            rw [Finset.mul_sum]
    _ = ∑ i : Fin d, ∑ j : Fin d, X (i, i) (j, j) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [← Finset.sum_mul]
      calc
        (d : ℂ) * (c * ((∑ j : Fin d, X (i, i) (j, j)) * c)) =
            ((d : ℂ) * c * c) * ∑ j : Fin d, X (i, i) (j, j) := by ring
        _ = ∑ j : Fin d, X (i, i) (j, j) := by rw [hdc, one_mul]

/-- Eom--Kye's factor-swapped pairing identity in the repository's normalized
maximally entangled convention. -/
theorem eomKyePairing_eq_omegaVec_quadraticForm_factorSwap {d : ℕ}
    (hd : 0 < d)
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    eomKyePairing A T =
      (d : ℂ) *
        (star (omegaVec d) ⬝ᵥ
          (tensorMapId T (tensorFactorSwap A) *ᵥ omegaVec d)) := by
  rw [eomKyePairing_eq_JPairing_tensorMapId_factorSwap,
    eomKyeJPairing_eq_omegaVec_quadraticForm hd]

/-- Simultaneously changing the chosen basis in the witness matrix and the
linear map leaves the Eom--Kye pairing unchanged. -/
theorem eomKyePairing_reindex {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (A : Matrix (I × I) (I × I) ℂ)
    (T : Matrix J J ℂ →ₗ[ℂ] Matrix J J ℂ) :
    eomKyePairing
        (Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) A) T =
      eomKyePairing A
        ((Matrix.reindexLinearEquiv ℂ ℂ e e).symm.toLinearMap ∘ₗ
          T ∘ₗ (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap) := by
  classical
  have hsingle (i j : I) :
      Matrix.reindex e e (Matrix.single i j (1 : ℂ)) =
        Matrix.single (e i) (e j) 1 := by
    ext a b
    simp [Matrix.single_apply, e.eq_symm_apply]
  have hsum4 (f : J → J → J → J → ℂ) :
      (∑ i : J, ∑ j : J, ∑ a : J, ∑ b : J, f i j a b) =
        ∑ i : I, ∑ j : I, ∑ a : I, ∑ b : I, f (e i) (e j) (e a) (e b) := by
    symm
    calc
      (∑ i : I, ∑ j : I, ∑ a : I, ∑ b : I, f (e i) (e j) (e a) (e b)) =
          ∑ i : I, ∑ j : I, ∑ a : I, ∑ b : J, f (e i) (e j) (e a) b := by
            refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
              Finset.sum_congr rfl fun a _ ↦ ?_
            exact e.sum_comp fun b ↦ f (e i) (e j) (e a) b
      _ = ∑ i : I, ∑ j : I, ∑ a : J, ∑ b : J, f (e i) (e j) a b := by
        refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
        exact e.sum_comp fun a ↦ ∑ b : J, f (e i) (e j) a b
      _ = ∑ i : I, ∑ j : J, ∑ a : J, ∑ b : J, f (e i) j a b := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        exact e.sum_comp fun j ↦ ∑ a : J, ∑ b : J, f (e i) j a b
      _ = ∑ i : J, ∑ j : J, ∑ a : J, ∑ b : J, f i j a b := by
        exact e.sum_comp fun i ↦ ∑ j : J, ∑ a : J, ∑ b : J, f i j a b
  have hA (i j a b : I) :
      Matrix.reindex (Equiv.prodCongr e e) (Equiv.prodCongr e e) A
          (e a, e i) (e b, e j) = A (a, i) (b, j) := by
    simp [Matrix.reindex_apply]
  have htransport (i j a b : I) :
      (((Matrix.reindexLinearEquiv ℂ ℂ e e).symm.toLinearMap ∘ₗ
          T ∘ₗ (Matrix.reindexLinearEquiv ℂ ℂ e e).toLinearMap)
          (Matrix.single i j 1)) a b =
        T (Matrix.single (e i) (e j) 1) (e a) (e b) := by
    simp only [LinearMap.comp_apply]
    change Matrix.reindex e.symm e.symm
        (T (Matrix.reindex e e (Matrix.single i j 1))) a b = _
    rw [hsingle]
    rfl
  simp only [eomKyePairing]
  rw [hsum4]
  simp_rw [hA, htransport]

/-! ## The cyclic realization of Ha's matrix -/

variable {d : ℕ} [NeZero d]

/-- The Choi-type map in the `Fin d` basis used by Ha's witness.  This is
only the coordinate transport of `choiTypeMap`; no positivity claim is part
of the definition. -/
noncomputable def choiTypeMapFin (d n : ℕ) [NeZero d] :
    Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
  (Matrix.reindexLinearEquiv ℂ ℂ (ZMod.finEquiv d) (ZMod.finEquiv d)).symm.toLinearMap ∘ₗ
    choiTypeMap d n ∘ₗ
    (Matrix.reindexLinearEquiv ℂ ℂ
      (ZMod.finEquiv d) (ZMod.finEquiv d)).toLinearMap

/-- The factor-swapped first decomposition still belongs to `V₂`. -/
theorem tensorFactorSwap_haAGamma_hasSchmidtNumberLE_two (γ : ℝ) :
    HasSchmidtNumberLE 2 (tensorFactorSwap (haAGamma d γ)) :=
  (haAGamma_hasSchmidtNumberLE_two γ).tensorFactorSwap

/-- Under the factor swap, Ha's displayed block transpose becomes the
first-factor partial transpose used in the Eom--Kye orientation. -/
theorem partialTransposeLeft_tensorFactorSwap_haAGamma_eq
    (hd : 3 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    partialTransposeLeft (tensorFactorSwap (haAGamma d γ)) =
      tensorFactorSwap (haBlockTransposeDecomposition d γ) := by
  rw [partialTransposeLeft_tensorFactorSwap,
    partialTransposeRight_haAGamma_eq_haBlockTransposeDecomposition hd hγ]

/-- The first-factor partial transpose of the factor-swapped matrix also
belongs to `V₂`. -/
theorem partialTransposeLeft_tensorFactorSwap_haAGamma_hasSchmidtNumberLE_two
    (hd : 3 ≤ d) {γ : ℝ} (hγ : 0 < γ) :
    HasSchmidtNumberLE 2
      (partialTransposeLeft (tensorFactorSwap (haAGamma d γ))) := by
  rw [partialTransposeLeft_tensorFactorSwap]
  exact (partialTransposeRight_haAGamma_hasSchmidtNumberLE_two hd hγ).tensorFactorSwap

/-- Ha's matrix with both tensor factors reindexed by the cyclic basis used by
`choiTypeMap`. -/
noncomputable def haAGammaCyclic (d : ℕ) [NeZero d] (γ : ℝ) :
    Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ :=
  Matrix.reindex
    (Equiv.prodCongr (ZMod.finEquiv d) (ZMod.finEquiv d))
    (Equiv.prodCongr (ZMod.finEquiv d) (ZMod.finEquiv d))
    (haAGamma d γ)

@[simp]
theorem haAGammaCyclic_apply (γ : ℝ) (p q : ZMod d × ZMod d) :
    haAGammaCyclic d γ p q =
      haAGamma d γ
        ((ZMod.finEquiv d).symm p.1, (ZMod.finEquiv d).symm p.2)
        ((ZMod.finEquiv d).symm q.1, (ZMod.finEquiv d).symm q.2) :=
  rfl

/-! ## Ha's scalar pairing -/

/-- Expanding the Choi-type map in the Eom--Kye pairing leaves three
coordinate sums: the unshifted diagonal part, the identity part, and the
forward cyclic diagonal shifts. -/
theorem eomKyePairing_choiTypeMap_eq_coordinate_sums
    (n : ℕ) (A : Matrix (ZMod d × ZMod d) (ZMod d × ZMod d) ℂ) :
    eomKyePairing A (choiTypeMap d n) =
      ((d : ℂ) - (n : ℂ)) * ∑ i : ZMod d, A (i, i) (i, i) -
        ∑ i : ZMod d, ∑ j : ZMod d, A (i, i) (j, j) +
          ∑ k : Fin n, ∑ i : ZMod d,
            A (i, i - ((k.1 + 1 : ℕ) : ZMod d))
              (i, i - ((k.1 + 1 : ℕ) : ZMod d)) := by
  classical
  have hslice (a b i j : ZMod d) :
      bipartiteSlice (tensorFactorSwap A) a b i j = A (a, i) (b, j) :=
    rfl
  rw [eomKyePairing_eq_JPairing_tensorMapId_factorSwap, eomKyeJPairing]
  simp only [tensorMapId_apply]
  simp_rw [choiTypeMap_apply]
  simp_rw [diagonalProjection_conj_choiTypeShift]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply,
    diagonalProjection_apply, Matrix.diagonal_apply, smul_eq_mul]
  simp_rw [hslice]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hdiag :
      (∑ x : ZMod d, ∑ y : ZMod d,
          ((d : ℂ) - (n : ℂ)) *
            if x = y then A (x, x) (y, x) else 0) =
        ((d : ℂ) - (n : ℂ)) * ∑ x : ZMod d, A (x, x) (x, x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    simp
  have hshift :
      (∑ x : ZMod d, ∑ y : ZMod d, ∑ k : Fin n,
          if x = y then
            A (x, x - ((k.1 + 1 : ℕ) : ZMod d))
              (y, x - ((k.1 + 1 : ℕ) : ZMod d))
          else 0) =
        ∑ k : Fin n, ∑ x : ZMod d,
          A (x, x - ((k.1 + 1 : ℕ) : ZMod d))
            (x, x - ((k.1 + 1 : ℕ) : ZMod d)) := by
    simp only [Nat.cast_add, Nat.cast_one, Finset.sum_ite_irrel,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact Finset.sum_comm
  rw [hdiag, hshift]

/-- Every correlated entry of Ha's root average is one. -/
theorem haAGammaCyclic_correlated_entry (hd : 3 ≤ d) (γ : ℝ)
    (i j : ZMod d) : haAGammaCyclic d γ (i, i) (j, j) = 1 := by
  let i' : Fin d := (ZMod.finEquiv d).symm i
  let j' : Fin d := (ZMod.finEquiv d).symm j
  change haAGamma d γ (i', i') (j', j') = 1
  rw [show haAGamma d γ (i', i') (j', j') =
      partialTransposeRight (haAGamma d γ) (i', j') (j', i') from rfl]
  rw [partialTransposeRight_haAGamma_apply hd γ]
  by_cases hij : i' = j'
  · rw [hij]
    simp only [haBlockTransposeEntry, ite_true]
    rw [haCyclicWeight_mul_star hd γ j' j']
    simp [(haCyclicSucc_ne hd j').symm]
    norm_num [Nat.cast_sub (by omega : 1 ≤ d)]
  · simp [haBlockTransposeEntry, hij]

/-- A diagonal entry of `A_γ` is the corresponding diagonal entry of Ha's
block-transpose formula. -/
theorem haAGammaCyclic_diag_entry (hd : 3 ≤ d) (γ : ℝ)
    (a b : ZMod d) :
    haAGammaCyclic d γ (a, b) (a, b) =
      haBlockTransposeEntry d γ
        ((ZMod.finEquiv d).symm a, (ZMod.finEquiv d).symm b)
        ((ZMod.finEquiv d).symm a, (ZMod.finEquiv d).symm b) := by
  change haAGamma d γ
      ((ZMod.finEquiv d).symm a, (ZMod.finEquiv d).symm b)
      ((ZMod.finEquiv d).symm a, (ZMod.finEquiv d).symm b) = _
  rw [show haAGamma d γ
      ((ZMod.finEquiv d).symm a, (ZMod.finEquiv d).symm b)
      ((ZMod.finEquiv d).symm a, (ZMod.finEquiv d).symm b) =
      partialTransposeRight (haAGamma d γ)
        ((ZMod.finEquiv d).symm a, (ZMod.finEquiv d).symm b)
        ((ZMod.finEquiv d).symm a, (ZMod.finEquiv d).symm b) from rfl]
  exact partialTransposeRight_haAGamma_apply hd γ _ _

omit [NeZero d] in
private theorem zmod_natCast_eq_one_iff_of_lt
    (hd : 1 < d) {k : ℕ} (hk : k < d) :
    ((k : ZMod d) = 1) ↔ k = 1 := by
  rw [← Nat.cast_one, ZMod.natCast_eq_natCast_iff']
  simp [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hd]

omit [NeZero d] in
private theorem zmod_natCast_ne_neg_one_of_le_sub_two
    {k : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ d - 2) :
    (k : ZMod d) ≠ -1 := by
  intro hk
  have hzero : ((k + 1 : ℕ) : ZMod d) = 0 := by
    calc
      ((k + 1 : ℕ) : ZMod d) = (k : ZMod d) + 1 := by norm_cast
      _ = -1 + 1 := by rw [hk]
      _ = 0 := by ring
  have hdvd : d ∣ k + 1 := (ZMod.natCast_eq_zero_iff (k + 1) d).mp hzero
  have hdle : d ≤ k + 1 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The forward shifted diagonal entries consist of one exceptional `γ²`
column and unit entries for the remaining source range. -/
theorem haAGammaCyclic_shifted_diag_entry
    (hd : 3 ≤ d) (γ : ℝ) {k : ℕ} (hk1 : 1 ≤ k) (hkd : k ≤ d - 2)
    (i : ZMod d) :
    haAGammaCyclic d γ (i, i - (k : ZMod d)) (i, i - (k : ZMod d)) =
      if k = 1 then
        (d : ℂ)⁻¹ * ((γ : ℂ) ^ 2 + (d - 1 : ℕ))
      else 1 := by
  let a : Fin d := (ZMod.finEquiv d).symm i
  let b : Fin d := (ZMod.finEquiv d).symm (i - (k : ZMod d))
  have hforward : a = haCyclicSucc b ↔ (k : ZMod d) = 1 := by
    constructor
    · intro hab
      have hz := congrArg (ZMod.finEquiv d) hab
      dsimp [a, b] at hz
      have hz' : i = (i - (k : ZMod d)) + 1 := by
        simpa [haCyclicSucc] using hz
      have hz'' : i - (i - (k : ZMod d)) = 1 := by
        calc
          i - (i - (k : ZMod d)) =
              ((i - (k : ZMod d)) + 1) - (i - (k : ZMod d)) := by
                exact congrArg (fun z ↦ z - (i - (k : ZMod d))) hz'
          _ = 1 := by abel
      calc
        (k : ZMod d) = i - (i - (k : ZMod d)) := by abel
        _ = 1 := hz''
    · intro hk
      apply (ZMod.finEquiv d).injective
      dsimp [a, b]
      simp [haCyclicSucc, hk]
  have hreverse : b = haCyclicSucc a ↔ (k : ZMod d) = -1 := by
    constructor
    · intro hba
      have hz := congrArg (ZMod.finEquiv d) hba
      dsimp [a, b] at hz
      have hz' : i - (k : ZMod d) = i + 1 := by
        simpa [haCyclicSucc] using hz
      calc
        (k : ZMod d) = i - (i - (k : ZMod d)) := by abel
        _ = i - (i + 1) := by
          exact congrArg (fun z ↦ i - z) hz'
        _ = -1 := by abel
    · intro hk
      apply (ZMod.finEquiv d).injective
      dsimp [a, b]
      simp [haCyclicSucc, hk]
  have hklt : k < d := by omega
  have hcast_one : (k : ZMod d) = 1 ↔ k = 1 :=
    zmod_natCast_eq_one_iff_of_lt (by omega) hklt
  have hforward_nat : a = haCyclicSucc b ↔ k = 1 := hforward.trans hcast_one
  have hreverse_ne : b ≠ haCyclicSucc a := fun hba ↦
    zmod_natCast_ne_neg_one_of_le_sub_two hk1 hkd (hreverse.mp hba)
  rw [haAGammaCyclic_diag_entry hd γ]
  change haBlockTransposeEntry d γ (a, b) (a, b) = _
  simp only [haBlockTransposeEntry, ite_true]
  rw [haCyclicWeight_mul_star hd γ a b]
  by_cases hk : k = 1
  · rw [ite_eq_left (hforward_nat.mpr hk), ite_eq_left hk]
    norm_num
  · rw [ite_eq_right (hforward_nat.not.mpr hk), ite_eq_right hreverse_ne,
      ite_eq_right hk]
    norm_num [Nat.cast_sub (by omega : 1 ≤ d)]

/-- **Ha 1998, p. 595.**  In the source range, the pairing of `A_γ` with
the Choi-type map is exactly `γ² - 1`.  The theorem is stated below after the
cyclic-coordinate calculation has been exposed as a separate lemma. -/
theorem eomKyePairing_haAGamma_choiTypeMap
    (hd : 3 ≤ d) {n : ℕ} (hn1 : 1 ≤ n) (hnd : n ≤ d - 2)
    {γ : ℝ} (_hγ : 0 < γ) :
    eomKyePairing (haAGammaCyclic d γ) (choiTypeMap d n) =
      ((γ ^ 2 - 1 : ℝ) : ℂ) := by
  classical
  cases n with
  | zero => omega
  | succ m =>
    have hshift (k : Fin (m + 1)) (i : ZMod d) :
        haAGammaCyclic d γ (i, i - ((k.1 + 1 : ℕ) : ZMod d))
            (i, i - ((k.1 + 1 : ℕ) : ZMod d)) =
          if k.1 + 1 = 1 then
            (d : ℂ)⁻¹ * ((γ : ℂ) ^ 2 + (d - 1 : ℕ))
          else 1 :=
      haAGammaCyclic_shifted_diag_entry hd γ (by omega) (by omega) i
    rw [eomKyePairing_choiTypeMap_eq_coordinate_sums]
    simp_rw [haAGammaCyclic_correlated_entry hd γ]
    simp_rw [hshift]
    simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    rw [Fin.sum_univ_succ]
    simp
    have hdne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp [hdne, Nat.cast_sub (by omega : 1 ≤ d)]
    ring

/-- The same scalar pairing in Ha's `Fin d` basis. -/
theorem eomKyePairing_haAGamma_choiTypeMapFin
    (hd : 3 ≤ d) {n : ℕ} (hn1 : 1 ≤ n) (hnd : n ≤ d - 2)
    {γ : ℝ} (hγ : 0 < γ) :
    eomKyePairing (haAGamma d γ) (choiTypeMapFin d n) =
      ((γ ^ 2 - 1 : ℝ) : ℂ) := by
  calc
    eomKyePairing (haAGamma d γ) (choiTypeMapFin d n) =
        eomKyePairing (haAGammaCyclic d γ) (choiTypeMap d n) := by
          simpa [choiTypeMapFin, haAGammaCyclic] using
            (eomKyePairing_reindex (ZMod.finEquiv d) (haAGamma d γ)
              (choiTypeMap d n)).symm
    _ = ((γ ^ 2 - 1 : ℝ) : ℂ) :=
      eomKyePairing_haAGamma_choiTypeMap hd hn1 hnd hγ

/-- Ha's scalar identity as the normalized maximally entangled quadratic
form.  The factor `d` is absent in the source only because its vectorized
identity is unnormalized. -/
theorem choiTypeMapFin_haAGamma_omegaVec_quadraticForm
    (hd : 3 ≤ d) {n : ℕ} (hn1 : 1 ≤ n) (hnd : n ≤ d - 2)
    {γ : ℝ} (hγ : 0 < γ) :
    (d : ℂ) *
        (star (omegaVec d) ⬝ᵥ
          (tensorMapId (choiTypeMapFin d n) (tensorFactorSwap (haAGamma d γ)) *ᵥ
            omegaVec d)) =
      ((γ ^ 2 - 1 : ℝ) : ℂ) := by
  calc
    (d : ℂ) *
          (star (omegaVec d) ⬝ᵥ
            (tensorMapId (choiTypeMapFin d n) (tensorFactorSwap (haAGamma d γ)) *ᵥ
              omegaVec d)) =
        eomKyePairing (haAGamma d γ) (choiTypeMapFin d n) :=
      (eomKyePairing_eq_omegaVec_quadraticForm_factorSwap (by omega)
        (haAGamma d γ) (choiTypeMapFin d n)).symm
    _ = ((γ ^ 2 - 1 : ℝ) : ℂ) :=
      eomKyePairing_haAGamma_choiTypeMapFin hd hn1 hnd hγ

/-- **Ha 1998, p. 595, negative pairing.**  For `0 < γ < 1`, the real
pairing of `A_γ` with the Choi-type map is strictly negative.  This is an
algebraic statement only; no positivity of the map is assumed here. -/
theorem eomKyePairing_haAGamma_choiTypeMap_re_neg
    (hd : 3 ≤ d) {n : ℕ} (hn1 : 1 ≤ n) (hnd : n ≤ d - 2)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (eomKyePairing (haAGammaCyclic d γ) (choiTypeMap d n)).re < 0 := by
  rw [eomKyePairing_haAGamma_choiTypeMap hd hn1 hnd hγ0]
  change γ ^ 2 - 1 < 0
  nlinarith

/-- The normalized factor-swapped quadratic form is negative in Ha's source
range.  This is the same negative pairing with its basis normalization made
explicit. -/
theorem choiTypeMapFin_haAGamma_omegaVec_quadraticForm_re_neg
    (hd : 3 ≤ d) {n : ℕ} (hn1 : 1 ≤ n) (hnd : n ≤ d - 2)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ((d : ℂ) *
      (star (omegaVec d) ⬝ᵥ
        (tensorMapId (choiTypeMapFin d n) (tensorFactorSwap (haAGamma d γ)) *ᵥ
          omegaVec d))).re < 0 := by
  rw [choiTypeMapFin_haAGamma_omegaVec_quadraticForm hd hn1 hnd hγ0]
  change γ ^ 2 - 1 < 0
  nlinarith

end Matrix
