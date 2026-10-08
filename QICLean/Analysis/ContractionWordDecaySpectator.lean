/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ContractionWordDecay
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Contraction-word decay with finite spectators

The finite contraction-word estimate remains valid after tensoring every product with
the identity on an arbitrary finite spectator. The proof writes an arbitrary, possibly
entangled vector as its spectator coordinate slices and sums the physical squared-norm
estimates. No spectator-dimension factor or nonemptiness assumption is introduced.

This is the finite-word spectator step for the excited-state estimate in the area-law
manuscript, `09-amplification.tex`, lines 235–249, source revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It does not identify a word law
with independent clocks or assert locality of the products.
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder Kronecker

namespace Matrix

variable {n a : Type*} [Fintype n] [DecidableEq n] [Fintype a] [DecidableEq a]

/-- An operator tensored with the spectator identity acts separately on each coordinate
slice, including slices of entangled vectors. -/
theorem kronecker_one_mulVec_apply_slice (A : Matrix n n ℂ)
    (ξ : EuclideanSpace ℂ (n × a)) (i : n) (r : a) :
    ((A ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ ξ) (i, r) =
      (A *ᵥ fun j => ξ (j, r)) i := by
  classical
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    Matrix.one_apply, mul_ite, ite_mul]

/-- The squared Euclidean norm is the sum of the squared norms of all spectator slices. -/
theorem norm_sq_eq_sum_spectator_slices (ξ : EuclideanSpace ℂ (n × a)) :
    ‖ξ‖ ^ 2 = ∑ r : a, ‖WithLp.toLp 2 (fun i => ξ (i, r))‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The output energy of an amplified matrix is exactly the sum of the output energies
on the physical slices. -/
theorem norm_sq_toEuclideanLin_kronecker_one_eq_sum (A : Matrix n n ℂ)
    (ξ : EuclideanSpace ℂ (n × a)) :
    ‖toEuclideanLin (A ⊗ₖ (1 : Matrix a a ℂ)) ξ‖ ^ 2 =
      ∑ r : a, ‖toEuclideanLin A (WithLp.toLp 2 (fun i => ξ (i, r)))‖ ^ 2 := by
  change ‖WithLp.toLp 2 ((A ⊗ₖ (1 : Matrix a a ℂ)) *ᵥ ξ)‖ ^ 2 =
    ∑ r : a, ‖WithLp.toLp 2 (A *ᵥ fun i => ξ (i, r))‖ ^ 2
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp_rw [kronecker_one_mulVec_apply_slice]
  exact Finset.sum_comm

variable {ι : Type*} [Fintype ι]

/-- Tensoring the chronological product with an identity commutes with adding the
latest event. -/
theorem contractionWord_snoc_kronecker_one (k : ι → Matrix n n ℂ) {m : ℕ}
    (w : Fin m → ι) (i : ι) :
    contractionWord k (m + 1) (Fin.snoc w i) ⊗ₖ (1 : Matrix a a ℂ) =
      (CFC.sqrt (1 - k i) ⊗ₖ (1 : Matrix a a ℂ)) *
        (contractionWord k m w ⊗ₖ (1 : Matrix a a ℂ)) := by
  rw [contractionWord_snoc, ← mul_kronecker_mul, Matrix.mul_one]

/-- Sum of squared output norms of the actual chronological products, tensored with a
spectator identity, over all words of the given length. -/
noncomputable def contractionWordSpectatorSum (k : ι → Matrix n n ℂ) (m : ℕ)
    (ξ : EuclideanSpace ℂ (n × a)) : ℝ :=
  ∑ w : Fin m → ι,
    ‖toEuclideanLin (contractionWord k m w ⊗ₖ (1 : Matrix a a ℂ)) ξ‖ ^ 2

/-- The spectator word sum decomposes into physical word sums, with no change to the
chronological products or their weights. -/
theorem contractionWordSpectatorSum_eq_sum_slices (k : ι → Matrix n n ℂ) (m : ℕ)
    (ξ : EuclideanSpace ℂ (n × a)) :
    contractionWordSpectatorSum k m ξ =
      ∑ r : a, contractionWordSum k m (WithLp.toLp 2 (fun i => ξ (i, r))) := by
  simp only [contractionWordSpectatorSum, norm_sq_toEuclideanLin_kronecker_one_eq_sum,
    contractionWordSum]
  exact Finset.sum_comm

@[simp] theorem contractionWordSpectatorSum_zero (k : ι → Matrix n n ℂ)
    (ξ : EuclideanSpace ℂ (n × a)) : contractionWordSpectatorSum k 0 ξ = ‖ξ‖ ^ 2 := by
  rw [contractionWordSpectatorSum_eq_sum_slices]
  simp_rw [contractionWordSum_zero]
  exact (norm_sq_eq_sum_spectator_slices ξ).symm

@[simp] theorem contractionWordSpectatorSum_zero_vector (k : ι → Matrix n n ℂ) (m : ℕ) :
    contractionWordSpectatorSum k m (0 : EuclideanSpace ℂ (n × a)) = 0 := by
  simp [contractionWordSpectatorSum]

/-- The gap gives a dimension-free bound for arbitrary entangled inputs whose physical
slices lie in the excited sector. -/
theorem contractionWordSpectatorSum_le_pow (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω : EuclideanSpace ℂ n} {ξ : EuclideanSpace ℂ (n × a)} {g : ℝ}
    (hΩ : ∀ i, toEuclideanLin (k i) Ω = 0)
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hg : g ≤ Fintype.card ι)
    (hξ : ∀ r : a, ⟪Ω, WithLp.toLp 2 (fun i => ξ (i, r))⟫_ℂ = 0) (m : ℕ) :
    contractionWordSpectatorSum k m ξ ≤ (Fintype.card ι - g) ^ m * ‖ξ‖ ^ 2 := by
  rw [contractionWordSpectatorSum_eq_sum_slices, norm_sq_eq_sum_spectator_slices,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => contractionWordSum_le_pow k hk hΩ hgap hg (hξ r) m

/-- If the gap is larger than the number of terms, every vector in the excited physical
sector tensored with an arbitrary finite spectator is zero. -/
theorem spectator_eq_zero_of_card_lt_gap (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω : EuclideanSpace ℂ n} {ξ : EuclideanSpace ℂ (n × a)} {g : ℝ}
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hξ : ∀ r : a, ⟪Ω, WithLp.toLp 2 (fun i => ξ (i, r))⟫_ℂ = 0)
    (hg : (Fintype.card ι : ℝ) < g) : ξ = 0 := by
  ext ⟨i, r⟩
  have hs := eq_zero_of_card_lt_gap k hk hgap (hξ r) hg
  exact congrFun (congrArg WithLp.ofLp hs) i

/-- The complementary rank-one projection has range orthogonal to a normalized vector. -/
theorem inner_toEuclideanLin_one_sub_vecMulVec_eq_zero {Ω : EuclideanSpace ℂ n}
    (hΩ : ‖Ω‖ = 1) (v : EuclideanSpace ℂ n) :
    ⟪Ω, toEuclideanLin (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) v⟫_ℂ = 0 := by
  simp only [map_sub, LinearMap.sub_apply, toLpLin_one, LinearMap.id_apply,
    toEuclideanLin_vecMulVec_star_self_apply, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hΩ]
  simp

/-- Applying the physical excited projection to an arbitrary joint vector makes every
spectator coordinate slice orthogonal to the ground vector. -/
theorem inner_spectatorSlice_excitedProjection_eq_zero {Ω : EuclideanSpace ℂ n}
    (hΩ : ‖Ω‖ = 1) (ζ : EuclideanSpace ℂ (n × a)) (r : a) :
    ⟪Ω, WithLp.toLp 2 (fun i =>
      (toEuclideanLin ((1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ⊗ₖ
        (1 : Matrix a a ℂ)) ζ) (i, r))⟫_ℂ = 0 := by
  have hs : WithLp.toLp 2 (fun i =>
      (toEuclideanLin ((1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ⊗ₖ
        (1 : Matrix a a ℂ)) ζ) (i, r)) =
      toEuclideanLin (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))
        (WithLp.toLp 2 (fun i => ζ (i, r))) := by
    ext i
    exact kronecker_one_mulVec_apply_slice _ ζ i r
  rw [hs]
  exact inner_toEuclideanLin_one_sub_vecMulVec_eq_zero hΩ _

/-- Finite-word decay after projecting an arbitrary entangled input to the excited
physical sector. -/
theorem contractionWordSpectatorSum_excitedProjection_le_pow (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω : EuclideanSpace ℂ n} {g : ℝ} (hnorm : ‖Ω‖ = 1)
    (hΩ : ∀ i, toEuclideanLin (k i) Ω = 0)
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hg : g ≤ Fintype.card ι) (ζ : EuclideanSpace ℂ (n × a)) (m : ℕ) :
    let ξ := toEuclideanLin ((1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ⊗ₖ
      (1 : Matrix a a ℂ)) ζ
    contractionWordSpectatorSum k m ξ ≤ (Fintype.card ι - g) ^ m * ‖ξ‖ ^ 2 := by
  exact contractionWordSpectatorSum_le_pow k hk hΩ hgap hg
    (inner_spectatorSlice_excitedProjection_eq_zero hnorm ζ) m

/-- In the large-gap case the projected joint input vanishes, without an upper bound
on the allowed gap or a nonempty spectator hypothesis. -/
theorem spectator_excitedProjection_eq_zero_of_card_lt_gap (k : ι → Matrix n n ℂ)
    (hk : ∀ i, k i ≤ 1) {Ω : EuclideanSpace ℂ n} {g : ℝ} (hnorm : ‖Ω‖ = 1)
    (hgap : (g : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ ∑ i, k i)
    (hg : (Fintype.card ι : ℝ) < g) (ζ : EuclideanSpace ℂ (n × a)) :
    toEuclideanLin ((1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ⊗ₖ
      (1 : Matrix a a ℂ)) ζ = 0 := by
  exact spectator_eq_zero_of_card_lt_gap k hk hgap
    (inner_spectatorSlice_excitedProjection_eq_zero hnorm ζ) hg

end Matrix
