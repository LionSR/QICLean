/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.CommonSchurCutoffs
import QICLean.Entropy.TypicalBellPinPowers
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-! # Common Schur cutoffs in the actual selected Bell range

OpenAI area-law manuscript, `07-comparators.tex`, lines 283–298 and 332–354.
The physical--auxiliary Bell factor is the actual selected Bell vector of the
original state. In the canonical product coordinates, every imposed cutoff
acts on the other factor. The common symmetric vector therefore remains in
the actual Bell range; no abstract commutation or Bell-range premise is used.
The exterior symmetric vector and its positive retained mass are explicit
inputs to this finite projection statement. The iid tail estimates are separate.

## References

* OpenAI area-law manuscript, `comparator:bell-pin` and
  `comparator:rough-overlap`, `07-comparators.tex`, lines 283–298 and 332–354.
-/

open scoped BigOperators Matrix Kronecker ComplexOrder InnerProductSpace TensorProduct
open Matrix PermutationRepresentation TensorPower

noncomputable section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

/-- Product coordinates for two actual vectors. -/
private def productVector (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ (m × n) := WithLp.toLp 2 (fun p ↦ x p.1 * y p.2)

/-- Inner products factor in the canonical product coordinates. -/
private theorem inner_productVector (x x' : EuclideanSpace ℂ m)
    (y y' : EuclideanSpace ℂ n) :
    ⟪productVector x y, productVector x' y'⟫_ℂ = ⟪x, x'⟫_ℂ * ⟪y, y'⟫_ℂ := by
  let b := (EuclideanSpace.basisFun m ℂ).tensorProduct (EuclideanSpace.basisFun n ℂ)
  have hrepr (u : EuclideanSpace ℂ m) (v : EuclideanSpace ℂ n) :
      productVector u v = b.repr (u ⊗ₜ[ℂ] v) := by
    ext i
    simp [productVector, b, OrthonormalBasis.tensorProduct_repr_tmul_apply', mul_comm]
  rw [hrepr, hrepr, LinearIsometryEquiv.inner_map_map, TensorProduct.inner_tmul]

variable [DecidableEq m] [DecidableEq n]

/-- A Kronecker product acts separately on its two actual vector factors. -/
private theorem toEuclideanLin_kronecker_productVector (M : Matrix m m ℂ)
    (N : Matrix n n ℂ) (x : EuclideanSpace ℂ m) (y : EuclideanSpace ℂ n) :
    toEuclideanLin (M ⊗ₖ N) (productVector x y) =
      productVector (toEuclideanLin M x) (toEuclideanLin N y) := by
  let bm := (EuclideanSpace.basisFun m ℂ).toBasis
  let bn := (EuclideanSpace.basisFun n ℂ).toBasis
  have h := Matrix.repr_toLin (bm.tensorProduct bn) (bm.tensorProduct bn)
    (M ⊗ₖ N) (x ⊗ₜ[ℂ] y)
  rw [Matrix.toLin_kronecker, TensorProduct.map_tmul] at h
  ext ⟨i, j⟩
  have hi := congrFun h (i, j)
  have hxy : ((bm.tensorProduct bn).repr (x ⊗ₜ[ℂ] y) : m × n → ℂ) =
      (fun p ↦ x p.1 * y p.2) := by
    funext ⟨i, j⟩
    simp only [Module.Basis.tensorProduct_repr_tmul_apply, bm, bn,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      smul_eq_mul, mul_comm]
  rw [hxy] at hi
  simp only [Module.Basis.tensorProduct_repr_tmul_apply, bm, bn,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    smul_eq_mul] at hi
  change ((M ⊗ₖ N) *ᵥ (fun p : m × n ↦ x p.1 * y p.2)) (i, j) =
    (toEuclideanLin M x) i * (toEuclideanLin N y) j
  simpa only [← toEuclideanLin_eq_toLin_orthonormal, mul_comm] using hi.symm

end Matrix

namespace TensorPower

variable {A B F : Type*} [Fintype A] [Fintype B] [DecidableEq A]
  [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  (ψ₀ : EuclideanSpace ℂ (A × B)) (E : Finset A) (k : ℕ)

local notation "hρA" =>
  Matrix.PosSemidef.partialTraceRight (Matrix.posSemidef_vecMulVec_self_star ψ₀)
local notation "zE" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E

/-- The common exterior cutoff lifts to a unit symmetric vector in the literal
selected Bell range. The coordinate grouping is the canonical equivalence between
copies of a product and the product of the copy spaces. OpenAI area-law manuscript,
`comparator:bell-pin` and `comparator:rough-overlap`, lines 283–298 and 332–354. -/
theorem exists_commonLabelCutoff_bell_vector (hz : 0 < zE)
    (regions : List (Finset F))
    (hnested : regions.Pairwise fun C D ↦ C ⊆ D ∨ D ⊆ C)
    (a : Finset F → ℝ) (R : Finset F) (hdisjoint : ∀ C ∈ regions, Disjoint C R)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) (ψ : EuclideanSpace ℂ (Config k ι))
    (hsym : (ψ : Config k ι → ℂ) ∈ symmetricSubspace k ι)
    (hpos : 0 < ‖toEuclideanLin (labelProj (subsystemPerm k ι R) ell) ψ‖ ^ 2 -
      (regions.map fun C ↦
        ‖toEuclideanLin (1 - labelCutoff (subsystemPerm k ι C) (a C)) ψ‖ ^ 2).sum) :
    let e := Equiv.arrowProdEquivProdArrow (Fin k)
      (fun _ ↦ A × E) (fun _ ↦ (f : F) → ι f)
    let post := WithLp.toLp 2 (fun x : (Fin k → A × E) × Config k ι ↦
      (∏ j, selectedBellVector ψ₀ E (x.1 j)) * ψ x.2)
    ∃ φ : EuclideanSpace ℂ ((Fin k → A × E) × Config k ι), ‖φ‖ = 1 ∧
      (fun x ↦ φ (e x)) ∈ invariantSubspace (copyPerm ((A × E) × ((f : F) → ι f)) k) ∧
      toEuclideanLin ((finKronecker fun _ : Fin k ↦ selectedBellProjection ψ₀ E) ⊗ₖ
        (1 : Matrix (Config k ι) (Config k ι) ℂ)) φ = φ ∧
      toEuclideanLin ((1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
        labelProj (subsystemPerm k ι R) ell) φ = φ ∧
      (∀ C ∈ regions,
        toEuclideanLin ((1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
          labelCutoff (subsystemPerm k ι C) (a C)) φ = φ) ∧
      ‖⟪φ, toEuclideanLin ((1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
        labelProj (subsystemPerm k ι R) ell) post⟫_ℂ‖ ^ 2 =
        ‖toEuclideanLin (commonLabelCutoff ι k regions a *
          labelProj (subsystemPerm k ι R) ell) ψ‖ ^ 2 := by
  intro e post
  obtain ⟨φ₀, hφnorm, hφsym, hφR, hφcut, hoverlap⟩ :=
    exists_commonLabelCutoff_vector ι k regions hnested a R hdisjoint ell ψ hsym hpos
  let b : EuclideanSpace ℂ (Fin k → A × E) :=
    WithLp.toLp 2 (fun x ↦ ∏ j, selectedBellVector ψ₀ E (x j))
  have hb : ‖b‖ = 1 := norm_prod_selectedBellVector ψ₀ E k hz
  have hproj : (finKronecker fun _ : Fin k ↦ selectedBellProjection ψ₀ E) =
      vecMulVec b (star b) := by
    ext x y
    simp only [b, selectedBellProjection, finKronecker_apply, vecMulVec_apply,
      Pi.star_apply, star_prod, Finset.prod_mul_distrib]
  have hbb : star b ⬝ᵥ b = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hb]
    norm_num
  have hfix : toEuclideanLin
      (finKronecker fun _ : Fin k ↦ selectedBellProjection ψ₀ E) b = b := by
    ext x
    change ((finKronecker fun _ : Fin k ↦ selectedBellProjection ψ₀ E) *ᵥ b) x = b x
    rw [hproj, vecMulVec_mulVec, hbb]
    simp
  refine ⟨Matrix.productVector b φ₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hn : ‖Matrix.productVector b φ₀‖ ^ 2 = 1 := by
      rw [@norm_sq_eq_re_inner ℂ, Matrix.inner_productVector,
        inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hb, hφnorm]
      norm_num
    nlinarith [norm_nonneg (Matrix.productVector b φ₀)]
  · intro σ
    rw [permOp_mulVec]
    funext x
    have hφperm := congrFun (hφsym σ) (fun j ↦ (x j).2)
    rw [permOp_mulVec] at hφperm
    change φ₀ (fun j ↦ (x (σ j)).2) = φ₀ (fun j ↦ (x j).2) at hφperm
    exact congrArg₂ (· * ·)
      (prod_selectedBellVector_perm ψ₀ E k σ (fun j ↦ (x j).1)) hφperm
  · rw [Matrix.toEuclideanLin_kronecker_productVector, hfix]
    simp
  · rw [Matrix.toEuclideanLin_kronecker_productVector, hφR]
    simp
  · intro C hC
    rw [Matrix.toEuclideanLin_kronecker_productVector, hφcut C hC]
    simp
  · change ‖⟪Matrix.productVector b φ₀,
        toEuclideanLin ((1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
          labelProj (subsystemPerm k ι R) ell) (Matrix.productVector b ψ)⟫_ℂ‖ ^ 2 = _
    rw [Matrix.toEuclideanLin_kronecker_productVector]
    simpa only [Matrix.toLpLin_one, LinearMap.id_apply, Matrix.inner_productVector,
      inner_self_eq_norm_sq_to_K, hb, RCLike.ofReal_one, one_pow, one_mul] using hoverlap

end TensorPower
