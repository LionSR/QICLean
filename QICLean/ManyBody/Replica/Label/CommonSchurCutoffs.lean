/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.Permutation.SchurSurprisal
import QICLean.Representation.TensorPower.SchurLabelCommutation
import QICLean.ManyBody.Entropy.Filter.SchmidtPinning
import QICLean.Entropy.Typical.BellPinPowers
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-! # A common Schur cutoff on the symmetric subspace

OpenAI area-law manuscript, `07-comparators.tex`, lines 332–354. The imposed
cutoffs are the actual spectral projections of a nested family of physical
regions. The auxiliary label belongs to a disjoint region. Their common
projection preserves the symmetric subspace, and its mass is controlled by
the sum of the individual failures. The exponential tail estimates and the
subsequent comparison with inverse-polynomial mass are separate inputs.

## Main results

* `TensorPower.exists_commonLabelCutoff_bell_vector`: common Schur cutoffs in the actual selected
  Bell range.

## References

* OpenAI area-law manuscript, `comparator:rough-overlap`,
  `07-comparators.tex`, lines 332–354.
-/

section CommonSchurCutoffs

open scoped BigOperators Matrix ComplexOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix PermutationRepresentation

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A finite commuting product is a projection onto the common ranges. -/
private theorem projection_prod_spec (l : List (Matrix n n ℂ))
    (hproj : ∀ P ∈ l, IsStarProjection P) (hcomm : l.Pairwise Commute) :
    IsStarProjection l.prod ∧ ∀ P ∈ l, P * l.prod = l.prod := by
  induction l with
  | nil => simp
  | cons P l ih =>
    rw [List.pairwise_cons] at hcomm
    have hP := hproj P List.mem_cons_self
    have htail := ih (fun Q hQ ↦ hproj Q (List.mem_cons_of_mem P hQ)) hcomm.2
    have hPl := Commute.list_prod_right l P hcomm.1
    refine ⟨by simpa only [List.prod_cons] using hP.mul htail.1 hPl, ?_⟩
    intro Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · simp only [List.prod_cons, ← mul_assoc, hP.isIdempotentElem.eq]
    · rw [List.prod_cons, ← mul_assoc, (hcomm.1 Q hQ).symm.eq, mul_assoc,
        htail.2 Q hQ]

/-- Orthogonal projection separates the squared norm into the retained and
removed components. -/
private theorem projection_norm_split {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (ψ : EuclideanSpace ℂ n) :
    ‖toEuclideanLin P ψ‖ ^ 2 + ‖toEuclideanLin (1 - P) ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  have hp : ‖toEuclideanLin P ψ‖ ^ 2 = (⟪ψ, toEuclideanLin P ψ⟫_ℂ).re := by
    rw [Entropy.norm_toEuclideanLin_sq, ← star_eq_conjTranspose, hP.isSelfAdjoint.star_eq,
      hP.isIdempotentElem.eq]
  have hc : toEuclideanLin (1 - P) ψ = ψ - toEuclideanLin P ψ := by
    simp
  rw [hc, norm_sub_sq (𝕜 := ℂ), RCLike.re_to_complex, ← hp]
  ring

/-- The loss under commuting projections is at most the sum of their individual
losses on the original vector, even after an additional commuting projection. -/
private theorem projection_union_bound (l : List (Matrix n n ℂ))
    (hproj : ∀ P ∈ l, IsStarProjection P) (hcomm : l.Pairwise Commute)
    {Q : Matrix n n ℂ} (hQ : IsStarProjection Q)
    (haux : ∀ P ∈ l, Commute P Q) (ψ : EuclideanSpace ℂ n) :
    ‖toEuclideanLin Q ψ‖ ^ 2 -
        (l.map fun P ↦ ‖toEuclideanLin (1 - P) ψ‖ ^ 2).sum ≤
      ‖toEuclideanLin (l.prod * Q) ψ‖ ^ 2 := by
  induction l with
  | nil => simp
  | cons P l ih =>
    rw [List.pairwise_cons] at hcomm
    have hP := hproj P List.mem_cons_self
    have htail := fun T hT ↦ hproj T (List.mem_cons_of_mem P hT)
    have hauxTail := fun T hT ↦ haux T (List.mem_cons_of_mem P hT)
    have hind := ih htail hcomm.2 hauxTail
    have hprod := (projection_prod_spec l htail hcomm.2).1
    have hprodQ := hprod.mul hQ
      ((Commute.list_prod_right l Q fun T hT ↦ (hauxTail T hT).symm).symm)
    have hPprod := (Commute.list_prod_right l P hcomm.1).mul_right
      (haux P List.mem_cons_self)
    have hcomp : Commute (1 - P) (l.prod * Q) :=
      (Commute.one_left _).sub_left hPprod
    have hnorm : ‖toEuclideanLin (1 - P) (toEuclideanLin (l.prod * Q) ψ)‖ ≤
        ‖toEuclideanLin (1 - P) ψ‖ := by
      rw [← Entropy.toEuclideanLin_mul_apply, hcomp.eq, Entropy.toEuclideanLin_mul_apply]
      exact Entropy.norm_toEuclideanLin_le_of_proj hprodQ.isSelfAdjoint.star_eq
        hprodQ.isIdempotentElem.eq _
    have hsplit := projection_norm_split hP (toEuclideanLin (l.prod * Q) ψ)
    have hnormsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    simp only [List.map_cons, List.sum_cons, List.prod_cons, mul_assoc]
    rw [Entropy.toEuclideanLin_mul_apply]
    nlinarith

end Matrix

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

/-- A selected set of Schur labels is an orthogonal projection. -/
private theorem isStarProjection_labelCutoff (φ : G →* Equiv.Perm X) (a : ℝ) :
    IsStarProjection (labelCutoff φ a) := by
  rw [labelCutoff_eq_spectralProjectionGE]
  have h := (isHermitian_labelObservable φ (fun l ↦ Real.log l.dim)).neg
  exact h.isStarProjection_spectralProjectionGE (-a)

/-- Commutation with every label projection implies commutation with the cutoff. -/
private theorem commute_labelCutoff_left (φ : G →* Equiv.Perm X) (a : ℝ)
    {M : Matrix X X ℂ} (h : ∀ l, Commute (labelProj φ l) M) :
    Commute (labelCutoff φ a) M := by
  exact Commute.sum_left _ _ _ fun l _ ↦ (h l).smul_left _

end PermutationRepresentation

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (k : ℕ)

/-- The product of the actual closed Schur cutoffs in the imposed regions.
OpenAI area-law manuscript, `07-comparators.tex`, lines 332–354. -/
def commonLabelCutoff (regions : List (Finset F)) (a : Finset F → ℝ) :
    Matrix (Config k ι) (Config k ι) ℂ :=
  (regions.map fun B ↦ labelCutoff (subsystemPerm k ι B) (a B)).prod

/-- Nestedness supplies all pairwise cutoff commutations, while disjointness
supplies commutation with the auxiliary label. -/
private theorem cutoffList_spec (regions : List (Finset F))
    (hnested : regions.Pairwise fun B C ↦ B ⊆ C ∨ C ⊆ B)
    (a : Finset F → ℝ) (A : Finset F) (hdisjoint : ∀ B ∈ regions, Disjoint B A)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) :
    let l := regions.map fun B ↦ labelCutoff (subsystemPerm k ι B) (a B)
    (∀ P ∈ l, IsStarProjection P) ∧ l.Pairwise Commute ∧
      ∀ P ∈ l, Commute P (labelProj (subsystemPerm k ι A) ell) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro P hP
    rcases List.mem_map.mp hP with ⟨B, _, rfl⟩
    exact isStarProjection_labelCutoff _ _
  · rw [List.pairwise_map]
    refine hnested.imp fun {B C} hBC ↦ ?_
    refine commute_labelCutoff_left _ _ fun μ ↦ ?_
    refine (commute_labelCutoff_left _ _ fun ν ↦ ?_).symm
    rcases hBC with hBC | hCB
    · exact (commute_labelProj_subsystemPerm_of_subset ι k hBC μ ν).symm
    · exact commute_labelProj_subsystemPerm_of_subset ι k hCB ν μ
  · intro P hP
    rcases List.mem_map.mp hP with ⟨B, hB, rfl⟩
    exact commute_labelCutoff_left _ _ fun μ ↦
      commute_labelProj_subsystemPerm_of_disjoint ι k (hdisjoint B hB) μ ell

/-- Every subsystem Schur label commutes with the full copy-permutation action. -/
private theorem commute_auxLabel_fullPerm (A : Finset F)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) (σ : Equiv.Perm (Fin k)) :
    Commute (labelProj (subsystemPerm k ι A) ell)
      (permOp (copyPerm ((f : F) → ι f) k) σ) := by
  have h := commute_groupAlgebraRep_subsystemPerm_of_subset ι k
    (Finset.subset_univ A) (IrrepLabel.centralIdem_mem_center ell)
    (MonoidAlgebra.single σ 1)
  simpa only [groupAlgebraRep_single, one_smul, subsystemPerm_univ, labelProj] using h

/-- The finite union bound for the actual nested cutoffs after selecting the
auxiliary label. OpenAI area-law manuscript, `07-comparators.tex`, lines 338–348.
The vector need not be normalized. -/
theorem norm_commonLabelCutoff_auxLabel_ge (regions : List (Finset F))
    (hnested : regions.Pairwise fun B C ↦ B ⊆ C ∨ C ⊆ B)
    (a : Finset F → ℝ) (A : Finset F) (hdisjoint : ∀ B ∈ regions, Disjoint B A)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) (ψ : EuclideanSpace ℂ (Config k ι)) :
    ‖toEuclideanLin (labelProj (subsystemPerm k ι A) ell) ψ‖ ^ 2 -
        (regions.map fun B ↦
          ‖toEuclideanLin (1 - labelCutoff (subsystemPerm k ι B) (a B)) ψ‖ ^ 2).sum ≤
      ‖toEuclideanLin (commonLabelCutoff ι k regions a *
        labelProj (subsystemPerm k ι A) ell) ψ‖ ^ 2 := by
  have hs := cutoffList_spec ι k regions hnested a A hdisjoint ell
  have hQ : IsStarProjection (labelProj (subsystemPerm k ι A) ell) :=
    ⟨labelProj_mul_self _ _, (isHermitian_labelProj _ _).isSelfAdjoint⟩
  simpa only [commonLabelCutoff, List.map_map, Function.comp_def] using
    Matrix.projection_union_bound _ hs.1 hs.2.1 hQ hs.2.2 ψ

/-- Positive retained mass produces the normalized common projection, with its
exact overlap and every actual cutoff condition. Symmetry is derived from the
subsystem permutation actions. OpenAI area-law manuscript, `comparator:rough-overlap`,
`07-comparators.tex`, lines 338–354. No unit-vector witness is assumed. -/
theorem exists_commonLabelCutoff_vector (regions : List (Finset F))
    (hnested : regions.Pairwise fun B C ↦ B ⊆ C ∨ C ⊆ B)
    (a : Finset F → ℝ) (A : Finset F) (hdisjoint : ∀ B ∈ regions, Disjoint B A)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) (ψ : EuclideanSpace ℂ (Config k ι))
    (hsym : (ψ : Config k ι → ℂ) ∈ symmetricSubspace k ι)
    (hpos : 0 < ‖toEuclideanLin (labelProj (subsystemPerm k ι A) ell) ψ‖ ^ 2 -
      (regions.map fun B ↦
        ‖toEuclideanLin (1 - labelCutoff (subsystemPerm k ι B) (a B)) ψ‖ ^ 2).sum) :
    ∃ φ : EuclideanSpace ℂ (Config k ι), ‖φ‖ = 1 ∧
      (φ : Config k ι → ℂ) ∈ symmetricSubspace k ι ∧
      toEuclideanLin (labelProj (subsystemPerm k ι A) ell) φ = φ ∧
      (∀ B ∈ regions, toEuclideanLin (labelCutoff (subsystemPerm k ι B) (a B)) φ = φ) ∧
      ‖⟪φ, toEuclideanLin (labelProj (subsystemPerm k ι A) ell) ψ⟫_ℂ‖ ^ 2 =
        ‖toEuclideanLin (commonLabelCutoff ι k regions a *
          labelProj (subsystemPerm k ι A) ell) ψ‖ ^ 2 := by
  let l := regions.map fun B ↦ labelCutoff (subsystemPerm k ι B) (a B)
  let P := l.prod
  let Q := labelProj (subsystemPerm k ι A) ell
  have hs := cutoffList_spec ι k regions hnested a A hdisjoint ell
  have hprod := Matrix.projection_prod_spec l hs.1 hs.2.1
  have hQ : IsStarProjection Q :=
    ⟨labelProj_mul_self _ _, (isHermitian_labelProj _ _).isSelfAdjoint⟩
  have hPQ : Commute P Q :=
    (Commute.list_prod_right l Q fun T hT ↦ (hs.2.2 T hT).symm).symm
  let v := toEuclideanLin (P * Q) ψ
  have hvpos : 0 < ‖v‖ ^ 2 := hpos.trans_le
    (norm_commonLabelCutoff_auxLabel_ge ι k regions hnested a A hdisjoint ell ψ)
  have hv : v ≠ 0 := by
    intro hv
    simp only [hv, norm_zero, zero_pow (by decide : 2 ≠ 0), lt_self_iff_false] at hvpos
  have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hQv : toEuclideanLin Q v = v := by
    dsimp only [v]
    rw [← Entropy.toEuclideanLin_mul_apply, ← mul_assoc, hPQ.symm.eq, mul_assoc,
      hQ.isIdempotentElem.eq]
  have hPv : toEuclideanLin P v = v := by
    dsimp only [v]
    rw [← Entropy.toEuclideanLin_mul_apply, ← mul_assoc, hprod.1.isIdempotentElem.eq]
  have hcutv (B : Finset F) (hB : B ∈ regions) :
      toEuclideanLin (labelCutoff (subsystemPerm k ι B) (a B)) v = v := by
    have hm : labelCutoff (subsystemPerm k ι B) (a B) ∈ l :=
      List.mem_map.mpr ⟨B, hB, rfl⟩
    dsimp only [v]
    rw [← Entropy.toEuclideanLin_mul_apply, ← mul_assoc, hprod.2 _ hm]
  have hfull (σ : Equiv.Perm (Fin k)) :
      Commute (P * Q) (permOp (copyPerm ((f : F) → ι f) k) σ) := by
    have hcut : ∀ T ∈ l, Commute T (permOp (copyPerm ((f : F) → ι f) k) σ) := by
      intro T hT
      rcases List.mem_map.mp hT with ⟨B, _, rfl⟩
      exact commute_labelCutoff_left _ _ fun μ ↦ commute_auxLabel_fullPerm ι k B μ σ
    exact ((Commute.list_prod_right l _ fun T hT ↦ (hcut T hT).symm).symm).mul_left
      (commute_auxLabel_fullPerm ι k A ell σ)
  have hvsym : (v : Config k ι → ℂ) ∈ symmetricSubspace k ι := by
    intro σ
    change permOp (copyPerm ((f : F) → ι f) k) σ *ᵥ ((P * Q) *ᵥ ψ) =
      (P * Q) *ᵥ ψ
    rw [mulVec_mulVec, (hfull σ).symm.eq, ← mulVec_mulVec, hsym σ]
  let φ := ((‖v‖⁻¹ : ℝ) : ℂ) • v
  refine ⟨φ, ?_, ?_, ?_, ?_, ?_⟩
  · simp [φ, norm_smul, hvnorm]
  · change ((‖v‖⁻¹ : ℝ) : ℂ) • (v : Config k ι → ℂ) ∈ symmetricSubspace k ι
    exact (symmetricSubspace k ι).smul_mem _ hvsym
  · change toEuclideanLin Q φ = φ
    simp only [φ, map_smul, hQv]
  · intro B hB
    simp only [φ, map_smul, hcutv B hB]
  · have hrep : toEuclideanLin P (toEuclideanLin Q ψ) = v := by
      rw [← Entropy.toEuclideanLin_mul_apply]
    have hi := LinearMap.adjoint_inner_left (toEuclideanLin P) (toEuclideanLin Q ψ) v
    rw [← toEuclideanLin_conjTranspose_eq_adjoint, ← star_eq_conjTranspose,
      hprod.1.isSelfAdjoint.star_eq,
      hPv, hrep] at hi
    have hn : ‖⟪φ, toEuclideanLin Q ψ⟫_ℂ‖ = ‖v‖ := by
      calc
        ‖⟪φ, toEuclideanLin Q ψ⟫_ℂ‖ = ‖v‖⁻¹ * ‖v‖ ^ 2 := by
          dsimp only [φ]
          rw [inner_smul_left, hi, inner_self_eq_norm_sq_to_K,
            norm_mul, RCLike.norm_conj]
          simp
        _ = ‖v‖ := by
          rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hvnorm, one_mul]
    exact congrArg (fun t : ℝ ↦ t ^ 2) hn

end TensorPower

end

end CommonSchurCutoffs

section CommonSchurBellCutoffs

/-! # Common Schur cutoffs in the actual selected Bell range

OpenAI area-law manuscript, `07-comparators.tex`, lines 283–298 and 332–354.
The physical--auxiliary Bell factor is the actual selected Bell vector of the
original state. In the canonical product coordinates, every imposed cutoff
acts on the other factor. The common symmetric vector therefore remains in
the actual Bell range; no abstract commutation or Bell-range premise is used.
The exterior symmetric vector and its positive retained mass are explicit
inputs to this finite projection statement. The iid tail estimates are separate.

### References

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
      toEuclideanLin ((piKronecker fun _ : Fin k ↦ selectedBellProjection ψ₀ E) ⊗ₖ
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
  have hproj : (piKronecker fun _ : Fin k ↦ selectedBellProjection ψ₀ E) =
      vecMulVec b (star b) := by
    ext x y
    simp only [b, selectedBellProjection, piKronecker_apply, vecMulVec_apply,
      Pi.star_apply, star_prod, Finset.prod_mul_distrib]
  have hbb : star b ⬝ᵥ b = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
      inner_self_eq_norm_sq_to_K, hb]
    norm_num
  have hfix : toEuclideanLin
      (piKronecker fun _ : Fin k ↦ selectedBellProjection ψ₀ E) b = b := by
    ext x
    change ((piKronecker fun _ : Fin k ↦ selectedBellProjection ψ₀ E) *ᵥ b) x = b x
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

end

end CommonSchurBellCutoffs
