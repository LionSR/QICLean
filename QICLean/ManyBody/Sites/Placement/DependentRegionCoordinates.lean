/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Combinatorics.FinSumPermutation
import QICLean.ManyBody.Sites.Placement.RegionPlacement
import QICLean.ManyBody.Sites.RegionMatrix
import QICLean.ManyBody.Sites.Cut
import QICLean.Entropy.Surprisal.FilterMoment
import QICLean.ManyBody.Sites.RegionState
import QICLean.ManyBody.Sites.Placement.Basic

/-!
# Regional operators and marginals under local basis relabelling

A family of equivalences from arbitrary finite site alphabets to `Fin` alphabets
identifies the placement of a regional matrix with `ManyBody.place` and the canonical
finite-product marginal with `ManyBody.regionState`. All identities are exact,
including for complex matrices that are not Hermitian. Empty regions, empty site
sets and empty local alphabets need no separate hypotheses.

The expectation formula of a placed operator is owned here, together with the canonical
identification `dependentGlobalConfigEquiv` of the full-region configurations of the regional
contraction with the global configurations. Variational outputs and their normalization
remain in `Entropy.Filter.Regularized.Marginal`; no optimization or commutation statement is used.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, `03-patches.tex`, lines 68–99, commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* `QICLean.Channel.FiniteProduct` and `QICLean.Entropy.LocalLift` for the
  canonical partial traces and regional operators.
-/

section
open scoped BigOperators Matrix
namespace ManyBody
variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}
variable {Out : V → Type*}

/-- Assemble a dependent vertex configuration from a region and its complement. -/
def assembleDependentRegionConfig (R : Finset V)
    (α : (w : {w : V // w ∈ R}) → Out w.1)
    (τ : (w : {w : V // w ∈ Finset.univ \ R}) → Out w.1) :
    (w : {w : V // w ∈ Finset.univ}) → Out w.1 :=
  fun w => if h : w.1 ∈ R then α ⟨w.1, h⟩ else τ ⟨w.1, by simp [h]⟩

end ManyBody
end

section
open scoped BigOperators Matrix
namespace ManyBody
variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}
variable {Out : V → Type*}

/-- Split an independent dependent configuration into regional coordinates
and complementary coordinates. -/
def dependentRegionConfigEquiv (R : Finset V) :
    ((w : {w : V // w ∈ Finset.univ}) → Out w.1) ≃
      (((w : {w : V // w ∈ R}) → Out w.1) ×
        ((w : {w : V // w ∈ Finset.univ \ R}) → Out w.1)) where
  toFun η := (fun w => η ⟨w.1, Finset.mem_univ w.1⟩,
    fun w => η ⟨w.1, Finset.mem_univ w.1⟩)
  invFun p := assembleDependentRegionConfig R p.1 p.2
  left_inv η := by
    funext w
    by_cases hw : w.1 ∈ R <;> simp [assembleDependentRegionConfig, hw]
  right_inv p := by
    apply Prod.ext
    · funext w
      simp [assembleDependentRegionConfig, w.2]
    · funext w
      simp [assembleDependentRegionConfig, (Finset.mem_sdiff.mp w.2).2]

end ManyBody
end

open scoped BigOperators Matrix Kronecker ComplexOrder
open Matrix

namespace ManyBody

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*}

/-- The canonical identification of the full-region configurations of the regional
contraction with the global configurations: forget the redundant membership witness. -/
def dependentGlobalConfigEquiv :
    ((v : (Finset.univ : Finset V)) → Out v.1) ≃ ((v : V) → Out v) where
  toFun σ v := σ ⟨v, Finset.mem_univ v⟩
  invFun σ v := σ v.1
  left_inv σ := by funext v; rfl
  right_inv σ := rfl

variable [∀ v, Fintype (Out v)] [∀ v, DecidableEq (Out v)]

/-- A placed regional operator pairs with the canonical finite-product marginal of the same
vector. This equality is complex-valued and requires no Hermiticity assumption on the
regional matrix. -/
theorem inner_place_eq_trace_reducedPure (R : Finset V)
    (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ)
    (ξ : EuclideanSpace ℂ ((v : V) → Out v)) :
    inner ℂ ξ (WithLp.toLp 2 (ManyBody.place R K *ᵥ ξ)) =
      Matrix.trace (ManyBody.regionState ξ R * K) := by
  classical
  let e := ManyBody.cutEquiv Out R
  let P := Matrix.vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))
  let Y := P.submatrix e.symm e.symm
  have hρ : ManyBody.regionState ξ R = Matrix.partialTraceRight Y := rfl
  have hpair : Matrix.trace (Matrix.partialTraceRight Y * K) =
      Matrix.trace (Y * (K ⊗ₖ 1)) := by
    let s := Equiv.prodComm (ManyBody.ComplConfig Out R)
      (ManyBody.RegionConfig Out R)
    have hswap : (K ⊗ₖ (1 : Matrix (ManyBody.ComplConfig Out R)
        (ManyBody.ComplConfig Out R) ℂ)).submatrix s s = 1 ⊗ₖ K := by
      ext p q
      exact mul_comm _ _
    calc
      _ = Matrix.trace (Matrix.partialTraceLeft (Y.submatrix s s) * K) := rfl
      _ = Matrix.trace (Y.submatrix s s * (1 ⊗ₖ K)) :=
        Matrix.trace_partialTraceLeft_mul K _
      _ = Matrix.trace ((Y * (K ⊗ₖ 1)).submatrix s s) := by
        rw [← hswap, Matrix.submatrix_mul_equiv]
      _ = Matrix.trace (Y * (K ⊗ₖ 1)) := Matrix.trace_submatrix_equiv s _
  have hLift : (ManyBody.place R K).submatrix e.symm e.symm = K ⊗ₖ 1 := by
    ext ⟨a, c⟩ ⟨b, f⟩
    simp only [Matrix.submatrix_apply, ManyBody.place_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply]
    have hR (x : ManyBody.RegionConfig Out R) (y : ManyBody.ComplConfig Out R) :
        (fun v : {v // v ∈ R} ↦ e.symm (x, y) v) = x :=
      funext fun v ↦ ManyBody.cutEquiv_symm_apply_mem x y v.2
    rw [hR, hR]
    have hC : (∀ v ∉ R, e.symm (a, c) v = e.symm (b, f) v) ↔ c = f := by
      constructor
      · intro h
        funext v
        have := h v v.2
        simpa [e, ManyBody.cutEquiv_symm_apply_not_mem _ _ v.2, v.2] using this
      · rintro rfl v hv
        simp [e, ManyBody.cutEquiv_symm_apply_not_mem _ _ hv]
    by_cases h : c = f
    · rw [ite_eq_left (hC.mpr h), ite_eq_left h, mul_one]
    · rw [ite_eq_right (fun h' ↦ h (hC.mp h')), ite_eq_right h, mul_zero]
  rw [hρ, hpair]
  calc
    _ = Matrix.trace (P * ManyBody.place R K) := by
      rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
      exact EuclideanSpace.inner_eq_star_dotProduct ξ _
    _ = Matrix.trace ((P * ManyBody.place R K).submatrix e.symm e.symm) :=
      (Matrix.trace_submatrix_equiv e.symm _).symm
    _ = Matrix.trace (Y * (K ⊗ₖ 1)) := by
      rw [← Matrix.submatrix_mul_equiv P (ManyBody.place R K) e.symm e.symm e.symm, hLift]

variable {n : V → ℕ}

/-- Relabel each local alphabet in a regional configuration. -/
def dependentRegionFinEquiv (e : ∀ v, Out v ≃ Fin (n v)) (R : Finset V) :
    ((v : R) → Out v.1) ≃ (ManyBody.RegionConfig (fun v ↦ Fin (n v)) R) :=
  Equiv.piCongrRight fun v ↦ e v.1

/-- The unitary basis relabelling of the global configuration space. -/
noncomputable def dependentGlobalFinIsometry (e : ∀ v, Out v ≃ Fin (n v)) :
    EuclideanSpace ℂ ((v : V) → Out v) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (∀ v, Fin (n v)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.piCongrRight e)

omit [∀ v, DecidableEq (Out v)] in
@[simp]
theorem dependentGlobalFinIsometry_apply (e : ∀ v, Out v ≃ Fin (n v))
    (ξ : EuclideanSpace ℂ ((v : V) → Out v)) (σ : (∀ v, Fin (n v))) :
    dependentGlobalFinIsometry e ξ σ = ξ (fun v ↦ (e v).symm (σ v)) := rfl

omit [∀ v, Fintype (Out v)] in
/-- Placed regional operators become the QIC local lifts under the same local basis
relabelling on their input and output indices. -/
theorem reindex_place (e : ∀ v, Out v ≃ Fin (n v))
    (R : Finset V) (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ) :
    Matrix.reindex (Equiv.piCongrRight e) (Equiv.piCongrRight e)
        (ManyBody.place R K) =
      ManyBody.place R
        (Matrix.reindex (dependentRegionFinEquiv e R) (dependentRegionFinEquiv e R) K) := by
  classical
  ext σ τ
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    ManyBody.place_apply, dependentRegionFinEquiv,
    Equiv.piCongrRight_symm_apply, Pi.map_apply]
  by_cases h : ∀ v ∉ R, σ v = τ v
  · rw [ite_eq_left fun v hv ↦ by rw [h v hv], ite_eq_left h]
    rfl
  · rw [ite_eq_right fun h' ↦ h fun v hv ↦ (e v).symm.injective (h' v hv), ite_eq_right h]

/-- The coordinate isometry intertwines the actions of the placed and QIC regional
operators on every vector. -/
theorem dependentGlobalFinIsometry_place (e : ∀ v, Out v ≃ Fin (n v))
    (R : Finset V) (K : Matrix ((v : R) → Out v.1) ((v : R) → Out v.1) ℂ)
    (ξ : EuclideanSpace ℂ ((v : V) → Out v)) :
    dependentGlobalFinIsometry e (WithLp.toLp 2 (ManyBody.place R K *ᵥ ξ)) =
      Matrix.toEuclideanLin (ManyBody.place R
        (Matrix.reindex (dependentRegionFinEquiv e R) (dependentRegionFinEquiv e R) K))
          (dependentGlobalFinIsometry e ξ) := by
  rw [← reindex_place]
  ext σ
  change (ManyBody.place R K *ᵥ ξ) ((Equiv.piCongrRight e).symm σ) =
    ((ManyBody.place R K).submatrix (Equiv.piCongrRight e).symm
      (Equiv.piCongrRight e).symm *ᵥ
        (fun τ ↦ ξ ((Equiv.piCongrRight e).symm τ))) σ
  rw [Matrix.submatrix_mulVec_equiv]
  simp only [Function.comp_def, Equiv.symm_symm, Equiv.symm_apply_apply]

omit [∀ v, DecidableEq (Out v)] in
/-- The canonical finite-product marginal, with its regional basis relabelled, is
exactly the QIC regional state of the relabelled global vector. -/
theorem reindex_reducedPure_eq_regionState (e : ∀ v, Out v ≃ Fin (n v))
    (R : Finset V) (ξ : EuclideanSpace ℂ ((v : V) → Out v)) :
    Matrix.reindex (dependentRegionFinEquiv e R) (dependentRegionFinEquiv e R)
        (ManyBody.regionState ξ R) =
      ManyBody.regionState (dependentGlobalFinIsometry e ξ) R := by
  classical
  let eR := dependentRegionFinEquiv e R
  let eC := Equiv.piCongrRight fun v : {v // v ∉ R} ↦ e v.1
  let P := Matrix.vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ))
  let Y := P.submatrix (ManyBody.cutEquiv Out R).symm
    (ManyBody.cutEquiv Out R).symm
  change (Matrix.partialTraceRight Y).submatrix eR.symm eR.symm = _
  rw [← Matrix.partialTraceRight_submatrix_prod_equiv eR eC]
  rw [ManyBody.regionState_eq_partialTraceRight_cutVector]
  congr 1
  ext p q
  change ξ ((ManyBody.cutEquiv Out R).symm ((eR.prodCongr eC).symm p)) *
      star (ξ ((ManyBody.cutEquiv Out R).symm ((eR.prodCongr eC).symm q))) =
    ξ ((Equiv.piCongrRight e).symm ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) R).symm p)) *
      star (ξ ((Equiv.piCongrRight e).symm ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) R).symm q)))
  have h (z : (ManyBody.RegionConfig (fun v ↦ Fin (n v)) R) × ((v : {v // v ∉ R}) → Fin (n v))) :
      (ManyBody.cutEquiv Out R).symm ((eR.prodCongr eC).symm z) =
        (Equiv.piCongrRight e).symm ((ManyBody.cutEquiv (fun v ↦ Fin (n v)) R).symm z) := by
    funext v
    by_cases hv : v ∈ R <;>
      simp [eR, eC, dependentRegionFinEquiv,
        ManyBody.cutEquiv, Equiv.piEquivPiSubtypeProd, hv]
  rw [h p, h q]

end ManyBody
