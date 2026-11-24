/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import QICLean.Algebra.Kronecker.PiKronecker

/-!
# Range of a Kronecker product of a finite family of matrices

For a finite family of rectangular matrices `F v : Matrix (κ v) (ι v) ℂ` whose row and column
labels may vary with the site `v`, a vector `ψ` on the configurations `∀ v, κ v` lies in the
range of `⊗_v F v` exactly when each of its one-site slices `s ↦ ψ (τ[v ↦ s])` lies in the range
of `F v`. No injectivity, surjectivity or common rank is assumed, and the label types and the
set of sites may be empty. The proof chooses a right inverse of each `F v` on its range
independently.

The second half reindexes the columns of a Kronecker product along bijections at the sites,
and shows that the Kronecker power of one injective matrix reflects invariance of a vector under
a permutation of the sites.

The map `ψ ↦ (⊗_v F v) ψ` is `(Matrix.piKronecker F).mulVecLin`; its composition and identity
rules are `Matrix.mulVec_mulVec` with `Matrix.piKronecker_mul`, and `Matrix.piKronecker_one`.

## Main results

* `Matrix.piKronecker_update_one_mulVec_apply`: one nonidentity factor acts on one slice.
* `Matrix.piKronecker_mulVec_eq_self_of_slice`: local fixing of all slices gives a fixed vector.
* `Matrix.mem_range_mulVecLin_piKronecker_iff`: the range is described by slices.
* `Matrix.piKronecker_mulVec_reindex_columns`: reindexing the columns at every site.
* `Matrix.eq_of_piKronecker_const_mulVec_comp_perm`: reflection of permutation invariance.

## References

* Schuch, Cirac and Pérez-García, arXiv:1001.3807, Section 7, lines 2992–3019 (the
  product-support argument).
* Molnar, Garre-Rubio, Pérez-García, Schuch and Cirac, arXiv:1804.04964, Applications,
  lines 1891–1894.
-/

open scoped BigOperators Matrix

namespace Matrix

variable {ν : Type*} [Fintype ν] [DecidableEq ν] {ι κ : ν → Type*}

/-- The entries of a Kronecker product applied to a vector. -/
theorem piKronecker_mulVec_apply [∀ v, Fintype (ι v)] (F : (v : ν) → Matrix (κ v) (ι v) ℂ)
    (ψ : ((v : ν) → ι v) → ℂ) (τ : (v : ν) → κ v) :
    (piKronecker F *ᵥ ψ) τ = ∑ σ : (v : ν) → ι v, (∏ v, F v (τ v) (σ v)) * ψ σ :=
  rfl

/-- A Kronecker product with one factor `P` at the site `v` and the identity elsewhere acts on
the slices at `v`. -/
theorem piKronecker_update_one_mulVec_apply [∀ v, Fintype (κ v)] [∀ v, DecidableEq (κ v)]
    (v : ν) (P : Matrix (κ v) (κ v) ℂ) (ψ : ((v : ν) → κ v) → ℂ) (τ : (v : ν) → κ v) :
    (piKronecker (Function.update (fun w ↦ (1 : Matrix (κ w) (κ w) ℂ)) v P) *ᵥ ψ) τ =
      ∑ s : κ v, P (τ v) s * ψ (Function.update τ v s) := by
  let e := Equiv.piSplitAt v κ
  have hcoeff (s : κ v) (β : (w : {w : ν // w ≠ v}) → κ w.1) :
      (∏ w, (Function.update (fun w ↦ (1 : Matrix (κ w) (κ w) ℂ)) v P w)
        (τ w) (e.symm (s, β) w)) =
        P (τ v) s * if (fun w : {w : ν // w ≠ v} ↦ τ w.1) = β then 1 else 0 := by
    rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ v)]
    have hfirst : (Function.update (fun w ↦ (1 : Matrix (κ w) (κ w) ℂ)) v P v)
        (τ v) (e.symm (s, β) v) = P (τ v) s := by
      simp [e, Equiv.piSplitAt]
    rw [hfirst]
    congr 1
    rw [Finset.prod_subtype (Finset.univ \ {v}) (p := fun w ↦ w ≠ v) (F := inferInstance)
      (fun w ↦ by simp)]
    have hout (w : {w : ν // w ≠ v}) :
        (Function.update (fun w ↦ (1 : Matrix (κ w) (κ w) ℂ)) v P w.1)
          (τ w.1) (e.symm (s, β) w.1) = if τ w.1 = β w then 1 else 0 := by
      simp [e, Equiv.piSplitAt, w.2, Matrix.one_apply]
    simp only [hout, Fintype.prod_boole, ← funext_iff]
  rw [piKronecker_mulVec_apply, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  simp only [hcoeff]
  rw [Finset.sum_eq_single (fun w : {w : ν // w ≠ v} ↦ τ w.1)]
  · have hcfg : e.symm (s, fun w : {w : ν // w ≠ v} ↦ τ w.1) = Function.update τ v s := by
      funext w
      by_cases h : w = v
      · subst w
        simp [e, Equiv.piSplitAt]
      · simp [e, Equiv.piSplitAt, h]
    simp only [hcfg, ite_true, mul_one]
  · intro β _ hβ
    rw [ite_eq_right (Ne.symm hβ), mul_zero, zero_mul]
  · simp

/-- If each matrix `P v` fixes every slice of `ψ` at the site `v`, then `⊗_v P v` fixes `ψ`.
The matrices need not be projections. -/
theorem piKronecker_mulVec_eq_self_of_slice [∀ v, Fintype (κ v)]
    (P : (v : ν) → Matrix (κ v) (κ v) ℂ) (ψ : ((v : ν) → κ v) → ℂ)
    (hψ : ∀ v τ, P v *ᵥ (fun s ↦ ψ (Function.update τ v s)) =
      fun s ↦ ψ (Function.update τ v s)) :
    piKronecker P *ᵥ ψ = ψ := by
  classical
  let F (S : Finset ν) (v : ν) : Matrix (κ v) (κ v) ℂ := if v ∈ S then P v else 1
  have hone (v : ν) :
      piKronecker (Function.update (fun w ↦ (1 : Matrix (κ w) (κ w) ℂ)) v (P v)) *ᵥ ψ = ψ := by
    funext τ
    rw [piKronecker_update_one_mulVec_apply]
    simpa only [Matrix.mulVec, dotProduct, Function.update_eq_self] using
      congr_fun (hψ v τ) (τ v)
  have hS (S : Finset ν) : piKronecker (F S) *ᵥ ψ = ψ := by
    induction S using Finset.induction with
    | empty =>
      simp only [F, Finset.notMem_empty, ite_false, piKronecker_one, one_mulVec]
    | @insert v S hv ih =>
      have hprod : (fun w ↦
          Function.update (fun w ↦ (1 : Matrix (κ w) (κ w) ℂ)) v (P v) w * F S w) =
          F (insert v S) := by
        funext w
        by_cases hw : w = v
        · subst w
          simp [F, hv]
        · simp [F, hw]
      rw [← hprod, ← piKronecker_mul, ← mulVec_mulVec, ih, hone]
  simpa only [F, Finset.mem_univ, ite_true] using hS Finset.univ

/-- Every one-site slice of `(⊗_v F v) ψ` lies in the range of the matrix at that site, for
arbitrary values at the other sites. -/
theorem piKronecker_mulVec_slice_mem_range [∀ v, Fintype (ι v)]
    (F : (v : ν) → Matrix (κ v) (ι v) ℂ) (ψ : ((v : ν) → ι v) → ℂ) (v : ν)
    (τ : (v : ν) → κ v) :
    (fun s ↦ (piKronecker F *ᵥ ψ) (Function.update τ v s)) ∈
      LinearMap.range (F v).mulVecLin := by
  classical
  have hsum : (fun s ↦ (piKronecker F *ᵥ ψ) (Function.update τ v s)) =
      ∑ σ : (v : ν) → ι v, ((∏ w ∈ Finset.univ.erase v, F w (τ w) (σ w)) * ψ σ) •
        (fun s ↦ F v s (σ v)) := by
    funext s
    simp only [piKronecker_mulVec_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v), Function.update_self]
    have hout : (∏ w ∈ Finset.univ.erase v, F w (Function.update τ v s w) (σ w)) =
        ∏ w ∈ Finset.univ.erase v, F w (τ w) (σ w) :=
      Finset.prod_congr rfl fun w hw ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
    rw [hout]
    ring
  rw [hsum]
  refine Submodule.sum_mem _ fun σ _ ↦ Submodule.smul_mem _ _ ⟨Pi.single (σ v) 1, ?_⟩
  ext s
  simp [Matrix.mulVec_single]

/-- A vector lies in the range of `⊗_v F v` exactly when each of its one-site slices lies in
the range of the matrix at that site. The label types may differ from site to site and may be
empty, and the matrices may have any ranks, including zero.

Schuch, Cirac and Pérez-García, arXiv:1001.3807, Section 7, lines 2992–3019. -/
theorem mem_range_mulVecLin_piKronecker_iff [∀ v, Fintype (ι v)] [∀ v, Finite (κ v)]
    (F : (v : ν) → Matrix (κ v) (ι v) ℂ) (ψ : ((v : ν) → κ v) → ℂ) :
    ψ ∈ LinearMap.range (piKronecker F).mulVecLin ↔
      ∀ v τ, (fun s ↦ ψ (Function.update τ v s)) ∈ LinearMap.range (F v).mulVecLin := by
  classical
  let := fun v ↦ Fintype.ofFinite (κ v)
  constructor
  · rintro ⟨χ, rfl⟩ v τ
    exact piKronecker_mulVec_slice_mem_range F χ v τ
  · intro hψ
    have hlocal (v : ν) : ∃ L : Matrix (ι v) (κ v) ℂ,
        ∀ q ∈ LinearMap.range (F v).mulVecLin, (F v * L) *ᵥ q = q := by
      let f := (F v).mulVecLin
      obtain ⟨r, hr⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
      obtain ⟨l, hl⟩ := r.exists_extend
      refine ⟨LinearMap.toMatrix' l, fun q hq ↦ ?_⟩
      rw [← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
      change f (l q) = q
      have hlq := LinearMap.congr_fun hl ⟨q, hq⟩
      have hrq := congr_arg Subtype.val (LinearMap.congr_fun hr ⟨q, hq⟩)
      exact hlq ▸ hrq
    choose L hL using hlocal
    refine ⟨piKronecker L *ᵥ ψ, ?_⟩
    rw [Matrix.mulVecLin_apply, mulVec_mulVec, piKronecker_mul]
    exact piKronecker_mulVec_eq_self_of_slice (fun v ↦ F v * L v) ψ
      fun v τ ↦ hL v _ (hψ v τ)

/-- Reindexing the columns of every factor along bijections `e v`, together with the vector,
leaves the image unchanged.

Supporting calculation for arXiv:1804.04964, lines 1891–1894. -/
theorem piKronecker_mulVec_reindex_columns {ι' : ν → Type*} [∀ v, Fintype (ι v)]
    [∀ v, Fintype (ι' v)] (e : (v : ν) → ι' v ≃ ι v) (F : (v : ν) → Matrix (κ v) (ι v) ℂ)
    (R : ((v : ν) → ι v) → ℂ) :
    piKronecker (fun v o i ↦ F v o (e v i)) *ᵥ (fun x ↦ R fun v ↦ e v (x v)) =
      piKronecker F *ᵥ R := by
  funext x
  simp only [piKronecker_mulVec_apply]
  exact (Equiv.piCongrRight e).sum_comp
    (fun σ : (v : ν) → ι v ↦ (∏ v, F v (x v) (σ v)) * R σ)

/-- The Kronecker power of one matrix commutes with a permutation of the sites: if `ψ` is
invariant under `τ`, so is its image. -/
private theorem piKronecker_const_mulVec_comp_perm {α β : Type*} [Fintype α]
    (M : Matrix β α ℂ) (τ : Equiv.Perm ν) (ψ : (ν → α) → ℂ)
    (hψ : ∀ σ, ψ (fun v ↦ σ (τ v)) = ψ σ) (x : ν → β) :
    (piKronecker (fun _ : ν ↦ M) *ᵥ ψ) (fun v ↦ x (τ v)) =
      (piKronecker (fun _ : ν ↦ M) *ᵥ ψ) x := by
  let e : (ν → α) ≃ (ν → α) :=
    { toFun := fun σ v ↦ σ (τ v)
      invFun := fun σ v ↦ σ (τ.symm v)
      left_inv := fun σ ↦ by funext v; simp
      right_inv := fun σ ↦ by funext v; simp }
  simp only [piKronecker_mulVec_apply]
  calc
    _ = ∑ σ : ν → α, (∏ v : ν, M (x (τ v)) (σ (τ v))) * ψ (fun v ↦ σ (τ v)) :=
        (e.sum_comp fun σ : ν → α ↦ (∏ v : ν, M (x (τ v)) (σ v)) * ψ σ).symm
    _ = _ := by
      refine Finset.sum_congr rfl fun σ _ ↦ ?_
      rw [hψ]
      congr 1
      exact Fintype.prod_equiv τ (fun v : ν ↦ M (x (τ v)) (σ (τ v)))
        (fun v : ν ↦ M (x v) (σ v)) fun _ ↦ rfl

/-- The Kronecker power of one injective matrix reflects invariance under a permutation of the
sites: if the image of `R` is invariant under `τ`, so is `R`. The left inverse of `F` is
obtained from injectivity.

Common-left-inverse step supporting arXiv:1804.04964, lines 1891–1894. -/
theorem eq_of_piKronecker_const_mulVec_comp_perm {α β : Type*} [Fintype α] [Finite β]
    (F : Matrix β α ℂ) (hF : Function.Injective F.mulVecLin) (τ : Equiv.Perm ν)
    (R : (ν → α) → ℂ)
    (hψ : ∀ σ, (piKronecker (fun _ : ν ↦ F) *ᵥ R) (fun v ↦ σ (τ v)) =
      (piKronecker (fun _ : ν ↦ F) *ᵥ R) σ)
    (x : ν → α) :
    R (fun v ↦ x (τ v)) = R x := by
  classical
  let := Fintype.ofFinite β
  obtain ⟨l, hl⟩ := F.mulVecLin.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hF)
  let L : Matrix α β ℂ := LinearMap.toMatrix' l
  have hLF : L * F = 1 := by
    calc
      L * F = LinearMap.toMatrix' l * LinearMap.toMatrix' (Matrix.toLin' F) := by
        rw [LinearMap.toMatrix'_toLin']
      _ = LinearMap.toMatrix' (l ∘ₗ Matrix.toLin' F) :=
        (LinearMap.toMatrix'_comp l (Matrix.toLin' F)).symm
      _ = 1 := by rw [Matrix.toLin'_apply', hl, LinearMap.toMatrix'_id]
  have hrec : piKronecker (fun _ : ν ↦ L) *ᵥ (piKronecker (fun _ : ν ↦ F) *ᵥ R) = R := by
    rw [mulVec_mulVec, piKronecker_mul]
    simp only [hLF, piKronecker_one, one_mulVec]
  have h := piKronecker_const_mulVec_comp_perm L τ (piKronecker (fun _ : ν ↦ F) *ᵥ R) hψ x
  simpa only [hrec] using h

end Matrix
