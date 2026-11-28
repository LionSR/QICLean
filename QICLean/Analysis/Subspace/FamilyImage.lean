/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Subspace.ViableSubspaceTensor
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Star
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Images of finite tensor families

A finite tensor decomposition sends a retained subspace tensored with its
whole environment into the span of the retained-factor images tensored
with that same environment. This is the containment argument in ALVV,
arXiv:1602.08828v2, Lemma `l:er`, lines 606–622. No contraction or
identity on a spectral band is used in this algebraic step.

The dimension of a finite supremum of subspaces is at most the sum of their dimensions
(`Submodule.finrank_iSup_le_sum`), so the span of finitely many images of a subspace has
dimension at most the number of maps times its dimension
(`Submodule.finrank_iSup_map_le_card_mul`).

Moved from TNLean, `TNLean/MPS/CanonicalForm/BNT/Basic.lean` at commit `021ba0bd19` (Apache-2.0).
-/

open scoped TensorProduct InnerProductSpace BigOperators
open TensorProduct Module

namespace Submodule

section General

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

omit [FiniteDimensional 𝕜 E] in
/-- The dimension of a finite supremum of subspaces is at most the sum of the dimensions. -/
theorem finrank_iSup_le_sum {ι : Type*} [Fintype ι] (f : ι → Submodule 𝕜 E)
    [∀ i, FiniteDimensional 𝕜 (f i)] :
    finrank 𝕜 ↥(⨆ i, f i) ≤ ∑ i, finrank 𝕜 (f i) := by
  classical
  rw [← Finset.sup_univ_eq_iSup]
  generalize (Finset.univ : Finset ι) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    have : FiniteDimensional 𝕜 ↥(s.sup f) := by
      rw [Finset.sup_eq_iSup]
      infer_instance
    exact (finrank_add_le_finrank_add_finrank _ _).trans (by gcongr)

end General

section ImageDimension

variable {𝕜 E F ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The span of finitely many linear images of one finite-dimensional
subspace has dimension at most the number of maps times its dimension.
This is the common dimension estimate in ALVV, arXiv:1602.08828v2,
Lemma `l:er`, lines 597–622, and the bootstrap argument, lines 1067–1075. -/
theorem finrank_iSup_map_le_card_mul
    (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] (A : ι → E →ₗ[𝕜] F) :
    Module.finrank 𝕜
        (↥((⨆ i, S.map (A i)) : Submodule 𝕜 F)) ≤
      Fintype.card ι * Module.finrank 𝕜 S := by
  classical
  calc
    Module.finrank 𝕜
        (↥((⨆ i, S.map (A i)) : Submodule 𝕜 F)) ≤
        ∑ i, Module.finrank 𝕜 (S.map (A i)) := finrank_iSup_le_sum _
    _ ≤ ∑ _i : ι, Module.finrank 𝕜 S :=
      Finset.sum_le_sum fun i _ ↦ finrank_map_le _ _
    _ = Fintype.card ι * Module.finrank 𝕜 S := by simp

end ImageDimension

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
theorem tmul_mem_tensorProd {S : Submodule 𝕜 E} {S' : Submodule 𝕜 F} {x : E} {y : F}
    (hx : x ∈ S) (hy : y ∈ S') : x ⊗ₜ[𝕜] y ∈ S.tensorProd S' :=
  ⟨⟨x, hx⟩ ⊗ₜ ⟨y, hy⟩, TensorProduct.map_tmul _ _ _ _⟩

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- `S ⊗ S'` lies in `N` exactly when every `x ⊗ y` with `x ∈ S` and `y ∈ S'` does. -/
theorem tensorProd_le_iff {S : Submodule 𝕜 E} {S' : Submodule 𝕜 F}
    {N : Submodule 𝕜 (E ⊗[𝕜] F)} :
    S.tensorProd S' ≤ N ↔ ∀ x ∈ S, ∀ y ∈ S', x ⊗ₜ[𝕜] y ∈ N := by
  refine ⟨fun h x hx y hy => h (tmul_mem_tensorProd hx hy), fun h => ?_⟩
  rintro _ ⟨z, rfl⟩
  induction z with
  | tmul x y =>
    rw [TensorProduct.map_tmul]
    exact h x x.2 y y.2
  | add z z' hz hz' =>
    rw [map_add]
    exact N.add_mem hz hz'

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] in
/-- The actual tensor-decomposed image is contained in the retained-factor
family span, with the whole environment left unrestricted. This is the
containment step of ALVV, arXiv:1602.08828v2, Lemma `l:er`, lines 606–622. -/
theorem map_tensorProd_top_le_iSup_map {ι : Type*} [Fintype ι]
    (S : Submodule 𝕜 E) (A : ι → E →L[𝕜] E) (B : ι → F →L[𝕜] F)
    {K : E ⊗[𝕜] F →L[𝕜] E ⊗[𝕜] F}
    (hdec : K = ∑ i, mapL (A i) (B i)) :
    (S.tensorProd (⊤ : Submodule 𝕜 F)).map K.toLinearMap ≤
      (⨆ i, S.map (A i : E →ₗ[𝕜] E)).tensorProd (⊤ : Submodule 𝕜 F) := by
  rw [map_le_iff_le_comap, tensorProd_le_iff]
  intro x hx y _
  change K (x ⊗ₜ[𝕜] y) ∈
    (⨆ i, S.map (A i : E →ₗ[𝕜] E)).tensorProd (⊤ : Submodule 𝕜 F)
  rw [hdec, _root_.sum_apply]
  refine sum_mem fun i _ ↦ ?_
  rw [mapL_tmul]
  exact tmul_mem_tensorProd (mem_iSup_of_mem i (mem_map_of_mem hx)) mem_top

end Submodule

section

open scoped BigOperators InnerProductSpace Matrix

open Filter Finset

section LinearAlgebra

variable {g : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Auxiliary: express `w j` in the span of `v` and extract its coefficients.
Given LI `v` and `w j ∈ Submodule.span ℂ (Set.range v)`, define the coefficients. -/
private noncomputable def changeBasisCoeffs
    (v w : Fin g → V)
    (hw_mem : ∀ j, w j ∈ Submodule.span ℂ (Set.range v)) :
    Fin g → Fin g → ℂ :=
  fun j => Classical.choose ((Submodule.mem_span_range_iff_exists_fun ℂ).mp (hw_mem j))

private lemma changeBasisCoeffs_spec
    (v w : Fin g → V)
    (hw_mem : ∀ j, w j ∈ Submodule.span ℂ (Set.range v)) :
    ∀ j, ∑ i : Fin g, changeBasisCoeffs v w hw_mem j i • v i = w j :=
  fun j => Classical.choose_spec ((Submodule.mem_span_range_iff_exists_fun ℂ).mp (hw_mem j))

/--
**Invertible change-of-basis lemma.**

If two finite families of vectors `v, w : Fin g → V` in a complex vector space are both
linearly independent and span the same subspace, then there exists an invertible
`g × g` matrix `U` such that `w j = ∑ i, U i j • v i` for all `j`.

This is the key algebraic step in the BNT permutation-matching argument: it converts the
subspace-level agreement of two BNT families into a *matrix* equation whose asymptotics
(as the system size grows) can then be analysed.
-/
lemma exists_invertible_changeBasis
    (v w : Fin g → V)
    (_hv : LinearIndependent ℂ v)
    (hw : LinearIndependent ℂ w)
    (hspan : Submodule.span ℂ (Set.range v) = Submodule.span ℂ (Set.range w)) :
    ∃ U : Matrix (Fin g) (Fin g) ℂ,
      U.det ≠ 0 ∧
      ∀ j : Fin g, w j = ∑ i : Fin g, U i j • v i := by
  classical
  -- Each `w j` lies in the span of `v`.
  have hw_mem : ∀ j, w j ∈ Submodule.span ℂ (Set.range v) := by
    intro j
    rw [hspan]
    exact Submodule.subset_span ⟨j, rfl⟩
  -- Extract coefficients: for each `j`, ∃ `c j : Fin g → ℂ` with `∑ i, c j i • v i = w j`.
  let c := changeBasisCoeffs v w hw_mem
  have hc := changeBasisCoeffs_spec v w hw_mem
  -- Define the matrix `U i j := c j i` (transpose of the natural coefficient ordering).
  let U : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => c j i
  -- The expansion holds by construction.
  have hU : ∀ j, w j = ∑ i : Fin g, U i j • v i := by
    intro j
    exact (hc j).symm
  -- It remains to show `U.det ≠ 0` from the triviality of the kernel of `U.mulVec`.
  have hmulVec_zero : ∀ a : Fin g → ℂ, U.mulVec a = 0 → a = 0 := by
    intro a ha
    -- It suffices to show ∑ j, a j • w j = 0 (then LI of w gives a = 0).
    suffices h : ∑ j : Fin g, a j • w j = 0 by
      exact funext (Fintype.linearIndependent_iff.mp hw a h)
    -- Compute: ∑ j, a j • w j = ∑ i, (U.mulVec a) i • v i = 0.
    calc ∑ j : Fin g, a j • w j
        = ∑ j, a j • (∑ i, U i j • v i) := by simp_rw [hU]
      _ = ∑ j, ∑ i, (a j * U i j) • v i := by simp_rw [Finset.smul_sum, smul_smul]
      _ = ∑ i, ∑ j, (a j * U i j) • v i := Finset.sum_comm
      _ = ∑ i, (∑ j, a j * U i j) • v i := by simp_rw [← Finset.sum_smul]
      _ = ∑ i, (U.mulVec a) i • v i := by
            congr 1; ext i; congr 1
            rw [Matrix.mulVec_apply_eq_sum]
            exact Finset.sum_congr rfl fun j _ => mul_comm (a j) (U i j)
      _ = 0 := by simp [ha]
  have hdet : U.det ≠ 0 := by
    intro hdet
    obtain ⟨a, ha, hUa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact ha (hmulVec_zero a hUa)
  exact ⟨U, hdet, hU⟩

end LinearAlgebra

end
