/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GramSchmidtMeasurable
import Mathlib.Data.Finset.Sort

/-!
# Borel orthonormal frames from finite generating families

Apply normalized Gram–Schmidt to every input vector, remove the zero
vectors and retain the original order. On each fixed-rank family this
constructs an actual Borel orthonormal frame with the same span. No
arbitrary orthonormal-basis choice is used. This is a prerequisite for the
varying input spaces in ALVV, arXiv:1602.08828v2, `l:rs`, lines 530–558,
rather than a joint adaptive sampling theorem.
-/

open MeasureTheory

namespace InnerProductSpace

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E]
  {n r : ℕ}

private noncomputable def nonzeroGSIndices (f : Fin n → E) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i ↦ gramSchmidtNormed 𝕜 f i ≠ 0

private noncomputable def frameOfCount
    (f : {f : Fin n → E // (nonzeroGSIndices 𝕜 f).card = r}) : Fin r → E :=
  fun i ↦ gramSchmidtNormed 𝕜 f.val ((nonzeroGSIndices 𝕜 f.val).orderEmbOfFin f.property i)

private theorem orthonormal_frameOfCount
    (f : {f : Fin n → E // (nonzeroGSIndices 𝕜 f).card = r}) :
    Orthonormal 𝕜 (frameOfCount 𝕜 f) := by
  classical
  let S := nonzeroGSIndices 𝕜 f.val
  let e : Fin r → {i : Fin n // gramSchmidtNormed 𝕜 f.val i ≠ 0} := fun i ↦
    ⟨S.orderEmbOfFin f.property i, by
      have hm := S.orderEmbOfFin_mem f.property i
      simpa only [S, nonzeroGSIndices, Finset.mem_filter, Finset.mem_univ, true_and] using hm⟩
  have hinj : Function.Injective e := by
    intro i j hij
    have heq : (e i).val = (e j).val := congrArg
      (fun x : {i : Fin n // gramSchmidtNormed 𝕜 f.val i ≠ 0} ↦ x.val) hij
    exact (S.orderEmbOfFin f.property).injective heq
  exact (gramSchmidtNormed_orthonormal' (𝕜 := 𝕜) f.val).comp e hinj

private theorem span_frameOfCount
    (f : {f : Fin n → E // (nonzeroGSIndices 𝕜 f).card = r}) :
    Submodule.span 𝕜 (Set.range (frameOfCount 𝕜 f)) =
      Submodule.span 𝕜 (Set.range f.val) := by
  classical
  rw [← span_gramSchmidt 𝕜 f.val, ← span_gramSchmidtNormed_range (𝕜 := 𝕜) f.val]
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : gramSchmidtNormed 𝕜 f.val i = 0
    · rw [hi]
      exact Submodule.zero_mem _
    · have hmem : i ∈ nonzeroGSIndices 𝕜 f.val := by simp [nonzeroGSIndices, hi]
      have hrange : i ∈ Set.range ((nonzeroGSIndices 𝕜 f.val).orderEmbOfFin f.property) := by
        rw [Finset.range_orderEmbOfFin]
        exact hmem
      obtain ⟨j, hj⟩ := hrange
      apply Submodule.subset_span
      exact ⟨j, congrArg (gramSchmidtNormed 𝕜 f.val) hj⟩

private theorem card_nonzeroGSIndices (f : Fin n → E) :
    (nonzeroGSIndices 𝕜 f).card = Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range f)) := by
  let g : {g : Fin n → E // (nonzeroGSIndices 𝕜 g).card = (nonzeroGSIndices 𝕜 f).card} := ⟨f, rfl⟩
  have hdim := finrank_span_eq_card (orthonormal_frameOfCount 𝕜 g).linearIndependent
  rw [span_frameOfCount, Fintype.card_fin] at hdim
  exact hdim.symm

/-- The actual ordered frame obtained by keeping the nonzero normalized
Gram–Schmidt vectors of a rank-r finite generating family. -/
noncomputable def finiteOrthonormalFrame
    (f : {f : Fin n → E // Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range f)) = r}) :
    Fin r → E :=
  frameOfCount 𝕜 ⟨f.val, (card_nonzeroGSIndices 𝕜 f.val).trans f.property⟩

/-- The selected frame is orthonormal, including rank zero. -/
theorem orthonormal_finiteOrthonormalFrame
    (f : {f : Fin n → E // Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range f)) = r}) :
    Orthonormal 𝕜 (finiteOrthonormalFrame 𝕜 f) :=
  orthonormal_frameOfCount 𝕜 _

/-- The selected orthonormal frame spans the original finite family. -/
theorem span_finiteOrthonormalFrame
    (f : {f : Fin n → E // Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range f)) = r}) :
    Submodule.span 𝕜 (Set.range (finiteOrthonormalFrame 𝕜 f)) =
      Submodule.span 𝕜 (Set.range f.val) :=
  span_frameOfCount 𝕜 _

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

private theorem measurable_frameOfCount :
    Measurable (frameOfCount 𝕜 (n := n) (r := r) (E := E)) := by
  classical
  let X := {f : Fin n → E // (nonzeroGSIndices 𝕜 f).card = r}
  let t := fun S : Finset (Fin n) ↦ {f : X | nonzeroGSIndices 𝕜 f.val = S}
  let g := fun (S : Finset (Fin n)) (f : X) ↦ if hS : S.card = r then
    (fun i : Fin r ↦ gramSchmidtNormed 𝕜 f.val (S.orderEmbOfFin hS i)) else 0
  have hcoord (i : Fin n) : Measurable (fun f : X ↦ gramSchmidtNormed 𝕜 f.val i) :=
    (measurable_pi_apply i).comp ((measurable_gramSchmidtNormed 𝕜).comp measurable_subtype_coe)
  have ht (S : Finset (Fin n)) : MeasurableSet (t S) := by
    have heq : t S = ⋂ i : Fin n,
        {f : X | (gramSchmidtNormed 𝕜 f.val i ≠ 0) ↔ i ∈ S} := by
      ext f
      simp only [t, Set.mem_ofPred_eq, Finset.ext_iff, nonzeroGSIndices,
        Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iInter]
    rw [heq]
    apply MeasurableSet.iInter
    intro i
    have hz : MeasurableSet {f : X | gramSchmidtNormed 𝕜 f.val i = 0} :=
      measurableSet_eq_fun (hcoord i) measurable_const
    by_cases hi : i ∈ S
    · convert hz.compl using 1
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, hi, iff_true]
    · convert hz using 1
      ext f
      simp only [Set.mem_ofPred_eq, hi, iff_false, not_not]
  have hg (S : Finset (Fin n)) : Measurable (g S) := by
    dsimp only [g]
    split_ifs with hS
    · exact measurable_pi_iff.mpr fun i ↦ hcoord (S.orderEmbOfFin hS i)
    · exact measurable_const
  have hdisjoint : Pairwise fun S T ↦ Set.EqOn (g S) (g T) (t S ∩ t T) := by
    intro S T hST f hf
    exact (hST (hf.1.symm.trans hf.2)).elim
  obtain ⟨phi, hphi, hbranch⟩ := exists_measurable_piecewise t ht g hg hdisjoint
  have heq : frameOfCount 𝕜 (n := n) (r := r) (E := E) = phi := by
    funext f
    unfold frameOfCount
    have hb := hbranch (nonzeroGSIndices 𝕜 f.val) (show f ∈ t (nonzeroGSIndices 𝕜 f.val) from rfl)
    simpa only [frameOfCount, g, dite_eq_left f.property] using hb.symm
  rw [heq]
  exact hphi

/-- The ordered orthonormal frame is Borel on each fixed-rank family.
There is no continuity assertion across a change of nonzero indices. -/
theorem measurable_finiteOrthonormalFrame :
    Measurable (finiteOrthonormalFrame 𝕜 (n := n) (r := r) (E := E)) := by
  have hmap : Measurable (fun f : {f : Fin n → E //
      Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range f)) = r} ↦
      (⟨f.val, (card_nonzeroGSIndices 𝕜 f.val).trans f.property⟩ :
        {f : Fin n → E // (nonzeroGSIndices 𝕜 f).card = r})) :=
    measurable_subtype_coe.subtype_mk
  exact (measurable_frameOfCount 𝕜).comp hmap

end InnerProductSpace
