/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.RegionEntropy
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Hamiltonian.KroneckerSum

/-!
# Zero entropy across a cut that splits no term

Let an interaction of Hermitian terms, each supported inside a region `B` or outside it, have a
gapped Hamiltonian, with positive gap and ground space the line through a unit vector `Ω`. In
the coordinates of the cut along `B` the Hamiltonian is `H_B ⊗ 1 + 1 ⊗ H_{Bᶜ}`, so `Ω` is a
product vector across the cut and `S_Ω(B) = 0`. No geometry of the sites enters.

Moved from TNLean, `TNLean/Lattice/ZeroEntropy.lean` at commit `e41c3b63`, restated for an
interaction on an arbitrary family of local alphabets.

## Main results

* `ManyBody.Interaction.entropy_eq_zero_of_forall_subset_or_disjoint` — zero entropy across a
  cut that splits no term.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Section 2, `01-preliminaries.tex`, lines 116–134 (Lemma 2.2).
* TNLean note, *A one-dimensional area law and matrix product state approximation from a
  global gap*, `part1_arealaw.tex`, Section 2 (`sec:setting`), first reduction.
-/

open Matrix
open scoped Kronecker

namespace ManyBody.Interaction

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {ι : Type*} [Fintype ι] {S : ι → Finset V}

/-- **Zero entropy across a cut that splits no term.** Let the terms of an interaction be
Hermitian and each supported inside the region `B` or outside it, and let its Hamiltonian be
gapped at `E₀` with positive gap and ground space the line through the unit vector `Ω`. Then
`S_Ω(B) = 0`. Two-dimensional area law, `01-preliminaries.tex`, lines 116–134 (Lemma 2.2). -/
theorem entropy_eq_zero_of_forall_subset_or_disjoint {Φ : Interaction X S}
    (hherm : ∀ i, (Φ.term i).IsHermitian) {E₀ Δ : ℝ} (hΔ : 0 < Δ)
    {Ω : EuclideanSpace ℂ (Config X)} (hΩ : ‖Ω‖ = 1) (hgs : IsGapped Φ.hamiltonian E₀ Δ)
    (hspan : groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Ω}) {B : Finset V}
    (hsplit : ∀ i, S i ⊆ B ∨ Disjoint (S i) B) :
    ManyBody.regionEntropy Ω B = 0 := by
  classical
  set c := cutEquiv X B
  obtain ⟨x₀⟩ : Nonempty (Config X) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : Ω = 0 := by
      apply WithLp.ofLp_injective 2
      funext x
      exact isEmptyElim x
    simp [this] at hΩ
  set s := Finset.univ.filter fun i ↦ S i ⊆ B
  set Hin := ∑ i ∈ s, Φ.term i
  set Hout := ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ S i ⊆ B), Φ.term i
  have hH : Φ.hamiltonian = Hin + Hout := (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hin : Hin ∈ supportedOperators X B :=
    sum_mem fun i hi ↦ supportedOperators_mono (Finset.mem_filter.mp hi).2 (Φ.mem i)
  have hout : Hout ∈ supportedOperators X Bᶜ := by
    refine sum_mem fun i hi ↦ supportedOperators_mono ?_ (Φ.mem i)
    exact Finset.subset_compl_iff_disjoint_right.mpr
      ((hsplit i).resolve_left (Finset.mem_filter.mp hi).2)
  have hsumH (t : Finset ι) : (∑ i ∈ t, Φ.term i).IsHermitian :=
    (isSelfAdjoint_sum _ fun i _ ↦ (hherm i).isSelfAdjoint).isHermitian
  obtain ⟨K, hK⟩ := exists_eq_place_of_mem_supportedOperators hin
  obtain ⟨L, hL⟩ := exists_eq_one_kronecker_of_mem_supportedOperators (D := B)
    disjoint_compl_left hout
  have hA : Hin = (K ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ)).submatrix c c := by
    simp [hK, place, reindex_apply, c]
  have hKherm : K.IsHermitian := by
    have hK' : (K ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ)).IsHermitian := by
      have := (hsumH s).submatrix c.symm
      rwa [show ∑ i ∈ s, Φ.term i = Hin from rfl, hA, submatrix_submatrix,
        Equiv.self_comp_symm, submatrix_id_id] at this
    refine IsHermitian.ext fun i j ↦ ?_
    simpa only [kroneckerMap_apply, one_apply_eq, mul_one] using
      hK'.apply (i, (c x₀).2) (j, (c x₀).2)
  have hLherm : L.IsHermitian := by
    have hL' : ((1 : Matrix (RegionConfig X B) (RegionConfig X B) ℂ) ⊗ₖ L).IsHermitian := by
      have := (hsumH (Finset.univ.filter fun i ↦ ¬ S i ⊆ B)).submatrix c.symm
      rwa [show ∑ i ∈ Finset.univ.filter (fun i ↦ ¬ S i ⊆ B), Φ.term i = Hout from rfl, hL,
        submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at this
    refine IsHermitian.ext fun i j ↦ ?_
    simpa only [kroneckerMap_apply, one_apply_eq, one_mul] using
      hL'.apply ((c x₀).1, i) ((c x₀).1, j)
  have hcut : Φ.hamiltonian.submatrix c.symm c.symm =
      K ⊗ₖ (1 : Matrix (ComplConfig X B) (ComplConfig X B) ℂ) +
        (1 : Matrix (RegionConfig X B) (RegionConfig X B) ℂ) ⊗ₖ L := by
    rw [hH, hA, hL]
    ext i j
    simp [c]
  have hgs' := (isGapped_submatrix_iff c.symm).mpr hgs
  have hspan' := groundSpace_submatrix_eq_span c.symm hspan
  rw [hcut] at hgs' hspan'
  have hn' : ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ c.symm.symm Ω‖ = 1 :=
    (LinearIsometryEquiv.norm_map _ _).trans hΩ
  obtain ⟨-, -, u, w, -, hprod, -, -⟩ :=
    exists_isGapped_factors_of_kronecker_sum hKherm hLherm hΔ hn' hgs' hspan'
  have hΩc : ∀ p, Ω (c.symm p) = u p.1 * w p.2 := fun p ↦ by
    simpa [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'] using hprod p
  have hρ : regionState Ω B =
      vecMulVec (WithLp.ofLp u) fun b ↦ star (u b) * ∑ y, w y * star (w y) := by
    ext a b
    simp only [regionState_eq_partialTraceRight_cutVector, partialTraceRight_apply,
      vecMulVec_apply, Pi.star_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [hΩc, hΩc, star_mul']
    ring
  rw []
  refine vonNeumannEntropy_eq_zero_of_rank_le_one (regionState_posSemidef B Ω)
    (by rw [trace_regionState, hΩ]; simp) ?_
  rw [hρ]
  exact rank_vecMulVec_le _ _

end ManyBody.Interaction
