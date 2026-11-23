/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.Spectral.Perturbation.OverlapEnergy

/-!
# Range-one Hamiltonians on the chain

A support of range one of the chain of `L` sites is a site or a pair of adjacent sites, and the
chain has at most `2L` of them. This file collects the facts about a range-one interaction on the
chain with term norms at most `J` that the estimates of Landau, Vazirani and Vidick use.

* The Hamiltonian has norm at most `2LJ`. For `J = 1` the ground energy has modulus at most
  `2L`, so a unit vector whose overlap with a ground vector is at least `1 - δ` has energy at
  most `E₀ + 8Lδ`.
* At the cut after the first `k` sites, the terms inside the first `k` sites form a part
  supported on them, and the other terms form a part supported from the site `k - 1` onward, of
  norm at most `2L` when `J = 1`: `H = H_L + (H_R + H_i)`.
* For positive terms of norm at most one, the terms crossing the cut are the one term on the
  adjacent pair at the cut, so `H = H_L + H_R + K` with `0 ≤ K ≤ 1`.

The interactions allow arbitrary Hermitian terms on single sites and on adjacent pairs, whereas
the source assumes positive terms on adjacent pairs; the norm estimates do not need positivity.

**Local fix (witness energy):** the source omits a factor of two when it converts its
unsquared overlap tolerance into an energy bound; the bound here is `8Lδ`. The correction is
recorded in `docs/paper-gaps/lvv13_witness_energy.tex`.

## Main results

* `ManyBody.ChainInteraction.norm_hamiltonian_le_of_range_one` — `‖H‖ ≤ 2LJ`.
* `ManyBody.ChainInteraction.re_inner_sub_le_of_overlap_of_range_one` — the energy of a unit
  vector from its overlap with a ground vector.
* `ManyBody.ChainInteraction.exists_gluing_decomposition_of_range_one` — `H = H_L + B` with
  `B` supported from the boundary site onward and `‖B‖ ≤ 2L`.
* `ManyBody.ChainInteraction.exists_cut_decomposition_of_range_one` — `H = H_L + H_R + K` with
  `0 ≤ K ≤ 1`.

## References

* Z. Landau, U. Vazirani and T. Vidick, *A polynomial-time algorithm for the ground state of 1D
  gapped local Hamiltonians*, arXiv:1307.5143v1, `algo53.tex`, lines 283 and 409–410 (the
  decompositions) and Lemma `l:within`, lines 509–515 (the energy from the overlap).
-/

open Matrix
open scoped InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace ManyBody

section Norm

/-- The Hamiltonian of a range-one interaction on the chain of `L` sites with term norms at most
`J` has norm at most `2LJ`. -/
theorem ChainInteraction.norm_hamiltonian_le_of_range_one {L q : ℕ} {J : ℝ}
    (h : ChainInteraction L q 1) (hhJ : ∀ X, ‖h.term X‖ ≤ J) :
    ‖h.hamiltonian‖ ≤ 2 * L * J := by
  classical
  by_cases hL : L = 0
  · subst L
    have hcard : Fintype.card (ChainSupport 0 1) = 0 := by
      have := card_chainSupport_range_one_le 0
      omega
    let := Fintype.card_eq_zero_iff.mp hcard
    simp [Interaction.hamiltonian]
  · have hJ := h.norm_bound_nonneg hhJ ⟨0, by omega⟩
    calc
      ‖h.hamiltonian‖ ≤ ∑ X, ‖h.term X‖ := norm_sum_le _ _
      _ ≤ ∑ _ : ChainSupport L 1, J := Finset.sum_le_sum fun X _ ↦ hhJ X
      _ = (Fintype.card (ChainSupport L 1) : ℝ) * J := by simp
      _ ≤ (2 * L : ℝ) * J :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_chainSupport_range_one_le L) hJ

end Norm

section Overlap

variable {L q : ℕ} {E₀ δ c : ℝ} {Ω v : EuclideanSpace ℂ (Fin L → Fin q)}

/-- Ground-state overlap controls the energy of a unit vector for a range-one Hamiltonian
with interaction norms at most one. This is the general norm variant of the auxiliary
energy inference in Landau–Vazirani–Vidick, arXiv:1307.5143v1, `algo53.tex`, proof of
Lemma `l:within`, lines 509–515. -/
theorem ChainInteraction.re_inner_sub_le_of_overlap_of_range_one
    (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ 1) (hΩ : ‖Ω‖ = 1)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (hv : ‖v‖ = 1) (hover : 1 - δ ≤ ‖⟪Ω, v⟫_ℂ‖) :
    (⟪v, toEuclideanLin h.hamiltonian v⟫_ℂ).re - E₀ ≤ 8 * L * δ := by
  let B := toEuclideanCLM (𝕜 := ℂ) h.hamiltonian
  have hB : ‖B‖ ≤ 2 * L := by
    simpa only [B, l2_opNorm_toEuclideanCLM, mul_one] using
        h.norm_hamiltonian_le_of_range_one hhJ
  have heig : B Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self _)
  have hE₀ : ‖(E₀ : ℂ)‖ ≤ ‖B‖ := by
    simpa only [heig, norm_smul, hΩ, mul_one] using B.le_opNorm Ω
  have hshift : ‖B - (E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖ ≤ 4 * L := by
    calc
      ‖B - (E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖
          ≤ ‖B‖ + ‖(E₀ : ℂ) • ContinuousLinearMap.id ℂ _‖ := norm_sub_le _ _
      _ ≤ ‖B‖ + ‖(E₀ : ℂ)‖ := by
        rw [norm_smul]
        exact add_le_add le_rfl ((mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin L → Fin q)))
          (norm_nonneg (E₀ : ℂ))).trans_eq (mul_one _))
      _ ≤ 4 * L := by linarith
  have hsymm : (toEuclideanLin h.hamiltonian).IsSymmetric :=
    (isSymmetric_toEuclideanLin_iff (A := h.hamiltonian)).mpr
        (Interaction.isHermitian_hamiltonian hh)
  calc
    (⟪v, toEuclideanLin h.hamiltonian v⟫_ℂ).re - E₀ ≤ 2 * (4 * L) * δ :=
      hsymm.re_inner_sub_eigenvalue_le_of_overlap (B := B) (e := E₀)
        (M := 4 * L) (δ := δ) hΩ hv heig hshift hover
    _ = 8 * L * δ := by ring

/-- At overlap tolerance `c/L`, the preceding general norm estimate gives excess energy
at most `8c`. This is an auxiliary bound for Landau–Vazirani–Vidick, arXiv:1307.5143v1,
`algo53.tex`, proof of Lemma `l:within`, lines 509–515. -/
theorem ChainInteraction.re_inner_le_of_overlap_div_of_range_one
    (h : ChainInteraction L q 1) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ 1) (hΩ : ‖Ω‖ = 1)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (hL : 0 < L) (hv : ‖v‖ = 1) (hover : 1 - c / L ≤ ‖⟪Ω, v⟫_ℂ‖) :
    (⟪v, toEuclideanLin h.hamiltonian v⟫_ℂ).re ≤ E₀ + 8 * c := by
  have henergy := h.re_inner_sub_le_of_overlap_of_range_one hh hhJ hΩ hspan hv hover
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  have hcancel : (8 : ℝ) * L * (c / L) = 8 * c := by field_simp [hL0]
  rw [hcancel] at henergy
  linarith

end Overlap

section Gluing

variable {L q : ℕ}

/-- The sum of the interactions not wholly inside the first `k` sites, those acting on the
boundary site `k - 1` and the right part of the chain, is supported from the boundary site
onward. Landau–Vazirani–Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 409–410, the term
`H_R + H_i`. -/
theorem ChainInteraction.isSupportedOn_partialHamiltonian_not_subset
    (h : ChainInteraction L q 1) (k : ℕ) :
    IsSupportedOn (X := fun _ ↦ Fin q)
      (h.partialHamiltonian (Finset.univ.filter fun X : ChainSupport L 1 ↦
        ¬ X.1 ⊆ interval L 0 k))
      (interval L 0 (k - 1))ᶜ := by
  change _ ∈ supportedOperators _ _
  refine h.partialHamiltonian_mem_supportedOperators fun X hX ↦ ?_
  have hX' := (Finset.mem_filter.mp hX).2
  obtain ⟨y, hy, hyA⟩ := Finset.not_subset.mp hX'
  have hyk : k ≤ y.val := by simpa [mem_interval, not_lt] using hyA
  intro x hx
  have hxk : k - 1 ≤ x.val := Nat.sub_le_iff_le_add.mpr (hyk.trans (X.2.2 x hx y hy))
  simpa [mem_interval, not_lt] using hxk

/-- The sum of the interactions not wholly inside the first `k` sites has norm at most `2L`
when every term has norm at most one. -/
theorem ChainInteraction.norm_partialHamiltonian_not_subset_le
    (h : ChainInteraction L q 1) (hhJ : ∀ X, ‖h.term X‖ ≤ 1) (k : ℕ) :
    ‖h.partialHamiltonian (Finset.univ.filter fun X : ChainSupport L 1 ↦
        ¬ X.1 ⊆ interval L 0 k)‖ ≤ 2 * (L : ℝ) := by
  classical
  set U := Finset.univ.filter (fun X : ChainSupport L 1 ↦ ¬ X.1 ⊆ interval L 0 k)
  have hcard : U.card ≤ 2 * L :=
    (Finset.card_le_univ U).trans (card_chainSupport_range_one_le L)
  calc
    _ ≤ ∑ _ ∈ U, (1 : ℝ) := norm_sum_le_of_le U fun X _ ↦ hhJ X
    _ ≤ 2 * (L : ℝ) := by
      simpa using (show (U.card : ℝ) ≤ 2 * (L : ℝ) by exact_mod_cast hcard)

/-- A normalized range-one Hamiltonian splits into a left-supported part and a part
supported from the boundary site onward, whose norm is at most `2L`: the partial
Hamiltonians of the supports inside the first `k` sites and of the other supports.
Landau–Vazirani–Vidick, arXiv:1307.5143v1, `algo53.tex`, lines 409–410. -/
theorem ChainInteraction.exists_gluing_decomposition_of_range_one
    (h : ChainInteraction L q 1) (hhJ : ∀ X, ‖h.term X‖ ≤ 1) (k : ℕ) :
    ∃ HL B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      h.hamiltonian = HL + B ∧
      IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k) ∧
      IsSupportedOn (X := fun _ ↦ Fin q) B (interval L 0 (k - 1))ᶜ ∧
      ‖B‖ ≤ 2 * (L : ℝ) :=
  ⟨h.partialHamiltonian (Finset.univ.filter fun X : ChainSupport L 1 ↦ X.1 ⊆ interval L 0 k),
    h.partialHamiltonian (Finset.univ.filter fun X : ChainSupport L 1 ↦ ¬ X.1 ⊆ interval L 0 k),
    (h.partialHamiltonian_filter_add_filter_not fun X : ChainSupport L 1 ↦
      X.1 ⊆ interval L 0 k).symm,
    h.partialHamiltonian_mem_supportedOperators fun _ hX ↦ (Finset.mem_filter.mp hX).2,
    h.isSupportedOn_partialHamiltonian_not_subset k,
    h.norm_partialHamiltonian_not_subset_le hhJ k⟩

end Gluing

section Cut

/-- Positive range-one interactions of norm at most one split at every cut as
`H = H_L + H_R + K`, with the two parts supported on their respective sides and
`0 ≤ K ≤ 1`. Landau–Vazirani–Vidick, arXiv:1307.5143v1, `algo53.tex`, line 283 and
lines 409–410. -/
theorem ChainInteraction.exists_cut_decomposition_of_range_one {L q : ℕ}
    (h : ChainInteraction L q 1) (hhJ : ∀ X, ‖h.term X‖ ≤ 1)
        (hpos : ∀ X, (h.term X).PosSemidef) (k : ℕ) :
    ∃ HL HR K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ,
      h.hamiltonian = HL + HR + K ∧
      IsSupportedOn (X := fun _ ↦ Fin q) HL (interval L 0 k) ∧
      IsSupportedOn (X := fun _ ↦ Fin q) HR (interval L 0 k)ᶜ ∧
      K.PosSemidef ∧ (1 - K).PosSemidef := by
  classical
  let A := interval L 0 k
  let S := Finset.univ.filter fun X : ChainSupport L 1 ↦ X.1 ⊆ A
  let U := Finset.univ.filter fun X : ChainSupport L 1 ↦ ¬X.1 ⊆ A
  let T := U.filter fun X ↦ X.1 ⊆ Aᶜ
  let C := U.filter fun X ↦ ¬X.1 ⊆ Aᶜ
  have hcross (X : ChainSupport L 1) (hXC : X ∈ C) :
      X.1 = interval L (k - 1) (k + 1) := by
    have hnotL := (Finset.mem_filter.mp (Finset.mem_filter.mp hXC).1).2
    have hnotR := (Finset.mem_filter.mp hXC).2
    apply X.2.eq_interval_of_splits_of_range_one
    constructor
    · obtain ⟨x, hx, hxA⟩ := Finset.not_subset.mp hnotR
      exact ⟨x, hx, by simpa [A, mem_interval] using hxA⟩
    · obtain ⟨y, hy, hyA⟩ := Finset.not_subset.mp hnotL
      refine ⟨y, hy, ?_⟩
      have : ¬y.val < k := by simpa [A, mem_interval] using hyA
      omega
  have hcard : C.card ≤ 1 := Finset.card_le_one.mpr fun X hX Y hY ↦
    Subtype.ext ((hcross X hX).trans (hcross Y hY).symm)
  let K := ∑ X ∈ C, h.term X
  have hK : K.PosSemidef := posSemidef_sum C fun X _ ↦ hpos X
  have hKn : ‖K‖ ≤ 1 := by
    calc
      ‖K‖ ≤ ∑ _ ∈ C, (1 : ℝ) := norm_sum_le_of_le C fun X _ ↦ hhJ X
      _ ≤ 1 := by simpa using (show (C.card : ℝ) ≤ 1 by exact_mod_cast hcard)
  have hK1 : (1 - K).PosSemidef :=
    Matrix.le_iff.mp ((CStarAlgebra.norm_le_one_iff_of_nonneg _ hK.nonneg).mp hKn)
  let HL := ∑ X ∈ S, h.term X
  let HR := ∑ X ∈ T, h.term X
  refine ⟨HL, HR, K, ?_, ?_, ?_, hK, hK1⟩
  · have hSU : h.hamiltonian = HL + ∑ X ∈ U, h.term X :=
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun X : ChainSupport L 1 ↦ X.1 ⊆ A) h.term).symm
    have hTC : (∑ X ∈ U, h.term X) = HR + K :=
      (Finset.sum_filter_add_sum_filter_not U (fun X ↦ X.1 ⊆ Aᶜ) h.term).symm
    rw [hSU, hTC, add_assoc]
  · change _ ∈ supportedOperators _ _
    exact sum_mem fun X hX ↦ IsSupportedOn.mono (h.mem X) (Finset.mem_filter.mp hX).2
  · change _ ∈ supportedOperators _ _
    exact sum_mem fun X hX ↦ IsSupportedOn.mono (h.mem X) (Finset.mem_filter.mp hX).2

end Cut

end ManyBody
