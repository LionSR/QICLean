/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalSpectrum
import QICLean.Analysis.EntropyDecomposition

/-!
# Density matrices restricted to selected spectral indices

A finite set of eigenvalue indices determines an orthogonal projection onto the
corresponding eigenvectors. The normalized spectral restriction is the matrix
obtained by retaining these eigenvalues, dividing by their total mass, and
setting the remaining eigenvalues to zero. The matrix acts on the original
Hilbert space. Its rank and von Neumann entropy give the cardinality and entropy
of the selected normalized spectrum.

## References

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), equations `comparator:typical-set` and `comparator:typical-entropies`,
`07-comparators.tex`, lines 39–55, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text reused.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:typical-set, comparator:typical-entropies.
Provenance-ID: 8753-qic-typical-density-01
Downstream declaration:
Matrix.IsHermitian.spectralSelection
Provenance-ID: 8753-qic-typical-density-02
Downstream declaration:
Matrix.IsHermitian.spectralRestrictionMass
Provenance-ID: 8753-qic-typical-density-03
Downstream declaration:
Matrix.IsHermitian.normalizedSpectralRestriction
Provenance-ID: 8753-qic-typical-density-04
Downstream declaration:
Matrix.IsHermitian.isStarProjection_spectralSelection
Provenance-ID: 8753-qic-typical-density-05
Downstream declaration:
Matrix.IsHermitian.commute_spectralSelection
Provenance-ID: 8753-qic-typical-density-06
Downstream declaration:
Matrix.PosSemidef.normalizedSpectralRestriction_posSemidef
Provenance-ID: 8753-qic-typical-density-07
Downstream declaration:
Matrix.IsHermitian.trace_normalizedSpectralRestriction
Provenance-ID: 8753-qic-typical-density-08
Downstream declaration:
Matrix.IsHermitian.normalizedSpectralRestriction_eq
Provenance-ID: 8753-qic-typical-density-09
Downstream declaration:
Matrix.PosSemidef.spectralRestrictionMass_le_one
Provenance-ID: 8753-qic-typical-density-10
Downstream declaration:
Matrix.IsHermitian.rank_normalizedSpectralRestriction
Provenance-ID: 8753-qic-typical-density-11
Downstream declaration:
Matrix.PosSemidef.entropy_normalizedSpectralRestriction
Provenance-ID: 8753-qic-typical-density-12
Downstream declaration:
Matrix.PosSemidef.typicalSpectralRestriction_entropy_bounds
-/

open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

/-- Projection onto a selected family of Hermitian eigenvectors. -/
def IsHermitian.spectralSelection (hρ : ρ.IsHermitian) (E : Finset n) : Matrix n n ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hρ.eigenvectorUnitary)
    (diagonal fun i ↦ if i ∈ E then 1 else 0)

/-- The mass carried by the selected eigenvalue indices.
OpenAI area-law manuscript, `comparator:typical-set`. -/
def IsHermitian.spectralRestrictionMass (hρ : ρ.IsHermitian) (E : Finset n) : ℝ :=
  ∑ i ∈ E, hρ.eigenvalues i

/-- The selected normalized spectrum, extended by zero on the other eigenspaces.
OpenAI area-law manuscript, `comparator:typical-set`. -/
def IsHermitian.normalizedSpectralRestriction (hρ : ρ.IsHermitian) (E : Finset n) :
    Matrix n n ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hρ.eigenvectorUnitary)
    (diagonal fun i ↦ if i ∈ E then
      ((hρ.eigenvalues i / hρ.spectralRestrictionMass E : ℝ) : ℂ) else 0)

/-- A spectral selection is an orthogonal projection. -/
theorem IsHermitian.isStarProjection_spectralSelection (hρ : ρ.IsHermitian) (E : Finset n) :
    IsStarProjection (hρ.spectralSelection E) := by
  rw [isStarProjection_iff']
  simp only [spectralSelection, ← map_mul, ← map_star, diagonal_mul_diagonal]
  constructor
  · congr 1
    apply congrArg diagonal
    funext i
    split_ifs <;> simp
  · congr 1
    rw [Matrix.star_eq_conjTranspose, diagonal_conjTranspose]
    apply congrArg diagonal
    funext i
    split_ifs <;> simp_all

/-- The selected projection commutes with the original Hermitian matrix. -/
theorem IsHermitian.commute_spectralSelection (hρ : ρ.IsHermitian) (E : Finset n) :
    Commute (hρ.spectralSelection E) ρ := by
  change hρ.spectralSelection E * ρ = ρ * hρ.spectralSelection E
  conv_lhs => rhs; rw [hρ.spectral_theorem]
  conv_rhs => lhs; rw [hρ.spectral_theorem]
  simp only [spectralSelection, ← map_mul, diagonal_mul_diagonal]
  congr 1
  apply congrArg diagonal
  funext i
  exact mul_comm _ _

/-- A positive-mass spectral restriction of a positive matrix is positive. -/
theorem PosSemidef.normalizedSpectralRestriction_posSemidef (hρ : ρ.PosSemidef)
    (E : Finset n) (hz : 0 < hρ.isHermitian.spectralRestrictionMass E) :
    (hρ.isHermitian.normalizedSpectralRestriction E).PosSemidef := by
  rw [IsHermitian.normalizedSpectralRestriction, Unitary.conjStarAlgAut_apply]
  have hd : (diagonal fun i ↦ if i ∈ E then
      ((hρ.isHermitian.eigenvalues i / hρ.isHermitian.spectralRestrictionMass E : ℝ) : ℂ)
      else 0).PosSemidef := by
    apply PosSemidef.diagonal
    intro i
    change 0 ≤ if i ∈ E then
      ((hρ.isHermitian.eigenvalues i / hρ.isHermitian.spectralRestrictionMass E : ℝ) : ℂ)
      else 0
    split_ifs
    · exact_mod_cast div_nonneg (hρ.eigenvalues_nonneg i) hz.le
    · exact le_rfl
  exact hd.mul_mul_conjTranspose_same _

/-- Normalizing a positive-mass selected spectrum gives trace one. -/
theorem IsHermitian.trace_normalizedSpectralRestriction (hρ : ρ.IsHermitian) (E : Finset n)
    (hz : hρ.spectralRestrictionMass E ≠ 0) :
    (hρ.normalizedSpectralRestriction E).trace = 1 := by
  rw [normalizedSpectralRestriction, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rw [Finset.sum_ite_mem_eq]
  norm_cast
  rw [← Finset.sum_div]
  exact div_self hz

/-- A spectral restriction is the normalized compression by its selected projection. -/
theorem IsHermitian.normalizedSpectralRestriction_eq (hρ : ρ.IsHermitian) (E : Finset n) :
    hρ.normalizedSpectralRestriction E = (hρ.spectralRestrictionMass E : ℂ)⁻¹ •
      (hρ.spectralSelection E * ρ * hρ.spectralSelection E) := by
  conv_rhs => arg 2; lhs; rhs; rw [hρ.spectral_theorem]
  simp only [spectralSelection, normalizedSpectralRestriction, ← map_mul,
    ← map_smul, diagonal_mul_diagonal, ← diagonal_smul]
  congr 1
  apply congrArg diagonal
  funext i
  split_ifs <;> simp_all [div_eq_mul_inv, mul_comm]

/-- For a trace-one positive matrix, a selected spectral mass is at most one. -/
theorem PosSemidef.spectralRestrictionMass_le_one (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (E : Finset n) : hρ.isHermitian.spectralRestrictionMass E ≤ 1 := by
  rw [IsHermitian.spectralRestrictionMass,
    ← posSemidef_trace_one_eigenvalues_sum_one hρ htr]
  exact Finset.sum_le_sum_of_subset_of_nonneg E.subset_univ
    (fun i _ _ ↦ hρ.eigenvalues_nonneg i)

/-- The rank of a normalized selected spectrum is the number of its positive indices. -/
theorem IsHermitian.rank_normalizedSpectralRestriction (hρ : ρ.IsHermitian) (E : Finset n)
    (hz : hρ.spectralRestrictionMass E ≠ 0)
    (hpos : ∀ i ∈ E, 0 < hρ.eigenvalues i) :
    (hρ.normalizedSpectralRestriction E).rank = E.card := by
  classical
  rw [normalizedSpectralRestriction, Unitary.conjStarAlgAut_apply,
    ← Unitary.coe_star]
  have hu := (isUnit_iff_isUnit_det _).mp
    (Unitary.isUnit_coe (U := hρ.eigenvectorUnitary))
  have hus := (isUnit_iff_isUnit_det _).mp
    (Unitary.isUnit_coe (U := star hρ.eigenvectorUnitary))
  rw [rank_mul_eq_left_of_isUnit_det _ _ hus,
    rank_mul_eq_right_of_isUnit_det _ _ hu, rank_diagonal]
  have hi (i : n) :
      (if i ∈ E then ((hρ.eigenvalues i / hρ.spectralRestrictionMass E : ℝ) : ℂ)
        else 0) ≠ 0 ↔ i ∈ E := by
    by_cases he : i ∈ E
    · simp [he, (hpos i he).ne', hz]
    · simp [he]
  exact (Fintype.card_congr (Equiv.subtypeEquivRight hi)).trans (Fintype.card_coe E)

/-- The von Neumann entropy of the actual spectral restriction is the Shannon
entropy of its selected normalized eigenvalues. -/
theorem PosSemidef.entropy_normalizedSpectralRestriction (hρ : ρ.PosSemidef) (E : Finset n)
    (hz : 0 < hρ.isHermitian.spectralRestrictionMass E) :
    vonNeumannEntropy (hρ.isHermitian.normalizedSpectralRestriction E)
      (hρ.normalizedSpectralRestriction_posSemidef E hz).isHermitian =
        Entropy.probabilityEntropy
          (Entropy.normalizedRestriction hρ.isHermitian.eigenvalues E) := by
  let q : n → ℝ := fun i ↦ if i ∈ E then
    hρ.isHermitian.eigenvalues i / hρ.isHermitian.spectralRestrictionMass E else 0
  let U := Unitary.toUnits hρ.isHermitian.eigenvectorUnitary
  have hd : (diagonal fun i ↦ (q i : ℂ)).IsHermitian := by
    rw [isHermitian_diagonal_iff]
    intro i
    simp [isSelfAdjoint_iff]
  have hUinv : U.val⁻¹ = (star hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ) := by
    rw [← Matrix.coe_units_inv]
    rfl
  have heq : hρ.isHermitian.normalizedSpectralRestriction E =
      U.val * (diagonal fun i ↦ (q i : ℂ)) * U.val⁻¹ := by
    rw [IsHermitian.normalizedSpectralRestriction, Unitary.conjStarAlgAut_apply, hUinv]
    apply congrArg (fun D : Matrix n n ℂ ↦
      U.val * D * (star hρ.isHermitian.eigenvectorUnitary : Matrix n n ℂ))
    apply congrArg diagonal
    funext i
    by_cases hi : i ∈ E <;> simp [q, hi]
  have hc : (U.val * (diagonal fun i ↦ (q i : ℂ)) * U.val⁻¹).IsHermitian :=
    heq ▸ (hρ.normalizedSpectralRestriction_posSemidef E hz).isHermitian
  rw [vonNeumannEntropy_congr heq _ hc, vonNeumannEntropy_units_conj U hd hc,
    vonNeumannEntropy_diagonal q hd]
  rw [Entropy.probabilityEntropy]
  simp only [Entropy.normalizedRestriction]
  rw [Finset.sum_coe_sort (s := E)
    (f := fun i ↦ Real.negMulLog (hρ.isHermitian.eigenvalues i /
      ∑ j ∈ E, hρ.isHermitian.eigenvalues j))]
  simp [q, apply_ite, IsHermitian.spectralRestrictionMass]

/-- Cardinality and von Neumann entropy estimates for the actual normalized
typical spectral restriction. OpenAI area-law manuscript,
`comparator:typical-entropies`. Only selected positive eigenvalues are required;
the original positive matrix may have a nontrivial kernel. -/
theorem PosSemidef.typicalSpectralRestriction_entropy_bounds (hρ : ρ.PosSemidef)
    (E : Finset n) (w : ℝ) (hz : 0 < hρ.isHermitian.spectralRestrictionMass E)
    (hE : ∀ i ∈ E,
      Real.exp (-vonNeumannEntropy ρ hρ.isHermitian - w) ≤ hρ.isHermitian.eigenvalues i ∧
        hρ.isHermitian.eigenvalues i ≤ Real.exp (-vonNeumannEntropy ρ hρ.isHermitian + w)) :
    |Real.log ((hρ.isHermitian.normalizedSpectralRestriction E).rank : ℝ) -
      vonNeumannEntropy ρ hρ.isHermitian| ≤
        w + |Real.log (hρ.isHermitian.spectralRestrictionMass E)| ∧
      |vonNeumannEntropy (hρ.isHermitian.normalizedSpectralRestriction E)
          (hρ.normalizedSpectralRestriction_posSemidef E hz).isHermitian -
        vonNeumannEntropy ρ hρ.isHermitian| ≤
          w + |Real.log (hρ.isHermitian.spectralRestrictionMass E)| := by
  have hpos (i : n) (hi : i ∈ E) : 0 < hρ.isHermitian.eigenvalues i :=
    (Real.exp_pos _).trans_le (hE i hi).1
  rw [hρ.isHermitian.rank_normalizedSpectralRestriction E hz.ne' hpos,
    hρ.entropy_normalizedSpectralRestriction E hz]
  exact Entropy.typicalSpectrum_entropy_bounds hz hE

end Matrix
