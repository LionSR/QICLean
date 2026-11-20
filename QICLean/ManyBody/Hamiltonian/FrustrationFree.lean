/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CompressionEnergyBounds
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Hamiltonian.DisjointRegionalGround

/-!
# Frustration-free interactions

An interaction is frustration free when one nonzero vector minimizes the energy of every term:
there are real numbers `e i` and a vector `ψ ≠ 0` with `hᵢ ψ = eᵢ ψ` and `hᵢ ≥ eᵢ` for every
term. Shifting each term by a constant shifts the energies and keeps the predicate. For terms
with finite index set, such a vector is a ground vector of the Hamiltonian at `∑ᵢ eᵢ`, the
ground space at that energy is the intersection of the ground spaces of the terms, and for
Hermitian terms frustration freeness says that the least eigenvalue of the Hamiltonian is the
sum of the least eigenvalues of the terms. The normalized form, positive semidefinite terms
with a common nonzero kernel vector, is the case `eᵢ = 0`.

## Main definitions

* `ManyBody.Interaction.IsFrustrationFree` — a common ground vector of all terms.

## Main results

* `ManyBody.Interaction.groundSpace_hamiltonian_eq_iInf` — the ground space of the
  Hamiltonian at `∑ᵢ eᵢ` is the intersection of the ground spaces of the terms.
* `ManyBody.Interaction.isFrustrationFree_iff_minEigenvalue` — for Hermitian terms, frustration
  freeness is additivity of the least eigenvalue.
* `ManyBody.Interaction.groundSpace_hamiltonian_zero` — for positive semidefinite terms the
  kernel of the Hamiltonian is the common kernel of the terms.
* `ManyBody.Interaction.isFrustrationFree_of_pairwise_disjoint` — Hermitian terms on pairwise
  disjoint regions are frustration free.

## References

* Cirac, Pérez-García, Schuch and Verstraete, arXiv:2011.12127, `TN-Review-main.tex`, line 537:
  the ground state minimizes the energy of each Hamiltonian term.
* Sanz, Pérez-García, Wolf and Cirac, arXiv:0909.5347, `main.tex`, lines 796–808: the
  definition for a translation-invariant chain, with the local minimum normalized to `0`.
* Pérez-García, Verstraete, Wolf and Cirac, quant-ph/0608197, `MPSarchive.tex`, lines 311–326.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

namespace Interaction

variable {ι : Type*} {T : ι → Finset V}

/-- An interaction is **frustration free** when one nonzero vector `ψ` minimizes the energy of
every term: there are real numbers `e i` with `hᵢ ψ = eᵢ ψ` and `hᵢ ≥ eᵢ`. The energies are not
fixed and the terms need not be positive, so the predicate is invariant under shifting each
term by a constant (`isFrustrationFree_iff_of_term_eq_sub`); the normalized form, positive
terms with a common kernel vector, is `isFrustrationFree_of_groundSpace_hamiltonian_zero_ne_bot`.
Cirac, Pérez-García, Schuch and Verstraete, arXiv:2011.12127, `TN-Review-main.tex`, line 537;
Sanz, Pérez-García, Wolf and Cirac, arXiv:0909.5347, `main.tex`, lines 796–808. -/
def IsFrustrationFree (Φ : Interaction X T) : Prop :=
  ∃ (e : ι → ℝ) (ψ : EuclideanSpace ℂ (Config X)), ψ ≠ 0 ∧
    ∀ i, ψ ∈ groundSpace (Φ.term i) (e i) ∧ (e i : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤
      Φ.term i

/-- Shifting every term by a constant does not change frustration freeness. -/
theorem isFrustrationFree_iff_of_term_eq_sub {T' : ι → Finset V} {Φ : Interaction X T}
    {Ψ : Interaction X T'} (c : ι → ℝ) (h : ∀ i, Ψ.term i = Φ.term i - (c i : ℂ) • 1) :
    Ψ.IsFrustrationFree ↔ Φ.IsFrustrationFree := by
  have hle (i : ι) (a : ℝ) : ((a - c i : ℝ) : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤
      Ψ.term i ↔ (a : ℂ) • 1 ≤ Φ.term i := by
    rw [h, Matrix.le_iff, Matrix.le_iff, Complex.ofReal_sub, sub_smul, sub_sub_sub_cancel_right]
  constructor
  · rintro ⟨e, ψ, hψ, he⟩
    refine ⟨fun i ↦ e i + c i, ψ, hψ, fun i ↦ ⟨?_, ?_⟩⟩
    · rw [← groundSpace_sub_smul_one _ (c i), add_sub_cancel_right, ← h]
      exact (he i).1
    · rw [← hle, add_sub_cancel_right]
      exact (he i).2
  · rintro ⟨e, ψ, hψ, he⟩
    refine ⟨fun i ↦ e i - c i, ψ, hψ, fun i ↦ ⟨?_, (hle i (e i)).mpr (he i).2⟩⟩
    rw [h, groundSpace_sub_smul_one]
    exact (he i).1

/-- A common ground vector of the terms in `s` is a ground vector of their sum, at the sum of
the energies. -/
theorem mem_groundSpace_sum (Φ : Interaction X T) (s : Finset ι) {e : ι → ℝ}
    {ψ : EuclideanSpace ℂ (Config X)} (h : ∀ i ∈ s, ψ ∈ groundSpace (Φ.term i) (e i)) :
    ψ ∈ groundSpace (∑ i ∈ s, Φ.term i) (∑ i ∈ s, e i) := by
  rw [mem_groundSpace_iff_mulVec, sum_mulVec, Complex.ofReal_sum, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i hi ↦ mem_groundSpace_iff_mulVec.mp (h i hi)

/-- Lower bounds on the terms in `s` add up to a lower bound on their sum. -/
theorem sum_smul_one_le_sum (Φ : Interaction X T) (s : Finset ι) {e : ι → ℝ}
    (he : ∀ i ∈ s, (e i : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤ Φ.term i) :
    ((∑ i ∈ s, e i : ℝ) : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤ ∑ i ∈ s, Φ.term i := by
  rw [Complex.ofReal_sum, Finset.sum_smul]
  exact Finset.sum_le_sum he

/-- **Disjoint supports.** Hermitian terms supported on pairwise disjoint regions form a
frustration-free interaction. ALVV, arXiv:1602.08828v2, Corollary `c:goodagsphardtrunc`,
lines 979–1005. -/
theorem isFrustrationFree_of_pairwise_disjoint [Finite ι] [∀ v, Nonempty (X v)]
    {Φ : Interaction X T}
    (hdisj : Pairwise fun i j ↦ Disjoint (T i) (T j)) (h : ∀ i, (Φ.term i).IsHermitian) :
    Φ.IsFrustrationFree := by
  have := Fintype.ofFinite ι
  obtain ⟨e, x, hx, hex, hle⟩ := exists_common_unit_ground_of_disjoint_family Finset.univ T
    Φ.term (fun i _ ↦ h i) (fun i _ j _ hij ↦ hdisj hij) fun i _ ↦ Φ.mem i
  refine ⟨e, WithLp.toLp 2 x, fun h0 ↦ ?_, fun i ↦
    ⟨mem_groundSpace_iff_mulVec.mpr (hex i (Finset.mem_univ i)),
      Matrix.le_iff.mpr (hle i (Finset.mem_univ i))⟩⟩
  have : x = 0 := by simpa using congrArg WithLp.ofLp h0
  simp [this] at hx

variable [Fintype ι]

/-- A common ground vector of all terms is a ground vector of the Hamiltonian at `∑ᵢ eᵢ`. -/
theorem mem_groundSpace_hamiltonian (Φ : Interaction X T) {e : ι → ℝ}
    {ψ : EuclideanSpace ℂ (Config X)} (h : ∀ i, ψ ∈ groundSpace (Φ.term i) (e i)) :
    ψ ∈ groundSpace Φ.hamiltonian (∑ i, e i) :=
  Φ.mem_groundSpace_sum Finset.univ fun i _ ↦ h i

/-- Lower bounds `hᵢ ≥ eᵢ` on the terms give `H ≥ ∑ᵢ eᵢ`. -/
theorem sum_smul_one_le_hamiltonian (Φ : Interaction X T) {e : ι → ℝ}
    (he : ∀ i, (e i : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤ Φ.term i) :
    ((∑ i, e i : ℝ) : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤ Φ.hamiltonian :=
  Φ.sum_smul_one_le_sum Finset.univ fun i _ ↦ he i

/-- **The ground space is the intersection.** If `hᵢ ≥ eᵢ` for every term, then the ground
space of the Hamiltonian at `∑ᵢ eᵢ` is the intersection of the ground spaces of the terms at
the `eᵢ`. Both sides are `⊥` unless the interaction is frustration free with these energies. -/
theorem groundSpace_hamiltonian_eq_iInf (Φ : Interaction X T) {e : ι → ℝ}
    (he : ∀ i, (e i : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤ Φ.term i) :
    groundSpace Φ.hamiltonian (∑ i, e i) = ⨅ i, groundSpace (Φ.term i) (e i) := by
  refine le_antisymm (fun ψ hψ ↦ Submodule.mem_iInf _ |>.mpr fun k ↦ ?_)
    fun ψ hψ ↦ Φ.mem_groundSpace_hamiltonian (Submodule.mem_iInf _ |>.mp hψ)
  have hsum : (∑ i, (Φ.term i - (e i : ℂ) • 1)) *ᵥ WithLp.ofLp ψ = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, ← Complex.ofReal_sum, sub_mulVec,
      smul_mulVec, one_mulVec, ← mem_groundSpace_iff_mulVec.mp hψ, hamiltonian, sub_self]
  have hk := PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero_of_mem
    (fun i _ ↦ Matrix.le_iff.mp (he i)) hsum (Finset.mem_univ k)
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hk
  exact mem_groundSpace_iff_mulVec.mpr hk

/-- An energy attained by a nonzero vector and below the whole spectrum is the least
eigenvalue. -/
private theorem eq_minEigenvalue_of_mem_groundSpace [Nonempty (Config X)]
    {M : Matrix (Config X) (Config X) ℂ} (hM : M.IsHermitian) {a : ℝ}
    {ψ : EuclideanSpace ℂ (Config X)} (hψ : ψ ∈ groundSpace M a) (hψ0 : ψ ≠ 0)
    (ha : (a : ℂ) • 1 ≤ M) : a = minEigenvalue hM := by
  set u : EuclideanSpace ℂ (Config X) := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
  have hu : u ∈ groundSpace M a := Submodule.smul_mem _ _ hψ
  have hunit : star (WithLp.ofLp u) ⬝ᵥ WithLp.ofLp u = 1 := by
    have h1 : ‖u‖ = 1 := by
      simp only [u, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hψ0)
    have h2 := (EuclideanSpace.inner_eq_star_dotProduct u u).symm
    rw [inner_self_eq_norm_sq_to_K, h1] at h2
    simpa [dotProduct_comm] using h2
  exact Matrix.minEigenvalue_eq_of_attained_lower_bounds M M hM a _ hunit
    (mem_groundSpace_iff_mulVec.mp hu) (Matrix.le_iff.mp ha)
    (sub_minEigenvalue_smul_one_posSemidef hM)

/-- **Frustration freeness by least eigenvalues.** For Hermitian terms on a system of sites
with nonempty basis types, the interaction is frustration free exactly when the least
eigenvalue of the Hamiltonian is the sum of the least eigenvalues of the terms. -/
theorem isFrustrationFree_iff_minEigenvalue [∀ v, Nonempty (X v)] {Φ : Interaction X T}
    (h : ∀ i, (Φ.term i).IsHermitian) :
    Φ.IsFrustrationFree ↔
      minEigenvalue (isHermitian_hamiltonian h) = ∑ i, minEigenvalue (h i) := by
  constructor
  · rintro ⟨e, ψ, hψ0, he⟩
    have hei (i : ι) : e i = minEigenvalue (h i) :=
      eq_minEigenvalue_of_mem_groundSpace (h i) (he i).1 hψ0 (he i).2
    rw [← eq_minEigenvalue_of_mem_groundSpace (isHermitian_hamiltonian h)
      (Φ.mem_groundSpace_hamiltonian fun i ↦ (he i).1) hψ0
      (Φ.sum_smul_one_le_hamiltonian fun i ↦ (he i).2)]
    exact Finset.sum_congr rfl fun i _ ↦ hei i
  · intro hmin
    have hlow (i : ι) : (minEigenvalue (h i) : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤
        Φ.term i :=
      Matrix.le_iff.mpr (sub_minEigenvalue_smul_one_posSemidef (h i))
    obtain ⟨k, hk⟩ := minEigenvalue_achieved (isHermitian_hamiltonian h)
    have hmem := eigenvectorBasis_mem_groundSpace (isHermitian_hamiltonian h) (hk.trans hmin)
    rw [Φ.groundSpace_hamiltonian_eq_iInf hlow] at hmem
    exact ⟨fun i ↦ minEigenvalue (h i), _,
      (isHermitian_hamiltonian h).eigenvectorBasis.orthonormal.ne_zero k,
      fun i ↦ ⟨Submodule.mem_iInf _ |>.mp hmem i, hlow i⟩⟩

/-- For positive semidefinite terms, the Hamiltonian annihilates a vector exactly when every
term does. -/
theorem hamiltonian_mulVec_eq_zero_iff {Φ : Interaction X T} (h : ∀ i, (Φ.term i).PosSemidef)
    {ψ : Config X → ℂ} : Φ.hamiltonian *ᵥ ψ = 0 ↔ ∀ i, Φ.term i *ᵥ ψ = 0 := by
  refine ⟨fun hψ i ↦ PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero_of_mem
    (fun i _ ↦ h i) hψ (Finset.mem_univ i), fun hψ ↦ ?_⟩
  simp [hamiltonian, sum_mulVec, hψ]

/-- For positive semidefinite terms, the kernel of the Hamiltonian is the common kernel of the
terms. -/
theorem groundSpace_hamiltonian_zero {Φ : Interaction X T} (h : ∀ i, (Φ.term i).PosSemidef) :
    groundSpace Φ.hamiltonian 0 = ⨅ i, groundSpace (Φ.term i) 0 := by
  simpa using Φ.groundSpace_hamiltonian_eq_iInf (e := 0) fun i ↦ by
    simpa using (h i).nonneg

/-- **The normalized form.** For positive semidefinite terms, the Hamiltonian has a nonzero
kernel exactly when the terms have a common nonzero kernel vector. -/
theorem groundSpace_hamiltonian_zero_ne_bot_iff {Φ : Interaction X T}
    (h : ∀ i, (Φ.term i).PosSemidef) :
    groundSpace Φ.hamiltonian 0 ≠ ⊥ ↔
      ∃ ψ : EuclideanSpace ℂ (Config X), ψ ≠ 0 ∧ ∀ i, Φ.term i *ᵥ WithLp.ofLp ψ = 0 := by
  rw [Submodule.ne_bot_iff]
  refine exists_congr fun ψ ↦ ?_
  rw [and_comm, mem_groundSpace_iff_mulVec]
  simp [hamiltonian_mulVec_eq_zero_iff h]

/-- Positive semidefinite terms whose Hamiltonian has a nonzero kernel form a frustration-free
interaction, with all energies `0`. -/
theorem isFrustrationFree_of_groundSpace_hamiltonian_zero_ne_bot {Φ : Interaction X T}
    (h : ∀ i, (Φ.term i).PosSemidef) (hne : groundSpace Φ.hamiltonian 0 ≠ ⊥) :
    Φ.IsFrustrationFree := by
  obtain ⟨ψ, hψ0, hψ⟩ := (groundSpace_hamiltonian_zero_ne_bot_iff h).mp hne
  refine ⟨0, ψ, hψ0, fun i ↦ ⟨mem_groundSpace_iff_mulVec.mpr (by simpa using hψ i), ?_⟩⟩
  simpa using (h i).nonneg

end Interaction

end ManyBody
