/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.CompressionEnergyBounds
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Hamiltonian.DisjointRegionalGround
import QICLean.ManyBody.Hamiltonian.KernelGap
import QICLean.ManyBody.Hamiltonian.Models
import QICLean.ManyBody.Sites.Lattice.Plane
import QICLean.Analysis.Support.ProjectionOrder

/-!
# Frustration-free interactions

An interaction is frustration free when one nonzero vector minimizes the energy of every term:
there are real numbers `e i` and a vector `ψ ≠ 0` with `hᵢ ψ = eᵢ ψ` and `hᵢ ≥ eᵢ` for every
term. Shifting each term by a constant shifts the energies and keeps the predicate. For terms
with finite index set, such a vector is a ground vector of the Hamiltonian at `∑ᵢ eᵢ`, the
ground space at that energy is the intersection of the ground spaces of the terms, and for
Hermitian terms frustration freeness says that the least eigenvalue of the Hamiltonian is the
sum of the least eigenvalues of the terms. The normalized form, positive semidefinite terms
with a common nonzero kernel vector, is the case `eᵢ = 0`: the common kernel is the zero space
of the interaction, it is the ground space of the Hamiltonian at `0`, and the gap of the
Hamiltonian above it has a quadratic-form and a norm characterization on its orthogonal
complement.

## Main definitions

* `ManyBody.Interaction.IsFrustrationFree` — a common ground vector of all terms.
* `ManyBody.Interaction.zeroSpace` — the vectors annihilated by every term.

## Main results

* `ManyBody.Interaction.groundSpace_hamiltonian_eq_iInf` — the ground space of the
  Hamiltonian at `∑ᵢ eᵢ` is the intersection of the ground spaces of the terms.
* `ManyBody.Interaction.isFrustrationFree_iff_minEigenvalue` — for Hermitian terms, frustration
  freeness is additivity of the least eigenvalue.
* `ManyBody.Interaction.mem_zeroSpace_iff`, `ManyBody.Interaction.zeroSpace_eq_iInf_ker` — the
  zero space as the common kernel of the terms.
* `ManyBody.Interaction.isFrustrationFree_of_zeroSpace_ne_bot` — positive semidefinite terms
  with a nonzero zero space are frustration free.
* `ManyBody.Interaction.zeroSpace_eq_groundSpace` — for positive semidefinite terms the zero
  space is the kernel of the Hamiltonian.
* `ManyBody.Interaction.zeroVector_tfae` — for positive semidefinite terms, the readings of
  zero energy of a vector are equivalent;
  `ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff_mem_zeroSpace` is the case of terms
  positive in the matrix order.
* `ManyBody.Interaction.mem_ker_toEuclideanLin_hamiltonian_iff` — for positive semidefinite
  terms, the kernel of the Hamiltonian is the common kernel of the operators of the terms.
* `ManyBody.Interaction.isGapped_hamiltonian_zero_iff_inner` — the gap of a positive interaction
  above its zero space, in quadratic form.
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
open scoped ComplexOrder MatrixOrder InnerProductSpace

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

namespace Interaction

variable {ι : Type*} {T : ι → Finset V}

/-- An interaction is **frustration free** when one nonzero vector `ψ` minimizes the energy of
every term: there are real numbers `e i` with `hᵢ ψ = eᵢ ψ` and `hᵢ ≥ eᵢ`. The energies are not
fixed and the terms need not be positive, so the predicate is invariant under shifting each
term by a constant (`isFrustrationFree_iff_of_term_eq_sub`); the normalized form, positive
terms with a common kernel vector, is `isFrustrationFree_of_zeroSpace_ne_bot`.
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

/-- The **zero space** of an interaction: the vectors annihilated by every term, the
intersection of the kernels of the terms. For positive semidefinite terms it is the ground space
of the Hamiltonian at energy `0` (`zeroSpace_eq_groundSpace`), and when it is nonzero the
interaction is frustration free (`isFrustrationFree_of_zeroSpace_ne_bot`). -/
noncomputable def zeroSpace (Φ : Interaction X T) :
    Submodule ℂ (EuclideanSpace ℂ (Config X)) :=
  ⨅ i, groundSpace (Φ.term i) 0

theorem mem_zeroSpace_iff {Φ : Interaction X T} {ψ : EuclideanSpace ℂ (Config X)} :
    ψ ∈ Φ.zeroSpace ↔ ∀ i, Φ.term i *ᵥ WithLp.ofLp ψ = 0 := by
  simp [zeroSpace, Submodule.mem_iInf, mem_groundSpace_iff_mulVec]

/-- The zero space is the intersection of the kernels of the terms as operators on the
Euclidean space. -/
theorem zeroSpace_eq_iInf_ker (Φ : Interaction X T) :
    Φ.zeroSpace = ⨅ i, LinearMap.ker (toEuclideanLin (Φ.term i)) := by
  simp only [zeroSpace, groundSpace_zero]

/-- **The normalized form.** Positive semidefinite terms with a nonzero common kernel vector
form a frustration-free interaction, with all energies `0`. -/
theorem isFrustrationFree_of_zeroSpace_ne_bot {Φ : Interaction X T}
    (h : ∀ i, (Φ.term i).PosSemidef) (hne : Φ.zeroSpace ≠ ⊥) : Φ.IsFrustrationFree := by
  obtain ⟨ψ, hψ, hψ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨0, ψ, hψ0, fun i ↦ ⟨Submodule.mem_iInf _ |>.mp hψ i, by simpa using (h i).nonneg⟩⟩

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

/-- Positive semidefinite terms have a positive semidefinite Hamiltonian. -/
theorem posSemidef_hamiltonian {Φ : Interaction X T} (h : ∀ i, (Φ.term i).PosSemidef) :
    Φ.hamiltonian.PosSemidef :=
  posSemidef_sum _ fun i _ ↦ h i

/-- **The zero space is the ground space.** For positive semidefinite terms, the kernel of the
Hamiltonian is the common kernel of the terms. -/
theorem zeroSpace_eq_groundSpace {Φ : Interaction X T} (h : ∀ i, (Φ.term i).PosSemidef) :
    Φ.zeroSpace = groundSpace Φ.hamiltonian 0 := by
  simpa [zeroSpace] using (Φ.groundSpace_hamiltonian_eq_iInf (e := 0) fun i ↦ by
    simpa using (h i).nonneg).symm

/-- For positive semidefinite terms, a vector lies in the zero space exactly when the
Hamiltonian annihilates it. -/
theorem mem_zeroSpace_iff_hamiltonian_mulVec_eq_zero {Φ : Interaction X T}
    (h : ∀ i, (Φ.term i).PosSemidef) {ψ : EuclideanSpace ℂ (Config X)} :
    ψ ∈ Φ.zeroSpace ↔ Φ.hamiltonian *ᵥ WithLp.ofLp ψ = 0 := by
  rw [mem_zeroSpace_iff, hamiltonian_mulVec_eq_zero_iff h]

/-- **The gap above the zero space, in quadratic form.** For positive semidefinite terms, the
Hamiltonian is gapped at `0` with gap `Δ` exactly when the zero space is nonzero and
`Δ ‖v‖² ≤ Re ⟨v, H v⟩` for every `v` orthogonal to it. -/
theorem isGapped_hamiltonian_zero_iff_inner {Φ : Interaction X T}
    (h : ∀ i, (Φ.term i).PosSemidef) {Δ : ℝ} :
    IsGapped Φ.hamiltonian 0 Δ ↔ Φ.zeroSpace ≠ ⊥ ∧
      ∀ v ∈ Φ.zeroSpaceᗮ, Δ * ‖v‖ ^ 2 ≤ (⟪v, toEuclideanLin Φ.hamiltonian v⟫_ℂ).re := by
  rw [isGapped_zero_iff_inner (posSemidef_hamiltonian h), zeroSpace_eq_groundSpace h,
    groundSpace_zero]

/-- **Zero vectors of a positive interaction.** For positive semidefinite terms, six readings of
"`Ω` has energy `0`" are equivalent: `Ω` lies in the zero space, every term annihilates `Ω`, the
Hamiltonian annihilates `Ω` as a matrix, as a linear map or as a continuous linear map on the
Euclidean space, and `Ω` lies in the ground space of the Hamiltonian at energy `0`.
Pérez-García, Verstraete, Wolf and Cirac, quant-ph/0608197, `MPSarchive.tex`, lines 311–326;
Sanz, Pérez-García, Wolf and Cirac, arXiv:0909.5347, `main.tex`, lines 796–808. -/
theorem zeroVector_tfae {Φ : Interaction X T} (hΦ : ∀ i, (Φ.term i).PosSemidef)
    (Ω : EuclideanSpace ℂ (Config X)) :
    List.TFAE
      [ Ω ∈ Φ.zeroSpace,
        ∀ i, Φ.term i *ᵥ WithLp.ofLp Ω = 0,
        Φ.hamiltonian *ᵥ WithLp.ofLp Ω = 0,
        toEuclideanLin Φ.hamiltonian Ω = 0,
        toEuclideanCLM (𝕜 := ℂ) (n := Config X) Φ.hamiltonian Ω = 0,
        Ω ∈ groundSpace Φ.hamiltonian 0 ] := by
  tfae_have 1 ↔ 2 := mem_zeroSpace_iff
  tfae_have 1 ↔ 3 := mem_zeroSpace_iff_hamiltonian_mulVec_eq_zero hΦ
  tfae_have 3 ↔ 4 := by rw [toLpLin_apply, WithLp.toLp_eq_zero]
  tfae_have 4 ↔ 5 := Iff.rfl
  tfae_have 4 ↔ 6 := by rw [groundSpace_zero, LinearMap.mem_ker]
  tfae_finish

/-- **Zero energy for positive terms in the matrix order.** For terms `0 ≤ hᵢ`, the Hamiltonian
annihilates `Ω` exactly when `Ω` lies in the zero space. -/
theorem hamiltonian_mulVec_eq_zero_iff_mem_zeroSpace {Φ : Interaction X T}
    (h0 : ∀ i, 0 ≤ Φ.term i) {Ω : EuclideanSpace ℂ (Config X)} :
    Φ.hamiltonian *ᵥ WithLp.ofLp Ω = 0 ↔ Ω ∈ Φ.zeroSpace :=
  (mem_zeroSpace_iff_hamiltonian_mulVec_eq_zero fun i ↦ nonneg_iff_posSemidef.mp (h0 i)).symm

/-- For positive semidefinite terms, the Hamiltonian of an interaction annihilates a vector
exactly when the operator of every term does. -/
theorem mem_ker_toEuclideanLin_hamiltonian_iff {Φ : Interaction X T}
    (hΦ : ∀ i, (Φ.term i).PosSemidef) {v : EuclideanSpace ℂ (Config X)} :
    v ∈ LinearMap.ker (toEuclideanLin Φ.hamiltonian) ↔ ∀ i, toEuclideanLin (Φ.term i) v = 0 := by
  simp only [LinearMap.mem_ker, toLpLin_apply, WithLp.toLp_eq_zero,
    hamiltonian_mulVec_eq_zero_iff hΦ]

end Interaction

end ManyBody

section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open ManyBody (IsGapped groundSpace PlaneInteraction)
open ManyBody (planeDomainGraph edgeBoundary)
namespace ManyBody
variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ}

/-- **The frustration-free model** (`eq:model` of the frustration-free area-law note,
TNLean `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Setting"): every term
satisfies `0 ≤ h_X ≤ J`, `Ω` is a unit vector, the Hamiltonian is gapped at energy zero with gap
`Δ`, and the zero space of the interaction `ManyBody.Interaction.zeroSpace`, the common kernel of
the terms, is the line through `Ω`. The terms then annihilate `Ω` (`mulVec_eq_zero`), the ground
space at energy zero is the line through `Ω` (`groundSpace_eq`), the interaction is frustration
free in the sense of `ManyBody.Interaction.IsFrustrationFree` (`isFrustrationFree`), and for
`Δ > 0` these are
exactly the conditions `0 ≤ h_X ≤ J`, `h_X Ω = 0`, `‖Ω‖ = 1`, `H ≥ Δ (1 - |Ω⟩⟨Ω|)` of the note
(`iff_model`). -/
structure IsFrustrationFreeGapped (h : PlaneInteraction Λ q R) (J Δ : ℝ)
    (Ω : EuclideanSpace ℂ (↥Λ → Fin q)) :
    Prop where
  /-- Every term is positive semidefinite. -/
  posSemidef : ∀ X, (h.term X).PosSemidef
  /-- Every term is at most `J`. -/
  le_bound : ∀ X, h.term X ≤ J • (1 : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)
  /-- `Ω` is a unit vector. -/
  norm_eq_one : ‖Ω‖ = 1
  /-- The Hamiltonian is gapped at energy zero with gap `Δ`. -/
  isGapped : IsGapped h.hamiltonian 0 Δ
  /-- The zero space of the interaction, the common kernel of the terms, is the line through
  `Ω`. -/
  zeroSpace_eq : h.zeroSpace = Submodule.span ℂ {Ω}

namespace IsFrustrationFreeGapped

variable {h : PlaneInteraction Λ q R} {J Δ : ℝ} {Ω : EuclideanSpace ℂ (↥Λ → Fin q)}

/-- The ground space at energy zero is the line through `Ω`, since for positive terms it is the
zero space of the interaction (`ManyBody.Interaction.zeroSpace_eq_groundSpace`). -/
theorem groundSpace_eq (hff : IsFrustrationFreeGapped h J Δ Ω) :
    groundSpace h.hamiltonian 0 = Submodule.span ℂ {Ω} :=
  (ManyBody.Interaction.zeroSpace_eq_groundSpace hff.posSemidef).symm.trans hff.zeroSpace_eq

/-- The model is a frustration-free interaction: `Ω` is a common ground vector of the terms,
all at energy zero. -/
theorem isFrustrationFree (hff : IsFrustrationFreeGapped h J Δ Ω) : h.IsFrustrationFree := by
  refine ManyBody.Interaction.isFrustrationFree_of_zeroSpace_ne_bot hff.posSemidef ?_
  rw [hff.zeroSpace_eq, Ne, Submodule.span_singleton_eq_bot]
  intro h0
  have h1 := hff.norm_eq_one
  simp [h0] at h1

/-- The gap inequality `H ≥ Δ (1 - |Ω⟩⟨Ω|)` of the note, for `Δ > 0`. -/
theorem gap (hff : IsFrustrationFreeGapped h J Δ Ω) (hΔ : 0 < Δ) :
    (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ h.hamiltonian := by
  have hH : h.hamiltonian.IsHermitian :=
    ManyBody.Interaction.isHermitian_hamiltonian fun X ↦ (hff.posSemidef X).isHermitian
  obtain ⟨-, -, hpsd⟩ := (ManyBody.isGapped_and_groundSpace_eq_span_iff (H := h.hamiltonian)
    (E₀ := 0) hΔ Ω).mpr ⟨hH, hff.norm_eq_one, hff.isGapped, hff.groundSpace_eq⟩
  rw [Matrix.le_iff]
  simpa using hpsd

/-- **Faithfulness of the model.** For `Δ > 0` the model is exactly `eq:model` of the note:
`0 ≤ h_X ≤ J`, `h_X Ω = 0`, `‖Ω‖ = 1` and `H ≥ Δ (1 - |Ω⟩⟨Ω|)`. Source:
TNLean `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Setting". -/
theorem iff_model (hΔ : 0 < Δ) :
    IsFrustrationFreeGapped h J Δ Ω ↔
      (∀ X, (h.term X).PosSemidef) ∧
        (∀ X, h.term X ≤ J • (1 : Matrix (↥Λ → Fin q) (↥Λ → Fin q) ℂ)) ∧
        (∀ X, h.term X *ᵥ WithLp.ofLp Ω = 0) ∧ ‖Ω‖ = 1 ∧
        (Δ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤ h.hamiltonian := by
  refine ⟨fun hff ↦ ⟨hff.posSemidef, hff.le_bound, ManyBody.Interaction.mem_zeroSpace_iff.mp
    (hff.zeroSpace_eq ▸ Submodule.mem_span_singleton_self Ω), hff.norm_eq_one,
    hff.gap hΔ⟩, fun ⟨hpos, hle, hzero, hΩ, hgap⟩ ↦ ?_⟩
  have hiff := (ManyBody.isGapped_and_groundSpace_eq_span_iff (H := h.hamiltonian) (E₀ := 0)
    hΔ Ω).mp ⟨hΩ, ?_, ?_⟩
  · exact ⟨hpos, hle, hΩ, hiff.2.2.1,
      (ManyBody.Interaction.zeroSpace_eq_groundSpace hpos).trans hiff.2.2.2⟩
  · rw [Complex.ofReal_zero, zero_smul]
    change WithLp.toLp 2 (h.hamiltonian *ᵥ WithLp.ofLp Ω) = 0
    rw [(ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff hpos).mpr hzero]
    rfl
  · simpa using Matrix.le_iff.mp hgap

/-- Every term has operator norm at most `J`. -/
theorem norm_term_le (hff : IsFrustrationFreeGapped h J Δ Ω) (hJ : 0 ≤ J) (X) :
    ‖h.term X‖ ≤ J :=
  (CStarAlgebra.norm_le_iff_le_algebraMap _ hJ (hff.posSemidef X).nonneg).mpr
    (by simpa [Algebra.algebraMap_eq_smul_one] using hff.le_bound X)

/-- **The range projections keep the gap.** With `Π_X` the range projection of `h_X`,
`(Δ / J) (1 - |Ω⟩⟨Ω|) ≤ ∑_X Π_X`. Source:
TNLean `docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`, "Contraction in one
sweep", where `∑_i k_i ≥ g (1 - P)` with `g = Δ / J`; here `Π_X ≥ h_X / J`. -/
theorem smul_sub_le_sum_supportProj (hff : IsFrustrationFreeGapped h J Δ Ω) (hJ : 0 < J)
    (hΔ : 0 < Δ) :
    ((Δ / J : ℝ) : ℂ) • (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) ≤
      ∑ X, (hff.posSemidef X).supportProj := by
  have hsum : h.hamiltonian ≤ J • ∑ X, (hff.posSemidef X).supportProj := by
    rw [ManyBody.Interaction.hamiltonian, Finset.smul_sum]
    exact Finset.sum_le_sum fun X _ ↦ (hff.posSemidef X).le_smul_supportProj (hff.le_bound X)
  have h1 := (hff.gap hΔ).trans hsum
  have hJ' : (0 : ℝ) < J⁻¹ := inv_pos.mpr hJ
  have h2 := smul_le_smul_of_nonneg_left h1 hJ'.le
  rw [smul_smul, inv_mul_cancel₀ hJ.ne', one_smul] at h2
  convert h2 using 1
  rw [div_eq_inv_mul, Complex.ofReal_mul, mul_smul, Complex.coe_smul]

end IsFrustrationFreeGapped

end ManyBody
end
