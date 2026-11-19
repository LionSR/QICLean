/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.HermitianHelpers
import QICLean.Algebra.MatrixAux
import QICLean.Analysis.EnergyTruncation
import QICLean.Analysis.GroundEnergyBounds
import QICLean.ManyBody.Hamiltonian.KroneckerSum
import QICLean.ManyBody.Sites.Placement

/-!
# Common ground vectors on disjoint regions

Operators supported on pairwise disjoint regions have a common unit vector attaining all their
minimum eigenvalues. For two complementary regions the cut of the system along the first
writes the operators as `A₀ ⊗ 1` and `1 ⊗ B₀`, and the product of minimizing eigenvectors of
`A₀` and `B₀` is such a vector; for a finite family, induct on the number of regions. The
regional minima stay fixed while any subfamily is clipped: the centered partially clipped sums
are positive, annihilate the common vector, commute with every regional operator, dominate
their high-energy spectral projections, and obey explicit norm budgets after a bounded positive
connecting operator is added.

Moved from TNLean, `TNLean/Lattice/DisjointRegionalGround.lean` at commit `e41c3b63`, restated
on a system of sites with nonempty basis types (in place of `Fin q` at every site with
`0 < q`).

## Main results

* `ManyBody.exists_disjoint_regional_clipping_structure` — one set of regional minima and one
  common vector for every clipping.

## References

* Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Definition 4.3 (`def:hard-trunc`),
  `local_alg_arxiv_v2.tex`, lines 873–886, Corollary `c:goodagsphardtrunc`, lines 979–1005,
  and Theorem `t:ais`, lines 1010–1024.
-/

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] [∀ v, Nonempty (X v)]

/-- A unit eigenvector for the minimum eigenvalue of a Hermitian matrix. -/
private theorem exists_unit_eigenvector_minEigenvalue {γ : Type*} [Fintype γ] [DecidableEq γ]
    [Nonempty γ] {H : Matrix γ γ ℂ} (hH : H.IsHermitian) :
    ∃ (a : ℝ) (u : γ → ℂ), H *ᵥ u = (a : ℂ) • u ∧ star u ⬝ᵥ u = 1 ∧
      (H - (a : ℂ) • 1).PosSemidef := by
  obtain ⟨i, hi⟩ := minEigenvalue_achieved hH
  refine ⟨minEigenvalue hH, ⇑(hH.eigenvectorBasis i), ?_, ?_,
    sub_minEigenvalue_smul_one_posSemidef hH⟩
  · rw [hH.mulVec_eigenvectorBasis, hi]
    simp [Complex.coe_smul]
  · have h := hH.eigenvectorBasis.inner_eq_one i
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    simpa [dotProduct_comm] using h

/-- Hermitian operators supported on a region and on its complement have a common unit vector
attaining both minimum eigenvalues. ALVV, arXiv:1602.08828v2, `def:hard-trunc`,
lines 873–886. -/
private theorem exists_common_unit_ground_of_complementary_support (S : Finset V)
    {A B : Matrix (Config X) (Config X) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAS : A ∈ supportedOperators X S) (hBS : B ∈ supportedOperators X Sᶜ) :
    ∃ (eA eB : ℝ) (x : Config X → ℂ),
      star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (eA : ℂ) • x ∧ B *ᵥ x = (eB : ℂ) • x ∧
      (A - (eA : ℂ) • 1).PosSemidef ∧ (B - (eB : ℂ) • 1).PosSemidef := by
  classical
  set c := cutEquiv X S
  obtain ⟨A₀, rfl⟩ := exists_eq_place_of_mem_supportedOperators hAS
  obtain ⟨B₀, hBe⟩ := exists_eq_one_kronecker_of_mem_supportedOperators (D := S)
    disjoint_compl_left hBS
  have hAe : place S A₀ =
      (A₀ ⊗ₖ (1 : Matrix (ComplConfig X S) (ComplConfig X S) ℂ)).submatrix c c := by
    simp [place, reindex_apply, c]
  have hA₀ : A₀.IsHermitian :=
    place_injective S (by rw [place_conjTranspose, hA.eq])
  let r₀ : RegionConfig X S := fun v ↦ Classical.arbitrary _
  have hB₀ : B₀.IsHermitian := by
    have hK : ((1 : Matrix (RegionConfig X S) (RegionConfig X S) ℂ) ⊗ₖ B₀).IsHermitian := by
      have := hB.submatrix c.symm
      rwa [hBe, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] at this
    refine IsHermitian.ext fun i j ↦ ?_
    simpa only [kroneckerMap_apply, one_apply_eq, one_mul] using hK.apply (r₀, i) (r₀, j)
  obtain ⟨eA, u, hu, hu1, huA⟩ := exists_unit_eigenvector_minEigenvalue hA₀
  obtain ⟨eB, w, hw, hw1, hwB⟩ := exists_unit_eigenvector_minEigenvalue hB₀
  let φ : RegionConfig X S × ComplConfig X S → ℂ := fun p ↦ u p.1 * w p.2
  have hφ : (φ ∘ c) ∘ c.symm = φ := by
    funext p
    simp
  refine ⟨eA, eB, φ ∘ c, ?_, ?_, ?_, ?_, ?_⟩
  · change (star φ) ∘ c ⬝ᵥ φ ∘ c = 1
    rw [comp_equiv_dotProduct_comp_equiv, star_mul_dotProduct_mul, hu1, hw1, one_mul]
  · rw [hAe, submatrix_mulVec_equiv, hφ, kronecker_mulVec_mul, one_mulVec, hu]
    funext σ
    simp only [φ, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [hBe, submatrix_mulVec_equiv, hφ, kronecker_mulVec_mul, one_mulVec, hw]
    funext σ
    simp only [φ, Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · rw [← place_one, ← place_smul, ← place_sub]
    exact posSemidef_place huA
  · have hsplit : B - (eB : ℂ) • 1 =
        ((1 : Matrix (RegionConfig X S) (RegionConfig X S) ℂ) ⊗ₖ
          (B₀ - (eB : ℂ) • 1)).submatrix c c := by
      have hk : (1 : Matrix (RegionConfig X S) (RegionConfig X S) ℂ) ⊗ₖ (B₀ - (eB : ℂ) • 1) =
          (1 : Matrix (RegionConfig X S) (RegionConfig X S) ℂ) ⊗ₖ B₀ - (eB : ℂ) • 1 := by
        ext ⟨i, j⟩ ⟨k, l⟩
        by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]
      rw [hk, hBe]
      ext σ τ
      simp only [Matrix.sub_apply, Matrix.smul_apply, submatrix_apply, one_apply, c.injective.eq_iff, c]
    rw [hsplit]
    exact (PosSemidef.one.kronecker hwB).submatrix c

/-- Hermitian operators on disjoint regions have a common unit vector realizing
their specified attained lower bounds. Auxiliary to ALVV,
arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, and
Corollary `c:goodagsphardtrunc`, lines 979–1005. -/
private theorem exists_common_unit_fixed_ground_of_disjoint_support
    (S T : Finset V) (hST : Disjoint S T)
    (A B : Matrix (Config X) (Config X) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAS : A ∈ supportedOperators X S)
    (hBT : B ∈ supportedOperators X T)
    (a b : ℝ) (xA xB : Config X → ℂ)
    (hAxA : A *ᵥ xA = (a : ℂ) • xA) (hxA : star xA ⬝ᵥ xA = 1)
    (hBxB : B *ᵥ xB = (b : ℂ) • xB) (hxB : star xB ⬝ᵥ xB = 1)
    (hAlow : (A - (a : ℂ) • 1).PosSemidef)
    (hBlow : (B - (b : ℂ) • 1).PosSemidef) :
    ∃ x : Config X → ℂ,
      star x ⬝ᵥ x = 1 ∧ A *ᵥ x = (a : ℂ) • x ∧ B *ᵥ x = (b : ℂ) • x := by
  have hBS : B ∈ supportedOperators X Sᶜ :=
    supportedOperators_mono (Finset.subset_compl_iff_disjoint_left.mpr hST) hBT
  obtain ⟨a', b', x, hx, hAx, hBx, hAlow', hBlow'⟩ :=
    exists_common_unit_ground_of_complementary_support S hA hB hAS hBS
  have ha : a' = a := groundEnergy_eq_of_normalized_eigenvectors A a' a x xA
    hAx hx hAxA hxA hAlow' hAlow
  have hb : b' = b := groundEnergy_eq_of_normalized_eigenvectors B b' b x xB
    hBx hx hBxB hxB hBlow' hBlow
  exact ⟨x, hx, by simpa only [ha] using hAx, by simpa only [hb] using hBx⟩

/-- Original regional operators with pairwise disjoint supports have a
common unit vector attaining their supplied genuine ground energies.
Auxiliary to the three successive truncations in ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005. -/
private theorem exists_common_unit_fixed_ground_of_disjoint_family
    {ι : Type*}
    (s : Finset ι) (R : ι → Finset V)
    (A : ι → Matrix (Config X) (Config X) ℂ) (e : ι → ℝ)
    (hdisj : (s : Set ι).Pairwise fun i j ↦ Disjoint (R i) (R j))
    (hsupp : ∀ i ∈ s, A i ∈ supportedOperators X (R i))
    (hlow : ∀ i ∈ s, (A i - (e i : ℂ) • 1).PosSemidef)
    (hattain : ∀ i ∈ s, ∃ x : Config X → ℂ,
      star x ⬝ᵥ x = 1 ∧ A i *ᵥ x = (e i : ℂ) • x) :
    ∃ x : Config X → ℂ,
      star x ⬝ᵥ x = 1 ∧ ∀ i ∈ s, A i *ᵥ x = (e i : ℂ) • x := by
  classical
  revert hdisj hsupp hlow hattain
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _ _
    refine ⟨Pi.single (Classical.arbitrary (Config X)) (1 : ℂ), ?_, ?_⟩
    · rw [dotProduct_single]
      simp
    · intro i hi
      simp at hi
  | @insert a s ha ih =>
    intro hdisj hsupp hlow hattain
    have hdisjs : (s : Set ι).Pairwise fun i j ↦ Disjoint (R i) (R j) := by
      intro i hi j hj hij
      exact hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_of_mem hj) hij
    obtain ⟨v, hvunit, hv⟩ := ih hdisjs
      (fun i hi ↦ hsupp i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hlow i (Finset.mem_insert_of_mem hi))
      (fun i hi ↦ hattain i (Finset.mem_insert_of_mem hi))
    let S : Finset V := s.biUnion R
    let B : Matrix (Config X) (Config X) ℂ :=
      ∑ i ∈ s, (A i - (e i : ℂ) • 1)
    have hBS : B ∈ supportedOperators X S := by
      apply sum_mem
      intro i hi
      apply sub_mem
      · exact supportedOperators_mono (fun z hz ↦ Finset.mem_biUnion.mpr ⟨i, hi, hz⟩)
          (hsupp i (Finset.mem_insert_of_mem hi))
      · exact SMulMemClass.smul_mem _ (one_mem (supportedOperators _ _))
    have hBpos : B.PosSemidef :=
      posSemidef_sum s (fun i hi ↦ hlow i (Finset.mem_insert_of_mem hi))
    have hvB : B *ᵥ v = (0 : ℂ) • v := by
      change (∑ i ∈ s, (A i - (e i : ℂ) • 1)) *ᵥ v = (0 : ℂ) • v
      rw [sum_mulVec, zero_smul]
      exact Finset.sum_eq_zero fun i hi ↦ by
        rw [sub_mulVec, smul_mulVec, one_mulVec, hv i hi, sub_self]
    have hST : Disjoint S (R a) := by
      apply (Finset.disjoint_biUnion_left s R (R a)).2
      intro i hi
      apply hdisj (Finset.mem_insert_of_mem hi) (Finset.mem_insert_self a s)
      intro hieq
      exact ha (hieq ▸ hi)
    have hAa : (A a).IsHermitian := by
      have hscalar : ((e a : ℂ) • (1 : Matrix (Config X)
          (Config X) ℂ)).IsHermitian := by
        rw [Complex.coe_smul]
        exact (IsSelfAdjoint.smul (IsSelfAdjoint.all (e a))
          (IsSelfAdjoint.one _)).isHermitian
      simpa only [sub_add_cancel] using
        (hlow a (Finset.mem_insert_self a s)).isHermitian.add hscalar
    obtain ⟨xA, hxAunit, hxA⟩ := hattain a (Finset.mem_insert_self a s)
    obtain ⟨w, hwunit, hwB, hwA⟩ := exists_common_unit_fixed_ground_of_disjoint_support
      S (R a) hST B (A a) hBpos.isHermitian hAa hBS
      (hsupp a (Finset.mem_insert_self a s)) 0 (e a) v xA hvB hvunit hxA hxAunit
      (by simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using hBpos)
      (hlow a (Finset.mem_insert_self a s))
    refine ⟨w, hwunit, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hwA
    · have hwBzero : B *ᵥ w = 0 := by simpa only [Complex.ofReal_zero, zero_smul] using hwB
      have hwi : (A i - (e i : ℂ) • 1) *ᵥ w = 0 :=
        PosSemidef.mulVec_eq_zero_of_sum_mulVec_eq_zero_of_mem
          (s := s) (B := fun j ↦ A j - (e j : ℂ) • 1)
          (fun j hj ↦ hlow j (Finset.mem_insert_of_mem hj)) hwBzero hi
      exact sub_eq_zero.mp (by
        simpa only [sub_mulVec, smul_mulVec, one_mulVec] using hwi)

/-- Hermitian operators with pairwise disjoint actual supports have a common
unit vector attaining their genuine ground energies. Auxiliary to ALVV,
arXiv:1602.08828v2, Corollary c:goodagsphardtrunc, lines 979–1005. -/
private theorem exists_common_unit_ground_of_disjoint_family
    {ι : Type*}
    (s : Finset ι) (R : ι → Finset V)
    (A : ι → Matrix (Config X) (Config X) ℂ)
    (hA : ∀ i ∈ s, (A i).IsHermitian)
    (hdisj : (s : Set ι).Pairwise fun i j ↦ Disjoint (R i) (R j))
    (hsupp : ∀ i ∈ s, A i ∈ supportedOperators X (R i)) :
    ∃ (e : ι → ℝ) (x : Config X → ℂ),
      star x ⬝ᵥ x = 1 ∧
        (∀ i ∈ s, A i *ᵥ x = (e i : ℂ) • x) ∧
        ∀ i ∈ s, (A i - (e i : ℂ) • 1).PosSemidef := by
  classical
  have hmin (i : ↥s) :
      ∃ (ei : ℝ) (v : Config X → ℂ),
        A i.val *ᵥ v = (ei : ℂ) • v ∧ star v ⬝ᵥ v = 1 ∧
          (A i.val - (ei : ℂ) • 1).PosSemidef :=
    exists_unit_eigenvector_minEigenvalue (hA i.val i.property)
  let e : ι → ℝ := fun i ↦
    if hi : i ∈ s then Classical.choose (hmin ⟨i, hi⟩) else 0
  have hdata (i : ι) (hi : i ∈ s) :
      ∃ v : Config X → ℂ,
        A i *ᵥ v = (e i : ℂ) • v ∧ star v ⬝ᵥ v = 1 ∧
          (A i - (e i : ℂ) • 1).PosSemidef := by
    simpa [e, hi] using Classical.choose_spec (hmin ⟨i, hi⟩)
  have hlow : ∀ i ∈ s, (A i - (e i : ℂ) • 1).PosSemidef := by
    intro i hi
    obtain ⟨v, _hv, _hunit, hvlow⟩ := hdata i hi
    exact hvlow
  have hattain : ∀ i ∈ s, ∃ v : Config X → ℂ,
      star v ⬝ᵥ v = 1 ∧ A i *ᵥ v = (e i : ℂ) • v := by
    intro i hi
    obtain ⟨v, hv, hunit, _hvlow⟩ := hdata i hi
    exact ⟨v, hunit, hv⟩
  obtain ⟨x, hxunit, hx⟩ := exists_common_unit_fixed_ground_of_disjoint_family
    s R A e hdisj hsupp hlow hattain
  exact ⟨e, x, hxunit, hx, hlow⟩

/-- **One set of regional minima for every clipping.** Let `A i` be supported on pairwise
disjoint regions `R i`, with `0 ≤ A i ≤ c i`, and let `0 ≤ Y ≤ C`. There are real numbers `e i`
and a unit vector `x` with `A i x = e i x` and `A i ≥ e i` for every `i` such that, for every
`t ≥ 0` and every set `T` of indices, `K = ∑ᵢ (Fᵢ - eᵢ)`, with `Fᵢ = min(A i, e i + t)` for
`i ∈ T` and `Fᵢ = A i` otherwise, satisfies: `K ≥ 0`, `K x = 0`, `K` commutes with every `A j`,
`u 1_{[e j + u, ∞)}(A j) ≤ K` for `0 ≤ u ≤ t`, `K + Y ≤ b` and `‖K + Y‖ ≤ b` with
`b = ∑_{i ∈ T} t + ∑_{i ∉ T} c i + C`, and `K + Y` has a unit eigenvector `z` at an eigenvalue
`E ∈ [0, C]` with `K + Y ≥ E`.
ALVV, arXiv:1602.08828v2, `def:hard-trunc`, lines 873–886, Corollary `c:goodagsphardtrunc`,
lines 979–1005, and Theorem `t:ais`, lines 1010–1024. -/
theorem exists_disjoint_regional_clipping_structure
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → Finset V)
    (A : ι → Matrix (Config X) (Config X) ℂ) (c : ι → ℕ)
    (hdisj : Pairwise fun i j ↦ Disjoint (R i) (R j))
    (hsupp : ∀ i, A i ∈ supportedOperators X (R i))
    (hpos : ∀ i, (A i).PosSemidef)
    (hcap : ∀ i, A i ≤ (c i : ℝ) • (1 : Matrix (Config X) (Config X) ℂ))
    (Y : Matrix (Config X) (Config X) ℂ) (C : ℕ)
    (hY : Y.PosSemidef) (hYC : Y ≤ (C : ℝ) • 1) :
    ∃ (e : ι → ℝ) (x : Config X → ℂ),
      star x ⬝ᵥ x = 1 ∧
      (∀ i, A i *ᵥ x = (e i : ℂ) • x) ∧
      (∀ i, (A i - (e i : ℂ) • 1).PosSemidef) ∧
      ∀ (t : ℝ), 0 ≤ t → ∀ T : Finset ι,
        let K := ∑ i, ((if i ∈ T then
          cfc (fun r : ℝ ↦ min r (e i + t)) (A i) else A i) -
            (e i : ℂ) • (1 : Matrix (Config X) (Config X) ℂ))
        K.PosSemidef ∧ K *ᵥ x = 0 ∧
        (∀ j, Commute K (A j)) ∧
        (∀ (j : ι) (u : ℝ), 0 ≤ u → u ≤ t →
          u • spectralProjectionGE (A j) (e j + u) ≤ K) ∧
        (K + Y ≤ ((∑ i, if i ∈ T then t else (c i : ℝ)) + (C : ℝ)) • 1) ∧
        (‖K + Y‖ ≤ (∑ i, if i ∈ T then t else (c i : ℝ)) + (C : ℝ)) ∧
        ∃ (E : ℝ) (z : Config X → ℂ),
          star z ⬝ᵥ z = 1 ∧ (K + Y) *ᵥ z = (E : ℂ) • z ∧
          (K + Y - (E : ℂ) • 1).PosSemidef ∧ 0 ≤ E ∧ E ≤ (C : ℝ) := by
  obtain ⟨e, x, hxunit, hx, helow⟩ := exists_common_unit_ground_of_disjoint_family
    Finset.univ R A (fun i _ ↦ (hpos i).isHermitian)
    (by intro i _ j _ hij; exact hdisj hij) (fun i _ ↦ hsupp i)
  have hxall (i : ι) : A i *ᵥ x = (e i : ℂ) • x := hx i (Finset.mem_univ i)
  have helowall (i : ι) : (A i - (e i : ℂ) • 1).PosSemidef :=
    helow i (Finset.mem_univ i)
  have he (i : ι) : (e i : ℂ) • (1 : Matrix (Config X) (Config X) ℂ) ≤ A i := le_iff.mpr (helowall i)
  have hcomm : Pairwise fun i j ↦ Commute (A i) (A j) := by
    intro i j hij
    exact commute_of_mem_supportedOperators_of_disjoint (hsupp i) (hsupp j) (hdisj hij)
  refine ⟨e, x, hxunit, hxall, helowall, ?_⟩
  intro t ht T K
  obtain ⟨hXpos, hXzero⟩ :=
    centered_partially_clipped_sum_posSemidef_and_mulVec_eq_zero
      A e t T (fun i ↦ (hpos i).isHermitian) he x hxall ht
  obtain ⟨hTotalpos, hTotalcap, hTotalnorm⟩ :=
    centered_partially_clipped_sum_norm_le_budget A e c t T hpos he hcap
      (fun _ ↦ x) hxall (fun _ ↦ hxunit) ht Y C hY hYC
  obtain ⟨E, z, hz, hzunit, hElow⟩ := exists_unit_eigenvector_minEigenvalue hTotalpos.isHermitian
  have hEb := groundEnergy_bounds_of_positive_boundary_and_zero_test
    K Y (C : ℝ) E hXpos hY
    (by simpa only [Complex.coe_smul] using hYC) x z hXzero hxunit hz hzunit hElow
  refine ⟨hXpos, hXzero, ?_, ?_, hTotalcap, hTotalnorm,
    E, z, hzunit, hz, hElow, hEb.1, hEb.2⟩
  · exact fun j ↦ commute_centered_partially_clipped_sum A e t T hcomm j
  · exact fun j u hu hut ↦ spectralProjectionGE_le_centered_partially_clipped_sum
      A e t u T (fun i ↦ (hpos i).isHermitian) he hu hut j
end ManyBody
