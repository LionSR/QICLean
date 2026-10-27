/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Channel.MaximalOverlap

/-!
# Unit approximations from viable subspaces

Let `S ⊆ ℂ^σ` be `δ`-viable for a target `T ⊆ ℂ^σ ⊗ ℂ^β`, with `δ < 1`.
Every unit target vector has a unit approximant in `S ⊗ ℂ^β` with squared
overlap at least `1 - δ` and Schmidt rank at most `dim S`. Consequently,
the leading `dim S` eigenvalues of its reduced density matrix retain at
least `1 - δ` of its mass. These are the individual-vector consequences
used in ALVV, arXiv:1602.08828v2, Definitions `d:vs` and `d:close`, and
the proof of Theorem `thm:al-dg`, lines 1080–1094 of the checked source.

A specified isometry from an original Hilbert space to the product
coordinates carries the approximating vector back to that space. The
Schmidt rank is measured in those specified coordinates. In particular,
the isometry can be the configuration splitting at a chain cut.

## Main results

* `Submodule.IsViable.exists_unit_mem_prodExt_schmidtRank_le`: a unit
  approximant with squared overlap at least `1 - δ` and rank at most `dim S`.
* `Submodule.IsViable.one_sub_le_kyFanNorm`: the corresponding lower bound
  on the leading eigenvalue mass of the reduced state.
* `Submodule.IsViable.exists_unit_schmidtRank_le_of_equiv`: the unit
  approximant in the original Hilbert space under a specified cut isometry.
-/

open scoped BigOperators TensorProduct InnerProductSpace ComplexOrder

namespace Submodule

/-- Every unit vector in a subspace approximated with squared error `δ < 1`
has a unit approximant in the approximating subspace with squared overlap at
least `1 - δ`. The approximant is its normalized orthogonal projection.
This is the vector interpretation of ALVV, arXiv:1602.08828v2,
Definition `d:close`, lines 469–474, and Definition `d:vs`, lines 433–440. -/
private theorem IsCloseTo.exists_unit_mem_norm_inner_sq_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {δ : ℝ} {S T : Submodule ℂ E}
    (h : IsCloseTo δ S T) (hδ : δ < 1) {ψ : E} (hψT : ψ ∈ T) (hψ : ‖ψ‖ = 1) :
    ∃ φ : E, φ ∈ S ∧ ‖φ‖ = 1 ∧ 1 - δ ≤ ‖⟪φ, ψ⟫_ℂ‖ ^ 2 := by
  let p := S.starProjection ψ
  have hproj : 1 - δ ≤ ‖p‖ ^ 2 := by
    simpa only [hψ, one_pow, mul_one] using isCloseTo_iff.mp h ψ hψT
  have hp : 0 < ‖p‖ := by nlinarith [norm_nonneg p]
  refine ⟨((‖p‖⁻¹ : ℝ) : ℂ) • p,
    S.smul_mem _ (S.starProjection_apply_mem ψ), ?_, ?_⟩
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos hp,
      inv_mul_cancel₀ hp.ne']
  · have hpp : ⟪p, ψ⟫_ℂ = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
      have he : S.starProjection p = p :=
        S.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem ψ)
      have hinner : ⟪p, ψ⟫_ℂ = ⟪p, p⟫_ℂ := by
        calc
          ⟪p, ψ⟫_ℂ = ⟪S.starProjection p, ψ⟫_ℂ := by rw [he]
          _ = ⟪p, S.starProjection ψ⟫_ℂ := S.inner_starProjection_left_eq_right _ _
      rw [hinner, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have hoverlap : ‖⟪((‖p‖⁻¹ : ℝ) : ℂ) • p, ψ⟫_ℂ‖ = ‖p‖ := by
      rw [inner_smul_left, hpp, Complex.conj_ofReal, ← Complex.ofReal_mul,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg p)) (sq_nonneg ‖p‖))]
      rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul]
    simpa only [hoverlap] using hproj

/-- A vector whose coefficient columns lie in a finite-dimensional subspace
has Schmidt rank at most the dimension of that subspace. This is the
coordinate rank bound used in ALVV, arXiv:1602.08828v2, proof of Theorem
`thm:al-dg`, local `local_alg_arxiv_v2.tex` lines 1080–1089.
The vector need not be normalized or nonzero. -/
private theorem schmidtRank_le_finrank_of_mem_prodExt
    {σ β : Type*} [Finite σ] [Fintype β]
    (S : Submodule ℂ (EuclideanSpace ℂ σ))
    {φ : EuclideanSpace ℂ (σ × β)} (hφ : φ ∈ prodExt S β) :
    Matrix.schmidtRank (WithLp.ofLp φ) ≤ Module.finrank ℂ S := by
  classical
  let := Fintype.ofFinite σ
  rw [Matrix.schmidtRank_eq_finrank_range_toEuclideanLin]
  apply Submodule.finrank_mono
  rintro _ ⟨v, rfl⟩
  have hsum :
      Matrix.toEuclideanLin (Matrix.schmidtCoeffMatrix (WithLp.ofLp φ)) v =
        ∑ b : β, v b • (WithLp.toLp 2 (fun a : σ ↦ φ (a, b)) :
          EuclideanSpace ℂ σ) := by
    ext a
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
      dotProduct, Matrix.schmidtCoeffMatrix, mul_comm]
  rw [hsum]
  exact S.sum_mem fun b _ ↦ S.smul_mem (v b) ((mem_prodExt.mp hφ) b)

variable {σ β : Type*} [Fintype σ] [Fintype β]

/-- A unit vector in a target approximated by the coordinate extension of `S`
has a unit approximant of Schmidt rank at most `dim S`. The squared overlap
is at least `1 - δ`. This is the individual-vector consequence of ALVV,
arXiv:1602.08828v2, Definitions `d:vs` and `d:close`, used in the proof of
Theorem `thm:al-dg`, lines 1080–1094 of the checked source. -/
private theorem IsCloseTo.exists_unit_mem_prodExt_schmidtRank_le
    {δ : ℝ} {S : Submodule ℂ (EuclideanSpace ℂ σ)}
    {T : Submodule ℂ (EuclideanSpace ℂ (σ × β))}
    (h : IsCloseTo δ (prodExt S β) T) (hδ : δ < 1)
    {ψ : EuclideanSpace ℂ (σ × β)} (hψT : ψ ∈ T) (hψ : ‖ψ‖ = 1) :
    ∃ φ : EuclideanSpace ℂ (σ × β), φ ∈ prodExt S β ∧ ‖φ‖ = 1 ∧
      1 - δ ≤ ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ∧
      Matrix.schmidtRank (WithLp.ofLp φ) ≤ Module.finrank ℂ S := by
  obtain ⟨φ, hφS, hφ, hoverlap⟩ :=
    h.exists_unit_mem_norm_inner_sq_ge hδ hψT hψ
  exact ⟨φ, hφS, hφ, hoverlap, schmidtRank_le_finrank_of_mem_prodExt S hφS⟩

variable [DecidableEq σ] [DecidableEq β]

/-- The tensor-product form of the preceding individual-vector consequence
of ALVV, arXiv:1602.08828v2, Definition `d:vs` and Theorem `thm:al-dg`,
lines 1080–1094. The input vector has the actual product coordinates, and
its image in the tensor product belongs to the target. No choice of a
Schmidt decomposition is an input. -/
theorem IsViable.exists_unit_mem_prodExt_schmidtRank_le
    {δ : ℝ} {S : Submodule ℂ (EuclideanSpace ℂ σ)}
    {T : Submodule ℂ (EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β)}
    (h : IsViable δ S T) (hδ : δ < 1)
    {ψ : EuclideanSpace ℂ (σ × β)}
    (hψT : euclideanTensorEquiv σ β ψ ∈ T) (hψ : ‖ψ‖ = 1) :
    ∃ φ : EuclideanSpace ℂ (σ × β), φ ∈ prodExt S β ∧ ‖φ‖ = 1 ∧
      1 - δ ≤ ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ∧
      Matrix.schmidtRank (WithLp.ofLp φ) ≤ Module.finrank ℂ S := by
  let U := T.comap ((euclideanTensorEquiv σ β).toLinearEquiv :
    EuclideanSpace ℂ (σ × β) →ₗ[ℂ]
      EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β)
  have hU : U.map ((euclideanTensorEquiv σ β).toLinearEquiv :
      EuclideanSpace ℂ (σ × β) →ₗ[ℂ]
        EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β) = T :=
    map_comap_eq_of_surjective (euclideanTensorEquiv σ β).surjective T
  have hclose : IsCloseTo δ (prodExt S β) U :=
    (isCloseTo_prodExt_iff_isViable S U).mpr (by rw [hU]; exact h)
  exact hclose.exists_unit_mem_prodExt_schmidtRank_le hδ
    (show ψ ∈ U from hψT) hψ

/-- A viable subspace retains at least `1 - δ` in the leading `dim S`
eigenvalues of the marginal of every unit target vector. This combines
ALVV, arXiv:1602.08828v2, Definition `d:vs` and the proof of Theorem
`thm:al-dg`, lines 1080–1094, with the maximal-overlap characterization
of Schmidt rank (Wolf, Chapter 3, Lemma 3.1). -/
theorem IsViable.one_sub_le_kyFanNorm
    {δ : ℝ} {S : Submodule ℂ (EuclideanSpace ℂ σ)}
    {T : Submodule ℂ (EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β)}
    (h : IsViable δ S T) (hδ : δ < 1)
    {ψ : EuclideanSpace ℂ (σ × β)}
    (hψT : euclideanTensorEquiv σ β ψ ∈ T) (hψ : ‖ψ‖ = 1) :
    1 - δ ≤
      (Matrix.posSemidef_self_mul_conjTranspose
        (Matrix.schmidtCoeffMatrix (WithLp.ofLp ψ))).isHermitian.kyFanNorm
          (Module.finrank ℂ S) := by
  obtain ⟨φ, _, hφ, hoverlap, hrank⟩ :=
    h.exists_unit_mem_prodExt_schmidtRank_le hδ hψT hψ
  calc
    1 - δ ≤ ‖⟪φ, ψ⟫_ℂ‖ ^ 2 := hoverlap
    _ = ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by rw [norm_inner_symm]
    _ ≤ _ := Matrix.normSq_inner_le_kyFanNorm ψ φ hφ (Module.finrank ℂ S) hrank

/-- A product-coordinate isometry carries the viable-subspace approximation
back to the original Hilbert space. In particular, the isometry may be the
configuration splitting at an actual chain cut. This is the unit-vector
approximation step of ALVV, arXiv:1602.08828v2, Theorem `thm:al-dg`,
lines 1080–1094; the rank is measured in the specified cut coordinates. -/
theorem IsViable.exists_unit_schmidtRank_le_of_equiv
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (σ × β))
    {δ : ℝ} {S : Submodule ℂ (EuclideanSpace ℂ σ)} {T : Submodule ℂ E}
    (h : IsViable δ S (T.map
      ((e.trans (euclideanTensorEquiv σ β)).toLinearEquiv :
        E →ₗ[ℂ] EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β)))
    (hδ : δ < 1) {ψ : E} (hψT : ψ ∈ T) (hψ : ‖ψ‖ = 1) :
    ∃ φ : E, ‖φ‖ = 1 ∧ e φ ∈ prodExt S β ∧
      1 - δ ≤ ‖⟪φ, ψ⟫_ℂ‖ ^ 2 ∧
      Matrix.schmidtRank (WithLp.ofLp (e φ)) ≤ Module.finrank ℂ S := by
  have hmem : euclideanTensorEquiv σ β (e ψ) ∈ T.map
      ((e.trans (euclideanTensorEquiv σ β)).toLinearEquiv :
        E →ₗ[ℂ] EuclideanSpace ℂ σ ⊗[ℂ] EuclideanSpace ℂ β) :=
    ⟨ψ, hψT, rfl⟩
  obtain ⟨φ, hφS, hφ, hoverlap, hrank⟩ :=
    h.exists_unit_mem_prodExt_schmidtRank_le hδ hmem
      (by simpa only [LinearIsometryEquiv.norm_map] using hψ)
  refine ⟨e.symm φ, ?_, ?_, ?_, ?_⟩
  · simpa only [LinearIsometryEquiv.norm_map] using hφ
  · simpa only [LinearIsometryEquiv.apply_symm_apply] using hφS
  · have hinner : ⟪e.symm φ, ψ⟫_ℂ = ⟪φ, e ψ⟫_ℂ := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (e.inner_map_map (e.symm φ) ψ).symm
    simpa only [hinner] using hoverlap
  · simpa only [LinearIsometryEquiv.apply_symm_apply] using hrank

end Submodule
