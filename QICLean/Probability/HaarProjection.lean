/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.UnitaryHaar
import QICLean.Probability.ComplexGaussian.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Projection of a unit vector onto a Haar-random coordinate subspace

Arad, Landau, Vazirani and Vidick, *Rigorous RG algorithms and area laws for low energy
eigenstates in 1D* (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Lemma `l:rs`, lines 532–547),
choose a uniformly random subspace of a fixed dimension and bound the squared norm of the
projection of a fixed unit vector onto it by "a standard concentration argument". This module
supplies the distributional identity that reduces the random subspace to Gaussian coordinates.

Let `W₀` be the span of the standard basis vectors indexed by a finite set `A`, let `U` be
distributed by the Haar probability measure on the unitary group, and let `x` be a unit vector.
The random subspace `U W₀` satisfies `‖P_{U W₀} x‖² = ∑_{i ∈ A} |(Uᴴ x)_i|²`, and for every real
`c` the probability that this is at most `c` equals the probability that
`∑_{i ∈ A} |g_i|² ≤ c ∑_i |g_i|²` for independent standard circular complex Gaussians `g_i`.

The proof uses Tonelli's theorem on the product of the unitary group and `ℂ^ι` with the standard
Gaussian measure: the Gaussian is invariant under every unitary, the Haar measure is invariant
under left multiplication, and the event is invariant under nonzero scalings.

## Main declarations

* `QICLean.HaarProjection.unitaryHaar_sum_norm_sq_le` — the distributional identity.
* `QICLean.HaarProjection.norm_sq_starProjection_map_coordinateSubspace` — the squared weight
  of `Uᴴ x` on `A` is the squared norm of the projection of `x` onto `U W₀`.
* `QICLean.HaarProjection.unitaryHaar_norm_sq_starProjection_le` — the identity stated for the
  projection onto the random subspace `U W₀`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace QICLean.HaarProjection

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The cone of vectors whose squared weight on `A` is at most `c` times their squared norm. -/
def weightCone (A : Finset ι) (c : ℝ) : Set (ι → ℂ) :=
  {v | ∑ i ∈ A, ‖v i‖ ^ 2 ≤ c * ∑ i, ‖v i‖ ^ 2}

theorem isClosed_weightCone (A : Finset ι) (c : ℝ) : IsClosed (weightCone A c) :=
  isClosed_le (by fun_prop) (by fun_prop)

/-- The weight cone is invariant under nonzero complex scalings. -/
theorem smul_mem_weightCone_iff (A : Finset ι) (c : ℝ) {a : ℂ} (ha : a ≠ 0) (v : ι → ℂ) :
    a • v ∈ weightCone A c ↔ v ∈ weightCone A c := by
  have hpos : 0 < ‖a‖ ^ 2 := by positivity
  simp only [weightCone, Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    ← Finset.mul_sum]
  rw [mul_left_comm c]
  exact mul_le_mul_iff_of_pos_left hpos

/-- The standard Gaussian measure on a nonzero real inner product space has no atom at the
origin. -/
theorem stdGaussian_singleton_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {a : E} (ha : a ≠ 0) :
    stdGaussian E {0} = 0 := by
  have hm : Measurable (ComplexGaussian.realField a) := by
    unfold ComplexGaussian.realField; fun_prop
  have hv : (‖a‖₊ ^ 2 : NNReal) ≠ 0 := by simpa using ha
  have := nullSingletonClass_gaussianReal (μ := 0) hv
  refine measure_mono_null (t := ComplexGaussian.realField a ⁻¹' {0}) ?_ ?_
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    simp [hy, ComplexGaussian.realField]
  · rw [← Measure.map_apply hm (measurableSet_singleton 0), ComplexGaussian.realField_law,
      measure_singleton]

/-- The real coordinates `(g (i, 0), g (i, 1))` assembled into the complex vector with entries
`g (i, 0) + g (i, 1) i`; a real linear isometry. -/
def sampleEquiv : ComplexGaussian.Sample ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι where
  toFun g := WithLp.toLp 2 fun i ↦ (g (i, 0) : ℂ) + (g (i, 1) : ℂ) * Complex.I
  invFun y := WithLp.toLp 2 fun p ↦ if p.2 = 0 then (y p.1).re else (y p.1).im
  map_add' g h := by
    ext i
    simp only [PiLp.add_apply, Complex.ofReal_add]
    ring
  map_smul' a g := by
    ext i
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, RingHom.id_apply,
      Complex.real_smul]
    ring
  left_inv g := by
    ext ⟨i, j⟩
    fin_cases j <;> simp
  right_inv y := by
    ext i
    apply Complex.ext <;> simp
  norm_map' g := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), EuclideanSpace.norm_sq_eq,
      EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    simp [Fin.sum_univ_two, Complex.sq_norm, Complex.normSq_add_mul_I]

/-- The circular complex coordinates are the complexified sample divided by `√2`. -/
theorem coordinate_eq (g : ComplexGaussian.Sample ι) :
    (fun i ↦ ComplexGaussian.coordinate i g) =
      ((Real.sqrt 2 : ℂ)⁻¹) • (sampleEquiv g).ofLp := by
  ext i
  simp [ComplexGaussian.coordinate_apply, sampleEquiv, div_eq_inv_mul, mul_comm Complex.I]

/-- The law of the complexified Gaussian sample is the standard Gaussian on `ℂ^ι`. -/
theorem law_map_sampleEquiv :
    (ComplexGaussian.law ι).map sampleEquiv = stdGaussian (EuclideanSpace ℂ ι) :=
  stdGaussian_map _

variable [DecidableEq ι]

/-- The action of a unitary matrix on Euclidean space, as a linear isometry. -/
def unitaryAction (U : unitaryGroup ι ℂ) : EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  Unitary.linearIsometryEquiv
    ⟨toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : Matrix ι ι ℂ), Unitary.map_mem _ U.2⟩

theorem ofLp_unitaryAction (U : unitaryGroup ι ℂ) (y : EuclideanSpace ℂ ι) :
    (unitaryAction U y).ofLp = (U : Matrix ι ι ℂ) *ᵥ y.ofLp := rfl

/-- The action of `Uᴴ` on Euclidean space, as a real linear isometry. -/
def starAction (U : unitaryGroup ι ℂ) : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  { (unitaryAction U⁻¹).toLinearEquiv.restrictScalars ℝ with
    norm_map' := (unitaryAction U⁻¹).norm_map }

theorem ofLp_starAction (U : unitaryGroup ι ℂ) (y : EuclideanSpace ℂ ι) :
    (starAction U y).ofLp = star (U : Matrix ι ι ℂ) *ᵥ y.ofLp := rfl

/-- A unitary matrix carries any unit vector to any other. -/
theorem exists_unitary_mulVec_eq {x z : EuclideanSpace ℂ ι} (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) :
    ∃ V : unitaryGroup ι ℂ, (V : Matrix ι ι ℂ) *ᵥ x.ofLp = z.ofLp := by
  have : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp [Subsingleton.elim x 0] at hx
  obtain ⟨i₀⟩ := this
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι := finrank_euclideanSpace
  have hon {w : EuclideanSpace ℂ ι} (hw : ‖w‖ = 1) :
      Orthonormal ℂ (({i₀} : Set ι).domRestrict fun _ ↦ w) :=
    ⟨fun _ ↦ hw, fun i j hij ↦ (hij (Subsingleton.elim i j)).elim⟩
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hon hx)
  obtain ⟨b', hb'⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hon hz)
  let f := b.repr.trans b'.repr.symm
  have hf : f x = z := by
    rw [← hb i₀ rfl, ← hb' i₀ rfl]
    simp [f]
  let u := Unitary.linearIsometryEquiv.symm f
  refine ⟨⟨(toEuclideanCLM (n := ι) (𝕜 := ℂ)).symm
    (u : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι), Unitary.map_mem _ u.2⟩, ?_⟩
  rw [← ofLp_toEuclideanCLM]
  simp only [StarAlgEquiv.apply_symm_apply]
  exact congrArg WithLp.ofLp hf

/-- The Haar measure of `{U | Uᴴ y ∈ K}` is the same for every nonzero `y` and every unit `x`,
when `K` is the weight cone: rotate `y / ‖y‖` to `x` and use left invariance. -/
theorem unitaryHaar_weightCone_eq_of_ne_zero (A : Finset ι) (c : ℝ) {x y : EuclideanSpace ℂ ι}
    (hx : ‖x‖ = 1) (hy : y ≠ 0) :
    unitaryHaar ι {U | star (U : Matrix ι ι ℂ) *ᵥ y.ofLp ∈ weightCone A c} =
      unitaryHaar ι {U | star (U : Matrix ι ι ℂ) *ᵥ x.ofLp ∈ weightCone A c} := by
  set r : ℂ := (‖y‖ : ℂ) with hr_def
  have hr : r ≠ 0 := by simpa [r] using hy
  have hz : ‖r⁻¹ • y‖ = 1 := by
    simp [r, norm_smul, hy]
  obtain ⟨V, hV⟩ := exists_unitary_mulVec_eq hx hz
  have hy' : y.ofLp = r • ((V : Matrix ι ι ℂ) *ᵥ x.ofLp) := by
    rw [hV, WithLp.ofLp_smul, smul_smul, mul_inv_cancel₀ hr, one_smul]
  have hset : {U : unitaryGroup ι ℂ | star (U : Matrix ι ι ℂ) *ᵥ y.ofLp ∈ weightCone A c} =
      (fun U ↦ V⁻¹ * U) ⁻¹'
        {U | star (U : Matrix ι ι ℂ) *ᵥ x.ofLp ∈ weightCone A c} := by
    ext U
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [hy', mulVec_smul, smul_mem_weightCone_iff _ _ hr, mulVec_mulVec]
    simp [star_mul]
  rw [hset, measure_preimage_mul]

/-- The Haar probability that `Uᴴ x` lies in the weight cone equals the standard Gaussian
probability of the weight cone in `ℂ^ι`, regarded as a real inner product space. The proof
integrates the indicator of `{(U, y) | Uᴴ y ∈ K}` in both orders: for fixed `U`, the Gaussian is
invariant under `Uᴴ`; for fixed `y ≠ 0`, the Haar probability does not depend on `y`. -/
theorem unitaryHaar_weightCone_eq_stdGaussian (A : Finset ι) (c : ℝ) {x : EuclideanSpace ℂ ι}
    (hx : ‖x‖ = 1) :
    unitaryHaar ι {U | star (U : Matrix ι ι ℂ) *ᵥ x.ofLp ∈ weightCone A c} =
      stdGaussian (EuclideanSpace ℂ ι) {y | y.ofLp ∈ weightCone A c} := by
  set μ := stdGaussian (EuclideanSpace ℂ ι)
  set K := weightCone A c
  have hKc := isClosed_weightCone A c
  let T : Set (unitaryGroup ι ℂ × EuclideanSpace ℂ ι) :=
    {p | star (p.1 : Matrix ι ι ℂ) *ᵥ p.2.ofLp ∈ K}
  have hT : MeasurableSet T := (hKc.preimage (by fun_prop)).measurableSet
  have hK : MeasurableSet {y : EuclideanSpace ℂ ι | y.ofLp ∈ K} :=
    (hKc.preimage (by fun_prop)).measurableSet
  have key := lintegral_lintegral_swap (μ := unitaryHaar ι) (ν := μ)
    (f := fun U y ↦ T.indicator 1 (U, y)) ((measurable_one.indicator hT).aemeasurable)
  have h1 (U : unitaryGroup ι ℂ) :
      ∫⁻ y, T.indicator 1 (U, y) ∂μ = μ {y | y.ofLp ∈ K} := by
    have hU : (fun y ↦ T.indicator (1 : unitaryGroup ι ℂ × EuclideanSpace ℂ ι → ℝ≥0∞) (U, y)) =
        (starAction U ⁻¹' {y | y.ofLp ∈ K}).indicator 1 := by
      ext y
      rfl
    rw [hU, lintegral_indicator_one (hK.preimage (starAction U).continuous.measurable),
      ← Measure.map_apply (starAction U).continuous.measurable hK, stdGaussian_map]
  have h2 (y : EuclideanSpace ℂ ι) (hy : y ≠ 0) :
      ∫⁻ U, T.indicator 1 (U, y) ∂unitaryHaar ι =
        unitaryHaar ι {U | star (U : Matrix ι ι ℂ) *ᵥ x.ofLp ∈ K} := by
    have hy' : (fun U ↦ T.indicator (1 : unitaryGroup ι ℂ × EuclideanSpace ℂ ι → ℝ≥0∞) (U, y)) =
        {U : unitaryGroup ι ℂ | star (U : Matrix ι ι ℂ) *ᵥ y.ofLp ∈ K}.indicator 1 := by
      ext U
      rfl
    have hm : MeasurableSet {U : unitaryGroup ι ℂ | star (U : Matrix ι ι ℂ) *ᵥ y.ofLp ∈ K} :=
      (hKc.preimage (by fun_prop)).measurableSet
    rw [hy', lintegral_indicator_one hm,
      unitaryHaar_weightCone_eq_of_ne_zero A c hx hy]
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hnull : μ {0} = 0 := stdGaussian_singleton_zero hx0
  have h3 : ∫⁻ y, ∫⁻ U, T.indicator 1 (U, y) ∂unitaryHaar ι ∂μ =
      unitaryHaar ι {U | star (U : Matrix ι ι ℂ) *ᵥ x.ofLp ∈ K} := by
    rw [lintegral_congr_ae (g := fun _ ↦ unitaryHaar ι
      {U | star (U : Matrix ι ι ℂ) *ᵥ x.ofLp ∈ K}) ?_]
    · simp
    · filter_upwards [compl_mem_ae_iff.mpr hnull] with y hy using h2 y hy
  rw [← h3, ← key]
  simp [h1]

/-- **Projection onto a Haar-random coordinate subspace.** For a unit vector `x`, the squared
weight of `Uᴴ x` on a fixed set of coordinates `A`, with `U` Haar distributed, has the law of
`∑_{i ∈ A} |g_i|² / ∑_i |g_i|²` for independent standard circular complex Gaussians `g_i`. -/
theorem unitaryHaar_sum_norm_sq_le (A : Finset ι) (c : ℝ) {x : EuclideanSpace ℂ ι}
    (hx : ‖x‖ = 1) :
    unitaryHaar ι {U | ∑ i ∈ A, ‖(star (U : Matrix ι ι ℂ) *ᵥ x.ofLp) i‖ ^ 2 ≤ c} =
      ComplexGaussian.law ι {g | ∑ i ∈ A, ‖ComplexGaussian.coordinate i g‖ ^ 2 ≤
        c * ∑ i, ‖ComplexGaussian.coordinate i g‖ ^ 2} := by
  have hL : {U : unitaryGroup ι ℂ |
      ∑ i ∈ A, ‖(star (U : Matrix ι ι ℂ) *ᵥ x.ofLp) i‖ ^ 2 ≤ c} =
      {U : unitaryGroup ι ℂ | star (U : Matrix ι ι ℂ) *ᵥ x.ofLp ∈ weightCone A c} := by
    ext U
    have hn : ∑ i, ‖(star (U : Matrix ι ι ℂ) *ᵥ x.ofLp) i‖ ^ 2 = 1 := by
      have h := EuclideanSpace.norm_sq_eq (starAction U x)
      rw [(starAction U).norm_map, hx, one_pow] at h
      exact h.symm
    simp [weightCone, hn]
  have hR : {g : ComplexGaussian.Sample ι | ∑ i ∈ A, ‖ComplexGaussian.coordinate i g‖ ^ 2 ≤
      c * ∑ i, ‖ComplexGaussian.coordinate i g‖ ^ 2} =
      sampleEquiv ⁻¹' {y | y.ofLp ∈ weightCone A c} := by
    ext g
    change (fun i ↦ ComplexGaussian.coordinate i g) ∈ weightCone A c ↔ _
    rw [coordinate_eq, smul_mem_weightCone_iff _ _ (by simp)]
    rfl
  have hK : MeasurableSet {y : EuclideanSpace ℂ ι | y.ofLp ∈ weightCone A c} :=
    ((isClosed_weightCone A c).preimage (by fun_prop)).measurableSet
  rw [hL, hR, ← Measure.map_apply sampleEquiv.continuous.measurable hK, law_map_sampleEquiv,
    unitaryHaar_weightCone_eq_stdGaussian A c hx]

/-- The coordinate subspace spanned by the standard basis vectors indexed by `A`. -/
def coordinateSubspace (A : Finset ι) : Submodule ℂ (EuclideanSpace ℂ ι) :=
  Submodule.span ℂ ((fun i ↦ EuclideanSpace.single i (1 : ℂ)) '' (A : Set ι))

/-- The orthogonal projection onto a coordinate subspace keeps the coordinates in `A` and
discards the others. -/
theorem starProjection_coordinateSubspace (A : Finset ι) (v : EuclideanSpace ℂ ι) :
    (coordinateSubspace A).starProjection v =
      WithLp.toLp 2 fun i ↦ if i ∈ A then v i else 0 := by
  have hp : (WithLp.toLp 2 fun i ↦ if i ∈ A then v i else 0 : EuclideanSpace ℂ ι) =
      ∑ i ∈ A, v i • EuclideanSpace.single i (1 : ℂ) := by
    ext j
    simp [Pi.single_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun w hw ↦ ?_
  · rw [hp]
    exact Submodule.sum_mem _ fun i hi ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨i, hi, rfl⟩ := hw
      simp [EuclideanSpace.inner_single_right, Finset.mem_coe.mp hi]
    | zero => simp
    | add w w' _ _ h h' => rw [inner_add_right, h, h', add_zero]
    | smul a w _ h => rw [inner_smul_right, h, mul_zero]

/-- The squared norm of the projection onto a coordinate subspace is the squared weight on its
coordinates. -/
theorem norm_sq_starProjection_coordinateSubspace (A : Finset ι) (v : EuclideanSpace ℂ ι) :
    ‖(coordinateSubspace A).starProjection v‖ ^ 2 = ∑ i ∈ A, ‖v i‖ ^ 2 := by
  rw [starProjection_coordinateSubspace, EuclideanSpace.norm_sq_eq]
  simp [apply_ite, Finset.sum_ite_mem]

/-- The squared weight of `Uᴴ x` on the coordinates `A` is the squared norm of the projection of
`x` onto the image under `U` of the coordinate subspace of `A`. -/
theorem norm_sq_starProjection_map_coordinateSubspace (A : Finset ι) (U : unitaryGroup ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    ‖((coordinateSubspace A).map (unitaryAction U).toLinearEquiv.toLinearMap).starProjection x‖
        ^ 2 = ∑ i ∈ A, ‖(star (U : Matrix ι ι ℂ) *ᵥ x.ofLp) i‖ ^ 2 := by
  rw [Submodule.starProjection_map_apply, LinearIsometryEquiv.norm_map,
    norm_sq_starProjection_coordinateSubspace]
  have h : ((unitaryAction U).symm x).ofLp = star (U : Matrix ι ι ℂ) *ᵥ x.ofLp := by
    change (star (toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : Matrix ι ι ℂ)) x).ofLp = _
    rw [← map_star]
    rfl
  rw [h]

/-- `unitaryHaar_sum_norm_sq_le` for the projection onto the Haar-random subspace `U W₀`, where
`W₀` is the coordinate subspace of `A`. -/
theorem unitaryHaar_norm_sq_starProjection_le (A : Finset ι) (c : ℝ) {x : EuclideanSpace ℂ ι}
    (hx : ‖x‖ = 1) :
    unitaryHaar ι {U | ‖((coordinateSubspace A).map
        (unitaryAction U).toLinearEquiv.toLinearMap).starProjection x‖ ^ 2 ≤ c} =
      ComplexGaussian.law ι {g | ∑ i ∈ A, ‖ComplexGaussian.coordinate i g‖ ^ 2 ≤
        c * ∑ i, ‖ComplexGaussian.coordinate i g‖ ^ 2} := by
  simp_rw [norm_sq_starProjection_map_coordinateSubspace]
  exact unitaryHaar_sum_norm_sq_le A c hx

end

end QICLean.HaarProjection
