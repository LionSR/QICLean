/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.BallNet
import QICLean.Analysis.TensorProductWeights
import QICLean.Probability.ComplexGaussian.RatioTail
import QICLean.Probability.HaarProjection
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Random sampling of a viable subspace

Arad, Landau, Vazirani and Vidick, *Rigorous RG algorithms and area laws for low energy
eigenstates in 1D* (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Lemma `l:rs`, lines 532–547),
show that a random `s`-dimensional subspace `W'` of a `q`-dimensional subspace `W` that is
`δ`-viable for an `r`-dimensional subspace `T` is still `(1 - δ')`-viable for `T`, with
`δ' = (1 - δ) s / (8 q)`, except with a small probability `η`.

The random subspace is the image, under a Haar-random unitary `U` of `ℂ^ι`, of the coordinate
subspace spanned by the basis vectors indexed by a set `A` of `s` coordinates, transported into
`W` by an orthonormal basis `b` of `W` indexed by `ι` (so `q` is the cardinality of `ι`). The
viability of the source (Definition `d:vs`) is stated for `H_L ⊗ H_M ⊗ H_R` with `W ⊆ H_M`; here
it is stated for `M ⊗ F`, with `F` standing for `H_L ⊗ H_R`, which agrees with the source up to
the associator and the swap of the first two factors.

The proof follows the source. For a unit vector `v ∈ T`, the projection `w` of `v` onto `W ⊗ F`
has `‖w‖² ≥ 1 - δ`, and `‖P_{W' ⊗ F} v‖² = ∑_k μ_k ‖P_{W'} f_k‖²` for an orthonormal basis `f_k`
of `W` and weights `μ_k ≥ 0` summing to `‖w‖²`. Each `‖P_{W'} f_k‖²` exceeds `s / (2q)` except
with probability `e^{-s/16}`, by the Haar–Gaussian identity and the Gaussian lower tail. A union
bound over a `√δ'`-net of the unit sphere of `T` and over the `q` vectors `f_k` gives
`‖P_{W' ⊗ F} v‖² ≥ 4 δ'` on the net, and then `‖P_{W' ⊗ F} t‖² ≥ δ'` on the whole unit sphere.

**Local fix (failure probability of Lemma `l:rs`):** the source prints
`η = (1 + 4 √(q / ((1 - δ) s)))^r q e^{-s/16}`. The volume net of the unit sphere of the complex
`r`-dimensional space `T`, a real space of dimension `2r`, at scale `ν = √((1 - δ) s / (8q))` has
at most `(1 + 2/ν)^{2r}` points, and `2/ν = 4 √2 √(q / ((1 - δ) s))`, so the argument as written
gives `η = (1 + 2/ν)^{2r} q e^{-s/16}`, which is the bound proved here. The area laws use only
that `η < 1` for large `s`, which is unaffected. Documented in
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`.

## Main statements

* `Submodule.starProjection_map_linearIsometry`: projections commute with linear isometries.
* `Submodule.isCloseTo_of_net`: the deterministic net step.
* `Submodule.randomSubspace`, `Submodule.finrank_randomSubspace`: the random subspace `W'`, of
  dimension `s`.
* `Submodule.unitaryHaar_not_isViable_randomSubspace_le`: Lemma `l:rs`, with the corrected `η`.
* `Submodule.exists_isViable_randomSubspace`: some `W'` is viable when `η < 1`.
-/

open MeasureTheory Matrix Module Real
open scoped TensorProduct InnerProductSpace ENNReal

namespace Submodule

section Deterministic

variable {𝕜 E M : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup M] [InnerProductSpace 𝕜 M]

/-- The orthogonal projection onto the image of a subspace under a linear isometry `e` (not
necessarily surjective) is conjugate to the projection onto the subspace: `P_{e K} (e x) =
e (P_K x)`. -/
theorem starProjection_map_linearIsometry (e : E →ₗᵢ[𝕜] M) (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] [(K.map e.toLinearMap).HasOrthogonalProjection] (x : E) :
    (K.map e.toLinearMap).starProjection (e x) = e (K.starProjection x) := by
  refine eq_starProjection_of_mem_of_inner_eq_zero ⟨_, K.starProjection_apply_mem x, rfl⟩ ?_
  rintro _ ⟨y, hy, rfl⟩
  change ⟪e x - e (K.starProjection x), e y⟫_𝕜 = 0
  rw [← map_sub, LinearIsometry.inner_map_map]
  exact inner_left_of_mem_orthogonal hy (K.sub_starProjection_mem_orthogonal x)

/-- **The net step of Lemma `l:rs`.** If every unit vector of `T` lies within `√c` of a vector
`v ∈ T` with `‖P_S v‖² ≥ 4c`, then `‖P_S t‖² ≥ c ‖t‖²` for every `t ∈ T`, that is, `S` is
`(1 - c)`-close to `T`. Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, the last sentence
of the proof of Lemma `l:rs` (lines 545–546). -/
theorem isCloseTo_of_net [FiniteDimensional 𝕜 E] {S T : Submodule 𝕜 E}
    [S.HasOrthogonalProjection] {c : ℝ} (hc : 0 ≤ c)
    (hnet : ∀ t ∈ T, ‖t‖ = 1 →
      ∃ v ∈ T, ‖t - v‖ ≤ √c ∧ 4 * c ≤ ‖S.starProjection v‖ ^ 2) :
    IsCloseTo (1 - c) S T := by
  rw [isCloseTo_iff]
  intro t ht
  rw [sub_sub_cancel]
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  have hn : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  set u : E := ((‖t‖⁻¹ : ℝ) : 𝕜) • t with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  obtain ⟨v, -, hdist, hv⟩ := hnet u (T.smul_mem _ ht) hu1
  have h2 : 2 * √c ≤ ‖S.starProjection v‖ := by
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp ?_
    rw [mul_pow, sq_sqrt hc]
    linarith
  have hPu : √c ≤ ‖S.starProjection u‖ := by
    have h1 : ‖S.starProjection v‖ ≤ ‖S.starProjection u‖ + ‖u - v‖ := by
      calc ‖S.starProjection v‖ = ‖S.starProjection u - S.starProjection (u - v)‖ := by
            rw [map_sub, sub_sub_cancel]
        _ ≤ ‖S.starProjection u‖ + ‖S.starProjection (u - v)‖ := norm_sub_le _ _
        _ ≤ ‖S.starProjection u‖ + ‖u - v‖ := by
            gcongr
            exact S.norm_starProjection_apply_le _
    linarith
  have hcu : c ≤ ‖S.starProjection u‖ ^ 2 := by
    calc c = √c ^ 2 := (sq_sqrt hc).symm
      _ ≤ ‖S.starProjection u‖ ^ 2 := by gcongr
  have hPt : ‖S.starProjection t‖ = ‖t‖ * ‖S.starProjection u‖ := by
    rw [hu, map_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, ← mul_assoc,
      mul_inv_cancel₀ hn.ne', one_mul]
  rw [hPt, mul_pow, mul_comm c]
  gcongr

omit [InnerProductSpace 𝕜 E] in
/-- `S ⊗ F` is monotone in `S`. -/
theorem tensorProd_mono_left {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    {S S' : Submodule 𝕜 M} (h : S ≤ S') (R : Submodule 𝕜 F) :
    S.tensorProd R ≤ S'.tensorProd R := by
  have : TensorProduct.map S.subtype R.subtype =
      TensorProduct.map S'.subtype R.subtype ∘ₗ TensorProduct.map (inclusion h) LinearMap.id := by
    rw [← TensorProduct.map_comp]
    rfl
  unfold tensorProd
  rw [this]
  exact LinearMap.range_comp_le_range _ _

end Deterministic

section RandomSubspace

open QICLean.HaarProjection

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  {W : Submodule ℂ M} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The linear isometry `ℂ^ι → M` onto `W` given by an orthonormal basis `b` of `W`. -/
noncomputable def basisEmbedding (b : OrthonormalBasis ι ℂ W) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] M :=
  W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry

omit [FiniteDimensional ℂ M] [DecidableEq ι] in
theorem basisEmbedding_mem (b : OrthonormalBasis ι ℂ W) (x : EuclideanSpace ℂ ι) :
    basisEmbedding b x ∈ W :=
  (b.repr.symm x).2

/-- The random subspace of Lemma `l:rs`: the image of the coordinate subspace of `A` under the
unitary `U`, carried into `W` by the orthonormal basis `b`. For `U` distributed by the Haar
measure it is a uniformly random subspace of `W` of dimension `#A`. -/
noncomputable def randomSubspace (b : OrthonormalBasis ι ℂ W) (A : Finset ι)
    (U : unitaryGroup ι ℂ) : Submodule ℂ M :=
  ((coordinateSubspace A).map (unitaryAction U).toLinearEquiv.toLinearMap).map
    (basisEmbedding b).toLinearMap

omit [FiniteDimensional ℂ M] in
theorem randomSubspace_le (b : OrthonormalBasis ι ℂ W) (A : Finset ι) (U : unitaryGroup ι ℂ) :
    randomSubspace b A U ≤ W := by
  rintro _ ⟨x, -, rfl⟩
  exact basisEmbedding_mem b x

omit [FiniteDimensional ℂ M] in
/-- The random subspace has dimension `#A`. -/
theorem finrank_randomSubspace (b : OrthonormalBasis ι ℂ W) (A : Finset ι)
    (U : unitaryGroup ι ℂ) : finrank ℂ (randomSubspace b A U) = A.card := by
  have hli : LinearIndependent ℂ fun i : (A : Set ι) => EuclideanSpace.single (i : ι) (1 : ℂ) := by
    have h := (EuclideanSpace.basisFun ι ℂ).toBasis.linearIndependent.comp
      (fun i : (A : Set ι) => (i : ι)) Subtype.coe_injective
    simpa [Function.comp_def, EuclideanSpace.basisFun_apply] using h
  rw [randomSubspace, ← (equivMapOfInjective _ (basisEmbedding b).injective _).finrank_eq,
    LinearEquiv.finrank_map_eq, coordinateSubspace, Set.image_eq_range,
    finrank_span_eq_card hli]
  simp

/-- **One vector.** For a unit vector `f ∈ W`, the squared norm of its projection onto the
random subspace is at most `#A / (2 #ι)` with Haar probability at most `e^{-#A/16}`.
Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, the concentration step in the proof of
Lemma `l:rs` (lines 539–541). -/
theorem unitaryHaar_norm_sq_starProjection_randomSubspace_le (b : OrthonormalBasis ι ℂ W)
    (A : Finset ι) {f : M} (hf : f ∈ W) (hf1 : ‖f‖ = 1) :
    unitaryHaar ι {U | ‖(randomSubspace b A U).starProjection f‖ ^ 2 ≤
        A.card / (2 * Fintype.card ι)} ≤ ENNReal.ofReal (rexp (-(A.card / 16))) := by
  set x : EuclideanSpace ℂ ι := b.repr ⟨f, hf⟩
  have hfx : basisEmbedding b x = f := by simp [basisEmbedding, x]
  have hx : ‖x‖ = 1 := by
    rw [← (basisEmbedding b).norm_map, hfx, hf1]
  have hset : {U : unitaryGroup ι ℂ | ‖(randomSubspace b A U).starProjection f‖ ^ 2 ≤
        A.card / (2 * Fintype.card ι)} =
      {U | ‖((coordinateSubspace A).map
        (unitaryAction U).toLinearEquiv.toLinearMap).starProjection x‖ ^ 2 ≤
          A.card / (2 * Fintype.card ι)} := by
    ext U
    simp only [Set.mem_ofPred_eq, randomSubspace]
    rw [← hfx, starProjection_map_linearIsometry, LinearIsometry.norm_map]
  rw [hset, unitaryHaar_norm_sq_starProjection_le A _ hx]
  exact QICLean.ComplexGaussian.measure_sum_norm_coordinate_sq_le_le A

/-- **Lemma `l:rs` (random sampling), with the corrected failure probability.** Let `W ⊆ M` have
the orthonormal basis `b` indexed by `ι`, with `q = #ι`, let `A ⊆ ι` have `s` elements, and let
`W ⊆ M` be `δ`-viable for `T ⊆ M ⊗ F` with `r = dim T`. Put
`δ' = (1 - δ) s / (8 q)` and `ν = √δ'`. For a Haar-random unitary `U`, the random
`s`-dimensional subspace `W' = randomSubspace b A U` of `W` fails to be `(1 - δ')`-viable for
`T` with probability at most `η = (1 + 2/ν)^{2r} q e^{-s/16}`. For `δ ≥ 1` the parameter `δ'` is
at most `0`, every subspace is `(1 - δ')`-viable, and the bound holds trivially.

Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2, Lemma `l:rs` (lines 532–547), with
`H_L ⊗ H_R` grouped into `F` (Definition `d:vs` up to the associator and the swap of factors).

**Local fix (failure probability of Lemma `l:rs`):** the source prints
`η = (1 + 4 √(q / ((1 - δ) s)))^r q e^{-s/16}`, undercounting the net of the unit sphere of the
real `2r`-dimensional space `T`; see `docs/paper-gaps/alvv16_random_sampling_net_count.tex`. -/
theorem unitaryHaar_not_isViable_randomSubspace_le (b : OrthonormalBasis ι ℂ W) (A : Finset ι)
    {δ : ℝ} {T : Submodule ℂ (M ⊗[ℂ] F)} (hT : IsViable δ W T) :
    unitaryHaar ι {U | ¬ IsViable (1 - (1 - δ) * A.card / (8 * Fintype.card ι))
        (randomSubspace b A U) T} ≤
      ENNReal.ofReal ((1 + 2 / √((1 - δ) * A.card / (8 * Fintype.card ι))) ^
        (2 * finrank ℂ T) * Fintype.card ι * rexp (-(A.card / 16))) := by
  set s : ℝ := (A.card : ℝ)
  set q : ℝ := (Fintype.card ι : ℝ)
  set c : ℝ := (1 - δ) * s / (8 * q) with hc_def
  rcases le_or_gt c 0 with hc | hc
  · -- `c ≤ 0`, that is `δ ≥ 1`: every subspace is `(1 - c)`-viable
    have hempty : {U | ¬ IsViable (1 - c) (randomSubspace b A U) T} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun U hU => hU ?_
      refine isCloseTo_iff.mpr fun t _ => ?_
      rw [sub_sub_cancel]
      exact (mul_nonpos_of_nonpos_of_nonneg hc (sq_nonneg _)).trans (sq_nonneg _)
    rw [hempty, measure_empty]
    exact bot_le
  have hc0 : 0 ≤ c := hc.le
  -- the weights of the projection of a vector `v` onto `W ⊗ F`
  have hwmem (v : M ⊗[ℂ] F) :
      (W.tensorProd (⊤ : Submodule ℂ F)).starProjection v ∈ W.tensorProd ⊤ :=
    starProjection_apply_mem _ v
  choose f μ hμ0 hμsum hμ using fun v => exists_weights_norm_sq_starProjection_tensorProd W
    (hwmem v)
  -- the net of the unit sphere of `T`
  set ν : ℝ := √c
  have hν : 0 < ν := sqrt_pos.mpr hc
  obtain ⟨C, hCsub, hCcard, hCnet⟩ := Metric.exists_finset_net_of_subset_closedBall hν
    (A := {t : T | ‖t‖ = 1}) fun t ht => mem_closedBall_zero_iff.mpr (le_of_eq ht)
  rw [finrank_real_of_complex] at hCcard
  have hq : finrank ℂ W = Fintype.card ι := finrank_eq_card_basis b.toBasis
  -- the bad event is covered by the bad events of the net points and basis vectors
  have hcover : {U | ¬ IsViable (1 - c) (randomSubspace b A U) T} ⊆
      ⋃ v ∈ C, ⋃ k, {U | ‖(randomSubspace b A U).starProjection (f (v : M ⊗[ℂ] F) k : M)‖ ^ 2
        ≤ s / (2 * q)} := by
    intro U hU
    by_contra hgood
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists, not_le] at hgood
    refine hU (isCloseTo_of_net hc0 fun t ht ht1 => ?_)
    obtain ⟨v, hvC, hdist⟩ := hCnet ⟨t, ht⟩ ht1
    have hv1 : ‖(v : M ⊗[ℂ] F)‖ = 1 := by
      have := hCsub hvC
      simpa using this
    refine ⟨v, v.2, by simpa [dist_eq_norm] using hdist, ?_⟩
    set w := (W.tensorProd (⊤ : Submodule ℂ F)).starProjection (v : M ⊗[ℂ] F)
    have hle : (randomSubspace b A U).tensorProd (⊤ : Submodule ℂ F) ≤ W.tensorProd ⊤ :=
      tensorProd_mono_left (randomSubspace_le b A U) ⊤
    have hPw : ((randomSubspace b A U).tensorProd (⊤ : Submodule ℂ F)).starProjection
        (v : M ⊗[ℂ] F) = ((randomSubspace b A U).tensorProd ⊤).starProjection w := by
      rw [← ContinuousLinearMap.comp_apply, starProjection_comp_starProjection_of_le hle]
    have hw : 1 - δ ≤ ‖w‖ ^ 2 := by
      have := (isCloseTo_iff.mp hT) _ v.2
      rwa [hv1, one_pow, mul_one] at this
    rw [hPw, hμ _ _ (randomSubspace_le b A U)]
    calc 4 * c ≤ s / (2 * q) * ‖w‖ ^ 2 := by
          have h4c : 4 * c = s / (2 * q) * (1 - δ) := by
            rw [hc_def]
            ring
          rw [h4c]
          gcongr
      _ = ∑ k, μ (v : M ⊗[ℂ] F) k * (s / (2 * q)) := by
          rw [← Finset.sum_mul, hμsum, mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (hgood v hvC k).le
            (hμ0 _ k)
  calc _ ≤ _ := measure_mono hcover
    _ ≤ ∑ v ∈ C, ∑ k, unitaryHaar ι {U | ‖(randomSubspace b A U).starProjection
          (f (v : M ⊗[ℂ] F) k : M)‖ ^ 2 ≤ s / (2 * q)} :=
        (measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun v _ => measure_iUnion_fintype_le _ _)
    _ ≤ ∑ _v ∈ C, ∑ _k : Fin (finrank ℂ W), ENNReal.ofReal (rexp (-(s / 16))) := by
        gcongr with v _ k
        exact unitaryHaar_norm_sq_starProjection_randomSubspace_le b A (f _ k).2
          (by rw [norm_coe]; exact (f (v : M ⊗[ℂ] F)).orthonormal.1 k)
    _ = ENNReal.ofReal (C.card * q * rexp (-(s / 16))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
        simp [Finset.sum_const, hq, mul_assoc]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by gcongr)

/-- **Existence form of Lemma `l:rs`.** When the failure probability
`η = (1 + 2/ν)^{2r} q e^{-s/16}` of `unitaryHaar_not_isViable_randomSubspace_le` is less than
`1`, some unitary `U` makes the `s`-dimensional subspace `randomSubspace b A U` of `W`
`(1 - δ')`-viable for `T`, with `δ' = (1 - δ) s / (8 q)`. This is the form used by the area-law
arguments of arXiv:1602.08828v2. -/
theorem exists_isViable_randomSubspace (b : OrthonormalBasis ι ℂ W) (A : Finset ι) {δ : ℝ}
    {T : Submodule ℂ (M ⊗[ℂ] F)} (hT : IsViable δ W T)
    (hη : (1 + 2 / √((1 - δ) * A.card / (8 * Fintype.card ι))) ^ (2 * finrank ℂ T) *
      Fintype.card ι * rexp (-(A.card / 16)) < 1) :
    ∃ U : unitaryGroup ι ℂ,
      IsViable (1 - (1 - δ) * A.card / (8 * Fintype.card ι)) (randomSubspace b A U) T := by
  by_contra h
  push Not at h
  have h1 := (measure_mono (μ := unitaryHaar ι) fun U (_ : U ∈ Set.univ) => h U).trans
    (unitaryHaar_not_isViable_randomSubspace_le b A hT)
  rw [measure_univ] at h1
  exact lt_irrefl _ (h1.trans_lt (ENNReal.ofReal_lt_one.mpr hη))

end RandomSubspace

end Submodule
