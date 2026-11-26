/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Filter.Gaussian.MatrixIntegral
import QICLean.ManyBody.Dynamics.GraphLocalization
import QICLean.ManyBody.Dynamics.HeisenbergEvolution
import QICLean.ManyBody.Dynamics.Interaction
import QICLean.ManyBody.Dynamics.MetricGraph
import QICLean.ManyBody.Hamiltonian.GaussianFilter
import QICLean.ManyBody.Sites.Twirl

/-!
# Locality of Gaussian-filtered terms

If the Heisenberg evolution `W(t) = e^{iHt} W e^{-iHt}` nearly commutes with an operator `O`
for all times `|t| ≤ T`, so does the Gaussian-filtered operator `W_tilde`, up to the Gaussian
mass of the times `|t| > T`, where the commutator is bounded crudely by `2 ‖W‖ ‖O‖`. The same
splitting of the filter integral localizes `W_tilde` by a region expectation. By the Duhamel
formula the change `W_tilde - W` made by the filter is nearly supported near the support of
`[H, W]`, with the first-moment Gaussian tail in place of the Gaussian mass.

For an interaction `Φ : Interaction X T` of Hermitian terms on a finite graph, with supports of
diameter at most `R` and at most `v_R` sites and a per-site budget `b₀`, the Lieb–Robinson
bounds of `ManyBody.Dynamics` supply the commutator and localization inputs: `W_tilde` is
approximated on the graph neighbourhood of the support of `W`. If the supports are single sites
(in a metric space, balls of radius zero), the terms commute and filtering fixes each of them.

**Local fix (the approximation `M_i`, eq. `mid`):** the supported approximation of `W_tilde` is its
region expectation onto the `l`-neighbourhood of the support of `W`, not the source's evolution
of `H_i` under the terms within distance `l_proj - R` of `i`; the source radius requires
`l = l_proj - R`, the constants are not identified with the source's, and the Gaussian weight
printed in eq. `mid` as `exp[-(tΔE)²/2]` is read as the weight `exp[-(tΔE)²/(2q)]` of eq.
`thd`. Documented in `docs/paper-gaps/hastings05_filtered_term_approximation.tex`. The source's
own truncated filter is in `ManyBody.Hamiltonian.GaussianFilterTruncation`.

**Scope restriction (geometric growth):** the region-expectation approximation on a graph
assumes polynomial sphere growth with size-independent constants, which source lines 169–190
do not impose; the metric version without growth hypothesis is in
`ManyBody.Hamiltonian.GaussianFilterMetric`. See
`docs/paper-gaps/hastings05_geometric_growth_scope.tex`.

**Local fix (error of the localized parts, arXiv:0705.2024v4, lines 816–828):** the source
prints `‖M_L - H_L‖ ≤ O(ΔE⁻¹ J² e^{-l/3ξ})`, which cannot hold in general; the next step needs
`‖M_L - H_tilde_L‖` small, which is what the increment estimate proves, with `M_L - H_L` supported
near the cut. Documented in `docs/paper-gaps/hastings07_filtered_part_localization.tex`.

## Main results

* `ManyBody.norm_commutator_gaussianFilteredTerm_le`,
  `ManyBody.norm_sub_regionExpectation_gaussianFilteredTerm_le` — eqs. `lbnd` and `apb` with the
  Lieb–Robinson input as a hypothesis.
* `ManyBody.norm_heisenbergEvolution_sub_sub_regionExpectation_le` — localization of the
  Heisenberg increment.
* `ManyBody.norm_gaussianFilteredTerm_sub_localized_le`,
  `ManyBody.norm_gaussianFilteredTerm_sub_self_le` — the change made by the filter.
* `ManyBody.norm_commutator_gaussianFilteredTerm_le_graphDistance`,
  `ManyBody.exists_local_approx_gaussianFilteredTerm` — the graph estimates for an interaction.
* `ManyBody.gaussianFilteredTerm_sum_eq_of_zero_range` — zero-range terms are fixed.

## References

* Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`:
  the setting at lines 169–190, eq. `lbnd` (lines 266–283, proved at lines 1419–1456), eqs.
  `mid`, `odef`, `hpdef`, `apb` (lines 285–320), eq. `facld` (lines 322–348).
* Hastings, *An area law for one-dimensional quantum systems*, arXiv:0705.2024v4, appendix,
  `law16.tex` lines 794–828.

Moved from TNLean, `TNLean/Lattice/GaussianFilteredLocality.lean`,
`GaussianFilteredIncrement.lean`, `GaussianFilteredTermLocalization.lean`,
`GaussianZeroRange.lean` and the localization lemma of `HeisenbergDuhamel.lean` at commit
`e113e005`. Changes: an interaction `Φ : Interaction X T` on any system of sites in place of a
family of terms with supports on `ι → Fin d`, so the hypotheses `[NeZero d]` and the support
hypothesis are gone; the time cutoff is written `τ` where the supports are `T`; the increment
localization is stated with `ManyBody.heisenbergEvolution`; the sharp tail is
`GaussianFilter.measure_compl_Icc_le`.
-/

open GaussianFilter Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal

namespace ManyBody

section FilterLocality

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Splitting the filter integral at `|t| = T`.** For a continuous linear map `L` on
matrices, if `‖L W(t)‖ ≤ ε` for `|t| ≤ T` and `‖L W(t)‖ ≤ C` for all `t`, then `‖L W_tilde‖` is at
most `ε` plus `C` times the Gaussian mass of the complement of `[-T, T]`. -/
theorem norm_map_gaussianFilteredTerm_le_mass (q ΔE : ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (W : Matrix n n ℂ) (L : Matrix n n ℂ →L[ℂ] Matrix n n ℂ)
    {T ε C : ℝ} (hε : 0 ≤ ε)
    (hloc : ∀ t ∈ Set.Icc (-T) T,
      ‖L (hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t))‖ ≤ ε)
    (hglob : ∀ t, ‖L (hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t))‖ ≤ C) :
    ‖L (gaussianFilteredTerm q ΔE H W)‖ ≤
      ε + C * (gaussianReal 0 (q / ΔE ^ 2).toNNReal).real (Set.Icc (-T) T)ᶜ := by
  set μ := gaussianReal 0 (q / ΔE ^ 2).toNNReal
  set f : ℝ → Matrix n n ℂ := fun t =>
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t)
  have hint : Integrable f μ := integrable_intertwinerIntegrand _ hH hH W
  rw [gaussianFilteredTerm, gaussianIntertwiner, ← L.integral_comp_comm hint,
    ← integral_add_compl (s := Set.Icc (-T) T) measurableSet_Icc (L.integrable_comp hint)]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_setIntegral_le_of_norm_le_const (μ := μ) (by finiteness) hloc)
    (norm_setIntegral_le_of_norm_le_const (μ := μ) (by finiteness) (fun t _ => hglob t))).trans ?_
  exact add_le_add (mul_le_of_le_one_right hε measureReal_le_one) le_rfl

/-- If `‖[W(t), O]‖ ≤ ε` for all `|t| ≤ T`, then `‖[W_tilde, O]‖` is at most `ε` plus `2 ‖W‖ ‖O‖`
times the Gaussian mass of the complement of `[-T, T]`. Hastings, arXiv:cond-mat/0508554v3,
proof of eq. `lbnd`, lines 1419–1456. -/
theorem norm_commutator_gaussianFilteredTerm_le_mass (q ΔE : ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (W O : Matrix n n ℂ) {T ε : ℝ} (hε : 0 ≤ ε)
    (hloc : ∀ t ∈ Set.Icc (-T) T,
      ‖hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) * O -
          O * (hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t))‖ ≤ ε) :
    ‖gaussianFilteredTerm q ΔE H W * O - O * gaussianFilteredTerm q ΔE H W‖ ≤
      ε + 2 * ‖W‖ * ‖O‖ *
        (gaussianReal 0 (q / ΔE ^ 2).toNNReal).real (Set.Icc (-T) T)ᶜ := by
  have := norm_map_gaussianFilteredTerm_le_mass q ΔE hH W (GaussianFilter.commutatorCLM O) hε
    (C := 2 * ‖W‖ * ‖O‖) (fun t ht => by
      rw [GaussianFilter.commutatorCLM_apply, norm_sub_rev]
      exact hloc t ht) fun t => by
      set f := hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t)
      rw [GaussianFilter.commutatorCLM_apply]
      calc ‖O * f - f * O‖ ≤ ‖O * f‖ + ‖f * O‖ := norm_sub_le _ _
        _ ≤ ‖O‖ * ‖f‖ + ‖f‖ * ‖O‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = 2 * ‖W‖ * ‖O‖ := by rw [norm_intertwinerIntegrand hH hH W t]; ring
  rw [norm_sub_rev]
  simpa only [GaussianFilter.commutatorCLM_apply] using this

/-- **Localization of a filtered term by partial trace.** If the normalized partial trace onto
`K` approximates `W(t)` within `ε` for all `|t| ≤ T`, then it approximates `W_tilde` within `ε` plus
`2 ‖W‖` times the Gaussian mass of the complement of `[-T, T]`. The approximant
`regionExpectation K W_tilde` acts on `K`
(`regionExpectation_mem_supportedOperators`) and has norm at most `‖W‖`
(`norm_regionExpectation_le`, `norm_gaussianFilteredTerm_le`).

This replaces the truncated dynamics of Hastings' `M_i`, arXiv:cond-mat/0508554v3, eqs. `mid`,
`odef` (lines 285–320) and eq. `truncb` (lines 1507–1522), by the partial trace. -/
theorem norm_sub_regionExpectation_gaussianFilteredTerm_le_mass {V : Type*} [Fintype V]
    [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] (q ΔE : ℝ)
    {H : Matrix (Config X) (Config X) ℂ}
    (hH : H.IsHermitian) (W : Matrix (Config X) (Config X) ℂ) (K : Finset V) {T ε : ℝ}
    (hε : 0 ≤ ε)
    (hloc : ∀ t ∈ Set.Icc (-T) T,
      ‖hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) -
          regionExpectation K
            (hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t))‖ ≤ ε) :
    ‖gaussianFilteredTerm q ΔE H W -
        regionExpectation K (gaussianFilteredTerm q ΔE H W)‖ ≤
      ε + 2 * ‖W‖ * (gaussianReal 0 (q / ΔE ^ 2).toNNReal).real (Set.Icc (-T) T)ᶜ := by
  set L := ContinuousLinearMap.id ℂ _ -
    regionExpectationCLM (X := X) K
  have hL : ∀ M, L M = M - regionExpectation K M := fun _ => rfl
  have := norm_map_gaussianFilteredTerm_le_mass q ΔE hH W L hε (C := 2 * ‖W‖)
    (by simpa only [hL] using hloc) fun t => by
      set f := hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t)
      rw [hL]
      calc ‖f - regionExpectation K f‖
          ≤ ‖f‖ + ‖regionExpectation K f‖ := norm_sub_le _ _
        _ ≤ ‖f‖ + ‖f‖ := by gcongr; exact (norm_regionExpectation_le (D := K) f)
        _ = 2 * ‖W‖ := by rw [norm_intertwinerIntegrand hH hH W t]; ring
  simpa only [hL] using this

/-- **Locality of a filtered term.** If `‖[W(t), O]‖ ≤ ε` for all `|t| ≤ T`, then
`‖[W_tilde, O]‖ ≤ ε + 2 ‖W‖ ‖O‖ exp(-(T ΔE)²/(2q))`. With the Lieb–Robinson bound
`ε = ‖W‖ ‖O‖ g(T, l)` and `T = c₁ l`, this is Hastings, arXiv:cond-mat/0508554v3, eq. `lbnd`
(lines 266–283), proved at lines 1419–1456. -/
theorem norm_commutator_gaussianFilteredTerm_le {q ΔE : ℝ} (hq : 0 ≤ q) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (W O : Matrix n n ℂ) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hloc : ∀ t ∈ Set.Icc (-T) T,
      ‖hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) * O -
          O * (hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t))‖ ≤ ε) :
    ‖gaussianFilteredTerm q ΔE H W * O - O * gaussianFilteredTerm q ΔE H W‖ ≤
      ε + 2 * ‖W‖ * ‖O‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  refine (norm_commutator_gaussianFilteredTerm_le_mass q ΔE hH W O hε hloc).trans ?_
  gcongr
  exact measure_compl_Icc_le_div_sq hq hT

/-- **Localization of a filtered term.** If the normalized partial trace onto `K` approximates
`W(t)` within `ε` for all `|t| ≤ T`, then it approximates `W_tilde` within
`ε + 2 ‖W‖ exp(-(T ΔE)²/(2q))`. This is the bound of Hastings, arXiv:cond-mat/0508554v3,
eq. `apb` (lines 300–320) for the partial-trace localization in place of the truncated
dynamics of eq. `mid`. -/
theorem norm_sub_regionExpectation_gaussianFilteredTerm_le {V : Type*} [Fintype V]
    [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] {q ΔE : ℝ}
    (hq : 0 ≤ q)
    {H : Matrix (Config X) (Config X) ℂ} (hH : H.IsHermitian)
    (W : Matrix (Config X) (Config X) ℂ) (K : Finset V) {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hloc : ∀ t ∈ Set.Icc (-T) T,
      ‖hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) -
          regionExpectation K
            (hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t))‖ ≤ ε) :
    ‖gaussianFilteredTerm q ΔE H W -
        regionExpectation K (gaussianFilteredTerm q ΔE H W)‖ ≤
      ε + 2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  refine (norm_sub_regionExpectation_gaussianFilteredTerm_le_mass q ΔE hH W K hε hloc).trans ?_
  gcongr
  exact measure_compl_Icc_le_div_sq hq hT

end FilterLocality

section HeisenbergIncrement

variable {V : Type*} [Fintype V] [DecidableEq V]
    {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- **Localization of the Heisenberg increment.** If every Duhamel integrand
`τ_s(i(HA - AH))`, for `s` between `0` and `t`, is within `ε` of its region expectation onto
`K`, then so is the increment `τ_t(A) - A`, up to the factor `|t|`.
Use site: Hastings, arXiv:0705.2024v4, appendix, `law16.tex` lines 816–828. -/
theorem norm_heisenbergEvolution_sub_sub_regionExpectation_le
    {H A : Matrix (Config X) (Config X) ℂ} (K : Finset V) {t ε : ℝ}
    (hloc : ∀ s ∈ Set.uIcc 0 t,
      ‖heisenbergEvolution H s (Complex.I • (H * A - A * H)) -
        regionExpectation K (heisenbergEvolution H s (Complex.I • (H * A - A * H)))‖ ≤ ε) :
    ‖(heisenbergEvolution H t A - A) - regionExpectation K (heisenbergEvolution H t A - A)‖ ≤
      ε * |t| := by
  let L := ContinuousLinearMap.id ℂ _ - regionExpectationCLM (X := X) K
  have hL (B : Matrix (Config X) (Config X) ℂ) : L B = B - regionExpectation K B := rfl
  have hcont : Continuous (fun s : ℝ => heisenbergEvolution H s
      (Complex.I • (H * A - A * H))) := by
    have := continuous_hermitianUnitaryPath H
    simp only [heisenbergEvolution]
    fun_prop
  rw [← hL (heisenbergEvolution H t A - A), heisenbergEvolution_sub_eq_integral,
    ← L.intervalIntegral_comp_comm (hcont.intervalIntegrable (μ := MeasureTheory.volume) 0 t)]
  simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := ε) fun s hs => (hL _).symm ▸ hloc s (Set.uIoc_subset_uIcc hs)

end HeisenbergIncrement

section IncrementSites

variable {V : Type*} [Fintype V] [DecidableEq V]
    {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- **Localizing the change made by the filter.** Suppose the evolved commutator
`C(s) = τ_s(i[H, W])` is within `ε` of its partial trace onto `K` for `|s| ≤ T`. Then
`M = W + E_K(W_tilde - W)` satisfies
`‖W_tilde - M‖ ≤ T ε + 2 ‖[H, W]‖ ∫_{|t| > T} |t| dμ`, where `μ` is the Gaussian of the filter.
For `|t| > T` the increment `τ_t(W) - W` is bounded by `|t| ‖[H, W]‖` (Duhamel), so the bound
involves only the commutator `[H, W]` and not `W` itself.
Hastings, arXiv:0705.2024v4, appendix, lines 816–828. -/
theorem norm_gaussianFilteredTerm_sub_localized_le_mass (q ΔE : ℝ)
    {H : Matrix (Config X) (Config X) ℂ} (hH : H.IsHermitian)
    (W : Matrix (Config X) (Config X) ℂ) (K : Finset V) {T ε : ℝ} (hT : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hloc : ∀ s ∈ Set.Icc (-T) T,
      ‖hermitianUnitaryPath H s * (Complex.I • (H * W - W * H)) * hermitianUnitaryPath H (-s) -
        regionExpectation K
          (hermitianUnitaryPath H s * (Complex.I • (H * W - W * H)) *
            hermitianUnitaryPath H (-s))‖ ≤ ε) :
    ‖gaussianFilteredTerm q ΔE H W -
        (W + regionExpectation K (gaussianFilteredTerm q ΔE H W - W))‖ ≤
      T * ε + 2 * ‖H * W - W * H‖ *
        ∫ t in (Set.Icc (-T) T)ᶜ, |t| ∂(gaussianReal 0 (q / ΔE ^ 2).toNNReal) := by
  set μ := gaussianReal 0 (q / ΔE ^ 2).toNNReal
  set c := ‖H * W - W * H‖
  set f : ℝ → Matrix (Config X) (Config X) ℂ := fun t =>
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) - W
  set L := ContinuousLinearMap.id ℂ _ -
    regionExpectationCLM (X := X) K
  have hL : ∀ M, L M = M - regionExpectation K M := fun _ => rfl
  have hint0 := integrable_intertwinerIntegrand (q / ΔE ^ 2).toNNReal hH hH W
  have hint : Integrable f μ := hint0.sub (integrable_const W)
  have hdiff : gaussianFilteredTerm q ΔE H W - W = ∫ t, f t ∂μ := by
    rw [integral_sub hint0 (integrable_const W), integral_const, probReal_univ, one_smul]
    rfl
  have hrw : gaussianFilteredTerm q ΔE H W -
      (W + regionExpectation K (gaussianFilteredTerm q ΔE H W - W)) =
      L (gaussianFilteredTerm q ΔE H W - W) := by
    rw [hL]; abel
  -- Duhamel: `‖τ_t(W) - W‖ ≤ |t| ‖[H, W]‖`.
  have hf : ∀ t, ‖f t‖ ≤ c * |t| := by
    intro t
    simp only [f]
    have hD := heisenbergEvolution_sub_eq_integral H W t
    simp only [heisenbergEvolution] at hD
    rw [hD]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := c)
      (f := fun s : ℝ => hermitianUnitaryPath H s * (Complex.I • (H * W - W * H)) *
        hermitianUnitaryPath H (-s)) fun s _ => by
      rw [norm_intertwinerIntegrand hH hH, norm_smul, Complex.norm_I, one_mul]
    simpa using this
  have habs : Integrable (fun t : ℝ => |t|) μ :=
    ((memLp_id_gaussianReal (μ := 0) (v := (q / ΔE ^ 2).toNNReal) 1).integrable
      le_rfl).abs
  have hshort (t : ℝ) (ht : t ∈ Set.Icc (-T) T) : ‖L (f t)‖ ≤ T * ε := by
    simp only [hL, f]
    refine (norm_heisenbergEvolution_sub_sub_regionExpectation_le K
      (fun s hs => hloc s ?_)).trans ?_
    · rcases ht with ⟨h1, h2⟩
      rcases Set.mem_uIcc.mp hs with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> constructor <;> linarith
    · rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ht) hε
  have hglob (t : ℝ) : ‖L (f t)‖ ≤ 2 * c * |t| := by
    rw [hL]
    calc ‖f t - regionExpectation K (f t)‖
        ≤ ‖f t‖ + ‖regionExpectation K (f t)‖ := norm_sub_le _ _
      _ ≤ ‖f t‖ + ‖f t‖ := by gcongr; exact (norm_regionExpectation_le (D := K) (f t))
      _ ≤ 2 * c * |t| := by linarith [hf t]
  rw [hrw, hdiff, ← L.integral_comp_comm hint,
    ← integral_add_compl (s := Set.Icc (-T) T) measurableSet_Icc (L.integrable_comp hint)]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_setIntegral_le_of_norm_le_const (μ := μ) (by finiteness) hshort)
    (norm_integral_le_of_norm_le (μ := μ.restrict (Set.Icc (-T) T)ᶜ)
      (habs.const_mul (2 * c)).integrableOn
      (ae_restrict_of_ae (Filter.Eventually.of_forall hglob)))).trans ?_
  rw [integral_const_mul]
  exact add_le_add (mul_le_of_le_one_right (mul_nonneg hT hε) measureReal_le_one) le_rfl

/-- `norm_gaussianFilteredTerm_sub_localized_le_mass` with the Gaussian first-moment tail:
`‖W_tilde - M‖ ≤ T ε + 2 ‖[H, W]‖ √(2h/π) e^{-T²/(2h)}`, where `h = q / ΔE²` is the variance of
the filter. Hastings, arXiv:0705.2024v4, appendix, lines 816–828. -/
theorem norm_gaussianFilteredTerm_sub_localized_le (q ΔE : ℝ)
    {H : Matrix (Config X) (Config X) ℂ} (hH : H.IsHermitian)
    (W : Matrix (Config X) (Config X) ℂ) (K : Finset V) {T ε : ℝ} (hT : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hloc : ∀ s ∈ Set.Icc (-T) T,
      ‖hermitianUnitaryPath H s * (Complex.I • (H * W - W * H)) * hermitianUnitaryPath H (-s) -
        regionExpectation K
          (hermitianUnitaryPath H s * (Complex.I • (H * W - W * H)) *
            hermitianUnitaryPath H (-s))‖ ≤ ε) :
    ‖gaussianFilteredTerm q ΔE H W -
        (W + regionExpectation K (gaussianFilteredTerm q ΔE H W - W))‖ ≤
      T * ε + 2 * ‖H * W - W * H‖ *
        (Real.sqrt (2 * (q / ΔE ^ 2).toNNReal / Real.pi) *
          Real.exp (-T ^ 2 / (2 * (q / ΔE ^ 2).toNNReal))) := by
  refine (norm_gaussianFilteredTerm_sub_localized_le_mass q ΔE hH W K hT hε hloc).trans ?_
  gcongr
  exact integral_compl_Icc_abs_gaussianReal_le _ hT

end IncrementSites

section Increment

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The change made by the filter.** `‖W_tilde - W‖ ≤ √(2h/π) ‖[H, W]‖`, where `h = q / ΔE²` is
the variance of the filter: by the Duhamel formula `‖τ_t(W) - W‖ ≤ |t| ‖[H, W]‖`, and the
Gaussian has first absolute moment `√(2h/π)`. Hastings, arXiv:0705.2024v4, appendix,
lines 816–828. -/
theorem norm_gaussianFilteredTerm_sub_self_le (q ΔE : ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (W : Matrix n n ℂ) :
    ‖gaussianFilteredTerm q ΔE H W - W‖ ≤
      Real.sqrt (2 * (q / ΔE ^ 2).toNNReal / Real.pi) * ‖H * W - W * H‖ := by
  set μ := gaussianReal 0 (q / ΔE ^ 2).toNNReal
  set c := ‖H * W - W * H‖
  set f : ℝ → Matrix n n ℂ := fun t =>
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) - W
  have hint0 := integrable_intertwinerIntegrand (q / ΔE ^ 2).toNNReal hH hH W
  have hdiff : gaussianFilteredTerm q ΔE H W - W = ∫ t, f t ∂μ := by
    rw [integral_sub hint0 (integrable_const W), integral_const, probReal_univ, one_smul]
    rfl
  have hf : ∀ t, ‖f t‖ ≤ c * |t| := by
    intro t
    simp only [f]
    have hD := heisenbergEvolution_sub_eq_integral H W t
    simp only [heisenbergEvolution] at hD
    rw [hD]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (C := c)
      (f := fun s : ℝ => hermitianUnitaryPath H s * (Complex.I • (H * W - W * H)) *
        hermitianUnitaryPath H (-s)) fun s _ => by
      rw [norm_intertwinerIntegrand hH hH, norm_smul, Complex.norm_I, one_mul]
    simpa using this
  have habs : Integrable (fun t : ℝ => |t|) μ :=
    ((memLp_id_gaussianReal (μ := 0) (v := (q / ΔE ^ 2).toNNReal) 1).integrable
      le_rfl).abs
  rw [hdiff]
  calc ‖∫ t, f t ∂μ‖ ≤ ∫ t, c * |t| ∂μ :=
        norm_integral_le_of_norm_le (habs.const_mul c) (Filter.Eventually.of_forall hf)
    _ = c * ∫ t, |t| ∂μ := integral_const_mul c _
    _ ≤ c * Real.sqrt (2 * (q / ΔE ^ 2).toNNReal / Real.pi) :=
        mul_le_mul_of_nonneg_left
          (integral_abs_gaussianReal_le_sqrt_two_mul_div_pi _) (norm_nonneg _)
    _ = _ := mul_comm _ _

end Increment

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V]
    {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]
  (G : SimpleGraph V) {T : κ → Finset V}
  (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)

include hHerm hDiam hCard hBudget

/-- **Locality of a filtered term on a finite graph.** Let `W` act on `S` and `B` on one site
`y` at graph distance at least `l` from every site of `S`. For every `μ ≥ 0` and `τ ≥ 0`,
`‖[W_tilde, B]‖ ≤ C |S| ‖W‖ ‖B‖ e^{vT - μl} + 2 ‖W‖ ‖B‖ e^{-(TΔE)²/(2q)}`, with
`C = 2 + 4 |b₀| e^{2μR}` and `v = 2 v_R |b₀| e^{2μR} + 1`.
Hastings, arXiv:cond-mat/0508554v3, eq. `lbnd` (lines 266–283), proved at lines 1419–1456:
the filter integral is split at `|t| = τ`, the Lieb–Robinson bound controls `|t| ≤ τ`, and the
Gaussian tail controls the rest. -/
theorem norm_commutator_gaussianFilteredTerm_le_graphDistance {q ΔE : ℝ} (hq : 0 ≤ q)
    (S : Finset V) {W B : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (y : V)
    (hB : B ∈ supportedOperators X ({y} : Finset V)) (μ : ℝ)
    (hμ : 0 ≤ μ) (l : ℕ)
    (hl : ∀ x ∈ S, (l : ℕ∞) ≤ G.edist x y) {τ : ℝ} (hT : 0 ≤ τ) :
    ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W * B -
        B * gaussianFilteredTerm q ΔE Φ.hamiltonian W‖ ≤
      (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * ‖B‖ *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * τ - μ * l) +
        2 * ‖W‖ * ‖B‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  refine norm_commutator_gaussianFilteredTerm_le hq hH W B hT (by positivity) fun t ht => ?_
  have hLR := norm_heisenberg_commutator_le_graphDistance_finset G Φ hHerm R
    hDiam vR hCard b₀ hBudget S hW y
    (by assumption) μ hμ l
    hl t
  refine hLR.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
  have hv : 0 ≤ 2 * vR * |b₀| * Real.exp (2 * μ * R) + 1 := by positivity
  have htT : |t| ≤ τ := abs_le.mpr ht
  nlinarith

/-- **The localized filtered term on a finite graph.** Let `W` act on `S`, and let `K` be the
set of sites within graph distance `l` of `S`. The normalized partial trace of `W_tilde` onto
`K` approximates `W_tilde` within
`C' |S|² ‖W‖ e^{vT - l/2} + 2 ‖W‖ e^{-(TΔE)²/(2q)}` for every `τ ≥ 0`, where
`C' = (2 + 4 |b₀| e^{2R}) K_g 2^{k_g} k_g! e^{1/2} / (1 - e^{-1/2})` and
`v = 2 v_R |b₀| e^{2R} + 1`, when every sphere of radius `r` has at most `K_g (r + 1)^{k_g}`
sites. This is an analogue of Hastings, arXiv:cond-mat/0508554v3, eq. `apb`
(lines 300–320, proved at lines 1458–1533), with the partial trace in place of truncated
dynamics and the radius conversion described in the module docstring. -/
theorem norm_gaussianFilteredTerm_sub_regionExpectation_le_graphNeighborhood
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (S : Finset V) {W : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (l : ℕ) {τ : ℝ} (hT : 0 ≤ τ) :
    ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W -
        regionExpectation (graphNeighborhood G S l)
          (gaussianFilteredTerm q ΔE Φ.hamiltonian W)‖ ≤
      (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
          (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
        2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  set v : ℝ := 2 * vR * |b₀| * Real.exp (2 * R) + 1 with hv_def
  set P : ℝ := (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
    (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) with hP_def
  have hden : 0 < 1 - Real.exp (-(1 / 2) : ℝ) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hP : 0 ≤ P := by
    rcases S.eq_empty_or_nonempty with hS | ⟨x, -⟩
    · simp [hP_def, hS]
    · have hKg : 0 ≤ Kg := by
        have := hGrowth x 0
        simp only [Nat.cast_zero, zero_add, one_pow, mul_one] at this
        exact (Nat.cast_nonneg _).trans this
      positivity
  have hv : 0 ≤ v := by positivity
  refine norm_sub_regionExpectation_gaussianFilteredTerm_le hq hH W _ hT (by positivity)
    fun t ht => ?_
  have hLR := norm_heisenberg_sub_regionExpectation_graphNeighborhood_le G Φ hHerm
    R hDiam vR hCard b₀ hBudget Kg kg hGrowth S hW l t
  refine hLR.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hP)
  have htT : |t| ≤ τ := abs_le.mpr ht
  nlinarith

/-- **The approximation `M` of a filtered term on a finite graph.** Let `W` act on `S`, and let
`K` be the set of sites within graph distance `l` of `S`. There is an operator `M` acting on
`K` with `‖M‖ ≤ ‖W‖`, Hermitian when `W` is, and with `‖W_tilde - M‖` at most the bound of
`norm_gaussianFilteredTerm_sub_regionExpectation_le_graphNeighborhood`. With `W = H_i` and
`‖H_i‖ ≤ J`, this gives an analogue of the approximation in Hastings,
arXiv:cond-mat/0508554v3, lines 285–320. If `H_i` is supported within radius `R` of `i`,
the support radius here is `l + R`; obtaining radius `l_proj` requires
`l = l_proj - R` with `R ≤ l_proj`. -/
theorem exists_local_approx_gaussianFilteredTerm (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (S : Finset V) {W : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (l : ℕ) {τ : ℝ} (hT : 0 ≤ τ) :
    ∃ M : Matrix (Config X) (Config X) ℂ,
      M ∈ supportedOperators X (graphNeighborhood G S l) ∧
      ‖M‖ ≤ ‖W‖ ∧ (W.IsHermitian → M.IsHermitian) ∧
      ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W - M‖ ≤
        (2 + 4 * |b₀| * Real.exp (2 * R)) * (S.card : ℝ) ^ 2 * ‖W‖ * Kg *
            (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
            Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
          2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  exact ⟨_, (regionExpectation_mem_supportedOperators _ _),
    (norm_regionExpectation_le _).trans (norm_gaussianFilteredTerm_le q ΔE hH W),
    fun hW' => (isHermitian_regionExpectation (isHermitian_gaussianFilteredTerm q ΔE hH
        hW')),
    norm_gaussianFilteredTerm_sub_regionExpectation_le_graphNeighborhood G Φ hHerm R hDiam vR hCard
      b₀ hBudget Kg kg hGrowth hq S hW l hT⟩

end Graph

section GroundApproximation

section Ground

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Excited component of an approximation of a filtered term.** Let every eigenvalue of `H`
equal `E₀` or be at least `E₀ + ΔE`, and let `ψ` be a ground vector. For every operator `M`,
the component of `M ψ` orthogonal to the ground eigenspace has norm at most
`(‖W‖ e^{-q/2} + ‖W_tilde - M‖) ‖ψ‖`. Hastings, arXiv:cond-mat/0508554v3, the triangle
inequality before eq. `facld` (lines 322–348); with `M` as in
`exists_local_approx_gaussianFilteredTerm`, the bound is eq. `facld` with `q` and `τ` free. -/
theorem norm_sub_starProjection_apply_le_of_gaussianFilteredTerm {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) {H : Matrix n n ℂ} (hH : H.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues k)
    (W M : Matrix n n ℂ) {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundSpace H E₀) :
    ‖toEuclideanLin M ψ - (groundSpace H E₀).starProjection (toEuclideanLin M ψ)‖ ≤
      (‖W‖ * Real.exp (-q / 2) + ‖gaussianFilteredTerm q ΔE H W - M‖) * ‖ψ‖ := by
  set K := groundSpace H E₀
  set x := toEuclideanLin (gaussianFilteredTerm q ΔE H W) ψ
  set z := toEuclideanLin (M - gaussianFilteredTerm q ΔE H W) ψ
  have hMxz : toEuclideanLin M ψ = x + z := by
    simp only [x, z, map_sub, LinearMap.sub_apply, add_sub_cancel]
  have hsplit : toEuclideanLin M ψ - K.starProjection (toEuclideanLin M ψ) =
      (x - K.starProjection x) + (z - K.starProjection z) := by
    rw [hMxz, map_add]; abel
  have hz : ‖z - K.starProjection z‖ ≤ ‖z‖ := by
    have := K.starProjection_add_starProjection_orthogonal z
    rw [show z - K.starProjection z = Kᗮ.starProjection z from
      sub_eq_iff_eq_add'.mpr this.symm]
    exact Kᗮ.norm_starProjection_apply_le z
  have hzψ : ‖z‖ ≤ ‖gaussianFilteredTerm q ΔE H W - M‖ * ‖ψ‖ := by
    rw [norm_sub_rev, ← l2_opNorm_toEuclideanCLM]
    exact (toEuclideanCLM (n := n) (𝕜 := ℂ) (M - gaussianFilteredTerm q ΔE H W)).le_opNorm ψ
  rw [hsplit, add_mul]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_sub_starProjection_gaussianFilteredTerm_le hq hΔE hH hgap W hψ) (hz.trans hzψ))

/-- **A unique gapped ground state is nearly an eigenvector of the approximation.** If `H` is
Hermitian and gapped at `E₀` with gap `ΔE > 0`, and its ground space is the line through the unit
vector `Ω`, then for every operator `M`,
`‖M Ω - ⟨Ω, M Ω⟩ Ω‖ ≤ ‖W‖ e^{-q/2} + ‖W_tilde - M‖`. Hastings, arXiv:cond-mat/0508554v3,
the case of one ground state (lines 375–387), where `M = M_i`. -/
theorem norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) {H : Matrix n n ℂ} {E₀ : ℝ} {Ω : EuclideanSpace ℂ n} (hH : H.IsHermitian)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped H E₀ ΔE) (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω})
    (W M : Matrix n n ℂ) :
    ‖toEuclideanLin M Ω - ⟪Ω, toEuclideanLin M Ω⟫_ℂ • Ω‖ ≤
      ‖W‖ * Real.exp (-q / 2) + ‖gaussianFilteredTerm q ΔE H W - M‖ := by
  have hmem : Ω ∈ groundSpace H E₀ := by
    rw [hspan]; exact Submodule.mem_span_singleton_self Ω
  have h := norm_sub_starProjection_apply_le_of_gaussianFilteredTerm hq hΔE hH
    ((isGapped_iff_eigenvalues hH).mp hgap).2 W M hmem
  rwa [hspan, Submodule.starProjection_unit_singleton ℂ hΩ, hΩ, mul_one] at h

/-- **The sum of the approximations.** If the terms `Wᵢ` sum to `H`, then any operators `Mᵢ`
satisfy `‖∑ᵢ Mᵢ - H‖ ≤ ∑ᵢ ‖W_tildeᵢ - Mᵢ‖`, since the filtered terms also sum to `H`.
Hastings, arXiv:cond-mat/0508554v3, lines 359–374: the difference between `H` and
`M = ∑ᵢ Mᵢ` is at most the sum of the errors of eq. `apb`. -/
theorem norm_sum_sub_le_of_sum_eq {κ : Type*} (s : Finset κ) (q ΔE : ℝ) {H : Matrix n n ℂ}
    (hH : H.IsHermitian) {W M : κ → Matrix n n ℂ} (hsum : ∑ i ∈ s, W i = H) :
    ‖∑ i ∈ s, M i - H‖ ≤ ∑ i ∈ s, ‖gaussianFilteredTerm q ΔE H (W i) - M i‖ := by
  have hW := sum_gaussianFilteredTerm s q ΔE hH hsum
  calc ‖∑ i ∈ s, M i - H‖
      = ‖∑ i ∈ s, (M i - gaussianFilteredTerm q ΔE H (W i))‖ := by
        rw [Finset.sum_sub_distrib, hW]
    _ ≤ ∑ i ∈ s, ‖M i - gaussianFilteredTerm q ΔE H (W i)‖ := norm_sum_le _ _
    _ = _ := Finset.sum_congr rfl fun i _ => norm_sub_rev _ _

end Ground

end GroundApproximation

section ZeroRangeFilter

section Commuting

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A commuting observable is fixed by the normalized Gaussian filter, at every variance. -/
theorem gaussianFilteredTerm_eq_of_commute (q ΔE : ℝ) {H W : Matrix n n ℂ}
    (hc : Commute H W) : gaussianFilteredTerm q ΔE H W = W := by
  have hconst (t : ℝ) : hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) = W := by
    have hWt : Commute W (hermitianUnitaryPath H t) := by
      unfold hermitianUnitaryPath
      exact Commute.exp_right ((hc.symm.smul_right Complex.I).smul_right t)
    rw [← hWt.eq, Matrix.mul_assoc, SpectralFilter.hermitianUnitaryPath_mul_neg, Matrix.mul_one]
  simp [gaussianFilteredTerm, gaussianIntertwiner, hconst]

/-- A commuting observable preserves every ground eigenspace. -/
theorem mem_groundSpace_apply_of_commute {H W : Matrix n n ℂ} (hc : Commute H W)
    {E₀ : ℝ} {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundSpace H E₀) :
    toEuclideanLin W ψ ∈ groundSpace H E₀ := by
  have hψ' := Module.End.mem_eigenspace_iff.mp hψ
  apply Module.End.mem_eigenspace_iff.mpr
  rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul (q := 2), hc.eq, Matrix.toLpLin_mul (q := 2),
    LinearMap.comp_apply, hψ', map_smul]

/-- A commuting observable has no component outside the ground eigenspace on a ground vector. -/
theorem starProjection_apply_eq_of_commute {H W : Matrix n n ℂ} (hc : Commute H W)
    {E₀ : ℝ} {ψ : EuclideanSpace ℂ n} (hψ : ψ ∈ groundSpace H E₀) :
    (groundSpace H E₀).starProjection (toEuclideanLin W ψ) = toEuclideanLin W ψ :=
  (groundSpace H E₀).starProjection_eq_self_iff.mpr
    (mem_groundSpace_apply_of_commute hc hψ)

end Commuting

section SingleSites

variable {V : Type*} [Fintype V] [DecidableEq V]
    {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- Terms supported on their individual sites commute pairwise. -/
theorem commute_of_singleton_support
    (Φ : Interaction X fun v : V ↦ ({v} : Finset V)) (i j : V) :
    Commute (Φ.term i) (Φ.term j) := by
  by_cases hij : i = j
  · subst j
    exact Commute.refl _
  · apply commute_of_mem_supportedOperators_of_disjoint (Φ.mem i) (Φ.mem j) _
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    simp only [Finset.mem_singleton] at hki hkj
    exact hij (hki.symm.trans hkj)

/-- Any partial sum of zero-range terms commutes with each individual term, even when the
partial sum omits its index. -/
theorem commute_sum_of_singleton_support
    (Φ : Interaction X fun v : V ↦ ({v} : Finset V))
    (s : Finset V) (i : V) :
    Commute (∑ j ∈ s, Φ.term j) (Φ.term i) := by
  change (∑ j ∈ s, Φ.term j) * Φ.term i = Φ.term i * ∑ j ∈ s, Φ.term j
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ (commute_of_singleton_support Φ j i).eq

/-- The local and full Gaussian filters are exact for physical zero-range terms. -/
theorem gaussianFilteredTerm_sum_eq_of_singleton_support
    (Φ : Interaction X fun v : V ↦ ({v} : Finset V))
    (s : Finset V) (q ΔE : ℝ) (i : V) :
    gaussianFilteredTerm q ΔE (∑ j ∈ s, Φ.term j) (Φ.term i) = Φ.term i :=
  gaussianFilteredTerm_eq_of_commute q ΔE (commute_sum_of_singleton_support Φ s i)

end SingleSites

section Metric

variable {V : Type*} [Fintype V] [DecidableEq V] [MetricSpace V] {X : V → Type*}
  [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- In a genuine metric, radius-zero balls are singletons. -/
theorem singleton_support_of_zero_range
    (Φ : Interaction X (metricRangeBall (0 : ℝ))) :
    ∀ i, Φ.term i ∈ supportedOperators X ({i} : Finset V) := by
  intro i
  convert Φ.mem i using 2
  ext j
  simp [mem_metricRangeBall, dist_le_zero, eq_comm]

/-- The Gaussian filter under every retained local generator fixes a zero-range term. -/
theorem gaussianFilteredTerm_sum_eq_of_zero_range
    (Φ : Interaction X (metricRangeBall (0 : ℝ)))
    (s : Finset V) (q ΔE : ℝ) (i : V) :
    gaussianFilteredTerm q ΔE (∑ j ∈ s, Φ.term j) (Φ.term i) = Φ.term i :=
  gaussianFilteredTerm_sum_eq_of_singleton_support
    (⟨Φ.term, singleton_support_of_zero_range Φ⟩ : Interaction X fun v : V ↦ ({v} : Finset V))
    s q ΔE i

/-- Full and truncated filters agree exactly in the physical metric zero-range case. -/
theorem gaussianFilteredTerm_full_and_sum_eq_of_zero_range
    (Φ : Interaction X (metricRangeBall (0 : ℝ)))
    (s : Finset V) (q ΔE : ℝ) (i : V) :
    gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i) = Φ.term i ∧
      gaussianFilteredTerm q ΔE (∑ j ∈ s, Φ.term j) (Φ.term i) = Φ.term i :=
  ⟨gaussianFilteredTerm_sum_eq_of_zero_range Φ Finset.univ q ΔE i,
    gaussianFilteredTerm_sum_eq_of_zero_range Φ s q ΔE i⟩

/-- A zero-range term preserves the full ground eigenspace exactly. -/
theorem starProjection_term_eq_of_zero_range
    (Φ : Interaction X (metricRangeBall (0 : ℝ)))
    {E₀ : ℝ} {ψ : EuclideanSpace ℂ (Config X)}
    (hψ : ψ ∈ groundSpace Φ.hamiltonian E₀) (i : V) :
    (groundSpace Φ.hamiltonian E₀).starProjection (toEuclideanLin (Φ.term i) ψ) =
      toEuclideanLin (Φ.term i) ψ :=
  starProjection_apply_eq_of_commute (commute_sum_of_singleton_support
    (⟨Φ.term, singleton_support_of_zero_range Φ⟩ : Interaction X fun v : V ↦ ({v} : Finset V))
    Finset.univ i) hψ

/-- Hastings, arXiv:cond-mat/0508554v3, eq. `facld`: in the metric zero-range case
its excited component vanishes exactly, for every retained generator. -/
theorem sub_starProjection_gaussianFilteredTerm_sum_eq_zero_of_zero_range
    (Φ : Interaction X (metricRangeBall (0 : ℝ)))
    (s : Finset V) (q ΔE : ℝ) {E₀ : ℝ} {ψ : EuclideanSpace ℂ (Config X)}
    (hψ : ψ ∈ groundSpace Φ.hamiltonian E₀) (i : V) :
    toEuclideanLin (gaussianFilteredTerm q ΔE (∑ j ∈ s, Φ.term j) (Φ.term i)) ψ -
      (groundSpace Φ.hamiltonian E₀).starProjection
        (toEuclideanLin (gaussianFilteredTerm q ΔE (∑ j ∈ s, Φ.term j) (Φ.term i)) ψ) = 0 := by
  rw [gaussianFilteredTerm_sum_eq_of_zero_range Φ s q ΔE i,
    starProjection_term_eq_of_zero_range Φ hψ i, sub_self]

end Metric

end ZeroRangeFilter

end ManyBody
