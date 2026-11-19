/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.GapPerturbation
import QICLean.ManyBody.Dynamics.MetricGraph
import QICLean.ManyBody.Hamiltonian.GaussianFilterTruncation

/-!
# Gaussian truncation in a finite metric space

Let an interaction `Φ : Interaction X (metricRangeBall R)` on a finite pseudometric space of
sites have one Hermitian term for each site `i`, supported in the ball of radius `R` about `i`,
with norm at most `J`, and let every such ball have at most `S` sites. For positive `R` and gap
`Δ`, constants independent of the space and of the interaction give exponential bounds in `ℓ`
for the truncated filter `M_i`, the filter of the term at `i` under the terms centred within
distance `ℓ - R` of `i`: its support in the ball of radius `ℓ`, its Hermiticity and norm, its
difference from the full filter, and its action on ground vectors. No polynomial growth
hypothesis is needed: the graph joining sites at distance at most `R` has degree at most `S`,
and a strong enough Lieb–Robinson weight makes its tails summable. The time window is `c₁ ℓ`
and the Gaussian parameter is `q = c₁ ℓ Δ`.

If a Hermitian `M` satisfies `‖H - M‖ ≤ ε`, a unit vector minimizing its Rayleigh quotient is an
eigenvector of `M` with excess energy at most `2ε` under `H`, so the gap of `H` controls its
projection onto the ground space of `H`; for a unique ground vector `Ω` the overlap defect is at
most `2ε/Δ` and the squared distance after a choice of phase at most `4ε/Δ`. For `M = ∑_i M_i`
an explicit logarithmic radius `ℓ` gives a ground vector of `M` with projection defect at most
any `η > 0`.

**Local fix (factorization length):** after eq. `facld`, the source prints the minimum of two
decay lengths; adding the decays requires the maximum of their lengths, equivalently the
minimum of their rates, which the explicit rate here uses. See
`docs/paper-gaps/hastings05_truncated_dynamics.tex`.

## Main results

* `ManyBody.exists_metric_truncated_filter_localization` — the truncated filters.
* `ManyBody.exists_metric_truncated_filter_sum_bound` — `‖∑_i M_i - H‖ ≤ N J C e^{-ηℓ}`.
* `ManyBody.exists_groundVector_overlap_of_norm_sub_le` — ground overlap of an approximation.
* `ManyBody.exists_metric_truncated_groundVector_projection`,
  `ManyBody.exists_metric_truncated_groundVector_overlap` — the ground vector of `∑_i M_i`.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 169–190, 285–374 and 1469–1533. The comparison with the polynomial-shell argument is
documented in `docs/paper-gaps/hastings05_geometric_growth_scope.tex`.

Moved from TNLean, `TNLean/Lattice/GaussianFilteredMetricTruncation.lean` and
`GaussianGroundStateOverlap.lean` at commit `e113e005`. Changes: an interaction
`Φ : Interaction X (metricRangeBall R)` on any system of sites in place of a family of terms on
`ι → Fin d` with a support hypothesis.
-/

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace ManyBody

section MetricTruncation

private theorem exp_neg_mul_ceil_metric_le {R β : ℝ} (hR : 0 < R) (hβ : 0 ≤ β) (ℓ : ℝ) :
    Real.exp (-(β * (Nat.ceil ((ℓ - R) / R) : ℝ))) ≤
      Real.exp β * Real.exp (-((β / R) * ℓ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left (Nat.le_ceil ((ℓ - R) / R)) hβ
  have he : β + -((β / R) * ℓ) = -(β * ((ℓ - R) / R)) := by field_simp; ring
  rw [he]
  exact neg_le_neg hh

/-- Uniform source constants control the sum of spectral leakage and actual physical-ball
truncation error. Hastings, arXiv:cond-mat/0508554v3, lines 169–190, 285–349 and 1469–1533. -/
theorem exists_metric_truncated_filter_budget {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {V : Type*} [PseudoMetricSpace V] [Fintype V] [DecidableEq V] {X : V → Type*}
        [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)],
        ∀ (Φ : Interaction X (metricRangeBall R))
          (_hHerm : ∀ i, (Φ.term i).IsHermitian)
          (_hNorm : ∀ i, ‖Φ.term i‖ ≤ J)
          (_hCard : ∀ i : V, (metricRangeBall R i).card ≤ S)
          (ℓ : ℝ), R ≤ ℓ → ∀ i : V,
          let q := c₁ * ℓ * Δ
          ‖Φ.term i‖ * Real.exp (-q / 2) +
            ‖gaussianFilteredTerm q Δ Φ.hamiltonian (Φ.term i) -
              gaussianFilteredTerm q Δ (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j) (Φ.term i)‖ ≤
            ‖Φ.term i‖ * C * Real.exp (-(η * ℓ)) := by
  let μ : ℝ := Real.log ((S : ℝ) + 1) + 1
  let v : ℝ := 4 * (S : ℝ) * |(S : ℝ) * J| * Real.exp (2 * μ * 2)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  let c₁ : ℝ := (1 / 2) / (2 * R * (v + 1))
  have hc₁ : 0 < c₁ := div_pos (by norm_num) (by positivity)
  have hc : 2 * R * (v + 1) * c₁ = (1 / 2 : ℝ) := by
    dsimp [c₁]
    field_simp
  let γ : ℝ := (1 / 2) / R - v * c₁
  have hγ : 0 < γ := by
    have hr : 0 < R * c₁ := mul_pos hR hc₁
    have hvc : v * c₁ * R < (1 / 2 : ℝ) := by nlinarith only [hc, hr]
    have := (lt_div_iff₀ hR).mpr hvc
    dsimp [γ]
    linarith only [this]
  let δ : ℝ := min (c₁ * Δ) γ
  have hδ : 0 < δ := lt_min (mul_pos hc₁ hΔ) hγ
  have hden : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by
    have := Real.exp_lt_one_iff.mpr (by norm_num : -(1 / 2 : ℝ) < 0)
    linarith
  let A : ℝ := 4 * ((S : ℝ) + 1) * Real.exp (μ * (2 * 2 + 1)) * J * c₁ *
    Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C : ℝ := 3 + A / (Real.exp 1 * (δ / 2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨c₁, δ / 2, C, hc₁, half_pos hδ, hC, ?_⟩
  intro V _ _ _ X _ _ Φ hHerm hNorm hCard ℓ hℓ i q
  have hℓ0 : 0 ≤ ℓ := hR.le.trans hℓ
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hS : 1 ≤ S := (Finset.one_le_card.mpr ⟨i, self_mem_metricRangeBall hR.le i⟩).trans
    (hCard i)
  have hDegree (x : V) : (metricRangeGraph R).degree x ≤ S := by
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using
      metricRangeGraph_neighbor_card_le hCard x
  have hrad (x : V) (hx : x ∈ metricRangeBall R i) :
      (metricRangeGraph R).edist i x ≤ (2 : ℕ∞) :=
    (metricRangeGraph_edist_le_one (mem_metricRangeBall.mp hx)).trans (by norm_num)
  have hAnchor (x : V) :
      ∑ j ∈ Finset.univ.filter (fun j : V ↦ id j = x), ‖Φ.term j‖ ≤ J := by
    rw [show Finset.univ.filter (fun j : V ↦ id j = x) = {x} by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, id_eq, Finset.mem_singleton]]
    simpa only [Finset.sum_singleton] using hNorm x
  have hμ : Real.log ((S : ℝ) + 1) < μ := by dsimp [μ]; linarith
  have hβ : (μ - Real.log ((S : ℝ) + 1)) / 2 = (1 / 2 : ℝ) := by dsimp [μ]; ring
  have hf := norm_gaussianFilteredTerm_sub_truncated_le_degree_tail
    (ΔE := Δ) (q := q) (τ := c₁ * ℓ)
    (metricRangeGraph R) S hDegree id
    (self_mem_metricRangeBall hR.le) Φ hHerm 2
    (metricRangeBall_graph_diameter_le_two R) S hS hCard ((S : ℝ) * J)
    (metricRangeBall_norm_budget_le hCard hJ Φ.term hNorm) J hJ hAnchor
    (metricRangeBall (ℓ - R) i) i (metricRangeBall R i) hrad (Φ.mem i)
    (Nat.ceil ((ℓ - R) / R))
    (fun j hj ↦ metricRangeGraph_omitted_threshold hR hj) hq hμ (mul_nonneg hc₁.le hℓ0)
  simp only [hβ] at hf
  have htime : q / Δ = c₁ * ℓ := by dsimp [q]; field_simp
  have hgauss := exp_neg_sq_div_eq_of_time_eq (q := q) hΔ.ne'
  rw [htime] at hgauss
  rw [hgauss] at hf
  have htail := exp_neg_mul_ceil_metric_le hR (by norm_num : (0 : ℝ) ≤ 1 / 2) ℓ
  have hexp : Real.exp (v * (c₁ * ℓ)) * Real.exp (-(((1 / 2 : ℝ) / R) * ℓ)) =
      Real.exp (-(γ * ℓ)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [γ]
    ring
  have hspatial :
      4 * (((metricRangeBall R i).card : ℝ) + 1) * Real.exp (μ * (2 * 2 + 1)) *
        ‖Φ.term i‖ * (c₁ * ℓ) * Real.exp (v * (c₁ * ℓ)) *
        (J * Real.exp (-((1 / 2 : ℝ) * (Nat.ceil ((ℓ - R) / R) : ℝ))) /
          (1 - Real.exp (-(1 / 2 : ℝ)))) ≤
      A * ‖Φ.term i‖ * ℓ * Real.exp (-(γ * ℓ)) := by
    calc
      _ ≤ 4 * ((S : ℝ) + 1) * Real.exp (μ * (2 * 2 + 1)) * ‖Φ.term i‖ * (c₁ * ℓ) *
          Real.exp (v * (c₁ * ℓ)) *
          (J * (Real.exp (1 / 2) * Real.exp (-(((1 / 2 : ℝ) / R) * ℓ))) /
            (1 - Real.exp (-(1 / 2 : ℝ)))) := by
        gcongr
        · exact_mod_cast hCard i
      _ = A * ‖Φ.term i‖ * ℓ *
          (Real.exp (v * (c₁ * ℓ)) * Real.exp (-(((1 / 2 : ℝ) / R) * ℓ))) := by
        dsimp [A]
        ring
      _ = _ := by rw [hexp]
  have herr :
      ‖gaussianFilteredTerm q Δ Φ.hamiltonian (Φ.term i) -
        gaussianFilteredTerm q Δ (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j) (Φ.term i)‖ ≤
      A * ‖Φ.term i‖ * ℓ * Real.exp (-(γ * ℓ)) + 2 * ‖Φ.term i‖ * Real.exp (-q / 2) :=
    hf.trans (add_le_add hspatial le_rfl)
  have hscalar := gaussian_truncation_bound_le_exp (mul_pos hc₁ hΔ) hγ hA (norm_nonneg (Φ.term i)) hℓ0
  calc _ ≤ ‖Φ.term i‖ * Real.exp (-q / 2) +
        (A * ‖Φ.term i‖ * ℓ * Real.exp (-(γ * ℓ)) + 2 * ‖Φ.term i‖ * Real.exp (-q / 2)) :=
      add_le_add le_rfl herr
    _ = 3 * ‖Φ.term i‖ * Real.exp (-((c₁ * Δ) * ℓ) / 2) +
        A * ‖Φ.term i‖ * ℓ * Real.exp (-(γ * ℓ)) := by
      rw [show -q / 2 = -((c₁ * Δ) * ℓ) / 2 by dsimp [q]; ring]
      ring
    _ ≤ ‖Φ.term i‖ * C * Real.exp (-(δ / 2 * ℓ)) := by
      simpa only [C, δ, neg_mul] using hscalar


/-- The actual physical-ball truncated filter has the support, Hermiticity and norm
asserted in Hastings, arXiv:cond-mat/0508554v3, lines 322–349 and 1469–1505. -/
theorem metric_truncated_filter_properties {V : Type*} [PseudoMetricSpace V]
    [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)] {R ℓ J : ℝ} (hℓ : R ≤ ℓ)
    (Φ : Interaction X (metricRangeBall R)) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (hNorm : ∀ i, ‖Φ.term i‖ ≤ J) (q Δ : ℝ) (i : V) :
    let M := gaussianFilteredTerm q Δ (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j) (Φ.term i)
    M ∈ supportedOperators X
        (metricRangeBall ℓ i) ∧ M.IsHermitian ∧ ‖M‖ ≤ J := by
  intro M
  have hHs : (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j).IsHermitian :=
    (isSelfAdjoint_sum _ fun j _ ↦ (hHerm j).isSelfAdjoint).isHermitian
  have hHsSupp : (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j) ∈
      supportedOperators X (metricRangeBall ℓ i : Finset V) :=
    sum_mem fun j hj ↦ supportedOperators_mono
      (metricRangeBall_retained_support hj) (Φ.mem j)
  have hWi := supportedOperators_mono (metricRangeBall_initial_support hℓ i) (Φ.mem i)
  refine ⟨?_, isHermitian_gaussianFilteredTerm q Δ hHs (hHerm i),
    (norm_gaussianFilteredTerm_le q Δ hHs (Φ.term i)).trans (hNorm i)⟩
  exact gaussianFilteredTerm_mem_supportedOperators q Δ hHsSupp hWi


/-- Source-faithful exponential localization for the actual physical-ball truncated
operators. Constants depend only on the range, local cardinality bound, interaction norm
bound and gap, and are uniform in the finite metric space and Hamiltonian. Hastings,
arXiv:cond-mat/0508554v3, eqs. `mid` and `facld`, lines 285–349. -/
theorem exists_metric_truncated_filter_localization {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {V : Type*} [PseudoMetricSpace V] [Fintype V] [DecidableEq V] {X : V → Type*}
        [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)],
        ∀ (Φ : Interaction X (metricRangeBall R))
          (_hHerm : ∀ i, (Φ.term i).IsHermitian)
          (_hNorm : ∀ i, ‖Φ.term i‖ ≤ J)
          (_hCard : ∀ i : V, (metricRangeBall R i).card ≤ S)
          (ℓ : ℝ), R ≤ ℓ → ∀ i : V,
          let q := c₁ * ℓ * Δ
          let M := gaussianFilteredTerm q Δ (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j) (Φ.term i)
          M ∈ supportedOperators X
              (metricRangeBall ℓ i) ∧ M.IsHermitian ∧ ‖M‖ ≤ J ∧
            ‖gaussianFilteredTerm q Δ Φ.hamiltonian (Φ.term i) - M‖ ≤ J * C * Real.exp (-(η * ℓ)) ∧
            (∀ (hH : Φ.hamiltonian.IsHermitian) {E₀ : ℝ}
              (_hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
              {ψ : EuclideanSpace ℂ (Config X)}, ψ ∈ groundSpace Φ.hamiltonian E₀ →
              ‖toEuclideanLin M ψ - (groundSpace Φ.hamiltonian E₀).starProjection
                (toEuclideanLin M ψ)‖ ≤ J * C * Real.exp (-(η * ℓ)) * ‖ψ‖) ∧
            (∀ {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Config X)}, ‖Ω‖ = 1 →
              IsGapped Φ.hamiltonian E₀ Δ → groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Ω} →
              ‖toEuclideanLin M Ω - ⟪Ω, toEuclideanLin M Ω⟫_ℂ • Ω‖ ≤
                J * C * Real.exp (-(η * ℓ))) := by
  obtain ⟨c₁, η, C, hc₁, hη, hC, hb⟩ := exists_metric_truncated_filter_budget hR S hJ hΔ
  refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
  intro V _ _ _ X _ _ Φ hHerm hNorm hCard ℓ hℓ i q M
  have hq : 0 ≤ q := mul_nonneg (mul_nonneg hc₁.le (hR.le.trans hℓ)) hΔ.le
  have hbudget := hb Φ hHerm hNorm hCard ℓ hℓ i
  have hbound : ‖Φ.term i‖ * C * Real.exp (-(η * ℓ)) ≤ J * C * Real.exp (-(η * ℓ)) := by
    gcongr
    exact hNorm i
  have htotal : ‖Φ.term i‖ * Real.exp (-q / 2) +
      ‖gaussianFilteredTerm q Δ Φ.hamiltonian (Φ.term i) - M‖ ≤ J * C * Real.exp (-(η * ℓ)) :=
    hbudget.trans hbound
  obtain ⟨hMsupp, hMHerm, hMnorm⟩ :=
    metric_truncated_filter_properties hℓ Φ hHerm hNorm q Δ i
  refine ⟨hMsupp, hMHerm, hMnorm, ?_, ?_, ?_⟩
  · exact (le_add_of_nonneg_left (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).trans htotal
  · intro hH E₀ hgap ψ hψ
    exact (norm_sub_starProjection_apply_le_of_gaussianFilteredTerm hq hΔ hH hgap (Φ.term i) M hψ).trans
      (mul_le_mul_of_nonneg_right htotal (norm_nonneg ψ))
  · intro E₀ Ω hΩ hgap hspan
    exact (norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm hq hΔ
      (Interaction.isHermitian_hamiltonian hHerm) hΩ hgap hspan (Φ.term i) M).trans htotal


/-- The sum of the actual physical-ball truncated operators approximates the Hamiltonian
with the number of sites times the uniform exponential error. Hastings,
arXiv:cond-mat/0508554v3, lines 343–374. -/
theorem exists_metric_truncated_filter_sum_bound {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ η C : ℝ, 0 < c₁ ∧ 0 < η ∧ 0 ≤ C ∧
      ∀ {V : Type*} [PseudoMetricSpace V] [Fintype V] [DecidableEq V] {X : V → Type*}
        [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)],
        ∀ (Φ : Interaction X (metricRangeBall R))
          (_hHerm : ∀ i, (Φ.term i).IsHermitian)
          (_hNorm : ∀ i, ‖Φ.term i‖ ≤ J)
          (_hCard : ∀ i : V, (metricRangeBall R i).card ≤ S)
          (ℓ : ℝ), R ≤ ℓ →
          ‖∑ i, gaussianFilteredTerm (c₁ * ℓ * Δ) Δ
              (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j) (Φ.term i) - Φ.hamiltonian‖ ≤
            Fintype.card V * (J * C * Real.exp (-(η * ℓ))) := by
  obtain ⟨c₁, η, C, hc₁, hη, hC, hb⟩ := exists_metric_truncated_filter_localization hR S hJ hΔ
  refine ⟨c₁, η, C, hc₁, hη, hC, ?_⟩
  intro V _ _ _ X _ _ Φ hHerm hNorm hCard ℓ hℓ
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  refine (norm_sum_sub_le_of_sum_eq Finset.univ (c₁ * ℓ * Δ) Δ hH (W := Φ.term)
    rfl).trans ?_
  calc
    _ ≤ ∑ _i : V, J * C * Real.exp (-(η * ℓ)) :=
      Finset.sum_le_sum fun i _ ↦ (hb Φ hHerm hNorm hCard ℓ hℓ i).2.2.2.1
    _ = _ := by simp

end MetricTruncation

section GroundStateOverlap

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem unit_energy_error_le {H M : Matrix n n ℂ} {ε : ℝ}
    (hHM : ‖H - M‖ ≤ ε) {v : EuclideanSpace ℂ n} (hv : ‖v‖ = 1) :
    |(⟪v, toEuclideanLin H v⟫_ℂ).re - (⟪v, toEuclideanLin M v⟫_ℂ).re| ≤ ε := by
  have hq := ((toEuclideanCLM (𝕜 := ℂ) (n := n) (H - M)).rayleighQuotient_le_norm v).trans hHM
  rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
    hv, one_pow, div_one] at hq
  change |(⟪toEuclideanLin (H - M) v, v⟫_ℂ).re| ≤ ε at hq
  rw [← inner_conj_symm (toEuclideanLin (H - M) v) v, Complex.conj_re] at hq
  simpa only [map_sub, LinearMap.sub_apply, inner_sub_right, Complex.sub_re] using hq

/-- The eigenvalue gap is the quadratic-form gap above the canonical ground eigenspace.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem groundSpace_gap_le_of_eigenvalues {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {E₀ Δ : ℝ} (hgap : ∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k)
    (ψ : EuclideanSpace ℂ n) :
    Δ * (‖ψ‖ ^ 2 - ‖(groundSpace H E₀).starProjection ψ‖ ^ 2) ≤
      (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 := by
  let K := groundSpace H E₀
  let b := hH.eigenvectorBasis
  let y := ψ - K.starProjection ψ
  have hb (k : n) : H *ᵥ WithLp.ofLp (b k) = (hH.eigenvalues k : ℂ) • WithLp.ofLp (b k) :=
    SpectralFilter.mulVec_eigenvectorBasis_complex hH k
  have hcoef (k : n) : ⟪b k, toEuclideanLin H ψ⟫_ℂ =
      (hH.eigenvalues k : ℂ) * ⟪b k, ψ⟫_ℂ := by
    have hs := isSymmetric_toEuclideanLin_iff.mpr hH
    have heig : toEuclideanLin H (b k) = (hH.eigenvalues k : ℂ) • b k := by
      exact (WithLp.ofLp_injective 2) (hb k)
    rw [← hs, heig, inner_smul_left, Complex.conj_ofReal]
  have henergy : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re =
      ∑ k, hH.eigenvalues k * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 := by
    rw [← b.sum_inner_mul_inner ψ (toEuclideanLin H ψ)]
    change Complex.reAddGroupHom (∑ k, ⟪ψ, b k⟫_ℂ * ⟪b k, toEuclideanLin H ψ⟫_ℂ) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hcoef, ← inner_conj_symm ψ (b k)]
    have heq : (starRingEnd ℂ) ⟪b k, ψ⟫_ℂ *
        ((hH.eigenvalues k : ℂ) * ⟪b k, ψ⟫_ℂ) =
        ((hH.eigenvalues k * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      calc _ = (hH.eigenvalues k : ℂ) *
          ((starRingEnd ℂ) ⟪b k, ψ⟫_ℂ * ⟪b k, ψ⟫_ℂ) := by ring
        _ = _ := by rw [Complex.conj_mul']; push_cast; rfl
    rw [heq]
    rfl
  have henergySub : (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2 =
      ∑ k, (hH.eigenvalues k - E₀) * ‖⟪b k, ψ⟫_ℂ‖ ^ 2 := by
    rw [henergy, ← b.sum_sq_norm_inner_right ψ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hres : ‖ψ‖ ^ 2 - ‖K.starProjection ψ‖ ^ 2 = ‖y‖ ^ 2 := by
    have hp := Submodule.norm_sq_eq_add_norm_sq_starProjection ψ K
    rw [K.starProjection_orthogonal_val ψ] at hp
    dsimp [y]
    linarith
  change Δ * (‖ψ‖ ^ 2 - ‖K.starProjection ψ‖ ^ 2) ≤ _
  rw [hres, ← b.sum_sq_norm_inner_right y, Finset.mul_sum, henergySub]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : hH.eigenvalues k = E₀
  · have hmem : b k ∈ K := eigenvectorBasis_mem_groundSpace hH hk
    have hzero : ⟪b k, y⟫_ℂ = 0 := by
      rw [inner_eq_zero_symm]
      exact K.starProjection_inner_eq_zero ψ (b k) hmem
    simp [hzero, hk]
  · have hzero : ⟪b k, K.starProjection ψ⟫_ℂ = 0 :=
      inner_eq_zero_of_mem_groundSpace hH hk (hb k) (K.starProjection_apply_mem ψ)
    have hge := (hgap k).resolve_left hk
    simp only [y, inner_sub_right, hzero, sub_zero]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- A unit eigenvector of a Hermitian approximation minimizes its quadratic form
and has excess original energy at most twice the operator-norm error.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_energy_le_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ ε : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      (⟪φ, toEuclideanLin H φ⟫_ℂ).re - E₀ ≤ 2 * ε := by
  have : Nontrivial (EuclideanSpace ℂ n) :=
    ⟨⟨Ω, 0, fun h ↦ by simp [h] at hΩ⟩⟩
  have hMsym : (toEuclideanCLM (𝕜 := ℂ) (n := n) M :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n).IsSymmetric :=
    isSymmetric_toEuclideanLin_iff.mpr hM
  obtain ⟨φ, hφ, heig, hmin⟩ := exists_unit_eigenvector_re_inner_le hMsym
  have hE₀ : (⟪Ω, toEuclideanLin H Ω⟫_ℂ).re = E₀ := by
    change (⟪Ω, toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω⟫_ℂ).re = E₀
    rw [hHΩ, inner_smul_right, inner_self_eq_norm_sq_to_K, hΩ]
    simp
  have hminΩ := hmin Ω
  have hdiffΩ := unit_energy_error_le hHM hΩ
  have hdiffφ := unit_energy_error_le hHM hφ
  have henergy : (⟪φ, toEuclideanLin H φ⟫_ℂ).re - E₀ ≤ 2 * ε := by
    rw [hΩ, one_pow, mul_one] at hminΩ
    change (⟪φ, toEuclideanLin M φ⟫_ℂ).re ≤
      (⟪Ω, toEuclideanLin M Ω⟫_ℂ).re at hminΩ
    linarith [(abs_le.mp hdiffΩ).1, (abs_le.mp hdiffφ).2]
  exact ⟨_, φ, hφ, heig, hmin, henergy⟩

/-- An actual ground vector of a Hermitian approximation has large overlap with the
unit vector spanning the ground space of a gapped Hermitian Hamiltonian.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_overlap_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ Δ ε : ℝ} {Ω : EuclideanSpace ℂ n} (hH : H.IsHermitian) (hΩ : ‖Ω‖ = 1)
    (hgs : IsGapped H E₀ Δ) (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) (hΔ : 0 < Δ)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      Δ * (1 - ‖⟪Ω, φ⟫_ℂ‖ ^ 2) ≤ 2 * ε ∧
      ∃ θ : ℝ, IsMinOn
        (fun α : ℝ ↦ ‖φ - Complex.exp (α * Complex.I) • Ω‖) Set.univ θ ∧
        ‖φ - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ 4 * ε / Δ := by
  have hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  obtain ⟨e, φ, hφ, heig, hmin, henergy⟩ :=
    exists_groundVector_energy_le_of_norm_sub_le hΩ hHΩ hM hHM
  have hgap : Δ * (1 - ‖⟪Ω, φ⟫_ℂ‖ ^ 2) ≤ 2 * ε := by
    have hg := (hgs.posSemidef_sub_smul_one hH hΩ hspan).gap_le φ
    rw [hφ, one_pow, mul_one] at hg
    exact hg.trans henergy
  obtain ⟨θ, hminθ, hθ⟩ := exists_isMinOn_sq_norm_sub_exp_smul_le_of_gap hΔ hφ hΩ hgap
  refine ⟨_, φ, hφ, heig, hmin, hgap, θ, hminθ, ?_⟩
  simpa only [show (2 : ℝ) * (2 * ε) = 4 * ε by ring] using hθ

/-- The same energy comparison controls mass outside the canonical ground eigenspace,
without a simplicity assumption on the original ground energy.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_projected_mass_of_norm_sub_le {H M : Matrix n n ℂ}
    {E₀ Δ ε : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hgap : ∀ ψ : EuclideanSpace ℂ n,
      Δ * (‖ψ‖ ^ 2 - ‖(groundSpace H E₀).starProjection ψ‖ ^ 2) ≤
        (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2)
    (hM : M.IsHermitian) (hHM : ‖H - M‖ ≤ ε) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      Δ * (1 - ‖(groundSpace H E₀).starProjection φ‖ ^ 2) ≤ 2 * ε ∧
      (2 * ε < Δ → (groundSpace H E₀).starProjection φ ≠ 0) := by
  obtain ⟨e, φ, hφ, heig, hmin, henergy⟩ :=
    exists_groundVector_energy_le_of_norm_sub_le hΩ hHΩ hM hHM
  have hmass : Δ * (1 - ‖(groundSpace H E₀).starProjection φ‖ ^ 2) ≤ 2 * ε := by
    have hg := hgap φ
    rw [hφ, one_pow, mul_one] at hg
    exact hg.trans henergy
  refine ⟨e, φ, hφ, heig, hmin, hmass, ?_⟩
  intro hsmall hz
  rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, mul_one] at hmass
  linarith

/-- A logarithmic radius makes an exponential approximation error smaller than
one quarter of the gap times a prescribed accuracy.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exp_error_le_of_log_radius {B β Δ τ ℓ : ℝ} (hβ : 0 < β) (hΔ : 0 < Δ)
    (hτ : 0 < τ) (hℓ : Real.log (4 * max B 1 / (Δ * τ)) / β ≤ ℓ) :
    B * Real.exp (-(β * ℓ)) ≤ Δ * τ / 4 := by
  let Q := max B 1
  have hQ : 0 < Q := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hr : 0 < 4 * Q / (Δ * τ) := by positivity
  have hlog : Real.log (4 * Q / (Δ * τ)) ≤ ℓ * β := (div_le_iff₀ hβ).mp hℓ
  have he : Real.exp (-(β * ℓ)) ≤ Δ * τ / (4 * Q) := by
    calc Real.exp (-(β * ℓ)) ≤ Real.exp (-Real.log (4 * Q / (Δ * τ))) :=
        Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_neg, Real.exp_log hr, inv_div]
  calc B * Real.exp (-(β * ℓ)) ≤ Q * Real.exp (-(β * ℓ)) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ Q * (Δ * τ / (4 * Q)) := mul_le_mul_of_nonneg_left he hQ.le
    _ = _ := by field_simp

/-- An exponential norm approximation gives a ground vector of nonzero overlap
and arbitrary phase-minimized accuracy at an explicit logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_overlap_of_exp_norm_bound {H M : Matrix n n ℂ}
    {E₀ Δ B β ℓ η : ℝ} {Ω : EuclideanSpace ℂ n} (hH : H.IsHermitian) (hΩ : ‖Ω‖ = 1)
    (hgs : IsGapped H E₀ Δ) (hspan : groundSpace H E₀ = Submodule.span ℂ {Ω}) (hΔ : 0 < Δ)
    (hM : M.IsHermitian) (hβ : 0 < β) (hη : 0 < η)
    (hHM : ‖H - M‖ ≤ B * Real.exp (-(β * ℓ)))
    (hℓ : Real.log (4 * max B 1 / (Δ * min η 1)) / β ≤ ℓ) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      ⟪Ω, φ⟫_ℂ ≠ 0 ∧
      ∃ θ : ℝ, IsMinOn
        (fun α : ℝ ↦ ‖φ - Complex.exp (α * Complex.I) • Ω‖) Set.univ θ ∧
        ‖φ - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ η := by
  have herr := exp_error_le_of_log_radius hβ hΔ (lt_min hη zero_lt_one) hℓ
  obtain ⟨e, φ, hφ, heig, hmin, hgap, θ, hminθ, hphase⟩ :=
    exists_groundVector_overlap_of_norm_sub_le hH hΩ hgs hspan hΔ hM hHM
  have hsmall : 2 * (B * Real.exp (-(β * ℓ))) ≤ Δ / 2 := by
    nlinarith [min_le_right η 1]
  have hnonzero : ⟪Ω, φ⟫_ℂ ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, mul_one] at hgap
    linarith
  refine ⟨e, φ, hφ, heig, hmin, hnonzero, θ, hminθ, hphase.trans ?_⟩
  apply le_trans _ (min_le_left η 1)
  apply (div_le_iff₀ hΔ).mpr
  nlinarith


/-- An exponential approximation gives a ground vector with nonzero projection onto
the full original ground eigenspace at a logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_groundVector_projection_of_exp_norm_bound {H M : Matrix n n ℂ}
    {E₀ Δ B β ℓ η : ℝ} {Ω : EuclideanSpace ℂ n} (hΩ : ‖Ω‖ = 1)
    (hHΩ : toEuclideanCLM (𝕜 := ℂ) (n := n) H Ω = (E₀ : ℂ) • Ω)
    (hgap : ∀ ψ : EuclideanSpace ℂ n,
      Δ * (‖ψ‖ ^ 2 - ‖(groundSpace H E₀).starProjection ψ‖ ^ 2) ≤
        (⟪ψ, toEuclideanLin H ψ⟫_ℂ).re - E₀ * ‖ψ‖ ^ 2)
    (hΔ : 0 < Δ) (hM : M.IsHermitian) (hβ : 0 < β) (hη : 0 < η)
    (hHM : ‖H - M‖ ≤ B * Real.exp (-(β * ℓ)))
    (hℓ : Real.log (4 * max B 1 / (Δ * min η 1)) / β ≤ ℓ) :
    ∃ (e : ℝ) (φ : EuclideanSpace ℂ n), ‖φ‖ = 1 ∧
      toEuclideanCLM (𝕜 := ℂ) (n := n) M φ = (e : ℂ) • φ ∧
      (∀ ψ : EuclideanSpace ℂ n,
        e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
      (groundSpace H E₀).starProjection φ ≠ 0 ∧
      1 - ‖(groundSpace H E₀).starProjection φ‖ ^ 2 ≤ η := by
  have herr := exp_error_le_of_log_radius hβ hΔ (lt_min hη zero_lt_one) hℓ
  obtain ⟨e, φ, hφ, heig, hmin, hmass, hnonzero⟩ :=
    exists_groundVector_projected_mass_of_norm_sub_le hΩ hHΩ hgap hM hHM
  have hsmall : 2 * (B * Real.exp (-(β * ℓ))) < Δ := by
    nlinarith [min_le_right η 1]
  refine ⟨e, φ, hφ, heig, hmin, hnonzero hsmall, ?_⟩
  apply (mul_le_mul_iff_right₀ hΔ).mp
  nlinarith [min_le_left η 1]

/-- The actual metric-ball truncated Hamiltonian has a ground vector with nonzero
projection onto the full original ground eigenspace at a logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_metric_truncated_groundVector_projection {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ β C : ℝ, 0 < c₁ ∧ 0 < β ∧ 0 ≤ C ∧
      ∀ {V : Type*} [PseudoMetricSpace V] [Fintype V] [DecidableEq V] {X : V → Type*}
        [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)],
        ∀ (Φ : Interaction X (metricRangeBall R))
          (_hHerm : ∀ i, (Φ.term i).IsHermitian)
          (_hNorm : ∀ i, ‖Φ.term i‖ ≤ J)
          (_hCard : ∀ i : V, (metricRangeBall R i).card ≤ S)
          (hH : Φ.hamiltonian.IsHermitian) {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Config X)},
          ‖Ω‖ = 1 →
          toEuclideanCLM (𝕜 := ℂ) (n := Config X) Φ.hamiltonian Ω = (E₀ : ℂ) • Ω →
          (∀ k, hH.eigenvalues k = E₀ ∨ E₀ + Δ ≤ hH.eigenvalues k) →
          ∀ {η : ℝ}, 0 < η → ∀ ℓ : ℝ,
          max R (Real.log (4 * max ((Fintype.card V : ℝ) * (J * C)) 1 /
            (Δ * min η 1)) / β) ≤ ℓ →
          let M := ∑ i, gaussianFilteredTerm (c₁ * ℓ * Δ) Δ
            (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j) (Φ.term i)
          ∃ (e : ℝ) (φ : EuclideanSpace ℂ (Config X)), ‖φ‖ = 1 ∧
            toEuclideanCLM (𝕜 := ℂ) (n := Config X) M φ = (e : ℂ) • φ ∧
            (∀ ψ : EuclideanSpace ℂ (Config X),
              e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
            (groundSpace Φ.hamiltonian E₀).starProjection φ ≠ 0 ∧
            1 - ‖(groundSpace Φ.hamiltonian E₀).starProjection φ‖ ^ 2 ≤ η := by
  obtain ⟨c₁, β, C, hc₁, hβ, hC, hbound⟩ :=
    exists_metric_truncated_filter_sum_bound hR S hJ hΔ
  refine ⟨c₁, β, C, hc₁, hβ, hC, ?_⟩
  intro V _ _ _ X _ _ Φ hHerm hNorm hCard hH E₀ Ω hΩ hHΩ hgapSpec η hη ℓ hℓ M
  have hℓR : R ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓlog := (le_max_right _ _).trans hℓ
  have hM : M.IsHermitian :=
    (isSelfAdjoint_sum _ fun i _ ↦ (isHermitian_gaussianFilteredTerm _ _
      (isSelfAdjoint_sum _ fun j _ ↦ (hHerm j).isSelfAdjoint).isHermitian
      (hHerm i)).isSelfAdjoint).isHermitian
  have hgap := groundSpace_gap_le_of_eigenvalues hH hgapSpec
  apply exists_groundVector_projection_of_exp_norm_bound hΩ hHΩ hgap hΔ hM hβ hη _ hℓlog
  have hb := hbound Φ hHerm hNorm hCard ℓ hℓR
  rw [norm_sub_rev] at hb
  simpa only [M, mul_assoc] using hb

/-- The actual metric-ball truncated Hamiltonian has a ground vector with nonzero
original-ground-state overlap and arbitrary accuracy at a logarithmic radius.
Hastings, arXiv:cond-mat/0508554v3, lines 359–367. -/
theorem exists_metric_truncated_groundVector_overlap {R J Δ : ℝ} (hR : 0 < R)
    (S : ℕ) (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ c₁ β C : ℝ, 0 < c₁ ∧ 0 < β ∧ 0 ≤ C ∧
      ∀ {V : Type*} [PseudoMetricSpace V] [Fintype V] [DecidableEq V] {X : V → Type*}
        [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)],
        ∀ (Φ : Interaction X (metricRangeBall R))
          (_hHerm : ∀ i, (Φ.term i).IsHermitian)
          (_hNorm : ∀ i, ‖Φ.term i‖ ≤ J)
          (_hCard : ∀ i : V, (metricRangeBall R i).card ≤ S)
          {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Config X)}, ‖Ω‖ = 1 →
          IsGapped Φ.hamiltonian E₀ Δ → groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Ω} →
          ∀ {η : ℝ}, 0 < η → ∀ ℓ : ℝ,
          max R (Real.log (4 * max ((Fintype.card V : ℝ) * (J * C)) 1 /
            (Δ * min η 1)) / β) ≤ ℓ →
          let M := ∑ i, gaussianFilteredTerm (c₁ * ℓ * Δ) Δ
            (∑ j ∈ metricRangeBall (ℓ - R) i, Φ.term j) (Φ.term i)
          ∃ (e : ℝ) (φ : EuclideanSpace ℂ (Config X)), ‖φ‖ = 1 ∧
            toEuclideanCLM (𝕜 := ℂ) (n := Config X) M φ = (e : ℂ) • φ ∧
            (∀ ψ : EuclideanSpace ℂ (Config X),
              e * ‖ψ‖ ^ 2 ≤ (⟪ψ, toEuclideanLin M ψ⟫_ℂ).re) ∧
            ⟪Ω, φ⟫_ℂ ≠ 0 ∧
            ∃ θ : ℝ, IsMinOn
              (fun α : ℝ ↦ ‖φ - Complex.exp (α * Complex.I) • Ω‖) Set.univ θ ∧
              ‖φ - Complex.exp (θ * Complex.I) • Ω‖ ^ 2 ≤ η := by
  obtain ⟨c₁, β, C, hc₁, hβ, hC, hbound⟩ :=
    exists_metric_truncated_filter_sum_bound hR S hJ hΔ
  refine ⟨c₁, β, C, hc₁, hβ, hC, ?_⟩
  intro V _ _ _ X _ _ Φ hHerm hNorm hCard E₀ Ω hΩ hgs hspan η hη ℓ hℓ M
  have hℓR : R ≤ ℓ := (le_max_left _ _).trans hℓ
  have hℓlog := (le_max_right _ _).trans hℓ
  have hM : M.IsHermitian :=
    (isSelfAdjoint_sum _ fun i _ ↦ (isHermitian_gaussianFilteredTerm _ _
      (isSelfAdjoint_sum _ fun j _ ↦ (hHerm j).isSelfAdjoint).isHermitian
      (hHerm i)).isSelfAdjoint).isHermitian
  apply exists_groundVector_overlap_of_exp_norm_bound (Interaction.isHermitian_hamiltonian hHerm)
    hΩ hgs hspan hΔ hM hβ hη _ hℓlog
  have hb := hbound Φ hHerm hNorm hCard ℓ hℓR
  rw [norm_sub_rev] at hb
  simpa only [M, mul_assoc] using hb

end GroundStateOverlap

end ManyBody
