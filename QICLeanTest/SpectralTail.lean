import QICLean.Entropy.SpectralTail

/-! Canonical cutoff, zero-entropy, rank-deficient and distance-convention regressions. -/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

private def pureDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun i ↦ (![1, 0] i : ℝ))

private theorem pureDensity_psd : pureDensity.PosSemidef := by
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem pureDensity_trace : pureDensity.trace = 1 := by
  norm_num [pureDensity, trace, Fin.sum_univ_two]

/-- A zero eigenvalue has zero discarded mass, even at the zero-entropy cutoff one. -/
example : ((1 - spectralProjectionGE pureDensity 1) * pureDensity).trace.re = 0 := by
  have hproj : spectralProjectionGE pureDensity 1 = pureDensity := by
    rw [spectralProjectionGE, pureDensity,
      cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hproj]
  norm_num [pureDensity, sub_mul, diagonal_mul_diagonal, trace, Fin.sum_univ_two]

/-- The generic entropy-Markov theorem actually applies to a singular density. -/
example : ((1 - spectralProjectionGE pureDensity (1 / 2)) * pureDensity).trace.re ≤
    vonNeumannEntropy pureDensity pureDensity_psd.isHermitian / (-Real.log (1 / 2)) :=
  pureDensity_psd.trace_complement_spectralProjectionGE_le_entropy pureDensity_trace
    (by norm_num) (by norm_num)

private def mixedDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal (fun _ ↦ ((1 / 2 : ℝ) : ℂ))

/-- Equality at the cutoff belongs to the head, not the excluded mass. -/
example : spectralProjectionGE mixedDensity (1 / 2) = 1 ∧
    ((1 - spectralProjectionGE mixedDensity (1 / 2)) * mixedDensity).trace.re = 0 := by
  have h : spectralProjectionGE mixedDensity (1 / 2) = 1 := by
    rw [spectralProjectionGE, mixedDensity,
      cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
    norm_num [diagonal_one]
  exact ⟨h, by rw [h]; simp⟩

/-- Moving strictly above the maximal eigenvalue excludes all mass. -/
example : ((1 - spectralProjectionGE mixedDensity (3 / 4)) * mixedDensity).trace.re = 1 := by
  have h : spectralProjectionGE mixedDensity (3 / 4) = 0 := by
    rw [spectralProjectionGE, mixedDensity,
      cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
    norm_num
  rw [h]
  norm_num [mixedDensity, trace, Fin.sum_univ_two]

/-- Zero budget is handled at cutoff one, without assuming positive entropy. -/
example {n : Type*} [Fintype n] [DecidableEq n] {σ : Matrix n n ℂ}
    (hσ : σ.PosSemidef) (ht : σ.trace = 1)
    (hS : vonNeumannEntropy σ hσ.isHermitian ≤ 0) :
    (spectralProjectionGE σ (Real.exp (-16 * 0))).rank ≤ (1 : ℝ) ∧
      ((1 - spectralProjectionGE σ (Real.exp (-16 * 0))) * σ).trace.re = 0 := by
  simpa using hσ.spectralProjectionGE_one_of_entropy_nonpos ht hS

/-- The manuscript hypothesis is a full trace norm bound; the public distance is half. -/
example {D : ℕ} (ρ σ : Matrix (Fin D) (Fin D) ℂ)
    (h : traceNorm (ρ - σ) ≤ 1 / 16) : traceDistance ρ σ ≤ 1 / 32 := by
  rw [traceDistance_eq_traceNorm]
  linarith

/-- Empty index spaces cannot satisfy trace one. -/
example (σ : Matrix Empty Empty ℂ) : σ.trace ≠ 1 := by
  simp [Matrix.trace]

private def tiltedDensity : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- The original-state spectral projector need not commute with the target state. -/
example : ¬Commute (spectralProjectionGE pureDensity 1) tiltedDensity := by
  have hproj : spectralProjectionGE pureDensity 1 = pureDensity := by
    rw [spectralProjectionGE, pureDensity,
      cfc_diagonal _ _ ((Set.finite_range _).continuousOn _)]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hproj]
  intro h
  have h01 := congrFun (congrFun h.eq 0) 1
  norm_num [pureDensity, tiltedDensity, mul_apply, Fin.sum_univ_two] at h01

/-- The fixed original-state projector still has a valid transfer estimate. -/
example : ((1 - spectralProjectionGE pureDensity 1) * tiltedDensity).trace.re ≤
    ((1 - spectralProjectionGE pureDensity 1) * pureDensity).trace.re +
      traceDistance tiltedDensity pureDensity := by
  have ht : tiltedDensity.IsHermitian := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [tiltedDensity, conjTranspose_apply, starRingEnd_apply]
  have htr : tiltedDensity.trace = pureDensity.trace := by
    norm_num [tiltedDensity, pureDensity, trace, Fin.sum_univ_two]
  have hQ := pureDensity_psd.isHermitian.isStarProjection_spectralProjectionGE 1
  have h := re_trace_mul_sub_le_traceDistance ht pureDensity_psd.isHermitian htr
    hQ.one_sub.nonneg (sub_le_self _ hQ.nonneg)
  linarith
