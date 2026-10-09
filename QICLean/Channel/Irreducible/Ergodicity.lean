/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.FixedPoint.Cesaro
import QICLean.Channel.FixedPoint.MeanErgodicProjection
import QICLean.Channel.Irreducible.CollatzWielandt

/-!
# Ergodicity of irreducible positive trace-preserving maps

This file develops the fixed-state and zero-indexed Cesàro convergence results
needed for **Wolf Corollary 6.3**.  They hold for arbitrary positive
trace-preserving maps; complete positivity is not required.

For a positive trace-preserving map `E : M_D(ℂ) → M_D(ℂ)`, we prove:

* if `E` is irreducible, then there is a unique density-matrix fixed point `σ > 0`;
* consequently, for every density matrix `ρ`,

$$\lim_{N \to \infty} \frac{1}{N} \sum_{t=0}^{N-1} E^t(\rho) = \sigma.$$

This is the zero-indexed companion of Wolf Equation (6.35), whose literal
one-indexed form is stated in `PositiveMapErgodicity`.  It is the quantum
analogue of the classical ergodic theorem: the time average converges to a
unique full-rank stationary state.

The convergence proof follows Wolf's mean-ergodic projection from Equation
(6.14).  Irreducibility makes the density-matrix fixed point unique, so the
projection sends every density matrix to that state.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Corollary 6.3][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open Matrix Finset

variable {D : ℕ}

section Ergodicity

variable (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)

/-- **Wolf Corollary 6.3, qualitative form.**  An irreducible positive
trace-preserving map has a unique density-matrix fixed point, and this fixed
point is positive definite. -/
theorem IsPositiveMap.exists_unique_density_fixedPoint_of_irreducible [NeZero D]
    (hE : IsPositiveMap E) (hTP : IsTracePreservingMap E)
    (hIrr : IsIrreducibleMap E) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ ∈ densityMatrices D ∧ σ.PosDef ∧ E σ = σ ∧
      ∀ τ : Matrix (Fin D) (Fin D) ℂ,
        τ ∈ densityMatrices D → E τ = τ → τ = σ := by
  obtain ⟨σ, r, hσ_mem, hr, hσ_pd, hσ_eig, -⟩ :=
    exists_posDef_eigenvector_of_irreducible_positive E hE hIrr
  have hr_one : r = 1 := by
    have htrace := hTP σ
    rw [hσ_eig, Matrix.trace_smul, hσ_mem.2, smul_eq_mul, mul_one] at htrace
    exact_mod_cast htrace
  have hσ_fix : E σ = σ := by simpa [hr_one] using hσ_eig
  refine ⟨σ, hσ_mem, hσ_pd, hσ_fix, ?_⟩
  intro τ hτ_mem hτ_fix
  obtain ⟨c, hτ_eq⟩ :=
    eigenvector_eq_smul_of_irreducible_positive E hE hIrr zero_le_one
      hσ_pd (by simpa using hσ_fix) (by simpa using hτ_fix)
  have hc : c = 1 := by
    have htr : Matrix.trace (c • σ) = 1 := by
      simpa [hτ_eq] using hτ_mem.2
    rw [Matrix.trace_smul, hσ_mem.2] at htr
    simpa using htr
  simpa [hc] using hτ_eq

/-- Channel specialization of
`IsPositiveMap.exists_unique_density_fixedPoint_of_irreducible`. -/
theorem IsChannel.exists_unique_density_fixedPoint_of_irreducible
    (hE : IsChannel E) (hIrr : IsIrreducibleMap E) (hD : 0 < D) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ ∈ densityMatrices D ∧ σ.PosDef ∧ E σ = σ ∧
      ∀ τ : Matrix (Fin D) (Fin D) ℂ,
        τ ∈ densityMatrices D → E τ = τ → τ = σ := by
  let _ : NeZero D := ⟨Nat.ne_of_gt hD⟩
  exact IsPositiveMap.exists_unique_density_fixedPoint_of_irreducible
    (E := E) hE.pos hE.tp hIrr

/-- **Wolf Corollary 6.3 (zero-indexed time-average form).**  For an
irreducible positive trace-preserving map, the Cesàro mean of the iterates of
any density matrix converges to the unique positive-definite density-matrix
fixed point.

The proof identifies the limit with Wolf's mean-ergodic projection from
Equation (6.14). -/
theorem IsPositiveMap.cesaroMean_tendsto_of_irreducible [NeZero D]
    (hE : IsPositiveMap E) (hTP : IsTracePreservingMap E)
    (hIrr : IsIrreducibleMap E)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ ∈ densityMatrices D ∧ σ.PosDef ∧ E σ = σ ∧
      (∀ τ : Matrix (Fin D) (Fin D) ℂ,
        τ ∈ densityMatrices D → E τ = τ → τ = σ) ∧
      Filter.Tendsto (fun N => cesaroMean E ρ (N + 1)) Filter.atTop (nhds σ) := by
  obtain ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique⟩ :=
    IsPositiveMap.exists_unique_density_fixedPoint_of_irreducible
      (E := E) hE hTP hIrr
  let hbounded := hE.hasBoundedOrbits_of_tracePreserving hTP
  let P := LinearMap.meanErgodicProjection E hbounded
  have hPρ_mem : P ρ ∈ densityMatrices D := by
    refine ⟨(hE.meanErgodicProjection_isPositiveMap hbounded) ρ hρ.1, ?_⟩
    rw [hTP.meanErgodicProjection_isTracePreservingMap hbounded ρ, hρ.2]
  have hPρ_fix : E (P ρ) = P ρ := by
    have hcomp := congrArg
      (fun F : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ ↦ F ρ)
      hbounded.comp_meanErgodicProjection
    simpa only [P, LinearMap.comp_apply] using hcomp
  have hPρ_eq : P ρ = σ := hσ_unique (P ρ) hPρ_mem hPρ_fix
  have hzeroIndexed : Filter.Tendsto (fun N => cesaroMean E ρ N)
      Filter.atTop (nhds (P ρ)) := by
    simpa only [P, hbounded, cesaroMean_eq_birkhoffAverage] using
      hE.tendsto_birkhoffAverage_meanErgodicProjection_of_tracePreserving hTP ρ
  have h_tendsto : Filter.Tendsto (fun N => cesaroMean E ρ (N + 1))
      Filter.atTop (nhds σ) := by
    have hshift := hzeroIndexed.comp (Filter.tendsto_add_atTop_nat 1)
    change Filter.Tendsto
      ((fun N => cesaroMean E ρ N) ∘ fun N => N + 1) Filter.atTop (nhds σ)
    simpa only [hPρ_eq] using hshift
  exact ⟨σ, hσ_mem, hσ_pd, hσ_fix, hσ_unique, h_tendsto⟩

/-- Channel specialization of
`IsPositiveMap.cesaroMean_tendsto_of_irreducible`. -/
theorem IsChannel.cesaroMean_tendsto_of_irreducible
    (hE : IsChannel E) (hIrr : IsIrreducibleMap E) (hD : 0 < D)
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hρ : ρ ∈ densityMatrices D) :
    ∃ σ : Matrix (Fin D) (Fin D) ℂ,
      σ ∈ densityMatrices D ∧ σ.PosDef ∧ E σ = σ ∧
      (∀ τ : Matrix (Fin D) (Fin D) ℂ,
        τ ∈ densityMatrices D → E τ = τ → τ = σ) ∧
      Filter.Tendsto (fun N => cesaroMean E ρ (N + 1)) Filter.atTop (nhds σ) := by
  let _ : NeZero D := ⟨Nat.ne_of_gt hD⟩
  exact IsPositiveMap.cesaroMean_tendsto_of_irreducible
    (E := E) hE.pos hE.tp hIrr hρ

end Ergodicity
