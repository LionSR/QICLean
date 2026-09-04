/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.PerronFrobenius.Normalization
import QICLean.Channel.Irreducible.AdjointFamily
import QICLean.Channel.Irreducible.Growth.OneStep
import QICLean.Channel.KrausMap
import QICLean.Algebra.MatrixAux
import QICLean.Channel.FixedPoint.BrouwerDensityMatrices

/-!
# Perron–Frobenius eigenvector existence for positive maps

This module provides the **existence** of a positive semidefinite eigenvector for
a positive map on `M_D(ℂ)`, and derives from it a PosDef eigenvector of
the adjoint Kraus map of an irreducible Kraus family.

The transfer-map specializations for MPS tensors (the trace-preserving and
unital gauge normalizations of an irreducible tensor) live in
`TNLean.MPS.Irreducible.PerronGauge`.

## Brouwer fixed-point theorem on density matrices

The density-normalized existence theorem is proved via Brouwer's fixed-point
theorem applied to the normalization map
`ρ ↦ E(ρ) / tr(E(ρ))` on the compact convex set of density matrices.

Wolf states Theorem 6.5 at local source lines 743--747 without giving a proof.
The Brouwer argument in this module is supplied by the present development; it
is not attributed to the lecture notes.

The required density-matrix Brouwer theorem is proved in
`TNLean.Channel.FixedPoint.BrouwerDensityMatrices`.

## Main results

* `exists_density_eigenvector_of_positive_of_nonvanishing`: density-normalized
  eigenvector existence for positive maps which do not vanish on density matrices
* `exists_posSemidef_eigenvector`: the established nonzero-PSD interface
  (with nonvanishing hypothesis, eigenvalue `r > 0`)
* `exists_posSemidef_eigenvector_general`: PSD eigenvector existence for *any*
  positive map (no nonvanishing hypothesis, eigenvalue `r ≥ 0`)
* `Kraus.exists_posDef_adjoint_eigenvector`:
    PosDef eigenvector for the adjoint Kraus map of an irreducible family

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 6.2
  Theorems 6.3/6.5][Wolf2012QChannels]
* [Cirac et al., arXiv:1606.00608, Appendix A][Cirac2017Annals]
* [Evans–Høegh-Krohn, *Spectral properties of positive maps*, 1978][Evans1978Spectral]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset

variable {d D : ℕ}

/-! ## Core existence theorem -/

/-- A positive map which does not vanish on density matrices has a
density-matrix eigenvector with a strictly positive real eigenvalue.

This is the density-normalized Brouwer construction used in the
positive-regularization proof of Wolf Theorem 6.5.  Wolf states that theorem,
without a proof, at local source lines 743--747.  The fixed-point argument here
is supplied by the present development. -/
theorem exists_density_eigenvector_of_positive_of_nonvanishing
    [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hpos : IsPositiveMap E)
    (hNZ : ∀ ρ ∈ densityMatrices D, E ρ ≠ 0) :
    ∃ ρ ∈ densityMatrices D, ∃ r : ℝ,
      0 < r ∧ E ρ = (r : ℂ) • ρ := by
  classical
  have hMapsTo : Set.MapsTo (normMap (D := D) E) (densityMatrices D) (densityMatrices D) := by
    intro ρ hρ
    exact normMap_mem_densityMatrices (D := D) (E := E) hpos hNZ ρ hρ
  have hCont : ContinuousOn (normMap (D := D) E) (densityMatrices D) :=
    continuousOn_normMap_densityMatrices (D := D) (E := E) hpos hNZ
  obtain ⟨ρ, hρ, hρfix⟩ :=
    brouwer_fixedPoint_densityMatrices (D := D) (f := normMap (D := D) E) hCont hMapsTo
  have hEρpsd : (E ρ).PosSemidef := hpos ρ hρ.1
  have hEρne : E ρ ≠ 0 := hNZ ρ hρ
  have htrace_ne : Matrix.trace (E ρ) ≠ 0 := by
    intro htrace
    exact hEρne ((hEρpsd.trace_eq_zero_iff).1 htrace)
  have hEig : E ρ = Matrix.trace (E ρ) • ρ :=
    (eq_normMap_iff_eigenvector (D := D) (E := E) ρ htrace_ne).1 hρfix
  let r : ℝ := (Matrix.trace (E ρ)).re
  have hr_nonneg : 0 ≤ r := by
    simpa [r] using (RCLike.nonneg_iff.mp hEρpsd.trace_nonneg).1
  have htrace_eq : Matrix.trace (E ρ) = (r : ℂ) := by
    symm
    exact
      (RCLike.ofReal_eq_re_of_isSelfAdjoint
        (IsSelfAdjoint.of_nonneg hEρpsd.trace_nonneg)).mp rfl
  have hr_ne : r ≠ 0 := by
    intro hr
    exact htrace_ne (by simp [htrace_eq, hr])
  have hr : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_ne)
  exact ⟨ρ, hρ, r, hr, by simpa [htrace_eq] using hEig⟩

/-- **Perron–Frobenius eigenvector existence for positive maps**
(a fixed-point ingredient for Wolf Theorem 6.5).

Let `E` be a positive linear map on `M_D(ℂ)` (with `D > 0`) such that `E ρ ≠ 0` for every
nonzero PSD matrix `ρ`. Then there exists a nonzero PSD matrix `ρ` and a positive real `r`
such that `E ρ = r • ρ`.

Wolf Theorem 6.5 states the stronger spectral-radius conclusion for every
positive map.  The declaration here records the nonvanishing Brouwer
ingredient and does not claim that its eigenvalue is the spectral radius.

It is a wrapper around the density-normalized theorem above. -/
theorem exists_posSemidef_eigenvector
    [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hpos : IsPositiveMap E)
    (hNZ : ∀ {ρ : Matrix (Fin D) (Fin D) ℂ}, ρ.PosSemidef → ρ ≠ 0 → E ρ ≠ 0) :
    ∃ (ρ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ),
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 < r ∧ E ρ = (r : ℂ) • ρ := by
  have hNZ_density : ∀ ρ ∈ densityMatrices D, E ρ ≠ 0 := by
    intro ρ hρ
    apply hNZ hρ.1
    intro hρzero
    have := hρ.2
    simp [hρzero] at this
  obtain ⟨ρ, hρ, r, hr, hEig⟩ :=
    exists_density_eigenvector_of_positive_of_nonvanishing E hpos hNZ_density
  have hρ_ne : ρ ≠ 0 := by
    intro hρzero
    have := hρ.2
    simp [hρzero] at this
  exact ⟨ρ, r, hρ.1, hρ_ne, hr, hEig⟩

/-- **Perron–Frobenius eigenvector existence for general positive maps.**

For *any* positive linear map `E` on `M_D(ℂ)` (with `D > 0`), there exists a
nonzero PSD matrix `ρ` and a nonneg real `r ≥ 0` such that `E ρ = r • ρ`.

This generalises `exists_posSemidef_eigenvector` by removing the `hNZ` hypothesis
(E need not be nonvanishing on the PSD cone). The trade-off is that the eigenvalue
is only `0 ≤ r` (not `0 < r`): when E annihilates a nonzero PSD matrix, that
matrix is itself an eigenvector for eigenvalue 0.

This is weaker than Wolf Theorem 6.5: it does not identify `r` with the
spectral radius.  Wolf states the stronger theorem, without a proof, at local
source lines 743--747.

The proof is a case split:
* If E is nonvanishing on nonzero PSD matrices, apply `exists_posSemidef_eigenvector`.
* Otherwise, any nonzero PSD matrix in the kernel is an eigenvector for eigenvalue 0. -/
theorem exists_posSemidef_eigenvector_general
    [NeZero D]
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (hpos : IsPositiveMap E) :
    ∃ (ρ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ),
      ρ.PosSemidef ∧ ρ ≠ 0 ∧ 0 ≤ r ∧ E ρ = (r : ℂ) • ρ := by
  classical
  -- Case split: does E annihilate some nonzero PSD matrix?
  by_cases hNZ : ∀ (ρ : Matrix (Fin D) (Fin D) ℂ), ρ.PosSemidef → ρ ≠ 0 → E ρ ≠ 0
  · -- E is nonvanishing on nonzero PSD matrices → use existing theorem (r > 0).
    obtain ⟨ρ, r, hρ_psd, hρ_ne, hr_pos, hEig⟩ :=
      exists_posSemidef_eigenvector E hpos (hNZ := fun hpsd hne => hNZ _ hpsd hne)
    exact ⟨ρ, r, hρ_psd, hρ_ne, hr_pos.le, hEig⟩
  · -- E kills some nonzero PSD matrix → eigenvalue 0.
    push Not at hNZ
    obtain ⟨ρ₀, hρ₀_psd, hρ₀_ne, hEρ₀⟩ := hNZ
    exact ⟨ρ₀, 0, hρ₀_psd, hρ₀_ne, le_refl 0, by simp [hEρ₀]⟩

/-! ## Application to Kraus families -/

namespace Kraus

/-- **PosDef eigenvector of the adjoint Kraus map.**

For an irreducible finite Kraus family `K` with `D > 0` and some `K i ≠ 0`, there
exist a positive definite matrix `σ` and a positive real `r` with
`∑ᵢ (K i)ᴴ σ K i = r • σ`.

This theorem applies the project-supplied Brouwer theorem
`exists_posSemidef_eigenvector` to the conjugate-transposed Kraus map, noting
that irreducibility passes to that family, and then upgrades the resulting PSD
eigenvector to a PosDef one using irreducibility (Wolf Theorem 6.3 item 2). -/
theorem exists_posDef_adjoint_eigenvector
    [NeZero D]
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hIrr : IsIrreducibleMap (mapLM K))
    (hK : ∃ i, K i ≠ 0) :
    ∃ (σ : Matrix (Fin D) (Fin D) ℂ) (r : ℝ),
      σ.PosDef ∧ 0 < r ∧
      mapLM (fun i => (K i)ᴴ) σ = (r : ℂ) • σ := by
  -- Step 1: The conjugate-transposed Kraus map is CP.
  have hcp : IsCPMap (mapLM fun i => (K i)ᴴ) := isCPMap_mapLM _
  -- Step 2: It is nonzero.
  have hK_adj : ∃ i, (K i)ᴴ ≠ 0 := by
    obtain ⟨i, hi⟩ := hK
    exact ⟨i, fun h => hi (Matrix.conjTranspose_eq_zero.mp h)⟩
  have hE_ne : mapLM (fun i => (K i)ᴴ) ≠ 0 :=
    mapLM_ne_zero_of_exists_ne_zero _ hK_adj
  -- Step 3: Irreducibility passes to the conjugate-transposed family, so the map
  -- does not annihilate nonzero PSD matrices.
  have hIrrAdj : IsIrreducibleMap (mapLM fun i => (K i)ᴴ) :=
    isIrreducibleMap_mapLM_conjTranspose K hIrr
  have hNZ :
      ∀ {ρ : Matrix (Fin D) (Fin D) ℂ}, ρ.PosSemidef → ρ ≠ 0 →
        mapLM (fun i => (K i)ᴴ) ρ ≠ 0 :=
    IsIrreducibleMap.map_posSemidef_ne_zero
      (E := mapLM fun i => (K i)ᴴ) hcp hIrrAdj hE_ne
  -- Step 4: Get a PSD eigenvector by the core theorem.
  obtain ⟨σ, r, hσ_psd, hσ_ne, hr_pos, hσ_eig⟩ :=
    exists_posSemidef_eigenvector
      (E := mapLM fun i => (K i)ᴴ)
      hcp.isPositiveMap (hNZ := hNZ)
  -- Step 5: Upgrade PSD → PosDef (Wolf Theorem 6.3(2)).
  have hσ_pd : σ.PosDef :=
    posDef_of_posSemidef_eigenvector_irreducible_cp
      _ hcp hIrrAdj σ r hσ_psd hσ_ne hr_pos hσ_eig
  exact ⟨σ, r, hσ_pd, hr_pos, hσ_eig⟩

end Kraus
