/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TypicalSet
import QICLean.Entropy.TypicalPureState

/-!
# Typical spectral states from a surprisal tail

The canonical typical set of a density matrix is selected by its own eigenvalues
and entropy. A tail bound smaller than one gives positive selected mass. The
existing normalized spectral restriction then has the expected rank and entropy,
and a unit pure state is close to its selected vector.

## References

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), Lemma 3.1 (`lem:tail`), `02-initial.tex`, and
`comparator:typical-set`, `comparator:typical-entropies`, `07-comparators.tex`,
lines 39–55, at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are finite-dimensional consequences conditional on the spectral tail
bound. The physical choice of width and the asymptotic tail estimate are not
proved in this module.

Independently written from the manuscript; no upstream Lean proof text is reused.
-/

/-
Source: September 24, 2026.
Independently written; no upstream Lean proof text is reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:typical-set, comparator:typical-entropies.
Provenance-ID: 8753-qic-typical-tail-01
Downstream declaration:
Matrix.PosSemidef.typicalSet_normalizedSpectralRestriction_bounds
Provenance-ID: 8753-qic-typical-tail-02
Downstream declaration:
Matrix.typicalPureState_typicalSet_bounds
-/

open scoped BigOperators Matrix ComplexOrder InnerProductSpace

noncomputable section

private theorem abs_log_le_of_mass_bounds {z δ : ℝ} (hz : 0 < z) (hz1 : z ≤ 1)
    (hδ : δ < 1) (hzδ : 1 - δ ≤ z) : |Real.log z| ≤ -Real.log (1 - δ) := by
  rw [abs_of_nonpos (Real.log_nonpos hz.le hz1)]
  exact neg_le_neg (Real.log_le_log (by linarith) hzδ)

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : Matrix n n ℂ}

section Density

variable (hρ : ρ.PosSemidef) (w δ : ℝ)

local notation "p" => hρ.isHermitian.eigenvalues
local notation "S" => vonNeumannEntropy ρ hρ.isHermitian
local notation "E" => Entropy.typicalSet p S w
local notation "z" => hρ.isHermitian.spectralRestrictionMass E
local notation "σ" => hρ.isHermitian.normalizedSpectralRestriction E

private theorem typicalSet_mass_bounds (htr : ρ.trace = 1)
    (htail : Entropy.surprisalTail p S w ≤ δ) (hδ : δ < 1) :
    1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 := by
  have hm := Entropy.one_sub_surprisalTail_le_typicalMass hρ.eigenvalues_nonneg
    (posSemidef_trace_one_eigenvalues_sum_one hρ htr) S w
  have hzδ : 1 - δ ≤ z := (sub_le_sub_left htail 1).trans hm
  exact ⟨hzδ, (sub_pos.mpr hδ).trans_le hzδ, hρ.spectralRestrictionMass_le_one htr E⟩

/-- A spectral surprisal tail at most `δ < 1` gives selected mass between
`1 - δ` and one, and in particular positive mass. The actual normalized spectral
restriction is positive semidefinite with trace one and rank equal to the size
of the canonical typical set. Its logarithmic rank and entropy differ from the
original entropy by at most `w - log (1 - δ)`.
OpenAI area-law manuscript, `comparator:typical-set`, `comparator:typical-entropies`,
`07-comparators.tex`, lines 39–55, following Lemma 3.1. This finite-dimensional
consequence assumes the tail estimate, without a physical scale specialization. -/
theorem PosSemidef.typicalSet_normalizedSpectralRestriction_bounds (htr : ρ.trace = 1)
    (htail : Entropy.surprisalTail p S w ≤ δ) (hδ : δ < 1) :
    1 - δ ≤ z ∧ 0 < z ∧ z ≤ 1 ∧
      ∃ hσ : (σ).PosSemidef, (σ).trace = 1 ∧ (σ).rank = (E).card ∧
        |Real.log ((σ).rank : ℝ) - S| ≤ w - Real.log (1 - δ) ∧
        |vonNeumannEntropy σ hσ.isHermitian - S| ≤ w - Real.log (1 - δ) := by
  obtain ⟨hzδ, hz, hz1⟩ := typicalSet_mass_bounds hρ w δ htr htail hδ
  have hb := hρ.typicalSpectralRestriction_entropy_bounds E w hz
    (fun i hi ↦ Entropy.exp_le_of_mem_typicalSet hi)
  refine ⟨hzδ, hz, hz1, hρ.normalizedSpectralRestriction_posSemidef E hz,
    hρ.isHermitian.trace_normalizedSpectralRestriction E hz.ne',
    hρ.isHermitian.rank_normalizedSpectralRestriction E hz.ne'
      (fun i hi ↦ (Entropy.mem_typicalSet.mp hi).1), ?_, ?_⟩
  · exact hb.1.trans ((add_le_add (le_refl w) (abs_log_le_of_mass_bounds hz hz1 hδ hzδ)).trans_eq
      (sub_eq_add_neg w (Real.log (1 - δ))).symm)
  · exact hb.2.trans ((add_le_add (le_refl w) (abs_log_le_of_mass_bounds hz hz1 hδ hzδ)).trans_eq
      (sub_eq_add_neg w (Real.log (1 - δ))).symm)

end Density

section PureState

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
variable (ψ : EuclideanSpace ℂ (A × B)) (w δ : ℝ)

local notation "ρA" => partialTraceRight (vecMulVec ψ (star ψ))
local notation "hρA" => PosSemidef.partialTraceRight (posSemidef_vecMulVec_self_star ψ)
local notation "pA" => Matrix.IsHermitian.eigenvalues (Matrix.PosSemidef.isHermitian hρA)
local notation "SA" => vonNeumannEntropy ρA (Matrix.PosSemidef.isHermitian hρA)
local notation "EA" => Entropy.typicalSet pA SA w
local notation "φ" => typicalPureState ψ EA
local notation "ρE" => partialTraceRight (vecMulVec φ (star φ))
local notation "hρE" => PosSemidef.partialTraceRight (posSemidef_vecMulVec_self_star φ)

/-- For a unit bipartite vector, the canonical typical set of its actual first
marginal gives a unit selected vector with distance at most `sqrt (2 * δ)`.
Its actual first marginal has rank equal to the size of that same typical set;
its logarithmic rank and entropy differ from the original marginal entropy by
at most `w - log (1 - δ)`. OpenAI area-law manuscript,
`comparator:typical-set`, `comparator:typical-entropies`, `07-comparators.tex`,
lines 39–55 and 240–247, following Lemma 3.1. -/
theorem typicalPureState_typicalSet_bounds (hψ : ‖ψ‖ = 1)
    (htail : Entropy.surprisalTail pA SA w ≤ δ) (hδ : δ < 1) :
    ‖φ‖ = 1 ∧ ‖ψ - φ‖ ≤ Real.sqrt (2 * δ) ∧ (ρE).rank = (EA).card ∧
      |Real.log ((ρE).rank : ℝ) - SA| ≤ w - Real.log (1 - δ) ∧
      |vonNeumannEntropy ρE (hρE).isHermitian - SA| ≤ w - Real.log (1 - δ) := by
  have htr : (ρA).trace = 1 := by
    rw [trace_partialTraceRight]
    change ⟪ψ, ψ⟫_ℂ = 1
    simp [hψ]
  obtain ⟨hzδ, hz, _, hσ, _, hrank, hlog, hent⟩ :=
    (hρA).typicalSet_normalizedSpectralRestriction_bounds w δ htr htail hδ
  have hs := norm_sub_typicalPureState_sq_le ψ EA hψ hz
  have hsq : ‖ψ - φ‖ ^ 2 ≤ 2 * δ := by linarith
  have hmarginal := partialTraceRight_typicalPureState ψ EA hz
  refine ⟨norm_typicalPureState ψ EA hz, Real.le_sqrt_of_sq_le hsq,
    (congrArg Matrix.rank hmarginal).trans hrank, ?_, ?_⟩
  · simpa only [hmarginal] using hlog
  · simpa only [vonNeumannEntropy_congr hmarginal (hρE).isHermitian hσ.isHermitian] using hent

end PureState

end Matrix
