/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.Product.ProductVector
import QICLean.ManyBody.Entropy.Filter.Optimizer
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.Entropy.Typical.TypicalSet
import QICLean.Algebra.Matrix.MatrixReindex
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.Models

/-!
# Marginal surprisal tails for finite-range interactions on the square lattice

Lemma 3.1 of the area-law manuscript holds for any finite tensor product
(`Entropy.log_surprisalMoment_cut_le`, `Entropy.surprisalTail_cut_le`). This module states it
for a finite-range interaction `ManyBody.PlaneInteraction Λ q R` on a finite domain `Λ` of the
square lattice: the regional state of a gapped unique ground vector satisfies the moment and
tail bounds with `ℬ = 1 + ∑ log² (e q^{|X|})` over the supports `X` that meet both sides of the
cut, and its typical spectrum carries the mass `1 - (n + 2)^{-M}`.

Moved from TNLean, `TNLean/Lattice/MarginalTails.lean`. Changes: the ground vector lies in
`EuclideanSpace ℂ (↥Λ → Fin q)` and the sites are written `↥Λ`, without the abbreviations
`StateSpace Λ q` and `Site Λ`.

## Main results

* `ManyBody.PlaneInteraction.log_surprisalMoment_regionState_le` — `eq:initial-tail-mgf` for
  the regional state.
* `ManyBody.PlaneInteraction.surprisalTail_regionState_le` — `eq:initial-tail-probability` for
  the regional state.
* `ManyBody.PlaneInteraction.one_sub_rpow_le_typicalMass_regionState` — the typical marginal
  spectrum at the concentration width `Entropy.concentrationWidth`.
* `Entropy.concentrationWidth`, `Entropy.one_sub_rpow_le_typicalMass_cut`: the typical marginal
  spectrum of a gapped ground vector.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–69, and the
  concentration statement after it, lines 209–219.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

section TypicalMarginalMass

/-!
## The typical marginal spectrum of a gapped ground vector

Lemma 3.1 of the two-dimensional area law bounds the surprisal tail of the marginal spectrum
of a gapped ground vector across a cut by `2 e^{e/2} exp(-w / (32 √((1 + ϑ) ℬ)))`, with
`ϑ = c₀ / g₀` and the cut budget `ℬ`. At the concentration width
`w = 32 √((1 + ϑ) ℬ) (M log (N + 2) + e/2 + log 2)` this tail is `(N + 2)^{-M}`, so the
eigenvalues whose surprisal lies within `w` of the entropy carry mass at least
`1 - (N + 2)^{-M}`. The statement holds on any finite tensor product, with the hypotheses of
`Entropy.surprisalTail_cut_le`.

Moved from TNLean, `TNLean/Lattice/MarginalTails.lean` at commit `e41c3b63`, restated at the
generality of `Entropy.surprisalTail_cut_le`; the lattice instance there is the case of a
finite-range interaction on a domain of the square lattice.

### Main definitions

* `Entropy.concentrationWidth` — the concentration width.

### Main results

* `Entropy.one_sub_rpow_le_typicalMass_cut` — the typical marginal spectrum carries mass at
  least `1 - (N + 2)^{-M}`.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–69, and the concentration statement
  after it, lines 209–219.
-/

namespace Entropy

/-- The concentration width `32 √((1 + ϑ) ℬ) (M log (N + 2) + e/2 + log 2)` at which the
marginal tail of Lemma 3.1, with ratio `ϑ` of norm bound to gap and cut budget `ℬ`, drops
to `(N + 2)^{-M}`. Two-dimensional area law, `02-initial.tex`, lines 209–219. -/
noncomputable def concentrationWidth (ϑ ℬ : ℝ) (N : ℕ) (M : ℝ) : ℝ :=
  32 * Real.sqrt ((1 + ϑ) * ℬ) * (M * Real.log (N + 2) + Real.exp 1 / 2 + Real.log 2)

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} {ι : Type*} [Fintype ι]
  {h : ι → Matrix (∀ v, Fin (n v)) (∀ v, Fin (n v)) ℂ} {D : ι → Finset V} {c₀ E₀ g₀ : ℝ}
  {Ψ : EuclideanSpace ℂ (∀ v, Fin (n v))} {B : Finset V}
  {ρ : Matrix ((v : {v // v ∈ B}) → Fin (n v)) ((v : {v // v ∈ B}) → Fin (n v)) ℂ}

/-- **The typical marginal spectrum.** In the setting of `surprisalTail_cut_le`, the
eigenvalues of the marginal `ρ` whose surprisal lies within the concentration width of
`S(ρ)` carry mass at least `1 - (N + 2)^{-M}`, for every `N` and every real `M`.
Two-dimensional area law, `02-initial.tex`, lines 209–219, the concentration statement after
Lemma 3.1, before the lattice bound on the cut budget is inserted. -/
theorem one_sub_rpow_le_typicalMass_cut (hsupp : ∀ i, ManyBody.IsSupportedOn (h i) (D i))
    (hherm : ∀ i, (h i).IsHermitian) (hc₀ : 0 ≤ c₀) (hnorm : ∀ i, ‖h i‖ ≤ c₀) (hΨ : ‖Ψ‖ = 1)
    (hg₀ : 0 < g₀) (heig : toEuclideanLin (∑ i, h i) Ψ = (E₀ : ℂ) • Ψ)
    (hgap : ((∑ i, h i) - (E₀ : ℂ) • 1 -
      (g₀ : ℂ) • (1 - vecMulVec (WithLp.ofLp Ψ) (star (WithLp.ofLp Ψ)))).PosSemidef)
    (hρdef : partialTraceRight (vecMulVec (WithLp.ofLp (ManyBody.cutVector B Ψ))
      (star (WithLp.ofLp (ManyBody.cutVector B Ψ)))) = ρ) (hρ : ρ.IsHermitian) (N : ℕ) (M : ℝ) :
    1 - ((N : ℝ) + 2) ^ (-M) ≤
      typicalMass hρ.eigenvalues (vonNeumannEntropy ρ hρ)
        (concentrationWidth (c₀ / g₀) (ManyBody.cutLogBudget D n B)
          N M) := by
  set ℬ := ManyBody.cutLogBudget D n B
  set w := concentrationWidth (c₀ / g₀) ℬ N M
  have hpsd : ρ.PosSemidef := by
    rw [← hρdef, ← ManyBody.regionState_eq_partialTraceRight_cutVector B Ψ]
    exact ManyBody.regionState_posSemidef B Ψ
  have hs : ∑ i, hρ.eigenvalues i = 1 := by
    have h1 : ρ.trace = 1 := by
      rw [← hρdef, ← ManyBody.regionState_eq_partialTraceRight_cutVector B Ψ]
      exact (ManyBody.trace_regionState B Ψ).trans (by simp [hΨ])
    have htr := hρ.trace_eq_sum_eigenvalues
    rw [h1] at htr
    have h2 := congrArg Complex.re htr
    simp only [Complex.one_re, Complex.re_sum] at h2
    exact h2.symm
  have htail := surprisalTail_cut_le hsupp hherm hc₀ hnorm hΨ hg₀ heig hgap hρdef hρ w
  have hmass := one_sub_surprisalTail_le_typicalMass hpsd.eigenvalues_nonneg hs
    (vonNeumannEntropy ρ hρ) w
  have hR : 0 < Real.sqrt ((1 + c₀ / g₀) * ℬ) := Real.sqrt_pos.mpr (by
    have : 0 ≤ c₀ / g₀ := div_nonneg hc₀ hg₀.le
    have := one_le_cutLogBudget (ManyBody.crossingTerms D B) (supportDim n ∘ D)
    positivity)
  have hexp : 2 * Real.exp (Real.exp 1 / 2) *
      Real.exp (-(w / (32 * Real.sqrt ((1 + c₀ / g₀) * ℬ)))) = ((N : ℝ) + 2) ^ (-M) := by
    have hw : w / (32 * Real.sqrt ((1 + c₀ / g₀) * ℬ)) =
        M * Real.log (N + 2) + Real.exp 1 / 2 + Real.log 2 := by
      simp only [w, concentrationWidth]
      exact mul_div_cancel_left₀ _ (by positivity)
    rw [hw, Real.rpow_def_of_pos (by positivity),
      show -(M * Real.log (N + 2) + Real.exp 1 / 2 + Real.log 2) =
        Real.log (N + 2) * -M + (-(Real.exp 1 / 2) + -Real.log 2) by ring, Real.exp_add,
      Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log two_pos]
    field_simp
  have h2 := htail.trans (min_le_right _ _)
  rw [hexp] at h2
  linarith

end Entropy

end TypicalMarginalMass

section PlaneMarginalTails

namespace ManyBody

variable {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}

/-- **Lemma 3.1 for a finite-range lattice Hamiltonian, moment bound.** For a gapped
ground vector `Ω` with gap `Δ > 0` of a finite-range Hamiltonian with term norms at most
`J ≥ 0`, and any cut `A`, the surprisal of the regional state satisfies
`log E e^{uK} ≤ u S(A) + 512 e (J/Δ) ℬ u²` for `|u| ≤ 1/(32 √((1 + J/Δ) ℬ))`, where
`ℬ = 1 + ∑ log² (e q^{|X|})` is the cut budget `ManyBody.cutLogBudget` of the admissible
supports `X` meeting both sides of the cut.
Area-law manuscript, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–63,
`eq:initial-tail-mgf`. -/
theorem PlaneInteraction.log_surprisalMoment_regionState_le
    (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (↥Λ → Fin q)} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (↥Λ)) {u : ℝ}
    (hu : |u| ≤ Entropy.tailRadius (J / Δ)
      (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A)) :
    Real.log (Entropy.surprisalMoment (ManyBody.regionState_isHermitian A Ω).eigenvalues u) ≤
      u * ManyBody.regionEntropy Ω A +
        512 * Real.exp 1 * (J / Δ) *
          ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A * u ^ 2 := by
  have heig : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  exact Entropy.log_surprisalMoment_cut_le (n := fun _ ↦ q) (B := A)
    (fun X ↦ (h.mem X))
    hh hJ hhJ hΩ hΔ heig
    (hgap.posSemidef_sub_smul_one (ManyBody.Interaction.isHermitian_hamiltonian hh) hΩ hspan)
        (ManyBody.regionState_eq_partialTraceRight_cutVector A Ω).symm
    (ManyBody.regionState_isHermitian A Ω) hu

/-- **Lemma 3.1 for a finite-range lattice Hamiltonian, tail bound.** Under the hypotheses
of `ManyBody.PlaneInteraction.log_surprisalMoment_regionState_le`, for every real `w` (the
manuscript states `w ≥ 0`),
`Pr {|K - S(A)| > w} ≤ min {1, 2 e^{e/2} exp (-w / (32 √((1 + J/Δ) ℬ)))}`.
Area-law manuscript, Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 64–69,
`eq:initial-tail-probability`. -/
theorem PlaneInteraction.surprisalTail_regionState_le (h : PlaneInteraction Λ q R)
    (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (↥Λ → Fin q)} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (↥Λ)) (w : ℝ) :
    Entropy.surprisalTail (ManyBody.regionState_isHermitian A Ω).eigenvalues
        (ManyBody.regionEntropy Ω A) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt ((1 + J / Δ) *
          ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A))))) := by
  have heig : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  exact Entropy.surprisalTail_cut_le (n := fun _ ↦ q) (B := A)
    (fun X ↦ (h.mem X))
    hh hJ hhJ hΩ hΔ heig
    (hgap.posSemidef_sub_smul_one (ManyBody.Interaction.isHermitian_hamiltonian hh) hΩ hspan)
        (ManyBody.regionState_eq_partialTraceRight_cutVector A Ω).symm
    (ManyBody.regionState_isHermitian A Ω) w

/-- **Typical marginal spectrum.** The positive eigenvalues of the regional state whose
surprisal lies within the concentration width of `S_Ω(A)` carry mass at least
`1 - (n + 2)^{-M}`.
Area-law manuscript, `02-initial.tex`, lines 209–219, the concentration statement after
Lemma 3.1, before the lattice budget `ℬ_A ≤ C (1 + |∂_Λ A|)` is inserted. -/
theorem PlaneInteraction.one_sub_rpow_le_typicalMass_regionState
    (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
        (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (↥Λ → Fin q)} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (A : Finset (↥Λ)) (n : ℕ) (M : ℝ) :
    1 - ((n : ℝ) + 2) ^ (-M) ≤
      Entropy.typicalMass (ManyBody.regionState_isHermitian A Ω).eigenvalues
        (ManyBody.regionEntropy Ω A)
        (Entropy.concentrationWidth (J / Δ)
          (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M) := by
  have hpsd := ManyBody.regionState_posSemidef A Ω
  have hp : ∀ i, 0 ≤ (ManyBody.regionState_isHermitian A Ω).eigenvalues i :=
    hpsd.eigenvalues_nonneg
  have hs : ∑ i, (ManyBody.regionState_isHermitian A Ω).eigenvalues i = 1 := by
    have htr := (ManyBody.regionState_isHermitian A Ω).trace_eq_sum_eigenvalues
    have h1 : (ManyBody.regionState Ω A).trace = 1 := ManyBody.trace_regionState_eq_one hΩ
    rw [h1] at htr
    have h2 := congrArg Complex.re htr
    simp only [Complex.one_re, Complex.re_sum] at h2
    rw [h2]
    exact Finset.sum_congr rfl fun i _ ↦ by simp
  have htail := h.surprisalTail_regionState_le hh hhJ hJ hΔ hΩ hgap hspan A
    (Entropy.concentrationWidth (J / Δ)
      (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M)
  have hmass := Entropy.one_sub_surprisalTail_le_typicalMass hp hs (ManyBody.regionEntropy Ω A)
    (Entropy.concentrationWidth (J / Δ)
      (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M)
  set Rr := Real.sqrt ((1 + J / Δ) *
    ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A)
  have hB : 1 ≤ ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A :=
    Entropy.one_le_cutLogBudget _ _
  have hR : 0 < Rr := Real.sqrt_pos.mpr (by
    have : 0 ≤ J / Δ := div_nonneg hJ hΔ.le
    positivity)
  have hexp : 2 * Real.exp (Real.exp 1 / 2) *
      Real.exp (-(Entropy.concentrationWidth (J / Δ)
        (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M /
          (32 * Rr))) =
        ((n : ℝ) + 2) ^ (-M) := by
    have hw : Entropy.concentrationWidth (J / Δ)
        (ManyBody.cutLogBudget (fun X : AdmissibleSupport Λ R ↦ X.1) (fun _ ↦ q) A) n M /
          (32 * Rr) =
        M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2 := by
      unfold Entropy.concentrationWidth
      change 32 * Rr * _ / (32 * Rr) = _
      field_simp
    rw [hw, Real.rpow_def_of_pos (by positivity)]
    rw [show -(M * Real.log (n + 2) + Real.exp 1 / 2 + Real.log 2) =
      Real.log (n + 2) * -M + (-(Real.exp 1 / 2) + -Real.log 2) by ring, Real.exp_add,
      Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log two_pos]
    field_simp
  have h2 := htail.trans (min_le_right _ _)
  rw [hexp] at h2
  linarith

end ManyBody

end PlaneMarginalTails
