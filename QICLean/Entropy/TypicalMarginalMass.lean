/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TypicalSet
import QICLean.Entropy.SupportedMarginalTails

/-!
# The typical marginal spectrum of a gapped ground vector

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

## Main definitions

* `Entropy.concentrationWidth` — the concentration width.

## Main results

* `Entropy.one_sub_rpow_le_typicalMass_cut` — the typical marginal spectrum carries mass at
  least `1 - (N + 2)^{-M}`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026,
  Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 34–69, and the concentration statement
  after it, lines 209–219.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

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
        (concentrationWidth (c₀ / g₀) (cutLogBudget (ManyBody.crossingTerms D B) (supportDim n ∘ D))
          N M) := by
  set ℬ := cutLogBudget (ManyBody.crossingTerms D B) (supportDim n ∘ D)
  set w := concentrationWidth (c₀ / g₀) ℬ N M
  have hpsd : ρ.PosSemidef := hρdef ▸ ManyBody.regionState_posSemidef B Ψ
  have hs : ∑ i, hρ.eigenvalues i = 1 := by
    have h1 : ρ.trace = 1 := by
      rw [← hρdef]
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
