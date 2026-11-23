/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.ManyBody.Entropy.SupportedMarginalTails
import QICLean.ManyBody.Hamiltonian.GroundSpace
import QICLean.ManyBody.Hamiltonian.Models

/-!
# Regional entropies on the chain

Two facts about the regional entropies of a vector on the chain of `L` sites with local
dimension `q`.

* A uniform bound `C` on the entropies of all intervals gives `S(A) ≤ C |∂A|` for every region
  `A`, where `∂A` is the set of edges of the chain with exactly one endpoint in `A`. Every region
  is a disjoint union of maximal runs of consecutive sites, each run contributes at most `C` by
  subadditivity, and the edge just after a run (or just before it, when the run reaches the end
  of the chain) is a boundary edge of the region that the remaining runs do not share.
* For a gapped ground vector of a finite-range interaction, the marginal tail bound of
  `QICLean.ManyBody.Entropy.SupportedMarginalTails` holds at every cut, with the cut budget
  `ManyBody.cutLogBudget` of the supports of range `R` and local dimension `q`.

## Main results

* `ManyBody.regionEntropy_le_mul_card_boundaryEdges_of_intervals` — interval bounds give the
  area law on the chain.
* `ManyBody.ChainInteraction.surprisalTail_regionState_le` — the marginal tail bound for a
  gapped ground vector at every cut.

## References

* Two-dimensional area-law manuscript (September 24, 2026), Lemma 3.1 (`lem:tail`),
  `02-initial.tex`, lines 34–69.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace ManyBody

variable {L q R : ℕ} {J : ℝ}

/-- Interval bounds give the area law on a chain: if every interval region of the chain of `L`
sites has regional entropy at most `C`, then every region `A` has regional entropy at most `C`
times the number of edges of the chain leaving `A`. -/
theorem regionEntropy_le_mul_card_boundaryEdges_of_intervals
    {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΩ : ‖Ω‖ = 1) {C : ℝ} (hC : 0 ≤ C)
    (hI : ∀ a b : ℕ, regionEntropy (X := fun _ ↦ Fin q) Ω (interval L a b) ≤ C)
    (A : Finset (Fin L)) :
    regionEntropy (X := fun _ ↦ Fin q) Ω A ≤ C * (boundaryEdges L A).card := by
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases hA : A = Finset.univ
    · subst hA
      rw [regionEntropy_univ _ Ω hΩ, boundaryEdges_univ]
      simp
    rcases A.eq_empty_or_nonempty with rfl | hne
    · rw [regionEntropy_empty _ Ω hΩ, boundaryEdges_empty]
      simp
    obtain ⟨a, b, hIA, hIne, hss⟩ := exists_interval_subset_boundaryEdges_sdiff_ssubset hne hA
    have h1 := ih _ (Finset.sdiff_ssubset hIA hIne)
    have h2 : regionEntropy (X := fun _ ↦ Fin q) Ω A ≤
        regionEntropy (X := fun _ ↦ Fin q) Ω (interval L a b) +
          regionEntropy (X := fun _ ↦ Fin q) Ω (A \ interval L a b) := by
      conv_lhs => rw [← Finset.union_sdiff_of_subset hIA]
      exact regionEntropy_union_le _ Ω hΩ _ _ Finset.disjoint_sdiff
    have h3 : ((boundaryEdges L (A \ interval L a b)).card : ℝ) + 1 ≤
        (boundaryEdges L A).card := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.card_lt_card hss)
    calc regionEntropy (X := fun _ ↦ Fin q) Ω A
        ≤ C + C * (boundaryEdges L (A \ interval L a b)).card := by linarith [hI a b]
      _ = C * ((boundaryEdges L (A \ interval L a b)).card + 1) := by ring
      _ ≤ C * (boundaryEdges L A).card := by gcongr

/-- **The marginal tail bound on a chain.** For a gapped ground vector `Ω` with gap `Δ > 0`
of a finite-range Hamiltonian with term norms at most `J ≥ 0`, and any cut `A`, the
surprisal of the regional state on `A` satisfies, for every real `w`,
`Pr {|K - S(A)| > w} ≤ min {1, 2 e^{e/2} exp (-w / (32 √((1 + J/Δ) ℬ_A)))}`.
Area-law manuscript, Lemma 3.1 (`lem:tail`), `eq:initial-tail-probability`. -/
theorem ChainInteraction.surprisalTail_regionState_le (h : ChainInteraction L q R)
    (hh : ∀ X, (h.term X).IsHermitian) (hhJ : ∀ X, ‖h.term X‖ ≤ J)
    (hJ : 0 ≤ J) {E₀ Δ : ℝ} {Ω : EuclideanSpace ℂ (Fin L → Fin q)} (hΔ : 0 < Δ)
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω}) (A : Finset (Fin L)) (w : ℝ) :
    Entropy.surprisalTail (regionState_isHermitian (X := fun _ ↦ Fin q) A Ω).eigenvalues
        (regionEntropy (X := fun _ ↦ Fin q) Ω A) w ≤
      min 1 (2 * Real.exp (Real.exp 1 / 2) *
        Real.exp (-(w / (32 * Real.sqrt ((1 + J / Δ) *
          cutLogBudget (fun X : ChainSupport L R ↦ X.1) (fun _ ↦ q) A))))) := by
  have heig : toEuclideanLin h.hamiltonian Ω = (E₀ : ℂ) • Ω :=
    mem_groundSpace_iff.mp (hspan ▸ Submodule.mem_span_singleton_self Ω)
  have hgap := hgap.posSemidef_sub_smul_one
      (Interaction.isHermitian_hamiltonian hh) hΩ hspan
  exact Entropy.surprisalTail_cut_le (n := fun _ : Fin L ↦ q) (B := A) h.mem hh hJ
    hhJ hΩ hΔ heig hgap (regionState_eq_partialTraceRight_cutVector A Ω).symm
    (regionState_isHermitian A Ω) w

end ManyBody
