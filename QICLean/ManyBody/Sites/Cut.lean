/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Fintype.Basic
import QICLean.Entropy.Surprisal.GapSurprisal

/-!
# Supports crossing a cut

A region `B` cuts the sites into `B` and its complement. Given a family of supports
`D : ι → Finset V`, the terms crossing the cut are the indices whose support meets both sides.
Only the supports enter: for an interaction with supports `T`, its crossing terms at `B` are
`crossingTerms T B`.

Moved from `QICLean/ManyBody/Entropy/SupportedMarginalTails.lean`, where it was
`Entropy.crossingTerms`.

The crossing terms are unchanged by exchanging the region and its complement, and no support
crosses the empty region or the region of all sites.

With local dimensions `n : V → ℕ`, the support `D_i` has dimension `d_i = ∏_{v ∈ D_i} n_v`, and
the cut budget `ℬ_B = 1 + ∑_{i ∈ I×} log² (e d_i)` sums over the crossing terms `I×`. It is the
parameter of the marginal tail bound of `QICLean.ManyBody.Entropy.SupportedMarginalTails`.

## Main definitions

* `ManyBody.crossingTerms` — the indices whose support meets a region and its complement.
* `Entropy.supportDim` — the dimension `∏_{v ∈ D} n_v` of a support.
* `ManyBody.cutLogBudget` — the log budget of the terms crossing a cut.

## Main results

* `ManyBody.mem_crossingTerms` — membership in the crossing terms.
* `ManyBody.crossingTerms_compl` — complementary regions have the same crossing terms.
* `ManyBody.cutLogBudget_le`, `ManyBody.cutLogBudget_const_le` — the budget is at most
  `1 + |I×| log² (e d)` for crossing supports of dimension at most `d`, and so at most
  `1 + |I×| log² (e q^k)` for one local dimension `q` and supports of at most `k` sites.
-/

namespace ManyBody

variable {V ι : Type*} [Fintype ι]

/-- The terms whose support meets both sides of the cut at `B`: the indices `i` such that
`D i` contains a site of `B` and a site outside `B`.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, lines 47–48. -/
noncomputable def crossingTerms (D : ι → Finset V) (B : Finset V) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ (∃ v ∈ D i, v ∈ B) ∧ ∃ v ∈ D i, v ∉ B

variable {D : ι → Finset V} {B : Finset V} {i : ι}

theorem mem_crossingTerms : i ∈ crossingTerms D B ↔ (∃ v ∈ D i, v ∈ B) ∧ ∃ v ∈ D i, v ∉ B := by
  classical
  simp only [crossingTerms, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A support inside the region does not cross it. -/
theorem notMem_crossingTerms_of_subset (h : D i ⊆ B) : i ∉ crossingTerms D B := fun hi ↦ by
  obtain ⟨-, _, hv, hvB⟩ := mem_crossingTerms.mp hi
  exact hvB (h hv)

/-- A support disjoint from the region does not cross it. -/
theorem notMem_crossingTerms_of_disjoint (h : Disjoint (D i) B) : i ∉ crossingTerms D B :=
  fun hi ↦ by
    obtain ⟨⟨_, hv, hvB⟩, -⟩ := mem_crossingTerms.mp hi
    exact Finset.disjoint_left.mp h hv hvB

@[simp] theorem crossingTerms_empty : crossingTerms D ∅ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hi ↦ by simp [mem_crossingTerms] at hi

/-- Exchanging a region and its complement preserves the crossing terms. -/
@[simp] theorem crossingTerms_compl [Fintype V] [DecidableEq V] :
    crossingTerms D Bᶜ = crossingTerms D B := by
  ext i
  simp only [mem_crossingTerms, Finset.mem_compl, not_not]
  exact and_comm

@[simp] theorem crossingTerms_univ [Fintype V] : crossingTerms D Finset.univ = ∅ :=
  Finset.eq_empty_of_forall_notMem fun _ hi ↦ by simp [mem_crossingTerms] at hi

end ManyBody

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

section Budget

variable {ι : Type*} [Fintype ι]

/-- The dimension `d_i = ∏_{v ∈ D_i} dim 𝓗_v` of a designated support.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, line 51. -/
def supportDim (n : V → ℕ) (D : Finset V) : ℕ := ∏ v ∈ D, n v

omit [Fintype V] [DecidableEq V] in
/-- A support of `k` sites with local dimension `q` at every site has dimension `q ^ k`. -/
theorem supportDim_const (q : ℕ) (D : Finset V) : supportDim (fun _ ↦ q) D = q ^ D.card :=
  Finset.prod_const q

omit [Fintype V] [DecidableEq V] in
/-- The dimension `q^{|D|}` of a region is at least one when `q ≥ 1`. -/
theorem _root_.ManyBody.one_le_supportDim_const {q : ℕ} (hq : 1 ≤ q) (D : Finset V) :
    1 ≤ Entropy.supportDim (fun _ : V ↦ q) D := by
  rw [Entropy.supportDim, Finset.prod_const]
  exact Nat.one_le_pow _ _ hq

omit [Fintype V] [DecidableEq V] in
/-- The **cut budget** `ℬ_B = 1 + ∑_{i ∈ I×} log² (e d_i)` of a family of supports `D` at the
region `B`. The sum runs over the supports crossing `B`, and `d_i = ∏_{v ∈ D_i} n_v` is the
dimension of the `i`th support for the local dimensions `n`. It is the parameter
`Entropy.cutLogBudget` of the marginal tail bound at the crossing terms; a chain, a lattice
domain or any family of designated supports gives its budget by choosing `D`.
Area-law manuscript, Lemma 3.1, `02-initial.tex`, lines 47–55. -/
noncomputable abbrev _root_.ManyBody.cutLogBudget (D : ι → Finset V) (n : V → ℕ)
    (B : Finset V) : ℝ :=
  Entropy.cutLogBudget (ManyBody.crossingTerms D B) (supportDim n ∘ D)

/-- Exchanging a region and its complement preserves the cut budget. -/
@[simp] theorem _root_.ManyBody.cutLogBudget_compl (D : ι → Finset V) (n : V → ℕ)
    (B : Finset V) : ManyBody.cutLogBudget D n Bᶜ = ManyBody.cutLogBudget D n B := by
  rw [ManyBody.cutLogBudget, ManyBody.crossingTerms_compl]

omit [Fintype V] [DecidableEq V] in
/-- No support crosses the empty region, so its cut budget is one. -/
@[simp] theorem _root_.ManyBody.cutLogBudget_empty (D : ι → Finset V) (n : V → ℕ) :
    ManyBody.cutLogBudget D n ∅ = 1 := by
  simp [ManyBody.cutLogBudget, Entropy.cutLogBudget]

omit [DecidableEq V] in
/-- No support crosses the region of all sites, so its cut budget is one. -/
@[simp] theorem _root_.ManyBody.cutLogBudget_univ (D : ι → Finset V) (n : V → ℕ) :
    ManyBody.cutLogBudget D n Finset.univ = 1 := by
  simp [ManyBody.cutLogBudget, Entropy.cutLogBudget]

omit [Fintype V] [DecidableEq V] in
/-- **The cut budget grows linearly with the number of crossing supports.** If every crossing
support has dimension at most `d`, then `ℬ_B ≤ 1 + |I×| log² (e d)`. -/
theorem _root_.ManyBody.cutLogBudget_le {D : ι → Finset V} {n : V → ℕ} {B : Finset V}
    {d : ℝ} (hdim : ∀ i ∈ ManyBody.crossingTerms D B, (supportDim n (D i) : ℝ) ≤ d) :
    ManyBody.cutLogBudget D n B ≤
      1 + (ManyBody.crossingTerms D B).card * Real.log (Real.exp 1 * d) ^ 2 := by
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hterm : ∀ i ∈ ManyBody.crossingTerms D B,
      Real.log (Real.exp 1 * ((supportDim n ∘ D) i : ℝ)) ^ 2 ≤
        Real.log (Real.exp 1 * d) ^ 2 := by
    intro i hi
    rcases Nat.eq_zero_or_pos (supportDim n (D i)) with h0 | hpos
    · have h0' : ((supportDim n ∘ D) i : ℝ) = 0 := by simp [h0]
      rw [h0', mul_zero, Real.log_zero, zero_pow two_ne_zero]
      exact sq_nonneg _
    · have h1 : (1 : ℝ) ≤ supportDim n (D i) := by exact_mod_cast hpos
      have hl : 0 ≤ Real.log (Real.exp 1 * supportDim n (D i)) :=
        Real.log_nonneg (one_le_mul_of_one_le_of_one_le he h1)
      exact pow_le_pow_left₀ hl (Real.log_le_log (by positivity)
        (mul_le_mul_of_nonneg_left (hdim i hi) (Real.exp_pos 1).le)) 2
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hsum
  change 1 + _ ≤ _
  linarith

omit [Fintype V] [DecidableEq V] in
/-- **The cut budget for one local dimension.** With local dimension `q ≥ 1` at every site and
crossing supports of at most `k` sites, `ℬ_B ≤ 1 + |I×| log² (e q^k)`. -/
theorem _root_.ManyBody.cutLogBudget_const_le {D : ι → Finset V} {q k : ℕ} {B : Finset V}
    (hq : 1 ≤ q) (hcard : ∀ i ∈ ManyBody.crossingTerms D B, (D i).card ≤ k) :
    ManyBody.cutLogBudget D (fun _ ↦ q) B ≤
      1 + (ManyBody.crossingTerms D B).card * Real.log (Real.exp 1 * (q : ℝ) ^ k) ^ 2 := by
  refine ManyBody.cutLogBudget_le fun i hi ↦ ?_
  rw [supportDim_const, Nat.cast_pow]
  exact pow_le_pow_right₀ (by exact_mod_cast hq) (hcard i hi)

end Budget

end Entropy
