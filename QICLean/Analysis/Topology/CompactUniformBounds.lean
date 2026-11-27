/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform bounds from local bounds on a compact set

A neighborhood bound at each parameter can be made uniform on a compact parameter set when it
persists after decreasing its positive real constant and increasing its natural-number
threshold. The finite subcover provides finitely many local bounds; their minimum and maximum
give the uniform ones. This is the compactness step in the gap argument of arXiv:1010.3732,
Appendix A; its gap form is `IsCompact.exists_uniform_isGapped`.

Moved from TNLean, `TNLean/Algebra/CompactGapBounds.lean` at commit `414a18fb88`, with no change
to the statement.

## Main results

* `IsCompact.exists_uniform_pos_nat_bounds` — a positive constant and a threshold, valid locally
  at every point of a compact set, chosen uniformly.
* `Filter.eventually_forall_le_of_tendsto_all_selections`: uniform upper bounds from convergence
  along all selections.
-/

section CompactUniformBounds

open scoped Topology

namespace IsCompact

/-- A positive constant and a natural-number threshold, valid locally at
every point of a compact set, can be chosen uniformly when the assertion is
monotone under weakening these bounds. Source: arXiv:1010.3732, Appendix A. -/
theorem exists_uniform_pos_nat_bounds {X : Type*} [TopologicalSpace X]
    {S : Set X} (hS : IsCompact S) (P : ℝ → ℕ → X → Prop)
    (hδ : ∀ {δ δ' : ℝ} {N : ℕ} {x : X}, δ ≤ δ' → P δ' N x → P δ N x)
    (hN : ∀ {δ : ℝ} {N N' : ℕ} {x : X}, N ≤ N' → P δ N x → P δ N' x)
    (hlocal : ∀ x ∈ S, ∃ δ : ℝ, 0 < δ ∧
      ∃ N : ℕ, ∀ᶠ y in 𝓝 x, P δ N y) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ x ∈ S, P δ N x := by
  classical
  have hlocal' : ∀ x : S, ∃ b : ℝ × ℕ,
      0 < b.1 ∧ ∀ᶠ y in 𝓝 (x : X), P b.1 b.2 y := by
    intro x
    obtain ⟨δ, hδpos, N, hnear⟩ := hlocal x x.property
    exact ⟨(δ, N), hδpos, hnear⟩
  choose b hb using hlocal'
  let U : ∀ x ∈ S, Set X := fun x hx ↦
    {y | P (b ⟨x, hx⟩).1 (b ⟨x, hx⟩).2 y}
  obtain ⟨t, hcover⟩ := hS.elim_nhds_subcover' U (by
    intro x hx
    exact (hb ⟨x, hx⟩).2)
  by_cases ht : t.Nonempty
  · let δ : ℝ := t.inf' ht (fun x ↦ (b x).1)
    let N : ℕ := t.sup (fun x ↦ (b x).2)
    have hδpos : 0 < δ := (Finset.lt_inf'_iff _).2 (by
      intro x _
      exact (hb x).1)
    refine ⟨δ, hδpos, N, ?_⟩
    intro x hx
    have hxcover := hcover hx
    simp only [Set.mem_iUnion] at hxcover
    obtain ⟨j, hj, hxj⟩ := hxcover
    have hδj : δ ≤ (b j).1 := Finset.inf'_le _ hj
    have hNj : (b j).2 ≤ N := Finset.le_sup (f := fun x ↦ (b x).2) hj
    exact hN hNj (hδ hδj hxj)
  · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    refine ⟨1, zero_lt_one, 0, ?_⟩
    intro x hx
    have hfalse : False := by simpa [ht0] using (hcover hx)
    exact hfalse.elim

end IsCompact

end CompactUniformBounds

section UniformSelectionBounds

/-!
## Uniform upper bounds from convergence along all selections

Suppose a real-valued family \(e_i(x)\) tends to zero along every choice
\(x_i\) of its auxiliary parameter. Then, for every positive tolerance,
all auxiliary parameters satisfy the upper bound eventually. The index
filter is arbitrary and the nonempty parameter space has no topology.

This elementary selection argument turns limits with an arbitrarily varying auxiliary
parameter into one common bound. Source: Nachtergaele, arXiv:cond-mat/9410110,
Lemma commutation (ii), lines 2442--2531; only the uniformization implication is proved here.

Moved from TNLean, `TNLean/Algebra/UniformSelectionBounds.lean` at commit `49b78ed821`
(Apache-2.0). Changes: docstrings only.
-/

namespace Filter

/-- Convergence to zero along every choice of the auxiliary parameter gives
an eventual uniform upper bound. Neither countability of the parameter space
nor nonnegativity of the family is required. Source: the uniform projection
comparison in Nachtergaele, arXiv:cond-mat/9410110, Lemma commutation (ii),
lines 2442--2531; this is the elementary selection implication used there. -/
theorem eventually_forall_le_of_tendsto_all_selections
    {ι X : Type*} [Nonempty X] {f : Filter ι}
    (e : ι → X → ℝ)
    (h : ∀ x : ι → X, Tendsto (fun i => e i (x i)) f (nhds 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ i in f, ∀ x, e i x ≤ ε := by
  classical
  have hChoice : ∀ i, ∃ x, e i x ≤ ε → ∀ y, e i y ≤ ε := by
    intro i
    by_cases hi : ∀ y, e i y ≤ ε
    · exact ⟨Classical.arbitrary X, fun _ => hi⟩
    · rcases not_forall.mp hi with ⟨x, hx⟩
      exact ⟨x, fun hle => (hx hle).elim⟩
  choose x hx using hChoice
  exact ((h x).eventually (Iio_mem_nhds hε)).mono fun i hi => hx i hi.le

end Filter

end UniformSelectionBounds
