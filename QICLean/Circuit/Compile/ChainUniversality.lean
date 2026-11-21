/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.SwapRouting
import QICLean.Circuit.Compile.Universality
import QICLean.Circuit.Gate.UnitaryExtension

/-!
# Universality of neighbouring two-site gates on an open chain

On the open chain of `n` sites with the same finite basis `α` at every site, a unitary on two
sites is a product of at most `2n` gates on neighbouring sites (swap routing,
`isGateProduct_of_mem_supportedOperators_pair`). Universality relative to the cost of two-site
unitaries (`isGateProduct_unitaryGateCount`) then writes every unitary on the chain as an exact
product of at most `2n · unitaryGateCount` neighbouring gates, with its global phase and with no
auxiliary sites. With at least two basis vectors per site this is at most `12 m⁵` gates for the
Hilbert-space dimension `m = |α|ⁿ`; an isometry on prescribed input columns extends to such a
product.

This is the step "can be further expressed with a low-depth circuit of local gates" of
arXiv:2307.01696 (caption of Fig. 1), for the unitaries with constant support of the paragraph
"The sequential-RG circuit", and the quantitative synthesis used in Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The declarations restate `exists_isPairProduct` of `TNLean/Circuit/Gates/TwoSiteUniversality.lean`
and `isPairProduct_unitaryGateCount`, `isPairProduct_le_hilbertDimension_pow` and
`exists_isPairProduct_apply_embedding_eq` of `TNLean/Circuit/QuantitativeUnitaryGates.lean` at
commit `414a18fb88` (Apache-2.0). The changes: any finite basis `α` at the sites in place of
`Fin d`; the count is `2n · unitaryGateCount`, with one-site gates free, and its polynomial bound
is `12 m⁵` in place of `38 m⁶`.

## Main results

* `QuantumCircuit.isGateProduct_pathGraph_unitaryGateCount` — every unitary on the chain.
* `QuantumCircuit.isGateProduct_pathGraph_le_card_pow` — the bound `12 m⁵`.
* `QuantumCircuit.exists_isGateProduct_pathGraph_apply_embedding_eq` — isometries on prescribed
  columns.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- **Unitaries on an open chain.** For `n ≥ 1`, every unitary on the open chain of `n` sites
with basis `α` at every site is an exact product of at most `2n · unitaryGateCount` unitaries on
neighbouring pairs of sites, one-site unitaries being free.

Source: arXiv:2307.01696, caption of Fig. 1: the unitaries with constant support "can be further
expressed with a low-depth circuit of local gates". -/
theorem isGateProduct_pathGraph_unitaryGateCount [NeZero n]
    {U : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ}
    (hU : U ∈ unitaryGroup _ ℂ) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n))
      (unitaryGateCount (Fin n) (fun _ ↦ α) * (2 * n)) U :=
  isGateProduct_unitaryGateCount
    (fun i j hij Z hZu hZ ↦ isGateProduct_of_mem_supportedOperators_pair i j hij Z hZu hZ) hU

/-- **A polynomial gate count.** With at least two basis vectors per site, every unitary on the
open chain of `n ≥ 1` sites is an exact product of at most `12 m⁵` neighbouring gates, where
`m = |α|ⁿ` is the Hilbert-space dimension.

Derived synthesis estimate for Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem isGateProduct_pathGraph_le_card_pow [NeZero n] (hα : 2 ≤ Fintype.card α)
    {U : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ}
    (hU : U ∈ unitaryGroup _ ℂ) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n))
      (12 * (Fintype.card α ^ n) ^ 5) U := by
  refine (isGateProduct_pathGraph_unitaryGateCount hU).mono ?_
  have hcount := unitaryGateCount_le (S := Fin n) (X := fun _ ↦ α) fun _ ↦ hα
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcount
  set m := Fintype.card α ^ n
  have hnm : n ≤ m := Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hα n)
  calc unitaryGateCount (Fin n) (fun _ ↦ α) * (2 * n) ≤ 6 * m ^ 4 * (2 * m) :=
        Nat.mul_le_mul hcount (Nat.mul_le_mul_left 2 hnm)
    _ = 12 * m ^ 5 := by ring

/-- **Isometries on prescribed columns.** With at least two basis vectors per site, an isometry
`V` from a finite set `κ` into the open chain of `n ≥ 1` sites, prescribed on the input columns
`e k`, extends to a unitary that is a product of at most `12 m⁵` neighbouring gates.

Derived leaf construction for Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem exists_isGateProduct_pathGraph_apply_embedding_eq [NeZero n] {κ : Type} [DecidableEq κ]
    (hα : 2 ≤ Fintype.card α)
    {V : Matrix (Config fun _ : Fin n ↦ α) κ ℂ} (hV : V.IsIsometry)
    (e : κ ↪ Config fun _ : Fin n ↦ α) :
    ∃ U : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ,
      IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n))
        (12 * (Fintype.card α ^ n) ^ 5) U ∧ ∀ u k, U u (e k) = V u k := by
  obtain ⟨U, hU, hUV⟩ := Matrix.exists_mem_unitaryGroup_apply_embedding_eq hV e
  exact ⟨U, isGateProduct_pathGraph_le_card_pow hα hU, hUV⟩

end QuantumCircuit
