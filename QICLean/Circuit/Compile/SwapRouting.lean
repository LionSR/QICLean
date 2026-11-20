/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.GateSubstitution
import QICLean.Circuit.Geometry.Graph
import QICLean.ManyBody.Sites.Relabel

/-!
# Routing gates along an open chain by SWAP gates

On the open chain of `n` sites with the same basis `α` at every site, the cells are the pairs
of neighbouring sites `{p, p + 1}`, each of cost `1`. The SWAP of two neighbouring sites, the
site permutation operator of their transposition, is one gate. Conjugating by SWAP gates moves
a unitary acting on two sites `i < j` to the neighbouring pair `{i, i + 1}` and back, so it is
a product of at most `2 (j - i) - 1 ≤ 2n` gates on neighbouring sites. A permutation of the
sites is a product of at most `n` transpositions, so its operator is a product of at most
`2 n²` gates, and conjugating a product of gates by it adds at most `4 n²` gates.

By gate substitution, a product of gates of cost `K` on the geometry of all sites and ordered
pairs of sites, with pairs of cost at least `1`, is a product of at most `2 n K` gates on
neighbouring sites; one-site gates are onsite families and cost nothing. A product of gates on
windows of two consecutive sites, with any bases at the sites, is a product of the same number
of gates on neighbouring sites.

This is the use of SWAP gates in arXiv:2307.01696, paragraph "The sequential-RG circuit": "the
inputs of the unitary ... are separated by `O(q)` sites, which requires one to implement SWAP
gates", and the placement and routing step and the register regrouping in Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

The declarations restate `isNeighbourGate_permOp_swap`, `isPairProduct_embedOp_pairSites`,
`isPairProduct_of_mem_supportedOperators_pair` and `isPairProduct_permOp_swap` of
`TNLean/Circuit/PairProduct.lean`, `IsPairProduct.embedOp_injective` of
`TNLean/Circuit/ArbitrarySiteGateEmbedding.lean`, `Equiv.Perm.swapFactorsAux_length_le`,
`Equiv.Perm.swapFactors_length_le_card`, `isPairProduct_permOp` and
`IsPairProduct.conjugate_permOp` of `TNLean/Circuit/QuantitativeSitePermutation.lean`, and
`IsWindowGate.isNeighbourGate` and `IsWindowProduct.isPairProduct_two` of
`TNLean/Circuit/WindowProduct.lean`, at commit `414a18fb88` (Apache-2.0). The changes: the
gates are the cells of the graph geometry of the path, a gate on two sites is a unitary
supported on them instead of a placed two-site matrix, the local basis is any finite type, the
routing bound is sharpened to `2 (j - i) - 1`, and placing a circuit at arbitrary sites is gate
substitution from the geometry of all ordered pairs.

## Main results

* `Equiv.Perm.swapFactorsAux_length_le`, `Equiv.Perm.swapFactors_length_le_card` — a
  permutation of a finite type is a product of at most one transposition per element.
* `QuantumCircuit.isGateProduct_sitePermOp_swap_of_succ` — the SWAP of neighbouring sites is one
  gate.
* `QuantumCircuit.isGateProduct_of_mem_supportedOperators_pair_of_lt`,
  `QuantumCircuit.isGateProduct_of_mem_supportedOperators_pair_dist`,
  `QuantumCircuit.isGateProduct_of_mem_supportedOperators_pair` — a unitary on two sites `i`, `j`
  is a product of at most `2 |i - j| - 1 ≤ 2n` gates.
* `QuantumCircuit.isGateProduct_sitePermOp_swap`, `QuantumCircuit.isGateProduct_sitePermOp` — a
  SWAP of any two sites, and any permutation of the sites.
* `QuantumCircuit.IsGateProduct.sitePermOp_mul_mul_conjTranspose` — conjugation by a permutation
  of the sites.
* `QuantumCircuit.IsGateProduct.of_sitesAndPairs` — gates on arbitrary pairs of sites.
* `QuantumCircuit.IsGateProduct.of_window_two` — gates on windows of two sites.
-/

/-! ### Transpositions in a permutation -/

namespace Equiv.Perm

variable {β : Type*} [DecidableEq β]

/-- The factorization of a permutation along a list `l` containing its non-fixed points uses at
most one transposition per element of `l`. -/
theorem swapFactorsAux_length_le (l : List β) (τ : Perm β) (h : ∀ {x}, τ x ≠ x → x ∈ l) :
    (swapFactorsAux l τ h).val.length ≤ l.length := by
  induction l generalizing τ with
  | nil => simp [swapFactorsAux]
  | cons x l ih =>
    rw [swapFactorsAux]
    dsimp only
    split_ifs with hfx
    · have htail : ∀ {y}, τ y ≠ y → y ∈ l := by
        intro y hy
        refine List.mem_of_ne_of_mem ?_ (h hy)
        rintro rfl
        exact hy hfx.symm
      exact (ih τ htail).trans (Nat.le_succ _)
    · have htail : ∀ {y}, (swap x (τ x) * τ) y ≠ y → y ∈ l := by
        intro y hy
        have hne := ne_and_ne_of_swap_mul_apply_ne_self hy
        exact List.mem_of_ne_of_mem hne.2 (h hne.1)
      exact Nat.succ_le_succ (ih (swap x (τ x) * τ) htail)

/-- A permutation of a finite type is a product of at most one transposition per element. -/
theorem swapFactors_length_le_card [Fintype β] [LinearOrder β] (τ : Perm β) :
    (swapFactors τ).val.length ≤ Fintype.card β := by
  unfold swapFactors
  exact (swapFactorsAux_length_le (Finset.univ.sort) τ
    (fun {_ _} ↦ (Finset.mem_sort _).2 (Finset.mem_univ _))).trans (by
      simpa only [Finset.card_univ] using
        (Finset.length_sort (s := (Finset.univ : Finset β)) (· ≤ ·)).le)

end Equiv.Perm

open Matrix ManyBody

namespace QuantumCircuit

variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-! ### SWAP gates -/

/-- **The SWAP of neighbouring sites.** The operator exchanging the contents of the sites `p`
and `p + 1` of the open chain is one gate. -/
theorem isGateProduct_sitePermOp_swap_of_succ {p p' : Fin n} (h : p'.val = p.val + 1) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) 1
      (sitePermOp (α := α) (Equiv.swap p p')) := by
  refine IsGateProduct.of_mem_supportedOperators (b := Geometry.pathCell h)
    (sitePermOp_mem_unitary _) ?_
  rw [Geometry.pathCell_cell]
  refine sitePermOp_mem_supportedOperators fun v hv ↦ ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
  exact Equiv.swap_apply_of_ne_of_ne hv.1 hv.2

/-- Moving a unitary on the sites `i < j` to `{i, i + 1}`, `k = j - i - 1` steps away. -/
private theorem isGateProduct_of_mem_supportedOperators_pair_aux (k : ℕ) :
    ∀ (i j : Fin n), j.val = i.val + k + 1 →
      ∀ Z ∈ unitaryGroup (Config fun _ : Fin n ↦ α) ℂ,
        Z ∈ supportedOperators (fun _ : Fin n ↦ α) {i, j} →
          IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (2 * k + 1) Z := by
  induction k with
  | zero =>
    intro i j hij Z hZu hZ
    refine IsGateProduct.of_mem_supportedOperators (b := Geometry.pathCell (p := i) (p' := j)
      (by omega)) hZu ?_
    rwa [Geometry.pathCell_cell]
  | succ k ih =>
    intro i j hij Z hZu hZ
    let j' : Fin n := ⟨j.val - 1, by omega⟩
    have hj' : j'.val = i.val + k + 1 := by simp only [j']; omega
    have hjj : j.val = j'.val + 1 := by simp only [j']; omega
    have hij' : i ≠ j' := fun h ↦ by rw [h] at hj'; omega
    have hij2 : i ≠ j := fun h ↦ by rw [h] at hij; omega
    set P := sitePermOp (α := α) (Equiv.swap j' j)
    have hPu : P ∈ unitaryGroup (Config fun _ : Fin n ↦ α) ℂ := sitePermOp_mem_unitary _
    have hPP : Pᴴ * P = 1 := mem_unitaryGroup_iff'.mp hPu
    have hZ' : P * Z * Pᴴ ∈ supportedOperators (fun _ : Fin n ↦ α) {i, j'} := by
      have h := sitePermOp_mul_mul_conjTranspose_mem_supportedOperators (Equiv.swap j' j) hZ
      rwa [Finset.image_insert, Finset.image_singleton, Equiv.swap_apply_of_ne_of_ne hij' hij2,
        Equiv.swap_apply_right] at h
    have hZ'u : P * Z * Pᴴ ∈ unitaryGroup (Config fun _ : Fin n ↦ α) ℂ :=
      mul_mem (mul_mem hPu hZu) (Unitary.star_mem hPu)
    have hS := isGateProduct_sitePermOp_swap_of_succ (α := α) hjj
    have heq : Z = Pᴴ * (P * Z * Pᴴ) * P := by
      simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
      rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
    rw [heq]
    exact ((hS.conjTranspose.mul (ih i j' hj' _ hZ'u hZ')).mul hS).mono (by omega)

/-- **A gate on distant sites.** A unitary acting on two sites `i < j` of the open chain is a
product of at most `2 (j - i) - 1` gates on neighbouring sites: SWAP gates bring `j` next to
`i` and back.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit": the inputs "are separated by
`O(q)` sites, which requires one to implement SWAP gates". -/
theorem isGateProduct_of_mem_supportedOperators_pair_of_lt {i j : Fin n} (hij : i < j)
    {Z : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ}
    (hZu : Z ∈ unitaryGroup _ ℂ) (hZ : Z ∈ supportedOperators (fun _ : Fin n ↦ α) {i, j}) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (2 * (j.val - i.val) - 1) Z := by
  have hij' : i.val < j.val := hij
  exact (isGateProduct_of_mem_supportedOperators_pair_aux (j.val - i.val - 1) i j (by omega) Z
    hZu hZ).mono (by omega)

/-- A unitary acting on two distinct sites `i`, `j` of the open chain is a product of at most
`2 |i - j| - 1` gates on neighbouring sites. -/
theorem isGateProduct_of_mem_supportedOperators_pair_dist {i j : Fin n} (hij : i ≠ j)
    {Z : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ}
    (hZu : Z ∈ unitaryGroup _ ℂ) (hZ : Z ∈ supportedOperators (fun _ : Fin n ↦ α) {i, j}) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (2 * Nat.dist i j - 1) Z := by
  rcases lt_or_gt_of_ne hij with h | h
  · refine (isGateProduct_of_mem_supportedOperators_pair_of_lt h hZu hZ).mono ?_
    have h' : i.val < j.val := h
    unfold Nat.dist
    omega
  · rw [Finset.pair_comm] at hZ
    refine (isGateProduct_of_mem_supportedOperators_pair_of_lt h hZu hZ).mono ?_
    have h' : j.val < i.val := h
    unfold Nat.dist
    omega

/-- **Gates on distant sites.** A unitary acting on two distinct sites of the open chain of `n`
sites is a product of at most `2n` gates on neighbouring sites.

Source: arXiv:2307.01696, paragraph "The sequential-RG circuit". -/
theorem isGateProduct_of_mem_supportedOperators_pair (i j : Fin n) (hij : i ≠ j)
    (Z : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ)
    (hZu : Z ∈ unitaryGroup _ ℂ) (hZ : Z ∈ supportedOperators (fun _ : Fin n ↦ α) {i, j}) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (2 * n) Z :=
  (isGateProduct_of_mem_supportedOperators_pair_dist hij hZu hZ).mono (by
    have := i.isLt
    have := j.isLt
    unfold Nat.dist
    omega)

/-- **The SWAP of two sites.** The operator exchanging the contents of two sites `i`, `j` of
the open chain is a product of at most `2 |i - j| - 1` gates on neighbouring sites. -/
theorem isGateProduct_sitePermOp_swap (i j : Fin n) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (2 * Nat.dist i j - 1)
      (sitePermOp (α := α) (Equiv.swap i j)) := by
  by_cases h : i = j
  · rw [h, Equiv.swap_self, ← Equiv.Perm.one_def, sitePermOp_one]
    exact IsGateProduct.one _ _ _
  · refine isGateProduct_of_mem_supportedOperators_pair_dist h (sitePermOp_mem_unitary _)
      (sitePermOp_mem_supportedOperators fun v hv ↦ ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact Equiv.swap_apply_of_ne_of_ne hv.1 hv.2

/-- **Permutations of the sites.** The operator of a permutation of the sites of the open chain
of `n` sites is a product of at most `2 n²` gates on neighbouring sites: it is a product of at
most `n` transpositions, each routed by SWAP gates.

Source: register regrouping in Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`; the factorization is Mathlib's
`Equiv.Perm.swapFactors`. -/
theorem isGateProduct_sitePermOp (τ : Equiv.Perm (Fin n)) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (2 * n ^ 2)
      (sitePermOp (α := α) τ) := by
  set l := (Equiv.Perm.swapFactors τ).val
  have hprod : l.prod = τ := (Equiv.Perm.swapFactors τ).property.1
  have hswap : ∀ σ ∈ l, σ.IsSwap := (Equiv.Perm.swapFactors τ).property.2
  have hlength : l.length ≤ n := by
    simpa only [Fintype.card_fin] using Equiv.Perm.swapFactors_length_le_card τ
  rw [← hprod, ← list_prod_map_sitePermOp]
  refine (IsGateProduct.list_prod (K := 2 * n) _ fun U hU ↦ ?_).mono ?_
  · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hU
    obtain ⟨i, j, -, rfl⟩ := hswap σ hσ
    refine (isGateProduct_sitePermOp_swap i j).mono ?_
    have := i.isLt
    have := j.isLt
    unfold Nat.dist
    omega
  · rw [List.length_map]
    calc l.length * (2 * n) ≤ n * (2 * n) := Nat.mul_le_mul_right _ hlength
      _ = 2 * n ^ 2 := by ring

/-- **Conjugation by a permutation of the sites.** Conjugating a product of `K` gates on the
open chain of `n` sites by the operator of a permutation of the sites gives a product of at most
`K + 4 n²` gates.

Source: register regrouping in Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem IsGateProduct.sitePermOp_mul_mul_conjTranspose (τ : Equiv.Perm (Fin n)) {K : ℕ}
    {U : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ}
    (hU : IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) K U) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (K + 4 * n ^ 2)
      (sitePermOp τ * U * (sitePermOp τ)ᴴ) := by
  have hτ := isGateProduct_sitePermOp (α := α) τ
  exact ((hτ.mul hU).mul hτ.conjTranspose).mono (by ring_nf; omega)

/-! ### Gate substitution on the open chain -/

/-- **Placing a circuit at arbitrary sites.** On the open chain of `n` sites, a product of gates
of cost `K` on the geometry of all sites and ordered pairs of distinct sites, with pairs of cost
at least `1`, is a product of at most `2 n K` gates on neighbouring sites. One-site gates are
onsite families and cost nothing; a gate on a pair is routed by SWAP gates.

Source: Section 5 of TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex` (placing a
circuit at arbitrary distinct sites increases its gate count by at most `2n` per gate). -/
theorem IsGateProduct.of_sitesAndPairs {c₁ c₂ K : ℕ} (hc₂ : 1 ≤ c₂)
    {U : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ}
    (hU : IsGateProduct (Geometry.sitesAndPairs (Fin n) c₁ c₂) K U) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (2 * n * K) U := by
  refine hU.substitute fun b V hV ↦ ?_
  rcases b with a | ⟨⟨a, a'⟩, haa'⟩
  · exact IsGateProduct.place_singleton a hV _
  · have hZ : ManyBody.place ({a} ∪ {a'}) V ∈
        supportedOperators (fun _ : Fin n ↦ α) {a, a'} := by
      rw [Finset.insert_eq]
      exact place_mem_supportedOperators V
    exact (isGateProduct_of_mem_supportedOperators_pair a a' haa' _ (place_mem_unitaryGroup hV)
      hZ).mono (Nat.le_mul_of_pos_right _ hc₂)

section Window

variable {X : Fin n → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- **A gate on a window of two sites.** On a chain of at least two sites, a unitary placed on a
window of two consecutive sites is one gate on neighbouring sites; near the right end the window
is cut off and lies in the last pair. -/
theorem IsGateProduct.place_window_two (hn : 2 ≤ n) (a : (Geometry.window n 2).Cell)
    {V : Matrix (RegionConfig X ((Geometry.window n 2).cell a))
      (RegionConfig X ((Geometry.window n 2).cell a)) ℂ}
    (hV : V ∈ unitaryGroup _ ℂ) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) 1
      (ManyBody.place ((Geometry.window n 2).cell a) V) := by
  let p : Fin n := ⟨min a.val (n - 2), by omega⟩
  let p' : Fin n := ⟨min a.val (n - 2) + 1, by omega⟩
  refine IsGateProduct.of_mem_supportedOperators (b := Geometry.pathCell (p := p) (p' := p') rfl)
    (place_mem_unitaryGroup hV) (supportedOperators_mono ?_ (place_mem_supportedOperators V))
  rw [Geometry.pathCell_cell]
  intro q hq
  rw [Geometry.mem_window_cell] at hq
  have := q.isLt
  simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, p, p']
  omega

/-- **Windows of two sites.** On a chain of at least two sites, a product of gates of cost `K`
on windows of two consecutive sites is a product of at most `K` gates on neighbouring sites. -/
theorem IsGateProduct.of_window_two (hn : 2 ≤ n) {K : ℕ}
    {U : Matrix (Config X) (Config X) ℂ} (hU : IsGateProduct (Geometry.window n 2) K U) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) K U := by
  simpa only [one_mul] using hU.substitute (C := 1) fun a V hV ↦
    IsGateProduct.place_window_two hn a hV

end Window

end QuantumCircuit
