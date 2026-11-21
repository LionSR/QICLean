/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixReindexUnitary
import QICLean.Circuit.Compile.ChainUniversality
import QICLean.Circuit.Compile.GateSubstitution
import QICLean.Circuit.Model.UnitaryPlacement

/-!
# Gates on windows through neighbouring gates

On the open chain of `n` sites with the same basis `α` at every site, a unitary supported on a
window of `m ≥ 1` consecutive sites is a unitary on a shorter chain of at most `m` sites placed
on consecutive sites, so by universality on that chain (`isGateProduct_pathGraph_le_card_pow`)
and placement (`IsGateProduct.place_pathGraph`) it is a product of at most `12 (|α|ᵐ)⁵`
neighbouring gates, a number independent of `n`. By gate substitution, a product of `K` gates
on windows of `m` sites is a product of at most `12 (|α|ᵐ)⁵ K` neighbouring gates.

Gates on `k + 1` consecutive sites are the gates of the sequential preparation of arXiv:2307.01696,
eq. (14) (paragraph "The sequential-RG circuit"): each acts on a register of `k` sites and one
fresh site; the caption of Fig. 1 states that they "can be further expressed with a low-depth
circuit of local gates".

The declarations restate `isWindowGate_embedOp`, `isWindowGate_of_le` and
`IsWindowProduct.exists_isPairProduct` of `TNLean/Circuit/WindowProduct.lean` at commit
`414a18fb88` (Apache-2.0). The changes: a gate on a window is a unitary supported on a cell of
`Geometry.window n m`, a product of such gates is `IsGateProduct (Geometry.window n m)`; any
finite basis `α` with at least two elements; the constant is explicit, `12 (|α|ᵐ)⁵`.

## Main results

* `QuantumCircuit.isGateProduct_pathGraph_of_mem_supportedOperators_interval` — a unitary on a
  window of `m` sites.
* `QuantumCircuit.IsGateProduct.of_window` — windows of `m` sites through neighbouring gates.
* `QuantumCircuit.IsGateProduct.window_of_mem_supportedOperators` — a unitary supported on a
  window is one gate on it.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {n : ℕ} {α : Type} [Fintype α] [DecidableEq α]

/-- The sites `a, a + 1, …, a + w - 1` of the window `[a, a + m)` of the chain of `n` sites,
`w = min m (n - a)`, numbered from `0`. -/
private noncomputable def windowEquiv (a : Fin n) (m : ℕ) :
    Fin (min m (n - a.val)) ≃ {s // s ∈ ManyBody.interval n a (a + m)} :=
  Equiv.ofBijective (fun j ↦ ⟨⟨a.val + j.val, by have := j.isLt; omega⟩,
      ManyBody.mem_interval.mpr ⟨by simp, by have := j.isLt; simp; omega⟩⟩) (by
    constructor
    · intro j j' h
      have := congrArg (fun s : {s // s ∈ ManyBody.interval n a (a + m)} ↦ s.1.val) h
      exact Fin.ext (by simpa using this)
    · rintro ⟨s, hs⟩
      obtain ⟨h₁, h₂⟩ := ManyBody.mem_interval.mp hs
      exact ⟨⟨s.val - a.val, by have := s.isLt; omega⟩, Subtype.ext (Fin.ext (by simp; omega))⟩)

private theorem windowEquiv_val (a : Fin n) (m : ℕ) (j : Fin (min m (n - a.val))) :
    ((windowEquiv a m j).1 : ℕ) = a.val + j.val :=
  rfl

/-- **Unitaries on a window of `m` sites.** With at least two basis vectors per site, a unitary
supported on the window `[a, a + m)` of the open chain, `m ≥ 1`, is a product of at most
`12 (|α|ᵐ)⁵` neighbouring gates.

Source: arXiv:2307.01696, caption of Fig. 1: the unitaries with constant support "can be further
expressed with a low-depth circuit of local gates". -/
theorem isGateProduct_pathGraph_of_mem_supportedOperators_interval (hα : 2 ≤ Fintype.card α)
    {m : ℕ} (hm : 1 ≤ m) (a : Fin n)
    {Z : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ}
    (hZu : Z ∈ unitaryGroup _ ℂ)
    (hZ : Z ∈ supportedOperators (fun _ : Fin n ↦ α) (ManyBody.interval n a (a + m))) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n)) (12 * (Fintype.card α ^ m) ^ 5)
      Z := by
  set D := ManyBody.interval n a (a + m)
  set w := min m (n - a.val)
  have : NeZero w := ⟨by have := a.isLt; omega⟩
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨V', rfl⟩ := exists_eq_place_of_mem_supportedOperators hZ
  have hV' : V' ∈ unitaryGroup _ ℂ :=
    (place_mem_unitaryGroup_iff (X := fun _ : Fin n ↦ α) (D := D)).mp hZu
  set e := windowEquiv a m
  set σ := siteConfigurationEquiv (X := fun _ : Fin w ↦ α) (X' := fun _ : {s // s ∈ D} ↦ α) e
    fun _ ↦ Equiv.refl α
  have hV := isGateProduct_pathGraph_le_card_pow (n := w) hα
    (reindex_mem_unitaryGroup σ.symm V' hV')
  have hplace := IsGateProduct.place_pathGraph (X := fun _ : Fin n ↦ α) e
    (fun p p' h ↦ by rw [windowEquiv_val, windowEquiv_val, h]; omega) hV
  rw [reindex_apply, reindex_apply, submatrix_submatrix, Equiv.symm_symm, Equiv.self_comp_symm,
    submatrix_id_id] at hplace
  refine hplace.mono (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left
    (Nat.pow_le_pow_right (by omega) (min_le_left _ _)) 5))

/-- A unitary supported on a window is one gate on it. -/
theorem IsGateProduct.window_of_mem_supportedOperators {X : Fin n → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {m : ℕ} (a : Fin n)
    {Z : Matrix (Config X) (Config X) ℂ} (hZu : Z ∈ unitaryGroup _ ℂ)
    (hZ : Z ∈ supportedOperators X (ManyBody.interval n a (a + m))) :
    IsGateProduct (Geometry.window n m) 1 Z :=
  IsGateProduct.of_mem_supportedOperators (Γ := Geometry.window n m) (b := a) hZu hZ

/-- **Gates on windows through neighbouring gates.** With at least two basis vectors per site and
`m ≥ 1`, a product of gates of cost `K` on windows of `m` sites of the open chain is a product of
at most `12 (|α|ᵐ)⁵ K` neighbouring gates; the factor depends only on `|α|` and `m`.

Source: arXiv:2307.01696, caption of Fig. 1 and paragraph "The sequential-RG circuit". -/
theorem IsGateProduct.of_window (hα : 2 ≤ Fintype.card α) {m K : ℕ} (hm : 1 ≤ m)
    {U : Matrix (Config fun _ : Fin n ↦ α) (Config fun _ : Fin n ↦ α) ℂ}
    (hU : IsGateProduct (Geometry.window n m) K U) :
    IsGateProduct (Geometry.graph (SimpleGraph.pathGraph n))
      (12 * (Fintype.card α ^ m) ^ 5 * K) U :=
  hU.substitute fun b V hV ↦ by
    rw [mul_one]
    exact isGateProduct_pathGraph_of_mem_supportedOperators_interval hα hm b
      (place_mem_unitaryGroup hV) (place_mem_supportedOperators V)

end QuantumCircuit
