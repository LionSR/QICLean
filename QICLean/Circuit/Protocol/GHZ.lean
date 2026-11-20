/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.PermutationMatrixUnitary
import QICLean.Circuit.Geometry.Ring
import QICLean.Circuit.Model.Measurement

/-!
# GHZ-type states in constant depth with measurements

The GHZ-type state `|χ⟩ = ∑ⱼ αⱼ |j⟩^{⊗ι}` on the sites `ι`, with one basis `β` at every site, is
the weighted superposition of the constant configurations. Its connected correlations do not
decay with distance, while those of a vector prepared by a unitary circuit of depth `T` vanish
beyond the light cone (`QuantumCircuit.IsPreparedInDepth.dotProduct_mul_mul`); arXiv:2103.13367,
Example 1, uses this to show that the GHZ state needs a depth growing with the system size. With
measurements it is prepared in constant depth: arXiv:2307.01696, paragraph "Long-range MPS using
measurements", states that "the creation of GHZ-like states `|χ_M⟩ = ∑_{i=1}^b αᵢ |i⟩^{⊗M}`
becomes possible in only constant depth", citing among others arXiv:2103.13367, whose Example 1
gives the preparation for qubits. This file proves it for every finite abelian group `β` of
basis labels, such as `ℤ_b` for qudits, and every nonzero `α`, with one round of measurements
and a unitary circuit of depth `2` for every `M`, the depth of that example
(`QuantumCircuit.isOneRoundConversion_withZeroAncillas_ghzState`).

## The protocol

The system qudit `n` sits at the site `2n` of a ring of `2M` sites and its ancilla at `2n + 1`,
between the system qudits `n` and `n + 1`. The protocol is Example 1 of arXiv:2103.13367 for
qudits, with the differences of neighbouring system values measured through the ancillas.

* Product vector: the first system qudit is in `∑ᵢ αᵢ |i⟩`, the other system qudits in the
  uniform superposition `∑ᵢ |i⟩`, and the ancillas in `|0⟩`.
* Two layers of controlled shifts, `|k⟩|a⟩ ↦ |k⟩|a + k⟩` from the system qudit `n` into the
  ancilla `n`, then `|a⟩|k⟩ ↦ |a - k⟩|k⟩` from the system qudit `n + 1`, write the difference
  `kₙ - k_{n+1}` of neighbouring system values into the ancilla `n`, for `n < M - 1`.
* Measuring the ancillas `n < M - 1` in the computational basis gives outcomes `mₙ`, and leaves
  `∑ᵢ αᵢ ⊗ₙ |i - pₙ⟩` on the system qudits with `pₙ = m₀ + ⋯ + m_{n-1}`.
* The single-site shifts `X^{pₙ}` on the system qudit `n` and `X^{-mₙ}` on the ancilla `n`,
  free corrections, give `|χ_M⟩` with every ancilla back in `|0⟩`.

The correction at the system qudit `n` depends on all the outcomes `m₀, …, m_{n-1}`, which is
where the global classical communication of the model is used. Every gate of the circuit acts on
a cell `{k, k + 1}` of the ring, so the depth `2` counted here bounds the depth of
arXiv:2103.13367, where the ancillas are attached to their sites. Every outcome gives exactly
`|χ_M⟩` (`QuantumCircuit.ghzProtocol_output`): no outcome is post-selected.

## Main definitions

* `QuantumCircuit.ghzState` — the state `|χ⟩`.
* `QuantumCircuit.withZeroAncillas` — a state of the system qudits, with every ancilla in `|0⟩`,
  as a state of the ring of `2M` sites.
* `QuantumCircuit.ghzInitial` — the product vector the protocol starts from.
* `QuantumCircuit.ghzCircuit`, `QuantumCircuit.ghzMeasured`, `QuantumCircuit.ghzCorrection` — the
  two layers of controlled shifts, the measured ancillas and the corrections.

## Main results

* `QuantumCircuit.ghzState_apply`, `QuantumCircuit.ghzState_eq_sum`,
  `QuantumCircuit.ghzState_smul` — the amplitudes of `|χ⟩`, the sum of its constant branches,
  and its linearity in the weights.
* `QuantumCircuit.depth_ghzCircuit_le` — the circuit has depth at most `2`.
* `QuantumCircuit.ghzProtocol_output` — every outcome gives `|χ_M⟩`.
* `QuantumCircuit.isOneRoundConversion_withZeroAncillas_ghzState` — the preparation with one round
  of measurements.

The declarations restate `ghzState` and `ghzState_apply` of `TNLean/Circuit/GHZState.lean` and
the protocol of `TNLean/Circuit/Measurement/GHZ.lean` at commit `414a18fb88` (Apache-2.0). The
changes: the GHZ-type state is defined on any finite set of sites with any finite basis; the
protocol is a one-round conversion of the measurement model (`QuantumCircuit.IsOneRoundConversion`)
on the ring geometry, with the controlled shifts written as permutation gates on the cells, and
for any finite abelian group of basis labels in place of `ℤ_b`; the initial vector is the
product vector `σ ↦ ∏ₛ vₛ(σₛ)`; the site `2n + r` is `finProdFinEquiv (n, r)`.

## References

* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraph "Long-range MPS using measurements",
  and eq. (19) with the paragraph after it.
* arXiv:2103.13367 (Piroli, Styliaris, Cirac), Example 1 ("The GHZ and `W` states").
-/

open Matrix ManyBody

namespace QuantumCircuit

/-! ### The GHZ-type state -/

section State

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]

/-- The GHZ-type state `|χ⟩ = ∑ⱼ αⱼ |j⟩^{⊗ι}` on the sites `ι` with the basis `β` at every site
(arXiv:2307.01696, the paragraph after eq. (19)): its amplitude at `s` is `∑ⱼ αⱼ` times the
product of the coordinates `s k` of the basis vector `|j⟩`. -/
def ghzState (α : β → ℂ) (s : ι → β) : ℂ :=
  ∑ j, α j * ∏ k, (Pi.single j 1 : β → ℂ) (s k)

/-- The amplitude of `|χ⟩` at `s` is `α (s i₀)` if all the values `s k` are equal, and `0`
otherwise. -/
theorem ghzState_apply (α : β → ℂ) (s : ι → β) (i₀ : ι) :
    ghzState α s = if ∀ k, s k = s i₀ then α (s i₀) else 0 := by
  simp only [ghzState, Pi.single_apply, Finset.prod_boole, Finset.mem_univ, true_implies]
  rw [Finset.sum_eq_single (s i₀)]
  · split_ifs <;> simp
  · intro j _ hj
    rw [ite_eq_right fun h ↦ hj (h i₀).symm, mul_zero]
  · simp

/-- `|χ⟩` is the sum of its constant branches `αⱼ |j⟩^{⊗ι}`. -/
theorem ghzState_eq_sum (α : β → ℂ) :
    ghzState (ι := ι) α = ∑ j, α j • Pi.single (fun _ : ι ↦ j) (1 : ℂ) := by
  funext s
  simp only [ghzState, Pi.single_apply, Finset.prod_boole, Finset.mem_univ, true_implies,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, funext_iff]

/-- `|χ⟩` is linear in the weights. -/
theorem ghzState_smul (c : ℂ) (α : β → ℂ) : ghzState (ι := ι) (c • α) = c • ghzState α := by
  funext s
  simp only [ghzState, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

end State

/-! ### Sites of the ring -/

section Sites

variable {β : Type} [Zero β] [DecidableEq β] {M : ℕ}

/-- The state `ψ` of the `M` system qudits, with every ancilla in `|0⟩`, as a state of the ring
of `2M` sites: the system qudit `n` at the site `2n` and its ancilla at `2n + 1`.

Source: arXiv:2103.13367, paragraph "Quantum circuits and LOCC" (ancillas initialized in a
product state) and Example 1. -/
def withZeroAncillas (ψ : (Fin M → β) → ℂ) : (Fin (M * 2) → β) → ℂ := fun x ↦
  ψ (fun n ↦ x (finProdFinEquiv (n, 0))) * ∏ n, if x (finProdFinEquiv (n, 1)) = 0 then 1 else 0

/-- The site `2n + r` of the system qudit `n` (`r = 0`) or of its ancilla (`r = 1`). -/
private def site (n : Fin M) (r : Fin 2) : Fin (M * 2) :=
  finProdFinEquiv (n, r)

private theorem site_val (n : Fin M) (r : Fin 2) : (site n r).val = r.val + 2 * n.val :=
  rfl

omit [Zero β] [DecidableEq β] in
private theorem site_inj {n n' : Fin M} {r r' : Fin 2} (h : site n r = site n' r') :
    n = n' ∧ r = r' := by
  simpa [site] using h

private theorem site_symm (j : Fin (M * 2)) :
    site (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2 = j :=
  finProdFinEquiv.apply_symm_apply j

private theorem symm_site (n : Fin M) (r : Fin 2) : finProdFinEquiv.symm (site n r) = (n, r) :=
  finProdFinEquiv.symm_apply_apply _

private theorem withZeroAncillas_site (ψ : (Fin M → β) → ℂ) (x : Fin (M * 2) → β) :
    withZeroAncillas ψ x =
      ψ (fun n ↦ x (site n 0)) * ∏ n, if x (site n 1) = 0 then 1 else 0 :=
  rfl

end Sites

/-! ### The protocol -/

section Protocol

variable {β : Type} [Fintype β] [DecidableEq β] [AddCommGroup β] {M : ℕ}

/-- The measured ancillas: the sites `2n + 1` with `n < M - 1`. -/
def ghzMeasured : Finset (Fin (M * 2)) :=
  (Finset.univ.filter fun n : Fin M ↦ n.val + 1 < M).image fun n ↦ finProdFinEquiv (n, 1)

/-- The left sites `2n` of the cells `{2n, 2n + 1}` of the first layer, `n < M - 1`. -/
private def firstCells : Finset (Fin (M * 2)) :=
  (Finset.univ.filter fun n : Fin M ↦ n.val + 1 < M).image fun n ↦ site n 0

private theorem mem_firstCells {k : Fin (M * 2)} :
    k ∈ firstCells ↔ ∃ n : Fin M, n.val + 1 < M ∧ site n 0 = k := by
  simp [firstCells]

private theorem mem_ghzMeasured {k : Fin (M * 2)} :
    k ∈ ghzMeasured ↔ ∃ n : Fin M, n.val + 1 < M ∧ site n 1 = k := by
  simp [ghzMeasured, site]

/-- The configurations of a region shifted at the target `t` by `f` of the value at the control
`c`: the action `u ↦ u + f(u_c) e_t` of a controlled shift. -/
private def addEquiv {S : Type} [DecidableEq S] {D : Finset S} (t c : {v // v ∈ D})
    (htc : t ≠ c) (f : β → β) : Equiv.Perm (RegionConfig (fun _ : S ↦ β) D) where
  toFun u := Function.update u t (u t + f (u c))
  invFun u := Function.update u t (u t - f (u c))
  left_inv u := by
    funext v
    by_cases hv : v = t
    · subst hv
      simp [Function.update_of_ne htc.symm]
    · simp [Function.update_of_ne hv]
  right_inv u := by
    funext v
    by_cases hv : v = t
    · subst hv
      simp [Function.update_of_ne htc.symm]
    · simp [Function.update_of_ne hv]

omit [Fintype β] [DecidableEq β] in
private theorem addEquiv_apply {S : Type} [DecidableEq S] {D : Finset S} (t c : {v // v ∈ D})
    (htc : t ≠ c) (f : β → β) (u : RegionConfig (fun _ : S ↦ β) D) (v : {v // v ∈ D}) :
    addEquiv t c htc f u v = if v = t then u t + f (u c) else u v :=
  Function.update_apply ..

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem permMatrix_apply' {α : Type} [DecidableEq α] (σ : Equiv.Perm α) (u u' : α) :
    σ.permMatrix ℂ u u' = if σ u = u' then 1 else 0 := by
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

/-- **A layer of configuration permutations.** If `Q` agrees with the permutation `e b` of the
configurations of the cell `b` at the sites of every cell, and fixes the other sites, then the
layer of the permutation matrices of the `e b` acts on vectors by `v ↦ v ∘ Q`. -/
private theorem kraus_ofCells_permMatrix_mulVec {S : Type} [Fintype S] [DecidableEq S]
    {Γ : Geometry S} {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (C : Finset Γ.Cell) (hC : (C : Set Γ.Cell).PairwiseDisjoint Γ.cell)
    (e : (b : C) → Equiv.Perm (RegionConfig X (Γ.cell b))) (Q : Config X → Config X)
    (hQ : ∀ y (b : C) (s : {s // s ∈ Γ.cell b}), Q y s = e b (fun v ↦ y v) s)
    (hQ' : ∀ y s, s ∉ C.biUnion Γ.cell → Q y s = y s)
    (i : (Layer.ofCells (G := KrausGate) C hC fun b ↦
      KrausFamily.single ((e b).permMatrix ℂ)).Index) (w : Config X → ℂ) :
    (Layer.ofCells (G := KrausGate) C hC fun b ↦
      KrausFamily.single ((e b).permMatrix ℂ)).kraus KrausGate.ev i *ᵥ w = w ∘ Q := by
  funext y
  have hentry : ∀ x, (Layer.ofCells (G := KrausGate) C hC fun b ↦
      KrausFamily.single ((e b).permMatrix ℂ)).kraus KrausGate.ev i y x =
      if Q y = x then 1 else 0 := by
    intro x
    rw [Layer.kraus_apply]
    change (∏ b : C, (e b).permMatrix ℂ (fun v ↦ y v) (fun v ↦ x v)) *
      ∏ s : {s // s ∉ C.biUnion Γ.cell}, (1 : Matrix (X s) (X s) ℂ) (y s) (x s) = _
    simp only [permMatrix_apply', one_apply]
    by_cases h : Q y = x
    · subst h
      rw [ite_eq_left rfl,
        Fintype.prod_eq_one _ fun b ↦ ite_eq_left (funext fun s ↦ (hQ y b s).symm),
        Fintype.prod_eq_one _ fun s : {s // s ∉ C.biUnion Γ.cell} ↦
          ite_eq_left (hQ' y s.1 s.2).symm, mul_one]
    · rw [ite_eq_right h]
      obtain ⟨s, hs⟩ := Function.ne_iff.mp h
      by_cases hc : s ∈ C.biUnion Γ.cell
      · obtain ⟨b, hb, hsb⟩ := Finset.mem_biUnion.mp hc
        refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ ⟨b, hb⟩)
          (ite_eq_right fun he ↦ hs ?_)) _
        rw [hQ y ⟨b, hb⟩ ⟨s, hsb⟩]
        exact congrFun he ⟨s, hsb⟩
      · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨s, hc⟩)
          (ite_eq_right fun he ↦ hs ?_))
        rw [hQ' y s hc]
        exact he
  simp only [mulVec, dotProduct, hentry, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, Function.comp_apply]

/-- A product of permutation matrices acts on vectors by relabelling the configurations. -/
private theorem prodOp_permMatrix_mulVec {S : Type} [Fintype S] [DecidableEq S] {X : S → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (e : (s : S) → Equiv.Perm (X s))
    (w : Config X → ℂ) :
    prodOp (fun s ↦ (e s).permMatrix ℂ) *ᵥ w = fun x ↦ w fun s ↦ e s (x s) := by
  funext x
  rw [mulVec, dotProduct, Finset.sum_eq_single (fun s ↦ e s (x s))]
  · rw [prodOp_apply, Fintype.prod_eq_one _ fun s ↦ by rw [permMatrix_apply', ite_eq_left rfl],
      one_mul]
  · intro y _ hy
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hy
    rw [prodOp_apply, Finset.prod_eq_zero (Finset.mem_univ s)
      (by rw [permMatrix_apply', ite_eq_right (Ne.symm hs)]), zero_mul]
  · simp

section Ring

variable [NeZero M]

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem add_one_ne_self (k : Fin (M * 2)) : k + 1 ≠ k := by
  intro h
  have h2 : 2 ≤ M * 2 := by have := NeZero.ne M; omega
  have := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M * 2)] at this
  rcases Nat.lt_or_ge (k.val + 1) (M * 2) with hk | hk
  · rw [Nat.mod_eq_of_lt hk] at this; omega
  · have : k.val + 1 = M * 2 := by have := k.isLt; omega
    simp_all

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem site_zero_add_one (n : Fin M) : site n 0 + 1 = site n 1 := by
  ext
  rw [Fin.val_add_one_of_lt' (by rw [site_val]; omega), site_val, site_val]
  simp only [Fin.val_zero, Fin.val_one]
  omega

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem site_one_add_one (n : Fin M) (h : n.val + 1 < M) :
    site n 1 + 1 = site ⟨n.val + 1, h⟩ 0 := by
  ext
  rw [Fin.val_add_one_of_lt' (by rw [site_val]; omega), site_val, site_val]
  simp only [Fin.val_zero, Fin.val_one]
  omega

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem cell_site_zero (n : Fin M) :
    (Geometry.ring (M * 2)).cell (site n 0) = {site n 0, site n 1} := by
  rw [Geometry.ring_cell, site_zero_add_one]

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem cell_site_one (n : Fin M) (h : n.val + 1 < M) :
    (Geometry.ring (M * 2)).cell (site n 1) = {site n 1, site ⟨n.val + 1, h⟩ 0} := by
  rw [Geometry.ring_cell, site_one_add_one n h]

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem firstCells_pairwiseDisjoint :
    ((firstCells : Finset (Fin (M * 2))) : Set (Fin (M * 2))).PairwiseDisjoint
      (Geometry.ring (M * 2)).cell := by
  intro k hk k' hk' hkk'
  obtain ⟨n, -, rfl⟩ := mem_firstCells.mp hk
  obtain ⟨n', -, rfl⟩ := mem_firstCells.mp hk'
  have hn : n ≠ n' := fun h ↦ hkk' (h ▸ rfl)
  change Disjoint ((Geometry.ring (M * 2)).cell _) ((Geometry.ring (M * 2)).cell _)
  rw [cell_site_zero, cell_site_zero, Finset.disjoint_left]
  intro i hi hi'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi'
  rcases hi with rfl | rfl <;> rcases hi' with h | h <;> exact hn (site_inj h).1

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem ghzMeasured_pairwiseDisjoint :
    ((ghzMeasured : Finset (Fin (M * 2))) : Set (Fin (M * 2))).PairwiseDisjoint
      (Geometry.ring (M * 2)).cell := by
  intro k hk k' hk' hkk'
  obtain ⟨n, hn1, rfl⟩ := mem_ghzMeasured.mp hk
  obtain ⟨n', hn1', rfl⟩ := mem_ghzMeasured.mp hk'
  have hn : n ≠ n' := fun h ↦ hkk' (h ▸ rfl)
  change Disjoint ((Geometry.ring (M * 2)).cell _) ((Geometry.ring (M * 2)).cell _)
  rw [cell_site_one n hn1, cell_site_one n' hn1', Finset.disjoint_left]
  intro i hi hi'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi hi'
  rcases hi with rfl | rfl <;> rcases hi' with h | h
  · exact hn (site_inj h).1
  · exact absurd (site_inj h).2 (by decide)
  · exact absurd (site_inj h).2 (by decide)
  · exact hn (Fin.ext (by have := congrArg Fin.val (site_inj h).1; simp at this; omega))

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem finRotate_ne (k : Fin (M * 2)) : finRotate (M * 2) k ≠ k := by
  rw [finRotate_apply]
  exact add_one_ne_self k

omit [Fintype β] [DecidableEq β] [AddCommGroup β] [NeZero M] in
private theorem mem_cell_left (k : Fin (M * 2)) : k ∈ (Geometry.ring (M * 2)).cell k :=
  Finset.mem_insert_self _ _

omit [Fintype β] [DecidableEq β] [AddCommGroup β] [NeZero M] in
private theorem mem_cell_right (k : Fin (M * 2)) :
    finRotate (M * 2) k ∈ (Geometry.ring (M * 2)).cell k :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The controlled shift `|k⟩|a⟩ ↦ |k⟩|a + k⟩` of the first layer on the cell `{k, k + 1}`, as
the permutation `u ↦ u - u_k e_{k+1}` of its configurations. -/
private def firstShiftEquiv (k : Fin (M * 2)) :
    Equiv.Perm (RegionConfig (fun _ : Fin (M * 2) ↦ β) ((Geometry.ring (M * 2)).cell k)) :=
  addEquiv ⟨_, mem_cell_right k⟩ ⟨k, mem_cell_left k⟩
    (fun h ↦ finRotate_ne k (congrArg Subtype.val h)) Neg.neg

/-- The controlled shift `|a⟩|k⟩ ↦ |a - k⟩|k⟩` of the second layer on the cell `{k, k + 1}`, as
the permutation `u ↦ u + u_{k+1} e_k` of its configurations. -/
private def secondShiftEquiv (k : Fin (M * 2)) :
    Equiv.Perm (RegionConfig (fun _ : Fin (M * 2) ↦ β) ((Geometry.ring (M * 2)).cell k)) :=
  addEquiv ⟨k, mem_cell_left k⟩ ⟨_, mem_cell_right k⟩
    (fun h ↦ finRotate_ne k (congrArg Subtype.val h).symm) id

/-- The first layer of controlled shifts. -/
private noncomputable def firstLayer :
    Layer (Geometry.ring (M * 2)) KrausGate (fun _ ↦ β) (fun _ ↦ β) :=
  Layer.ofCells firstCells firstCells_pairwiseDisjoint fun b ↦
    KrausFamily.single ((firstShiftEquiv b.1).permMatrix ℂ)

/-- The second layer of controlled shifts. -/
private noncomputable def secondLayer :
    Layer (Geometry.ring (M * 2)) KrausGate (fun _ ↦ β) (fun _ ↦ β) :=
  Layer.ofCells ghzMeasured ghzMeasured_pairwiseDisjoint fun b ↦
    KrausFamily.single ((secondShiftEquiv b.1).permMatrix ℂ)

private theorem forall_firstLayer :
    (firstLayer (β := β) (M := M)).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Layer.forall_ofCells _ (KrausFamily.isUnitary_single (one_mem _)) _ _ _ fun _ ↦
    KrausFamily.isUnitary_single (Equiv.Perm.permMatrix_mem_unitaryGroup _)

private theorem forall_secondLayer :
    (secondLayer (β := β) (M := M)).Forall KrausGate.ev KrausFamily.IsUnitary :=
  Layer.forall_ofCells _ (KrausFamily.isUnitary_single (one_mem _)) _ _ _ fun _ ↦
    KrausFamily.isUnitary_single (Equiv.Perm.permMatrix_mem_unitaryGroup _)

/-- The two layers of controlled shifts of the protocol: `|k⟩|a⟩ ↦ |k⟩|a + k⟩` on the cells
`{2n, 2n + 1}`, then `|a⟩|k⟩ ↦ |a - k⟩|k⟩` on the cells `{2n + 1, 2n + 2}`, for `n < M - 1`.

Source: arXiv:2103.13367, Example 1, for qudits. -/
noncomputable def ghzCircuit : UnitaryCircuit (Geometry.ring (M * 2)) (fun _ ↦ β) :=
  (UnitaryCircuit.ofLayer firstLayer forall_firstLayer).comp
    (UnitaryCircuit.ofLayer secondLayer forall_secondLayer)

/-- The circuit of the protocol has depth at most `2`. -/
theorem depth_ghzCircuit_le : (ghzCircuit (β := β) (M := M)).depth ≤ 2 := by
  rw [ghzCircuit, UnitaryCircuit.depth_comp, UnitaryCircuit.depth_ofLayer,
    UnitaryCircuit.depth_ofLayer]
  exact Nat.add_le_add (Layer.depth_le_one _) (Layer.depth_le_one _)

/-- The action of the first layer on configurations: `x_{2n+1} ↦ x_{2n+1} - x_{2n}` for
`n < M - 1`. -/
private def firstShift (y : Fin (M * 2) → β) (j : Fin (M * 2)) : β :=
  if (finProdFinEquiv.symm j).2 = 1 ∧ (finProdFinEquiv.symm j).1.val + 1 < M then
    y j - y (site (finProdFinEquiv.symm j).1 0) else y j

/-- The action of the second layer on configurations: `x_{2n+1} ↦ x_{2n+1} + x_{2n+2}` for
`n < M - 1`. -/
private def secondShift (y : Fin (M * 2) → β) (j : Fin (M * 2)) : β :=
  if (finProdFinEquiv.symm j).2 = 1 ∧ (finProdFinEquiv.symm j).1.val + 1 < M then
    y j + y (j + 1) else y j

omit [Fintype β] [DecidableEq β] [NeZero M] in
private theorem firstShift_site_zero (y : Fin (M * 2) → β) (n : Fin M) :
    firstShift y (site n 0) = y (site n 0) := by
  rw [firstShift, symm_site]
  simp

omit [Fintype β] [DecidableEq β] [NeZero M] in
private theorem firstShift_site_one (y : Fin (M * 2) → β) (n : Fin M) :
    firstShift y (site n 1) =
      if n.val + 1 < M then y (site n 1) - y (site n 0) else y (site n 1) := by
  rw [firstShift, symm_site]
  simp

omit [Fintype β] [DecidableEq β] in
private theorem secondShift_site_zero (y : Fin (M * 2) → β) (n : Fin M) :
    secondShift y (site n 0) = y (site n 0) := by
  rw [secondShift, symm_site]
  simp

omit [Fintype β] [DecidableEq β] in
private theorem secondShift_site_one (y : Fin (M * 2) → β) (n : Fin M) :
    secondShift y (site n 1) = if h : n.val + 1 < M then
      y (site n 1) + y (site ⟨n.val + 1, h⟩ 0) else y (site n 1) := by
  rw [secondShift, symm_site]
  by_cases h : n.val + 1 < M
  · simp [h, site_one_add_one n h]
  · simp [h]

private theorem firstLayer_mulVec (i : (firstLayer (β := β) (M := M)).Index)
    (w : (Fin (M * 2) → β) → ℂ) : firstLayer.kraus KrausGate.ev i *ᵥ w = w ∘ firstShift := by
  refine kraus_ofCells_permMatrix_mulVec _ _ _ _ (fun y b s ↦ ?_) (fun y s hs ↦ ?_) i w
  · obtain ⟨b, hb⟩ := b
    obtain ⟨n, hn, rfl⟩ := mem_firstCells.mp hb
    obtain ⟨s, hs⟩ := s
    change firstShift y s = addEquiv _ _ _ _ _ _
    rw [addEquiv_apply]
    have hs' := hs
    rw [cell_site_zero, Finset.mem_insert, Finset.mem_singleton] at hs'
    rcases hs' with rfl | rfl
    · rw [ite_eq_right fun h ↦ finRotate_ne _ (congrArg Subtype.val h).symm, firstShift_site_zero]
    · have hrot : finRotate (M * 2) (site n 0) = site n 1 := by
        rw [finRotate_apply, site_zero_add_one]
      rw [ite_eq_left (Subtype.ext hrot.symm), firstShift_site_one, ite_eq_left hn]
      change _ = y (finRotate (M * 2) (site n 0)) + -y (site n 0)
      rw [hrot, sub_eq_add_neg]
  · unfold firstShift
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    refine hs (Finset.mem_biUnion.mpr ⟨site (finProdFinEquiv.symm s).1 0,
      mem_firstCells.mpr ⟨_, h2, rfl⟩, ?_⟩)
    rw [cell_site_zero, ← h1, site_symm]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

private theorem secondLayer_mulVec (i : (secondLayer (β := β) (M := M)).Index)
    (w : (Fin (M * 2) → β) → ℂ) : secondLayer.kraus KrausGate.ev i *ᵥ w = w ∘ secondShift := by
  refine kraus_ofCells_permMatrix_mulVec _ _ _ _ (fun y b s ↦ ?_) (fun y s hs ↦ ?_) i w
  · obtain ⟨b, hb⟩ := b
    obtain ⟨n, hn, rfl⟩ := mem_ghzMeasured.mp hb
    obtain ⟨s, hs⟩ := s
    change secondShift y s = addEquiv _ _ _ _ _ _
    rw [addEquiv_apply]
    have hs' := hs
    rw [cell_site_one n hn, Finset.mem_insert, Finset.mem_singleton] at hs'
    have hrot : finRotate (M * 2) (site n 1) = site ⟨n.val + 1, hn⟩ 0 := by
      rw [finRotate_apply, site_one_add_one n hn]
    rcases hs' with rfl | rfl
    · rw [ite_eq_left rfl, secondShift_site_one, dite_eq_left hn]
      change _ = y (site n 1) + id (y (finRotate (M * 2) (site n 1)))
      rw [hrot]
      rfl
    · rw [ite_eq_right fun h ↦ absurd (site_inj (congrArg Subtype.val h)).2 (by decide),
        secondShift_site_zero]
  · unfold secondShift
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    refine hs (Finset.mem_biUnion.mpr ⟨s, mem_ghzMeasured.mpr ⟨_, h2, ?_⟩, mem_cell_left s⟩)
    rw [← h1, site_symm]

/-- The circuit of the protocol acts on configurations by the two layers of shifts. -/
private theorem ghzCircuit_op_mulVec (w : (Fin (M * 2) → β) → ℂ) :
    (ghzCircuit (β := β) (M := M)).op *ᵥ w = fun z ↦ w (firstShift (secondShift z)) := by
  obtain ⟨i₁⟩ := (UnitaryCircuit.ofLayer firstLayer (forall_firstLayer (β := β) (M := M))
    ).nonempty_index _ (List.mem_singleton_self _)
  obtain ⟨i₂⟩ := (UnitaryCircuit.ofLayer secondLayer (forall_secondLayer (β := β) (M := M))
    ).nonempty_index _ (List.mem_singleton_self _)
  rw [ghzCircuit, UnitaryCircuit.op_comp, UnitaryCircuit.op_ofLayer _ _ i₁,
    UnitaryCircuit.op_ofLayer _ _ i₂, ← mulVec_mulVec, firstLayer_mulVec, secondLayer_mulVec]
  rfl

/-! ### Outcomes and corrections -/

/-- The outcome `mₙ` at the ancilla `n`, and `0` for the last ancilla, which is not measured. -/
private def outcome (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured) (n : Fin M) : β :=
  if h : site n 1 ∈ ghzMeasured then m ⟨site n 1, h⟩ else 0

/-- The prefix sum `pₙ = m₀ + ⋯ + m_{n-1}` of the outcomes. -/
private def prefixSum (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured) (n : Fin M) : β :=
  Fin.partialSum (outcome m) n.castSucc

/-- The correction, as the configuration it adds: `-pₙ` at the system qudit `n` and `mₙ` at the
ancilla `n`. -/
private def shiftOf (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured) (j : Fin (M * 2)) :
    β :=
  if (finProdFinEquiv.symm j).2 = 0 then -prefixSum m (finProdFinEquiv.symm j).1
    else outcome m (finProdFinEquiv.symm j).1

/-- The correction at the site `j` for the outcome `m`: the shift `|a⟩ ↦ |a - δ⟩`, `X^{pₙ}` at the
system qudit `n` and `X^{-mₙ}` at the ancilla `n`, with `pₙ = m₀ + ⋯ + m_{n-1}` the sum of the
outcomes before `n` and `m_{M-1} = 0`.

Source: arXiv:2103.13367, Example 1 ("Given the output `{k_j}`, we finally apply
`⊗ₙ (σ^x_n)^{∑_{m=2}^n k_m}` to the spins"), for qudits. -/
noncomputable def ghzCorrection (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured)
    (j : Fin (M * 2)) : Matrix β β ℂ :=
  (Equiv.addRight (shiftOf m j)).permMatrix ℂ

/-- The product vector of the protocol: `∑ᵢ αᵢ |i⟩` at the first system qudit, `∑ᵢ |i⟩` at the
other system qudits, and `|0⟩` at the ancillas.

Source: arXiv:2103.13367, Example 1, for qudits. -/
def ghzInitial (α : β → ℂ) (j : Fin (M * 2)) : β → ℂ :=
  if j = finProdFinEquiv (0, 0) then α
  else if (finProdFinEquiv.symm j).2 = 0 then fun _ ↦ 1 else Pi.single 0 1

omit [Fintype β] [DecidableEq β] [NeZero M] in
private theorem shiftOf_site_zero (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured)
    (n : Fin M) : shiftOf m (site n 0) = -prefixSum m n := by
  rw [shiftOf, symm_site]
  simp

omit [Fintype β] [DecidableEq β] [NeZero M] in
private theorem shiftOf_site_one (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured)
    (n : Fin M) : shiftOf m (site n 1) = outcome m n := by
  rw [shiftOf, symm_site]
  simp

omit [Fintype β] [DecidableEq β] in
private theorem prefixSum_zero (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured) :
    prefixSum m 0 = 0 := by
  simp [prefixSum]

omit [Fintype β] [DecidableEq β] [NeZero M] in
private theorem prefixSum_succ (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured)
    (n : Fin M) (hn : n.val + 1 < M) :
    prefixSum m ⟨n.val + 1, hn⟩ = prefixSum m n + outcome m n := by
  rw [prefixSum, show (⟨n.val + 1, hn⟩ : Fin M).castSucc = n.succ from rfl, Fin.partialSum_succ]
  rfl

omit [Fintype β] [DecidableEq β] [NeZero M] in
private theorem outcome_of_not_lt (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured)
    (n : Fin M) (hn : ¬n.val + 1 < M) : outcome m n = 0 := by
  refine dite_eq_right fun h ↦ hn ?_
  obtain ⟨n', hn', h'⟩ := mem_ghzMeasured.mp h
  rw [← (site_inj h').1]
  exact hn'

omit [Fintype β] [DecidableEq β] [NeZero M] in
/-- The outcome `m` is read on the corrected configuration `x + δ` exactly when every measured
ancilla of `x` is `0`. -/
private theorem restrict_add_shiftOf_eq_iff
    (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured) (x : Fin (M * 2) → β) :
    (fun v : {v // v ∈ ghzMeasured} ↦ x v + shiftOf m v) = m ↔
      ∀ n : Fin M, n.val + 1 < M → x (site n 1) = 0 := by
  constructor
  · intro h n hn
    have hi : site n 1 ∈ ghzMeasured := mem_ghzMeasured.mpr ⟨n, hn, rfl⟩
    have := congrFun h ⟨_, hi⟩
    rwa [shiftOf_site_one, outcome, dite_eq_left hi, add_eq_right] at this
  · intro h
    funext ⟨i, hi⟩
    obtain ⟨n, hn, rfl⟩ := mem_ghzMeasured.mp hi
    simp only [shiftOf_site_one, outcome, dite_eq_left hi, h n hn, zero_add]

omit [Fintype β] in
private theorem prod_ghzInitial (α : β → ℂ) (y : Fin (M * 2) → β) :
    ∏ s, ghzInitial α s (y s) = α (y (site 0 0)) * ∏ n, if y (site n 1) = 0 then 1 else 0 := by
  have h1 : ∀ n : Fin M, ghzInitial α (site n 1) = Pi.single 0 1 := fun n ↦ by
    rw [ghzInitial, ite_eq_right fun h : site n 1 = finProdFinEquiv (0, 0) ↦
      absurd (site_inj (n' := 0) (r' := 0) h).2 (by decide)]
    rw [symm_site]
    simp
  have h0 : ∀ n : Fin M, n ≠ 0 → ghzInitial α (site n 0) = fun _ ↦ 1 := fun n hn ↦ by
    rw [ghzInitial, ite_eq_right fun h : site n 0 = finProdFinEquiv (0, 0) ↦
      hn (site_inj (n' := 0) (r' := 0) h).1]
    rw [symm_site]
    simp
  rw [← Fintype.prod_equiv finProdFinEquiv
    (fun q ↦ ghzInitial α (site q.1 q.2) (y (site q.1 q.2))) _ fun _ ↦ rfl,
    Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two, Finset.prod_mul_distrib, h1, Pi.single_apply]
  congr 1
  rw [Finset.prod_eq_single 0 (fun n _ hn ↦ by rw [h0 n hn]) (by simp)]
  exact congrFun (ite_eq_left rfl) _

omit [Fintype β] [DecidableEq β] [AddCommGroup β] in
private theorem forall_succ_eq_iff (s : Fin M → β) :
    (∀ (n : Fin M) (hn : n.val + 1 < M), s ⟨n.val + 1, hn⟩ = s n) ↔ ∀ n, s n = s 0 := by
  constructor
  · intro h n
    obtain ⟨k, hk⟩ := n
    induction k with
    | zero => rfl
    | succ k ih => rw [h ⟨k, by omega⟩ hk, ih]
  · intro h n hn
    rw [h, h n]

omit [Fintype β] [AddCommGroup β] in
private theorem single_eq_diagonal {α : Type} [DecidableEq α] (m : α) :
    (single m m 1 : Matrix α α ℂ) = diagonal fun u ↦ if u = m then 1 else 0 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = m <;> simp [single_apply, ha, eq_comm]
  · rw [single_apply, diagonal_apply_ne _ hab]
    exact ite_eq_right fun h ↦ hab (h.1.symm.trans h.2)

/-- **Every outcome gives the GHZ-type state.** For every outcome `m` of the measurement of the
ancillas, the corrected vector of the protocol is `|χ_M⟩ = ∑ᵢ αᵢ |i⟩^{⊗M}` with every ancilla in
`|0⟩`: the scalar is `1`, so no outcome is post-selected.

Source: arXiv:2103.13367, Example 1 ("Given the output `{k_j}`, we finally apply
`⊗ₙ (σ^x_n)^{∑_{m=2}^n k_m}` to the spins"), for qudits. -/
theorem ghzProtocol_output (α : β → ℂ)
    (m : RegionConfig (fun _ : Fin (M * 2) ↦ β) ghzMeasured) :
    (prodOp (ghzCorrection m) * place ghzMeasured (single m m 1) * ghzCircuit.op) *ᵥ
      (fun σ ↦ ∏ s, ghzInitial α s (σ s)) = withZeroAncillas (ghzState α) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, ghzCircuit_op_mulVec, single_eq_diagonal]
  change prodOp (fun s ↦ (Equiv.addRight (shiftOf m s)).permMatrix ℂ) *ᵥ _ = _
  rw [prodOp_permMatrix_mulVec]
  funext x
  simp only [Equiv.coe_addRight]
  rw [place_diagonal_mulVec]
  simp only [restrict_add_shiftOf_eq_iff]
  rw [prod_ghzInitial, withZeroAncillas_site, ghzState_apply _ _ 0]
  set s : Fin M → β := fun n ↦ x (site n 0) with hs
  set z : Fin (M * 2) → β := fun j ↦ x j + shiftOf m j with hz
  have hz0 : ∀ n, z (site n 0) = s n - prefixSum m n := fun n ↦ by
    simp only [hz, hs, shiftOf_site_zero, sub_eq_add_neg]
  have hz1 : ∀ n, z (site n 1) = x (site n 1) + outcome m n := fun n ↦ by
    simp only [hz, shiftOf_site_one]
  have hy0 : firstShift (secondShift z) (site 0 0) = s 0 := by
    rw [firstShift_site_zero, secondShift_site_zero, hz0, prefixSum_zero, sub_zero]
  rw [hy0]
  by_cases hmeas : ∀ n : Fin M, n.val + 1 < M → x (site n 1) = 0
  · rw [ite_eq_left hmeas, one_mul]
    have hy : ∀ n, firstShift (secondShift z) (site n 1) = 0 ↔
        (∀ hn : n.val + 1 < M, s ⟨n.val + 1, hn⟩ = s n) ∧ x (site n 1) = 0 := fun n ↦ by
      by_cases hn : n.val + 1 < M
      · have hval : firstShift (secondShift z) (site n 1) = s ⟨n.val + 1, hn⟩ - s n := by
          rw [firstShift_site_one, ite_eq_left hn, secondShift_site_one, dite_eq_left hn,
            secondShift_site_zero, hz1, hz0, hz0, prefixSum_succ m n hn, hmeas n hn]
          abel
        rw [hval, sub_eq_zero]
        simp [hn, hmeas n hn]
      · rw [firstShift_site_one, ite_eq_right hn, secondShift_site_one, dite_eq_right hn, hz1,
          outcome_of_not_lt m n hn, add_zero]
        simp [hn]
    simp only [Finset.prod_boole, Finset.mem_univ, true_implies, hy]
    have hiff : (∀ n : Fin M, (∀ hn : n.val + 1 < M, s ⟨n.val + 1, hn⟩ = s n) ∧
        x (site n 1) = 0) ↔ (∀ n, s n = s 0) ∧ ∀ n : Fin M, x (site n 1) = 0 := by
      rw [forall_and, forall_succ_eq_iff]
    simp only [hiff]
    by_cases hc1 : ∀ n, s n = s 0 <;> by_cases hc2 : ∀ n : Fin M, x (site n 1) = 0 <;>
      simp only [hs] at hc1 ⊢ <;> simp [hc1, hc2]
  · rw [ite_eq_right hmeas, zero_mul]
    push Not at hmeas
    obtain ⟨n, -, hn⟩ := hmeas
    rw [Finset.prod_eq_zero (Finset.mem_univ n) (ite_eq_right hn), mul_zero]

/-- **GHZ-type states in constant depth with measurements.** For every `M ≥ 1`, every finite
abelian group `β` of basis labels, such as `ℤ_b` for qudits of dimension `b ≥ 1`, and every
nonzero `α`, the GHZ-type state `|χ_M⟩ = ∑ᵢ αᵢ |i⟩^{⊗M}`, with one ancilla per system qudit left
in `|0⟩`, is converted from a nonzero product vector on the ring of `2M` sites by one round of
measurements after a unitary circuit of depth `2`.

Source: arXiv:2307.01696, paragraph "Long-range MPS using measurements" ("the creation of
GHZ-like states `|χ_M⟩ = ∑_{i=1}^b αᵢ |i⟩^{⊗M}` becomes possible in only constant depth");
arXiv:2103.13367, Example 1 (`|0⟩ → |GHZ⟩` by `QCcc₂`), for qudits. -/
theorem isOneRoundConversion_withZeroAncillas_ghzState (α : β → ℂ) (hα : α ≠ 0) :
    IsOneRoundConversion (Geometry.ring (M * 2)) 2 0 (fun σ ↦ ∏ s, ghzInitial α s (σ s))
      (withZeroAncillas (ghzState α)) := by
  refine ⟨?_, ghzCircuit.op, 1, ghzMeasured, ghzCorrection,
    ⟨ghzCircuit, depth_ghzCircuit_le, rfl⟩, IsUnitaryCircuit.one _ _ 0,
    fun _ _ ↦ Equiv.Perm.permMatrix_mem_unitaryGroup _, fun m ↦ ⟨1, ?_⟩⟩
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hα
    intro h0
    have := congrFun h0 (fun j ↦ if j = site 0 0 then i else 0)
    rw [prod_ghzInitial] at this
    have hne : ∀ n : Fin M, site n 1 ≠ site 0 0 := fun n h ↦
      absurd (site_inj h).2 (by decide)
    exact hi (by simpa [hne] using this)
  · rw [Matrix.one_mul, one_smul]
    exact ghzProtocol_output α m

end Ring

end Protocol

end QuantumCircuit
