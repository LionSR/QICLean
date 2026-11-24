/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Frame
import QICLean.ManyBody.Sites.Block

/-!
# Ownership sheets on a finite set of sites

A sheet on a finite set `ι` of sites is the space `⊗_{x ∈ ι} ℂ^q` with an owner assigned to
each site. Held by the parties, it is the system whose basis at a party `p` is the configurations
of the sites owned by `p` (`Sheet.system`, the blocked system of the owner map); its
configurations are those of the sites (`ManyBody.blockConfigEquiv`), and a vector `Ω` of
`ℂ^{ι → Fin q}` is read on the sheet along them (`Sheet.refVec`). A sheet carries no encoded
holes. Two sheets held at once form the product system, whose configurations are pairs of
configurations of the sites (`Sheet.twoConfigEquiv`), and on which the vector `Ω` of each sheet
gives the product vector `Ω ⊗ Ω` (`Sheet.prodVec_refVec`).

The file also defines the changes of owner of a birth or a death and the two sheets after an
exchange inside a region, with the sets of sites of the two lemmas.

## Main definitions

* `QuantumCircuit.Party.Sheet`, `QuantumCircuit.Party.Sheet.system`,
  `QuantumCircuit.Party.Sheet.refVec`, `QuantumCircuit.Party.Sheet.twoConfigEquiv`.
* `QuantumCircuit.Party.Sheet.changeOwner`, `QuantumCircuit.Party.Sheet.birthEnv`: the sheet
  after handing a set `T` of sites to another party, and the set `E` of sites not owned by `P∘`.
* `QuantumCircuit.Party.Sheet.swapIn`, `QuantumCircuit.Party.Sheet.exchangeEnv`: the two-sheet
  exchange inside a region `Y`, and the set `Z` of sites whose two owners are not both `P∘`.
  The exchange is stated for any set `Z` containing it, with `T = Z ∩ Y`, `E = Z ∖ Y` and
  `A = Y ∖ Z`.

## Main results

* `QuantumCircuit.Party.Sheet.prodVec_refVec`, `QuantumCircuit.Party.Sheet.norm_refVec`.
* `QuantumCircuit.Party.Sheet.changeOwner_birth_owners`,
  `QuantumCircuit.Party.Sheet.owner_eq_of_notMem_exchangeEnv`,
  `QuantumCircuit.Party.Sheet.swapIn_owner_eq_of_notMem`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 13–18 (sheets) and
  94–96 (canonical site coordinates with the owners of the registers specified separately);
  Lemma 6.5 `lem:birth`, lines 396–447; Lemma 6.6 `lem:exchange`, lines 460–561.
* One-dimensional note, `part2b_mps_protocol.tex`, lines 67–68 (a sheet and its reference
  vector), Lemma `lem:birth`, lines 70–94, Lemma `lem:exchange`, lines 112–155, and the remark
  of lines 165–171: on a line no trijunctions occur and no encoded holes are needed.
-/
open Matrix ManyBody

namespace QuantumCircuit.Party

/-! ### Sheets -/

/-- **A sheet.** An owner for each site of a finite set `ι`; the raw register `ℂ^q` of a site is
held by its owner. Source: `05-frames.tex`, lines 13–18; one-dimensional note,
`part2b_mps_protocol.tex`, lines 67–68. -/
@[ext]
structure Sheet (ι P : Type) where
  /-- The owner of each site. -/
  owner : ι → P

namespace Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [DecidableEq P] (q : ℕ) (S : Sheet ι P)

/-- **The system of a sheet**: at every party, the configurations of the sites it owns, one
basis vector `|c⟩` of `ℂ^q` per site. Its configurations are those of the sites
(`ManyBody.blockConfigEquiv`), the canonical coordinates of the sheet. Source: `05-frames.tex`,
lines 13–18 and 94–96. -/
abbrev system : P → Type := blockSystem S.owner fun _ : ι ↦ Fin q

variable {q}

/-- The vector `Ω` of `ℂ^{ι → Fin q}` read on the sheet, along its canonical coordinates.
Source: `05-frames.tex`, lines 15–18; one-dimensional note, `part2b_mps_protocol.tex`,
line 68. -/
noncomputable def refVec [Fintype P] (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    EuclideanSpace ℂ (Config (S.system q)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (blockConfigEquiv S.owner fun _ ↦ Fin q).symm Ω

/-- The coordinate of the vector read on the sheet at a configuration of the sheet. -/
@[simp] theorem refVec_apply [Fintype P] (Ω : EuclideanSpace ℂ (ι → Fin q))
    (z : Config (S.system q)) :
    S.refVec Ω z = Ω (blockConfigEquiv S.owner (fun _ ↦ Fin q) z) := by
  simp [refVec, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

/-- Reading a vector on the sheet keeps its norm. -/
theorem norm_refVec [Fintype P] (Ω : EuclideanSpace ℂ (ι → Fin q)) : ‖S.refVec Ω‖ = ‖Ω‖ :=
  LinearIsometryEquiv.norm_map _ _

/-- A vector of norm at most one read on the sheet has norm at most one. -/
theorem norm_refVec_le [Fintype P] {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1) :
    ‖S.refVec Ω‖ ≤ 1 :=
  (S.norm_refVec Ω).trans_le hΩ

variable (q)

/-- **Two sheets in canonical coordinates.** The configurations of the product system of two
sheets are pairs of configurations of the sites, those of the first sheet first. -/
def twoConfigEquiv (S₁ S₂ : Sheet ι P) :
    Config (fun p ↦ S₁.system q p × S₂.system q p) ≃ (ι → Fin q) × (ι → Fin q) :=
  (Equiv.arrowProdEquivProdArrow P (S₁.system q) (S₂.system q)).trans
    ((blockConfigEquiv S₁.owner _).prodCongr (blockConfigEquiv S₂.owner _))

omit [DecidableEq ι] in
/-- The canonical coordinates of two sheets, site by site. -/
@[simp] theorem twoConfigEquiv_apply (S₁ S₂ : Sheet ι P)
    (z : Config fun p ↦ S₁.system q p × S₂.system q p) :
    twoConfigEquiv q S₁ S₂ z = (fun x ↦ (z (S₁.owner x)).1 ⟨x, by simp⟩,
      fun x ↦ (z (S₂.owner x)).2 ⟨x, by simp⟩) :=
  rfl

variable {q}

/-- **The reference vector of two sheets is `Ω ⊗ Ω`** in their canonical coordinates. -/
theorem prodVec_refVec [Fintype P] (S₁ S₂ : Sheet ι P) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    prodVec (S₁.refVec Ω) (S₂.refVec Ω) =
      LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (twoConfigEquiv q S₁ S₂).symm
        (EuclideanSpace.vecKron Ω Ω) := by
  ext z
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    EuclideanSpace.vecKron, twoConfigEquiv]

/-! ### Change of owner -/

/-- The sheet obtained by handing the sites of `T` to `Q`. Source: Lemma 6.5, `05-frames.tex`,
lines 397–399; one-dimensional note, Lemma `lem:birth`, `part2b_mps_protocol.tex`,
lines 70–80. -/
def changeOwner (T : Finset ι) (Q : P) : Sheet ι P :=
  ⟨fun x ↦ if x ∈ T then Q else S.owner x⟩

/-- The set `E = {x : the owner of x is not P∘}` of Lemma `lem:birth`. On a sheet the set
`E = {x : owner x ≠ P∘} ∪ H⁺(F)` of Lemma 6.5 has no hole part. Source: `05-frames.tex`,
lines 401–405; one-dimensional note, `part2b_mps_protocol.tex`, lines 71–73. -/
def birthEnv (P₀ : P) : Finset ι := Finset.univ.filter fun x ↦ S.owner x ≠ P₀

section Birth

variable {T : Finset ι} {P₀ Q : P}

omit [DecidableEq ι] in
/-- A site lies in `E` when it is not owned by `P∘`. -/
theorem mem_birthEnv {x : ι} : x ∈ S.birthEnv P₀ ↔ S.owner x ≠ P₀ := by
  simp [birthEnv]

omit [DecidableEq ι] in
/-- `T` and `E` are disjoint when `T` is owned by `P∘`. -/
theorem disjoint_birthEnv (hTP : ∀ x ∈ T, S.owner x = P₀) : Disjoint T (S.birthEnv P₀) := by
  rw [Finset.disjoint_left]
  intro x hxT hxE
  exact (S.mem_birthEnv).mp hxE (hTP x hxT)

omit [Fintype ι] [DecidableEq P] in
/-- Handing to `P∘` sites that `P∘` already owns leaves the sheet unchanged. -/
theorem changeOwner_eq_self (hTP : ∀ x ∈ T, S.owner x = P₀) : S.changeOwner T P₀ = S := by
  cases S
  simp only [changeOwner, Sheet.mk.injEq]
  funext v
  by_cases h : v ∈ T
  · simpa only [h, ite_true] using (hTP v h).symm
  · simp only [h, ite_false]

/-- The ownership facts of a birth: when `T` is owned by `P∘`, the sites outside `T ∪ E` are owned
by `P∘` before and after `T` is handed to `Q∘`, the sites of `T` are owned by `Q∘` afterwards,
and the owners on `E` are unchanged. -/
theorem changeOwner_birth_owners (hTP : ∀ x ∈ T, S.owner x = P₀) :
    (∀ x ∈ (T ∪ S.birthEnv P₀)ᶜ, S.owner x = P₀) ∧
      (∀ x ∈ T, (S.changeOwner T Q).owner x = Q) ∧
      (∀ x ∈ (T ∪ S.birthEnv P₀)ᶜ, (S.changeOwner T Q).owner x = P₀) ∧
      ∀ x ∈ S.birthEnv P₀, S.owner x = (S.changeOwner T Q).owner x := by
  have hB : ∀ x ∈ (T ∪ S.birthEnv P₀)ᶜ, S.owner x = P₀ := fun x hx ↦ by
    by_contra h
    exact Finset.mem_compl.mp hx (Finset.mem_union_right _ ((S.mem_birthEnv).mpr h))
  refine ⟨hB, fun x hx ↦ by simp [changeOwner, hx], fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hxT : x ∉ T := fun h ↦ Finset.mem_compl.mp hx (Finset.mem_union_left _ h)
    simpa [changeOwner, hxT] using hB x hx
  · have hxT : x ∉ T := fun hT ↦ Finset.disjoint_left.mp (S.disjoint_birthEnv hTP) hT hx
    simp [changeOwner, hxT]

end Birth

/-! ### Two-sheet exchange -/

/-- The sheet `S₁` after an exchange inside `Y` with `S₂`: inside `Y` it carries the owners of
`S₂`. Source: Lemma 6.6, `05-frames.tex`, lines 461–464; one-dimensional note, Lemma
`lem:exchange`, `part2b_mps_protocol.tex`, lines 113–115. -/
def swapIn (S₁ S₂ : Sheet ι P) (Y : Finset ι) : Sheet ι P :=
  ⟨fun x ↦ if x ∈ Y then S₂.owner x else S₁.owner x⟩

/-- The set `{x : the two owners of x are not both P∘}` of Lemma `lem:exchange`. The set `Z` of
Lemma 6.6 adds to it the hole parts `H⁺(F₁) ∪ H⁺(F₂)`, which are empty on sheets; the exchange
is therefore stated for every set `Z` containing this one. Source: `05-frames.tex`,
lines 466–470; one-dimensional note, `part2b_mps_protocol.tex`, line 118. -/
def exchangeEnv (S₁ S₂ : Sheet ι P) (P₀ : P) : Finset ι :=
  Finset.univ.filter fun x ↦ ¬(S₁.owner x = P₀ ∧ S₂.owner x = P₀)

variable (S₁ S₂ : Sheet ι P) (Y : Finset ι) (P₀ : P)

omit [DecidableEq ι] in
/-- A site lies in `Z` when its two owners are not both `P∘`. -/
theorem mem_exchangeEnv {x : ι} :
    x ∈ exchangeEnv S₁ S₂ P₀ ↔ ¬(S₁.owner x = P₀ ∧ S₂.owner x = P₀) := by
  simp [exchangeEnv]

omit [DecidableEq ι] in
/-- Both owners of a site outside `exchangeEnv S₁ S₂ P₀` are `P∘`. -/
theorem owner_eq_of_notMem_exchangeEnv {x : ι} (hx : x ∉ exchangeEnv S₁ S₂ P₀) :
    S₁.owner x = P₀ ∧ S₂.owner x = P₀ :=
  not_not.mp ((mem_exchangeEnv S₁ S₂ P₀).not.mp hx)

/-- `A = Y ∖ Z` lies in the complement of `T ∪ E = (Z ∩ Y) ∪ (Z ∖ Y)`. -/
theorem sdiff_subset_compl_inter_union_sdiff (Z : Finset ι) : Y \ Z ⊆ (Z ∩ Y ∪ Z \ Y)ᶜ := by
  intro x hx
  simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hx ⊢
  tauto

omit [Fintype ι] [DecidableEq P] in
/-- Let `Z` contain every site whose two owners are not both `P∘`. Every register outside
`T ∪ E = (Z ∩ Y) ∪ (Z ∖ Y)` is held by `P∘` on both sheets after the exchange. Source:
`05-frames.tex`, lines 500–501; one-dimensional note, `part2b_mps_protocol.tex`,
lines 131–132. -/
theorem swapIn_owner_eq_of_notMem {Z : Finset ι}
    (hZ : ∀ x ∉ Z, S₁.owner x = P₀ ∧ S₂.owner x = P₀) {x : ι} (hx : x ∉ Z ∩ Y ∪ Z \ Y) :
    (swapIn S₁ S₂ Y).owner x = P₀ ∧ (swapIn S₂ S₁ Y).owner x = P₀ := by
  have hxZ : x ∉ Z := by
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hx
    tauto
  obtain ⟨h₁, h₂⟩ := hZ x hxZ
  simp only [swapIn]
  split_ifs <;> exact ⟨by assumption, by assumption⟩

end Sheet

end QuantumCircuit.Party
