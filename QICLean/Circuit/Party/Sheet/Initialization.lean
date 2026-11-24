/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.FromWord
import QICLean.Circuit.Party.Sheet.Stack

/-!
# The initial reference vector of sheets held by one party each

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every copy of `Ω`, the main
copy at the root included, is initialized privately at its future owner, so the initial vector is
a pure product across the parties (`06-geometry.tex`, lines 658–667). For sheets of an arbitrary
type, each sheet `F` with a system `sys F` and a reference vector `ref F`, this is the following:
if every sheet is held by one party (the basis of every other party is a single point), the
reference vector of the sheets is a product vector across the parties, the factor of a party
being the product of the reference vectors of the sheets it holds
(`exists_productVector_eq_framesVec`); for sheets read from a unit vector `Ω`, every factor is a
unit vector (`Sheet.exists_productVector_eq_framesVec`). This is the product input of Theorem 5.2
(`04-compression.tex`, lines 137–139). The same vector is prepared from the system with one basis
vector at every party by one local operation at every party, an original circuit without
nonprivate gate (`exists_originalCircuit_framesVec`, `Sheet.exists_originalCircuit_framesVec`).

## Main definitions

* `QuantumCircuit.Party.framesVec`: the reference vector of a list of sheets.

## Main results

* `QuantumCircuit.Party.norm_framesVec`, `QuantumCircuit.Party.exists_productVector_eq_framesVec`,
  `QuantumCircuit.Party.Sheet.exists_productVector_eq_framesVec`.
* `QuantumCircuit.Party.exists_originalCircuit_framesVec`,
  `QuantumCircuit.Party.Sheet.exists_originalCircuit_framesVec`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 21–23 and 658–667; product inputs of Theorem 5.2,
  `04-compression.tex`, lines 137–139.
* One-dimensional note, `part2b_mps_protocol.tex`, lines 67–68.
-/
open Matrix ManyBody

namespace QuantumCircuit.Party

variable {κ : Type*} {P : Type} [DecidableEq P]

/-! ### Sheets held by one party each -/

section Initial

variable [Fintype P] {sys : κ → P → Type} [∀ F p, Fintype (sys F p)]
  (ref : ∀ F, EuclideanSpace ℂ (Config (sys F)))

/-- The reference vector of a list of sheets, with the trivial idle system. -/
noncomputable def framesVec (Fs : List κ) :
    EuclideanSpace ℂ (Config (stackSystem sys Fs fun _ ↦ Unit)) :=
  stackVec ref Fs (EuclideanSpace.single (fun _ ↦ ()) 1)

/-- The norm of the reference vector of a list of sheets is the product of their norms. -/
theorem norm_framesVec (Fs : List κ) : ‖framesVec ref Fs‖ = (Fs.map fun F ↦ ‖ref F‖).prod := by
  rw [framesVec, norm_stackVec]
  simp

open Classical in
/-- The factor at the party `p` of the reference vector of a sheet held by `holder F`: the
vector itself, read on the basis of `p`, if `p` holds the sheet, and the vector `1` of the
one-point basis otherwise. -/
private noncomputable def partyFactor (holder : κ → P) (F : κ) (p : P) : sys F p → ℂ :=
  if p = holder F then fun a ↦ ∑ z : Config (sys F), if z p = a then ref F z else 0
  else fun _ ↦ 1

omit [DecidableEq P] [Fintype P] [∀ F p, Fintype (sys F p)] in
/-- A configuration of a sheet held by one party is determined by its value at that party. -/
private theorem eq_of_apply_holder_eq [∀ F p, Fintype (sys F p)] {holder : κ → P} {F : κ}
    (hown : ∀ p ≠ holder F, Fintype.card (sys F p) = 1) {z z' : Config (sys F)}
    (h : z (holder F) = z' (holder F)) : z = z' := by
  funext p
  by_cases hp : p = holder F
  · subst hp
    exact h
  · exact (Fintype.card_le_one_iff_subsingleton.mp (hown p hp).le).elim _ _

/-- The product of the party factors of a sheet held by one party is its reference vector. -/
private theorem prod_partyFactor {holder : κ → P} {F : κ}
    (hown : ∀ p ≠ holder F, Fintype.card (sys F p) = 1) (z : Config (sys F)) :
    ∏ p, partyFactor ref holder F p (z p) = ref F z := by
  rw [Fintype.prod_eq_single (holder F) fun p hp ↦ by simp [partyFactor, hp]]
  simp only [partyFactor, ite_true]
  rw [Fintype.sum_eq_single z fun z' hz' ↦ ite_eq_right fun h ↦ hz' (eq_of_apply_holder_eq hown h),
    ite_eq_left rfl]

/-- The party factor of a sheet held by one party has the norm of the reference vector at the
holder and norm one elsewhere. -/
private theorem norm_partyFactor {holder : κ → P} {F : κ}
    (hown : ∀ p ≠ holder F, Fintype.card (sys F p) = 1) (p : P) :
    ‖(WithLp.toLp 2 (partyFactor ref holder F p) : EuclideanSpace ℂ (sys F p))‖ =
      if p = holder F then ‖ref F‖ else 1 := by
  by_cases hp : p = holder F
  · subst hp
    rw [ite_eq_left rfl]
    have hbij : Function.Bijective fun z : Config (sys F) ↦ z (holder F) := by
      refine ⟨fun z z' h ↦ eq_of_apply_holder_eq hown h, fun a ↦ ?_⟩
      classical
      refine ⟨fun p ↦ if h : p = holder F then h ▸ a else
        Classical.choice (Fintype.card_pos_iff.mp ((hown p h).symm ▸ Nat.one_pos)), ?_⟩
      simp
    set e := Equiv.ofBijective _ hbij
    have hf : partyFactor ref holder F (holder F) = fun a ↦ ref F (e.symm a) := by
      funext a
      simp only [partyFactor, ite_true]
      rw [Fintype.sum_eq_single (e.symm a) fun z hz ↦ ite_eq_right fun h ↦ hz
        (e.injective (h.trans (e.apply_symm_apply a).symm))]
      exact ite_eq_left (e.apply_symm_apply a)
    rw [hf, ← EuclideanSpace.norm_toLp_comp_equiv e.symm (fun z ↦ ref F z)]
    rfl
  · rw [ite_eq_right hp, EuclideanSpace.norm_eq]
    simp [partyFactor, hp, hown p hp]

/-- **Sheets held by one party each.** If every sheet `F` of the list `Fs` is held entirely by
the party `holder F` (the basis of every other party is a single point), the reference vector
of the sheets is a product vector across the parties, the factor of a party `p` being the
product of the reference vectors of the sheets it holds. So the initial vector of the protocol
is a product initialization across parties, with no nonprivate gate.

Source: `06-geometry.tex`, lines 21–23 and 658–667 ("Initialize all
required copies of `Ω` privately at their future owners, including the main copy at the root.
This is a pure product initialization across parties"), and the product inputs of Theorem 5.2,
`04-compression.tex`, lines 137–139. -/
theorem exists_productVector_eq_framesVec (holder : κ → P) :
    (Fs : List κ) → (∀ F ∈ Fs, ∀ p ≠ holder F, Fintype.card (sys F p) = 1) →
      ∃ φ : ∀ p, EuclideanSpace ℂ (stackSystem sys Fs (fun _ ↦ Unit) p),
        (∀ p, ‖φ p‖ = ((Fs.filter fun F ↦ holder F = p).map fun F ↦ ‖ref F‖).prod) ∧
        (WithLp.toLp 2 (productVector fun p x ↦ φ p x) :
          EuclideanSpace ℂ (Config (stackSystem sys Fs fun _ ↦ Unit))) = framesVec ref Fs
  | [], _ => ⟨fun _ ↦ EuclideanSpace.single () 1, fun _ ↦ by simp, by
      ext z
      simp [productVector, framesVec, stackVec]⟩
  | F :: Fs, hown => by
    obtain ⟨φ, hφn, hφ⟩ := exists_productVector_eq_framesVec holder Fs
      fun G hG ↦ hown G (List.mem_cons_of_mem F hG)
    have hF := hown F List.mem_cons_self
    refine ⟨fun p ↦ EuclideanSpace.vecKron (WithLp.toLp 2 (partyFactor ref holder F p)) (φ p),
      fun p ↦ ?_, ?_⟩
    · rw [EuclideanSpace.norm_vecKron, norm_partyFactor ref hF, hφn, List.filter_cons]
      by_cases hp : p = holder F
      · simp [hp]
      · simp [hp, Ne.symm hp]
    · ext z
      have hz := congrArg (fun v : EuclideanSpace ℂ _ ↦ v fun p ↦ (z p).2) hφ
      simp only at hz
      simp only [PiLp.toLp_apply, productVector, EuclideanSpace.vecKron, Finset.prod_mul_distrib]
      rw [show (∏ p, φ p (z p).2) = productVector (fun p x ↦ φ p x) (fun p ↦ (z p).2) from rfl,
        hz, prod_partyFactor ref hF]
      rfl

end Initial

/-- The reference vector of every sheet of a list, held by one party each and read from a unit
vector `Ω`, is a product of unit vectors across the parties: the initial step of the protocol.
Source: `06-geometry.tex`, lines 21–23 and 658–667; one-dimensional note,
`part2b_mps_protocol.tex`, lines 67–68. -/
theorem Sheet.exists_productVector_eq_framesVec {ι : Type} [Fintype ι] [DecidableEq ι]
    [Fintype P] {q : ℕ} {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    (Ss : List (Sheet ι P)) (holder : Sheet ι P → P)
    (hown : ∀ S ∈ Ss, ∀ x, S.owner x = holder S) :
    ∃ φ : ∀ p, EuclideanSpace ℂ (stackSystem (Sheet.system q) Ss (fun _ ↦ Unit) p),
      (∀ p, ‖φ p‖ = 1) ∧
      (WithLp.toLp 2 (productVector fun p x ↦ WithLp.ofLp (φ p) x) :
        EuclideanSpace ℂ (Config (stackSystem (Sheet.system q) Ss fun _ ↦ Unit))) =
        framesVec (fun S ↦ S.refVec Ω) Ss := by
  obtain ⟨φ, hφn, hφ⟩ := QuantumCircuit.Party.exists_productVector_eq_framesVec
    (fun S : Sheet ι P ↦ S.refVec Ω) holder Ss
    fun S hS p hp ↦ by
      simp only [Fintype.card_pi, Finset.prod_const, Fintype.card_fin]
      rw [Finset.card_univ, Fintype.card_coe,
        show blockPreimage S.owner {p} = ∅ from Finset.filter_eq_empty_iff.mpr fun x _ ↦ by
          simpa using fun h ↦ hp (h.symm.trans (hown S hS x)), Finset.card_empty, pow_zero]
  refine ⟨φ, fun p ↦ ?_, hφ⟩
  rw [hφn]
  exact List.prod_eq_one fun r hr ↦ by
    obtain ⟨S, -, rfl⟩ := List.mem_map.mp hr
    rw [S.norm_refVec, hΩ]

/-! ### The initial vector prepared by local operations -/

section Preparation

variable [Fintype P] {X : P → Type} [∀ p, Fintype (X p)]

/-- The product preparation maps the vector of the system with one basis vector at every party
to the product vector. -/
private theorem toEuclideanLin_op_prepareProduct [∀ p, DecidableEq (X p)]
    (φ : ∀ p, EuclideanSpace ℂ (X p)) :
    toEuclideanLin (Word.prepareProduct φ).op (EuclideanSpace.single (fun _ ↦ ()) 1) =
      WithLp.toLp 2 (productVector fun p x ↦ φ p x) := by
  have h : WithLp.ofLp (EuclideanSpace.single (fun _ : P ↦ ()) (1 : ℂ)) = fun _ ↦ 1 := by
    funext z
    rw [show z = fun _ ↦ () from Subsingleton.elim _ _]
    simp
  rw [← Word.op_prepareProduct_mulVec, ← h]
  rfl

/-- A product of unit vectors across the parties, prepared by one local operation at every party
from the system with one basis vector at every party, as an original circuit without nonprivate
gate. Source: `04-compression.tex`, lines 137–139. -/
private theorem exists_originalCircuit_productVector (φ : ∀ p, EuclideanSpace ℂ (X p))
    (hφ : ∀ p, ‖φ p‖ = 1) :
    ∃ c : OriginalCircuit (fun _ : P ↦ Unit) X, c.nonprivateCount = 0 ∧
      toEuclideanLin c.op (EuclideanSpace.single (fun _ ↦ ()) 1) =
        WithLp.toLp 2 (productVector fun p x ↦ φ p x) := by
  classical
  exact ⟨(Word.prepareProduct φ).toOriginalCircuit (Word.isAllowed_prepareProduct φ hφ),
    Word.nonprivateCount_toOriginalCircuit_of_sourceCount_eq_zero _ _ rfl, by
      rw [Word.op_toOriginalCircuit, toEuclideanLin_op_prepareProduct]⟩

end Preparation

/-- **The initial vector prepared by local operations.** If every sheet `F` of the list `Fs` is
held entirely by the party `holder F` and its reference vector has norm one, one local operation
at every party prepares the reference vector of the sheets from the system with one basis vector
at every party: an original circuit without nonprivate gate whose operator maps that basis vector
to the reference vector of the sheets. Source: `06-geometry.tex`, lines 21–23 and 658–667, and
`04-compression.tex`, lines 137–139. -/
theorem exists_originalCircuit_framesVec [Fintype P] {sys : κ → P → Type}
    [∀ F p, Fintype (sys F p)] (ref : ∀ F, EuclideanSpace ℂ (Config (sys F))) (holder : κ → P)
    {Fs : List κ}
    (hown : ∀ F ∈ Fs, ∀ p ≠ holder F, Fintype.card (sys F p) = 1)
    (href : ∀ F ∈ Fs, ‖ref F‖ = 1) :
    ∃ c : OriginalCircuit (fun _ : P ↦ Unit) (stackSystem sys Fs fun _ ↦ Unit),
      c.nonprivateCount = 0 ∧
        toEuclideanLin c.op (EuclideanSpace.single (fun _ ↦ ()) 1) = framesVec ref Fs := by
  obtain ⟨φ, hφn, hφ⟩ := exists_productVector_eq_framesVec ref holder Fs hown
  obtain ⟨c, hc0, hc⟩ := exists_originalCircuit_productVector φ fun p ↦ by
    rw [hφn]
    exact List.prod_eq_one fun r hr ↦ by
      obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hr
      exact href F (List.mem_filter.mp hF).1
  exact ⟨c, hc0, hc.trans hφ⟩

/-- **The initial step of the protocol prepared by local operations.** For sheets held by one
party each and read from a unit vector `Ω`, one local operation at every party prepares the
reference vector of the sheets from the system with one basis vector at every party, by an
original circuit without nonprivate gate. Source: `06-geometry.tex`, lines 21–23 and 658–667;
one-dimensional note, `part2b_mps_protocol.tex`, lines 67–68. -/
theorem Sheet.exists_originalCircuit_framesVec {ι : Type} [Fintype ι] [DecidableEq ι]
    [Fintype P] {q : ℕ} {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    (Ss : List (Sheet ι P)) (holder : Sheet ι P → P)
    (hown : ∀ S ∈ Ss, ∀ x, S.owner x = holder S) :
    ∃ c : OriginalCircuit (fun _ : P ↦ Unit) (stackSystem (Sheet.system q) Ss fun _ ↦ Unit),
      c.nonprivateCount = 0 ∧
        toEuclideanLin c.op (EuclideanSpace.single (fun _ ↦ ()) 1) =
          framesVec (fun S ↦ S.refVec Ω) Ss := by
  obtain ⟨φ, hφn, hφ⟩ := Sheet.exists_productVector_eq_framesVec hΩ Ss holder hown
  obtain ⟨c, hc0, hc⟩ := exists_originalCircuit_productVector φ hφn
  exact ⟨c, hc0, hc.trans hφ⟩

end QuantumCircuit.Party
