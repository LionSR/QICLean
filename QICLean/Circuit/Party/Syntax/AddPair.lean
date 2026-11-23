/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.Config
import QICLean.Analysis.Norm.VectorPreparation

/-!
# Fresh factors in front of the bases of two parties

The pair sources of the party calculus prepare a vector on fresh factors of two parties, and the
pair effects remove such factors. This module provides the basis types and matrices involved.
The system `addPair X hpq α β` is `X` with the fresh first factor `α` at `p` and `β` at `q ≠ p`;
its configurations are pairs of a configuration of the fresh factors and a configuration of `X`
(`addPairConfigEquiv`), and at one party its basis is the fresh factor there times the old basis
(`addPairSiteEquiv`). The preparation of a vector on a fresh factor is `Matrix.prepMatrix`.

## Main definitions

* `QuantumCircuit.Party.addPair`, `QuantumCircuit.Party.addPairLeft`,
  `QuantumCircuit.Party.addPairRight`, `QuantumCircuit.Party.addPairConfigEquiv`.
* `QuantumCircuit.Party.pairFactor`, `QuantumCircuit.Party.addPairSiteEquiv` — the fresh factors
  alone, and the basis of one party.

## Main results

* `QuantumCircuit.Party.addPairConfigEquiv_apply_fst`,
  `QuantumCircuit.Party.addPairConfigEquiv_symm_apply_left` and their companions — the two
  directions of `addPairConfigEquiv`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35 (pair
  sources and pair effects).
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### The canonical output: fresh factors in front -/

/-- The system `X` with the fresh first factor `α` at `p` and `β` at `q`. -/
def addPair (X : P → Type) {p q : P} (_hpq : p ≠ q) (α β : Type) : P → Type :=
  fun s ↦ if s = p then α × X s else if s = q then β × X s else X s

section addPair

variable {X : P → Type} {p q : P} (hpq : p ≠ q) (α β : Type)

/-- The bases of `addPair` are finite. -/
instance [∀ s, Fintype (X s)] [Fintype α] [Fintype β] (s : P) :
    Fintype (addPair X hpq α β s) := by
  unfold addPair; split_ifs <;> infer_instance

/-- The bases of `addPair` have decidable equality. -/
instance [∀ s, DecidableEq (X s)] [DecidableEq α] [DecidableEq β] (s : P) :
    DecidableEq (addPair X hpq α β s) := by
  unfold addPair; split_ifs <;> infer_instance

/-- The basis of `p` in `addPair`: the fresh factor in front of the old basis. -/
def addPairLeft : addPair X hpq α β p ≃ α × X p :=
  Equiv.cast (by simp [addPair])

/-- The basis of `q` in `addPair`: the fresh factor in front of the old basis. -/
def addPairRight : addPair X hpq α β q ≃ β × X q :=
  Equiv.cast (by simp [addPair, hpq.symm])

/-- Away from `p` and `q`, `addPair` keeps the basis of `X`. -/
theorem addPair_of_ne {s : P} (hp : s ≠ p) (hq : s ≠ q) : addPair X hpq α β s = X s := by
  simp [addPair, hp, hq]

/-- Outside the cell `{p, q}`, `addPair` keeps the basis of `X`, in the form the placements
take. -/
theorem addPair_eq_of_notMem : ∀ s ∉ ({p, q} : Finset P), addPair X hpq α β s = X s := by
  intro s hs
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
  exact addPair_of_ne hpq α β hs.1 hs.2

/-- A configuration of `addPair X hpq α β` is a configuration of the two fresh factors and a
configuration of `X`. -/
def addPairConfigEquiv : Config (addPair X hpq α β) ≃ (α × β) × Config X where
  toFun z :=
    (((addPairLeft hpq α β (z p)).1, (addPairRight hpq α β (z q)).1), fun s ↦
      if hp : s = p then cast (congrArg X hp.symm) (addPairLeft hpq α β (z p)).2
      else if hq : s = q then cast (congrArg X hq.symm) (addPairRight hpq α β (z q)).2
      else cast (addPair_of_ne hpq α β hp hq) (z s))
  invFun a s :=
    if hp : s = p then cast (by subst hp; rfl) ((addPairLeft hpq α β).symm (a.1.1, a.2 p))
    else if hq : s = q then cast (by subst hq; rfl) ((addPairRight hpq α β).symm (a.1.2, a.2 q))
    else cast (addPair_of_ne hpq α β hp hq).symm (a.2 s)
  left_inv z := by
    funext s
    by_cases hp : s = p
    · subst hp
      simp [addPairLeft, Equiv.symm_apply_eq]
    · by_cases hq : s = q
      · subst hq
        simp [addPairRight, hp, Equiv.symm_apply_eq]
      · simp [hp, hq]
  right_inv a := by
    obtain ⟨⟨a, b⟩, x⟩ := a
    refine Prod.ext (Prod.ext ?_ ?_) (funext fun s ↦ ?_)
    · simp [addPairLeft]
    · simp [addPairRight, hpq.symm]
    · by_cases hp : s = p
      · subst hp
        simp [addPairLeft]
      · by_cases hq : s = q
        · subst hq
          simp [addPairRight, hp]
        · simp [hp, hq]

/-- The fresh part of a configuration of `addPair`. -/
@[simp] theorem addPairConfigEquiv_apply_fst (z : Config (addPair X hpq α β)) :
    (addPairConfigEquiv hpq α β z).1 =
      ((addPairLeft hpq α β (z p)).1, (addPairRight hpq α β (z q)).1) :=
  rfl

/-- The old part of a configuration of `addPair`, at `p`. -/
@[simp] theorem addPairConfigEquiv_apply_snd_left (z : Config (addPair X hpq α β)) :
    (addPairConfigEquiv hpq α β z).2 p = (addPairLeft hpq α β (z p)).2 := by
  simp [addPairConfigEquiv]

/-- The old part of a configuration of `addPair`, at `q`. -/
@[simp] theorem addPairConfigEquiv_apply_snd_right (z : Config (addPair X hpq α β)) :
    (addPairConfigEquiv hpq α β z).2 q = (addPairRight hpq α β (z q)).2 := by
  simp [addPairConfigEquiv, hpq.symm]

/-- The old part of a configuration of `addPair`, away from `p` and `q`. -/
theorem addPairConfigEquiv_apply_snd_of_ne (z : Config (addPair X hpq α β)) {s : P}
    (hp : s ≠ p) (hq : s ≠ q) :
    (addPairConfigEquiv hpq α β z).2 s = cast (addPair_of_ne hpq α β hp hq) (z s) := by
  simp [addPairConfigEquiv, hp, hq]

/-- The configuration of `addPair` of a pair, at `p`. -/
@[simp] theorem addPairConfigEquiv_symm_apply_left (a : (α × β) × Config X) :
    (addPairConfigEquiv hpq α β).symm a p = (addPairLeft hpq α β).symm (a.1.1, a.2 p) := by
  simp [addPairConfigEquiv]

/-- The configuration of `addPair` of a pair, at `q`. -/
@[simp] theorem addPairConfigEquiv_symm_apply_right (a : (α × β) × Config X) :
    (addPairConfigEquiv hpq α β).symm a q = (addPairRight hpq α β).symm (a.1.2, a.2 q) := by
  simp [addPairConfigEquiv, hpq.symm]

/-- The configuration of `addPair` of a pair, away from `p` and `q`. -/
theorem addPairConfigEquiv_symm_apply_of_ne (a : (α × β) × Config X) {s : P} (hp : s ≠ p)
    (hq : s ≠ q) :
    (addPairConfigEquiv hpq α β).symm a s = cast (addPair_of_ne hpq α β hp hq).symm (a.2 s) := by
  simp [addPairConfigEquiv, hp, hq]

/-- The fresh factors of `addPair` alone: `A` at `p`, `B` at `q`, and one basis vector at the
other parties. -/
def pairFactor (_hpq : p ≠ q) (A B : Type) : P → Type :=
  fun s ↦ if s = p then A else if s = q then B else Unit

variable (A B : Type)

/-- The bases of `pairFactor` are finite. -/
instance [Fintype A] [Fintype B] (s : P) : Fintype (pairFactor hpq A B s) := by
  unfold pairFactor; split_ifs <;> infer_instance

/-- The bases of `pairFactor` have decidable equality. -/
instance [DecidableEq A] [DecidableEq B] (s : P) : DecidableEq (pairFactor hpq A B s) := by
  unfold pairFactor; split_ifs <;> infer_instance

/-- The fresh factors are trivial when `A` and `B` are. -/
@[instance_reducible]
def pairFactor.unique [Unique A] [Unique B] (s : P) : Unique (pairFactor hpq A B s) := by
  unfold pairFactor; split_ifs <;> infer_instance

/-- The basis of `addPair` at one party is the fresh factor there times the old basis. -/
def addPairSiteEquiv (X : P → Type) (s : P) :
    addPair X hpq A B s ≃ pairFactor hpq A B s × X s :=
  if hp : s = p then
    (Equiv.cast (show addPair X hpq A B s = (A × X s) by simp [addPair, hp])).trans
      ((Equiv.cast (show A = pairFactor hpq A B s by simp [pairFactor, hp])).prodCongr
        (Equiv.refl _))
  else if hq : s = q then
    (Equiv.cast (show addPair X hpq A B s = (B × X s) by simp [addPair, hq, hpq.symm])).trans
      ((Equiv.cast (show B = pairFactor hpq A B s by simp [pairFactor, hq, hpq.symm])).prodCongr
        (Equiv.refl _))
  else
    (Equiv.cast (show addPair X hpq A B s = X s by simp [addPair, hp, hq])).trans
      ((Equiv.punitProd (X s)).symm.trans
        ((Equiv.cast (show PUnit = pairFactor hpq A B s by simp [pairFactor, hp, hq])).prodCongr
          (Equiv.refl _)))

end addPair

end QuantumCircuit.Party
