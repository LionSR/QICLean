/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import QICLean.Circuit.Party.Compression.GateExpansion.Transfer

/-!
# Gate expansions with messages

A monomial of Theorem 5.2 may contain, besides local operations, pair sources and pair effects,
transfers of registers between parties ("messages"). A *message monomial* on the cell `D`
(`MessageMonomial`) is a monomial (`segment`), the identity transfer of a register (`transfer`),
or a chronological composition of two message monomials (`comp`). Expanding every transfer in
the standard basis of its register (`WeightedGate.transferTerms` with
`EuclideanSpace.basisFun`) gives a weighted list of monomials
(`MessageMonomial.expand`) with the operator of the message monomial; its length and its
coefficient sum are the product of the dimensions of the messages, and every term has the pair
effects of the message monomial. A *message gate* (`MessageGate`) is a weighted list of message
monomials; its expansion flattens the expansions of its terms, keeping the coefficients.

The composition of two expansions is their ordered Cartesian product (`WeightedGate.compTerms`):
the numbers of terms and the coefficient sums multiply, the numbers of pair effects add.

## Main definitions

* `QuantumCircuit.Party.WeightedGate.compTerms`.
* `QuantumCircuit.Party.MessageMonomial`, `MessageMonomial.op`, `IsAllowed`,
  `messageDimensions`, `effectCount`, `expand`.
* `QuantumCircuit.Party.MessageGate`, `MessageGate.op`, `MessageGate.expand`.

## Main results

* `QuantumCircuit.Party.WeightedGate.gate_toGate_compTerms`, `length_compTerms`,
  `sum_norm_compTerms`.
* `QuantumCircuit.Party.MessageMonomial.op_expand`, `isAllowed_effectCount_expand`,
  `expansion_size` and its bounded forms.
* `QuantumCircuit.Party.MessageGate.op_expand`, `expansion_size` and its bounded forms.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 32–45 and 143–147.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

open GateExpansion

variable {P : Type} [DecidableEq P]

/-! ### Composition of weighted lists of monomials -/

namespace WeightedGate

variable {D : Finset P} {A B C : ↥D → Type} [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)]

/-- The expansion of the second weighted list after the first: one term for each ordered pair of
terms, with the product of the coefficients and the composed monomial. Source:
`04-compression.tex`, lines 32–45. -/
def compTerms (L : List (ℂ × Monomial D A B)) (K : List (ℂ × Monomial D B C)) :
    List (ℂ × Monomial D A C) :=
  L.flatMap fun l ↦ K.map fun k ↦ (l.1 * k.1, PartyCircuit.comp l.2 k.2)

/-- A term of a composition is one ordered pair of terms. -/
theorem mem_compTerms {L : List (ℂ × Monomial D A B)} {K : List (ℂ × Monomial D B C)}
    {t : ℂ × Monomial D A C} :
    t ∈ compTerms L K ↔ ∃ l ∈ L, ∃ k ∈ K, t = (l.1 * k.1, PartyCircuit.comp l.2 k.2) := by
  simp only [compTerms, List.mem_flatMap, List.mem_map, eq_comm]

/-- Every ordered pair of terms gives one term of the composition. -/
theorem length_compTerms (L : List (ℂ × Monomial D A B)) (K : List (ℂ × Monomial D B C)) :
    (compTerms L K).length = L.length * K.length := by
  simp [compTerms, List.length_flatMap]

/-- The coefficient sums multiply under composition. -/
theorem sum_norm_compTerms (L : List (ℂ × Monomial D A B)) (K : List (ℂ × Monomial D B C)) :
    ((compTerms L K).map fun t ↦ ‖t.1‖).sum =
      (L.map fun t ↦ ‖t.1‖).sum * (K.map fun t ↦ ‖t.1‖).sum := by
  simp only [compTerms, List.map_flatten, List.flatMap_def, List.sum_flatten, List.map_map,
    Function.comp_def, norm_mul, List.sum_map_mul_left, List.sum_map_mul_right]

variable [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)]

/-- The terms of a composition of allowed lists are allowed. -/
theorem isAllowed_compTerms (L : List (ℂ × Monomial D A B)) (K : List (ℂ × Monomial D B C))
    (hL : ∀ l ∈ L, l.2.IsAllowed chainEv ChainGate.IsAllowed)
    (hK : ∀ k ∈ K, k.2.IsAllowed chainEv ChainGate.IsAllowed) :
    ∀ t ∈ compTerms L K, t.2.IsAllowed chainEv ChainGate.IsAllowed := by
  intro t ht
  obtain ⟨l, hl, k, hk, rfl⟩ := mem_compTerms.mp ht
  exact ⟨hL l hl, hK k hk⟩

omit [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] in
/-- The bounds on the numbers of pair effects add under composition. -/
theorem effectCount_compTerms_le (L : List (ℂ × Monomial D A B)) (K : List (ℂ × Monomial D B C))
    {r s : ℕ} (hL : ∀ l ∈ L, l.2.effectCount ≤ r) (hK : ∀ k ∈ K, k.2.effectCount ≤ s) :
    ∀ t ∈ compTerms L K, t.2.effectCount ≤ r + s := by
  intro t ht
  obtain ⟨l, hl, k, hk, rfl⟩ := mem_compTerms.mp ht
  exact (Monomial.effectCount_comp l.2 k.2).trans_le (Nat.add_le_add (hL l hl) (hK k hk))

variable [∀ s, Fintype (C s)] [∀ s, DecidableEq (C s)]

/-- **The composition of two expansions is the product of their gates**, the later on the left.
Source: `04-compression.tex`, lines 32–45. -/
theorem gate_toGate_compTerms (L : List (ℂ × Monomial D A B)) (K : List (ℂ × Monomial D B C)) :
    gate (toGate (compTerms L K)) = gate (toGate K) * gate (toGate L) := by
  rw [gate_toGate, gate_toGate, gate_toGate]
  induction L with
  | nil => simp [compTerms]
  | cons l L ih =>
    rw [compTerms, List.flatMap_cons, ← compTerms, List.map_append, List.sum_append, ih,
      List.map_cons, List.sum_cons, Matrix.mul_add, List.map_map]
    congr 1
    clear ih
    induction K with
    | nil => simp
    | cons k K ihK =>
      rw [List.map_cons, Function.comp_apply, List.sum_cons, ihK, List.map_cons, List.sum_cons,
        Matrix.add_mul, PartyCircuit.op_comp (P := ↥D) (G := ChainGate)]
      congr 1
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm l.1 k.1]

end WeightedGate

/-! ### Message monomials -/

/-- A monomial with messages on the cell `D`: a monomial, the identity transfer of a register
with basis `α` from the sender `p` to the receiver `q` (the basis `α × Z p` of `X p`, read
through `eX`, becomes the basis `α × Z q` of `Y q`, read through `eY`; the other parties keep
the system `Z`), or a chronological composition. Source: `04-compression.tex`,
lines 32–45. -/
inductive MessageMonomial (D : Finset P) : (↥D → Type) → (↥D → Type) → Type 1
  /-- A monomial of local operations, pair sources and pair effects. -/
  | segment {X Y : ↥D → Type} (M : Monomial D X Y) : MessageMonomial D X Y
  /-- The identity transfer of a register from `p` to `q`. -/
  | transfer {X Y Z : ↥D → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
      [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] (p q : ↥D) (α : Type) [Fintype α]
      (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
      (eY : Y q ≃ α × Z q) : MessageMonomial D X Y
  /-- Composition, in chronological order: first `M`, then `N`. -/
  | comp {X Y Z : ↥D → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
      (M : MessageMonomial D X Y) (N : MessageMonomial D Y Z) : MessageMonomial D X Z

namespace MessageMonomial

variable {D : Finset P}

/-- The operator of a message monomial, before any expansion of the messages. Source:
`04-compression.tex`, lines 32–45. -/
def op : {X Y : ↥D → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    MessageMonomial D X Y → Matrix (Config Y) (Config X) ℂ
  | _, _, _, _, segment M => M.op chainEv
  | _, _, _, _, transfer p q _ hZ eX hY eY => transferMatrix p q hZ eX hY eY
  | _, _, _, _, @comp _ _ _ _ _ _ _ _ M N => op N * op M

/-- The monomials of a message monomial are allowed; a transfer needs no condition. Source:
Theorem 5.2, `04-compression.tex`, lines 32–45 and 143–147. -/
def IsAllowed : {X Y : ↥D → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    MessageMonomial D X Y → Prop
  | _, _, _, _, segment M => M.IsAllowed chainEv ChainGate.IsAllowed
  | _, _, _, _, transfer .. => True
  | _, _, _, _, @comp _ _ _ _ _ _ _ _ M N => IsAllowed M ∧ IsAllowed N

/-- The dimensions of the messages, in chronological order, repeated messages counted
separately. Source: Theorem 5.2, `04-compression.tex`, lines 32–45 and 143–147. -/
def messageDimensions : {X Y : ↥D → Type} → MessageMonomial D X Y → List ℕ
  | _, _, segment _ => []
  | _, _, @transfer _ _ _ _ _ _ _ _ _ _ _ _ α _ _ _ _ _ => [Fintype.card α]
  | _, _, comp M N => messageDimensions M ++ messageDimensions N

/-- The number of pair effects; transfers have none. Source: Theorem 5.2,
`04-compression.tex`, lines 32–45 and 143–147. -/
def effectCount : {X Y : ↥D → Type} → MessageMonomial D X Y → ℕ
  | _, _, segment M => M.effectCount
  | _, _, transfer .. => 0
  | _, _, comp M N => effectCount M + effectCount N

/-- The expansion of every message in the standard basis of its register, the expansions
composed. Source: `04-compression.tex`, lines 32–45. -/
def expand : {X Y : ↥D → Type} → MessageMonomial D X Y → List (ℂ × Monomial D X Y)
  | _, _, segment M => [(1, M)]
  | _, _, @transfer _ _ _ _ _ _ _ _ _ _ p q α _ hZ eX hY eY =>
    WeightedGate.transferTerms p q hZ eX hY eY (EuclideanSpace.basisFun α ℂ)
  | _, _, @comp _ _ _ _ _ _ _ _ M N => WeightedGate.compTerms (expand M) (expand N)

section Rules

variable {X Y Z : ↥D → Type}

/-- A monomial has no message. -/
@[simp] theorem messageDimensions_segment (M : Monomial D X Y) :
    (segment M).messageDimensions = [] :=
  rfl

/-- The messages of a composition: those of the first part first. -/
@[simp] theorem messageDimensions_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (M : MessageMonomial D X Y) (N : MessageMonomial D Y Z) :
    (comp M N).messageDimensions = M.messageDimensions ++ N.messageDimensions :=
  rfl

/-- The pair effects of a monomial. -/
@[simp] theorem effectCount_segment (M : Monomial D X Y) :
    (segment M).effectCount = M.effectCount :=
  rfl

/-- The numbers of pair effects add under composition. -/
@[simp] theorem effectCount_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (M : MessageMonomial D X Y) (N : MessageMonomial D Y Z) :
    (comp M N).effectCount = M.effectCount + N.effectCount :=
  rfl

/-- A monomial is its own expansion, with coefficient one. -/
@[simp] theorem expand_segment (M : Monomial D X Y) : (segment M).expand = [(1, M)] :=
  rfl

/-- The expansion of a composition is the composition of the expansions. -/
@[simp] theorem expand_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (M : MessageMonomial D X Y) (N : MessageMonomial D Y Z) :
    (comp M N).expand = WeightedGate.compTerms M.expand N.expand :=
  rfl

/-- A transfer carries one message, of the dimension of its register. -/
@[simp] theorem messageDimensions_transfer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] (p q : ↥D) (α : Type) [Fintype α]
    (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
    (eY : Y q ≃ α × Z q) :
    (transfer (X := X) p q α hZ eX hY eY).messageDimensions = [Fintype.card α] :=
  rfl

/-- A transfer has no pair effect. -/
@[simp] theorem effectCount_transfer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] (p q : ↥D) (α : Type) [Fintype α]
    (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
    (eY : Y q ≃ α × Z q) :
    (transfer (X := X) p q α hZ eX hY eY).effectCount = 0 :=
  rfl

/-- A transfer is expanded in the standard basis of its register. -/
@[simp] theorem expand_transfer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] (p q : ↥D) (α : Type) [Fintype α]
    (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
    (eY : Y q ≃ α × Z q) :
    (transfer (X := X) p q α hZ eX hY eY).expand =
      WeightedGate.transferTerms p q hZ eX hY eY (EuclideanSpace.basisFun α ℂ) :=
  rfl

variable [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The operator of a monomial. -/
@[simp] theorem op_segment (M : Monomial D X Y) : (segment M).op = M.op chainEv :=
  rfl

/-- The operator of a composition is the product of the operators, the later on the left. -/
@[simp] theorem op_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (M : MessageMonomial D X Y) (N : MessageMonomial D Y Z) : (comp M N).op = N.op * M.op :=
  rfl

/-- The operator of a transfer is the identity transfer of its register. -/
@[simp] theorem op_transfer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] (p q : ↥D) (α : Type) [Fintype α]
    (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
    (eY : Y q ≃ α × Z q) :
    (transfer (X := X) p q α hZ eX hY eY).op = transferMatrix p q hZ eX hY eY :=
  rfl

/-- A monomial is allowed as a message monomial exactly when it is allowed. -/
@[simp] theorem isAllowed_segment (M : Monomial D X Y) :
    (segment M).IsAllowed ↔ M.IsAllowed chainEv ChainGate.IsAllowed :=
  Iff.rfl

/-- A transfer is allowed. -/
@[simp] theorem isAllowed_transfer [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] (p q : ↥D) (α : Type) [Fintype α]
    (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
    (eY : Y q ≃ α × Z q) :
    (transfer (X := X) p q α hZ eX hY eY).IsAllowed :=
  trivial

/-- A composition is allowed exactly when both parts are. -/
@[simp] theorem isAllowed_comp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (M : MessageMonomial D X Y) (N : MessageMonomial D Y Z) :
    (comp M N).IsAllowed ↔ M.IsAllowed ∧ N.IsAllowed :=
  Iff.rfl

end Rules

/-- **The expansion of a message monomial has its operator.** Source:
`04-compression.tex`, lines 32–45. -/
theorem op_expand : {X Y : ↥D → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    [∀ s, Fintype (Y s)] → [∀ s, DecidableEq (Y s)] → (M : MessageMonomial D X Y) →
      gate (WeightedGate.toGate M.expand) = M.op
  | _, _, _, _, _, _, segment M => by
    rw [expand, WeightedGate.gate_toGate]
    simp [op]
  | _, _, _, _, iF, iD, @transfer _ _ _ _ _ _ iF' iD' _ _ p q α _ hZ eX hY eY => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    obtain rfl : iD' = iD := Subsingleton.elim _ _
    exact WeightedGate.gate_toGate_transferTerms p q hZ eX hY eY _
  | _, _, _, _, _, _, @comp _ _ _ _ _ _ _ _ M N => by
    rw [expand, WeightedGate.gate_toGate_compTerms, op_expand M, op_expand N]
    rfl

/-- Every expanded term is allowed and has the pair effects of the message monomial. Source:
Theorem 5.2, `04-compression.tex`, lines 32–45 and 143–147. -/
theorem isAllowed_effectCount_expand : {X Y : ↥D → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → (M : MessageMonomial D X Y) → M.IsAllowed →
      ∀ t ∈ M.expand, t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount = M.effectCount
  | _, _, _, _, segment M, hM => fun t ht ↦ by
    rw [expand, List.mem_singleton] at ht
    subst ht
    exact ⟨hM, rfl⟩
  | _, _, _, _, @transfer _ _ _ _ _ _ _ _ _ _ p q α _ hZ eX hY eY, _ => fun _ ht ↦
    WeightedGate.isAllowed_effectCount_transferTerms p q hZ eX hY eY _ ht
  | _, _, _, _, @comp _ _ _ _ _ _ _ _ M N, hM => fun t ht ↦ by
    obtain ⟨l, hl, k, hk, rfl⟩ := WeightedGate.mem_compTerms.mp ht
    exact ⟨⟨(isAllowed_effectCount_expand M hM.1 l hl).1,
        (isAllowed_effectCount_expand N hM.2 k hk).1⟩,
      (Monomial.effectCount_comp l.2 k.2).trans (congrArg₂ (· + ·)
        (isAllowed_effectCount_expand M hM.1 l hl).2 (isAllowed_effectCount_expand N hM.2 k hk).2)⟩

/-- **The number of terms and the coefficient sum of the expansion are the product of the message
dimensions.** Source: Theorem 5.2, `04-compression.tex`, lines 32–45 and 143–147. -/
theorem expansion_size : {X Y : ↥D → Type} → (M : MessageMonomial D X Y) →
    M.expand.length = M.messageDimensions.prod ∧
      (M.expand.map fun t ↦ ‖t.1‖).sum = (M.messageDimensions.prod : ℝ)
  | _, _, segment M => by simp [expand, messageDimensions]
  | _, _, @transfer _ _ _ _ _ _ _ _ _ _ p q α _ hZ eX hY eY => by
    simp only [expand, WeightedGate.length_transferTerms,
      WeightedGate.sum_norm_coeff_transferTerms, messageDimensions, List.prod_cons, List.prod_nil,
      mul_one, and_self]
  | _, _, @comp _ _ _ _ _ _ _ _ M N => by
    simp only [expand, WeightedGate.length_compTerms, WeightedGate.sum_norm_compTerms,
      messageDimensions, List.prod_append, Nat.cast_mul, (expansion_size M).1,
      (expansion_size M).2, (expansion_size N).1, (expansion_size N).2, and_self]

/-- At most `m` messages of dimension at most `D₀ ≥ 1` give at most `D₀ ^ m` terms and the same
bound on the coefficient sum. Source: Theorem 5.2, `04-compression.tex`, lines 32–45 and
143–147. -/
theorem expansion_size_le {X Y : ↥D → Type} (M : MessageMonomial D X Y) (D₀ : ℝ) (m : ℕ)
    (hD : 1 ≤ D₀) (hd : ∀ d ∈ M.messageDimensions, (d : ℝ) ≤ D₀)
    (hm : M.messageDimensions.length ≤ m) :
    (M.expand.length : ℝ) ≤ D₀ ^ m ∧ (M.expand.map fun t ↦ ‖t.1‖).sum ≤ D₀ ^ m := by
  have hp : (M.messageDimensions.prod : ℝ) ≤ D₀ ^ m := by
    rw [Nat.cast_list_prod]
    exact (List.prod_map_le_pow_length₀ (f := Nat.castRingHom ℝ) (fun d _ ↦ Nat.cast_nonneg d)
      hd).trans (pow_le_pow_right₀ hD hm)
  exact ⟨(congrArg (Nat.cast : ℕ → ℝ) M.expansion_size.1).trans_le hp,
    M.expansion_size.2.trans_le hp⟩

/-- A bounded number of messages of polynomial dimension changes the number of terms and the
coefficient sum by a polynomial factor only. Source: Theorem 5.2, `04-compression.tex`,
lines 32–45 and 143–147. -/
theorem expansion_size_le_of_power_bounds {X Y : ↥D → Type} (M : MessageMonomial D X Y)
    (L C_D : ℝ) (v m : ℕ) (hL : 1 ≤ L) (hC : 1 ≤ C_D)
    (hd : ∀ d ∈ M.messageDimensions, (d : ℝ) ≤ C_D * L ^ v)
    (hm : M.messageDimensions.length ≤ m) :
    (M.expand.length : ℝ) ≤ C_D ^ m * L ^ (v * m) ∧
      (M.expand.map fun t ↦ ‖t.1‖).sum ≤ C_D ^ m * L ^ (v * m) := by
  have h := M.expansion_size_le (C_D * L ^ v) m
    (one_le_mul_of_one_le_of_one_le hC (one_le_pow₀ hL)) hd hm
  simpa only [mul_pow, ← pow_mul] using h

end MessageMonomial

/-! ### Message gates -/

/-- A gate with messages: a weighted list of message monomials, before the expansion of the
messages. Source: Theorem 5.2, `04-compression.tex`, lines 32–45 and 143–147. -/
abbrev MessageGate (D : Finset P) (X Y : ↥D → Type) := List (ℂ × MessageMonomial D X Y)

namespace MessageGate

variable {D : Finset P} {X Y : ↥D → Type}

/-- The operator of a message gate, with its coefficients. -/
def op [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (L : MessageGate D X Y) :
    Matrix (Config Y) (Config X) ℂ :=
  (L.map fun q ↦ q.1 • q.2.op).sum

/-- The expansions of the message monomials flattened, every coefficient kept. -/
def expand (L : MessageGate D X Y) : List (ℂ × Monomial D X Y) :=
  L.flatMap fun q ↦ q.2.expand.map fun t ↦ (q.1 * t.1, t.2)

/-- Every expanded term comes from a message monomial and a term of its expansion. -/
theorem mem_expand {L : MessageGate D X Y} {t : ℂ × Monomial D X Y} :
    t ∈ L.expand ↔ ∃ q ∈ L, ∃ u ∈ q.2.expand, t = (q.1 * u.1, u.2) := by
  simp only [expand, List.mem_flatMap, List.mem_map, eq_comm]

/-- **The expansion of a message gate has its operator.** Source:
`04-compression.tex`, lines 32–45. -/
theorem op_expand [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] (L : MessageGate D X Y) :
    gate (WeightedGate.toGate L.expand) = L.op := by
  rw [WeightedGate.gate_toGate]
  simp only [expand, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def, mul_smul]
  refine congrArg List.sum (List.map_congr_left fun q _ ↦ ?_)
  rw [← q.2.op_expand, WeightedGate.gate_toGate, List.smul_sum, List.map_map]
  rfl

/-- The expansion of allowed message monomials is allowed. -/
theorem isAllowed_expand [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (L : MessageGate D X Y)
    (hL : ∀ q ∈ L, q.2.IsAllowed) :
    ∀ t ∈ L.expand, t.2.IsAllowed chainEv ChainGate.IsAllowed := by
  intro t ht
  obtain ⟨q, hq, u, hu, rfl⟩ := mem_expand.mp ht
  exact (q.2.isAllowed_effectCount_expand (hL q hq) u hu).1

/-- The bound on the pair effects of the message monomials holds for every expanded term. -/
theorem effectCount_expand_le [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (L : MessageGate D X Y) (hL : ∀ q ∈ L, q.2.IsAllowed) {r : ℕ}
    (hr : ∀ q ∈ L, q.2.effectCount ≤ r) : ∀ t ∈ L.expand, t.2.effectCount ≤ r := by
  intro t ht
  obtain ⟨q, hq, u, hu, rfl⟩ := mem_expand.mp ht
  exact ((q.2.isAllowed_effectCount_expand (hL q hq) u hu).2).trans_le (hr q hq)

/-- The exact number of terms and coefficient sum of the expansion; equal message monomials at
different positions stay separate. -/
theorem expansion_size (L : MessageGate D X Y) :
    L.expand.length = (L.map fun q ↦ q.2.messageDimensions.prod).sum ∧
      (L.expand.map fun t ↦ ‖t.1‖).sum =
        (L.map fun q ↦ ‖q.1‖ * (q.2.messageDimensions.prod : ℝ)).sum := by
  constructor
  · simp only [expand, List.length_flatMap, List.length_map]
    exact congrArg List.sum (List.map_congr_left fun q _ ↦ q.2.expansion_size.1)
  · simp only [expand, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
      Function.comp_def, norm_mul, List.sum_map_mul_left]
    exact congrArg List.sum (List.map_congr_left fun q _ ↦ congrArg (‖q.1‖ * ·)
      q.2.expansion_size.2)

/-- At most `K` message monomials, each with at most `m` messages of dimension at most `D₀`, give
the bounds `K D₀ ^ m` on the number of terms and `(∑ ‖c‖) D₀ ^ m` on the coefficient sum. -/
theorem expansion_size_le (L : MessageGate D X Y) (D₀ : ℝ) (m K : ℕ) (hD : 1 ≤ D₀)
    (hK : L.length ≤ K) (hd : ∀ q ∈ L, ∀ d ∈ q.2.messageDimensions, (d : ℝ) ≤ D₀)
    (hm : ∀ q ∈ L, q.2.messageDimensions.length ≤ m) :
    (L.expand.length : ℝ) ≤ K * D₀ ^ m ∧
      (L.expand.map fun t ↦ ‖t.1‖).sum ≤ (L.map fun q ↦ ‖q.1‖).sum * D₀ ^ m := by
  have hp : ∀ q ∈ L, (q.2.messageDimensions.prod : ℝ) ≤ D₀ ^ m := fun q hq ↦
    q.2.expansion_size.2.symm.trans_le (q.2.expansion_size_le D₀ m hD (hd q hq) (hm q hq)).2
  constructor
  · rw [L.expansion_size.1, Nat.cast_list_sum, List.map_map]
    have hs : (L.map fun q ↦ (q.2.messageDimensions.prod : ℝ)).sum ≤ (L.length : ℝ) * D₀ ^ m :=
      (List.sum_le_sum hp).trans_eq (by simp)
    exact hs.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) (by positivity))
  · rw [L.expansion_size.2]
    have hs := List.sum_le_sum fun q hq ↦ mul_le_mul_of_nonneg_left (hp q hq) (norm_nonneg q.1)
    simpa only [List.sum_map_mul_right] using hs

/-- A bound on the individual coefficients gives the bound `K C D₀ ^ m` on the coefficient sum of
the expansion. -/
theorem expansion_size_le_of_coeff_le (L : MessageGate D X Y) (D₀ C : ℝ) (m K : ℕ)
    (hD : 1 ≤ D₀) (hC : 0 ≤ C) (hK : L.length ≤ K)
    (hd : ∀ q ∈ L, ∀ d ∈ q.2.messageDimensions, (d : ℝ) ≤ D₀)
    (hm : ∀ q ∈ L, q.2.messageDimensions.length ≤ m) (hc : ∀ q ∈ L, ‖q.1‖ ≤ C) :
    (L.expand.length : ℝ) ≤ K * D₀ ^ m ∧
      (L.expand.map fun t ↦ ‖t.1‖).sum ≤ (K : ℝ) * C * D₀ ^ m := by
  have hs : (L.map fun q ↦ ‖q.1‖).sum ≤ (L.length : ℝ) * C :=
    (List.sum_le_sum hc).trans_eq (by simp)
  have hmass : (L.map fun q ↦ ‖q.1‖).sum ≤ (K : ℝ) * C :=
    hs.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hK) hC)
  have hsize := L.expansion_size_le D₀ m K hD hK hd hm
  exact ⟨hsize.1, hsize.2.trans (mul_le_mul_of_nonneg_right hmass (by positivity))⟩

end MessageGate

end QuantumCircuit.Party
