/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Monomial.EffectStacks
import QICLean.Circuit.Party.Monomial.EffectChain

/-!
# The chain form of a circuit of pair sources and pair effects

A party circuit whose gates are pair sources and pair effects is a chain `F_n E_n ⋯ E_1 F_0` of
source-only pieces `F_i` and pair effects `E_i = ⟨η_i| ⊗ 1`, an `EffectChain` on the
configurations. The chain form is defined by one recursion on the syntax of the party circuit
(`chainFormAux`), which produces the effect chain, the list of effects, the identification of
the stack registers and the replacement words together, so that the stack registers of the
chain and the stacks of the effects match step by step. The recursion carries the source-only
word read so far (the current piece) and a rule `ChainCont` that completes a source-only word by
the rest of the circuit: a local operation or a pair source is appended to the current piece, a
pair effect closes it and starts a new piece, and a composition treats its first part, completed
by the chain form of the second part.
The chain form is computed step by step along the syntax of the circuit
(`chainFormAux_comp`, `chainFormAux_effect` and their companions).

The invariants of the recursion give the operator of the chain (`eval_chainFormAux`), its
allowedness, the ideal content of its stacks (`stackVector_chainFormAux`) and the replaced
terms as source-only words (`op_replaceWord_chainFormAux`); the monomial statements are in
`QICLean.Circuit.Party.Monomial.Chain`.

## Main definitions

* `QuantumCircuit.Party.ChainForm`, `QuantumCircuit.Party.ChainCont`,
  `QuantumCircuit.Party.chainFormAux` — the chain form.
* `QuantumCircuit.Party.PairEffectGate.toChain`, `QuantumCircuit.Party.Word.thenEffect` — the
  circuit of one effect, and a word followed by an effect and a circuit.

## Main results

* `QuantumCircuit.Party.eval_chainFormAux`, `isAllowed_chainFormAux`,
  `isAllowed_replaceWord_chainFormAux`, `stackVector_chainFormAux`,
  `op_replaceWord_chainFormAux`, `chainFormAux_toChain` — the invariants.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 32–35 (allowed monomials) and 96–123 (the terms of the replaced
  monomial).
-/

noncomputable section

open Matrix ManyBody EuclideanSpace CyclicInsertion
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ### The chain form of a circuit of sources and pair effects -/

/-- The chain form of a circuit of sources and pair effects from `X` to `W`: its effect chain,
the list of its effects in chronological order, the identification of the stack registers of the
chain with the stack configurations of that list, and the replacement words of its terms. The
four are produced together by `chainFormAux`. -/
structure ChainForm (X W : P → Type) : Type 1 where
  /-- The chain `F_n E_n ⋯ E_1 F_0`. -/
  chain : EffectChain (Config X) (Config W)
  /-- The pair effects, in chronological order. -/
  effects : List (PairSource P)
  /-- The stack registers of the chain are the stack configurations of the effects. -/
  indexEquiv : ∀ m, chain.stackIndex m ≃ stackIdx m effects
  /-- The term of the replaced chain with insertion positions `κ`, as a source-only word. -/
  replaceWord : ∀ m, (Fin chain.effectCount → Fin m) → Word X (stackApp m effects W)

/-- The chain form of a source-only word: the chain of one piece, no effect, and the word
itself as its only replacement word. -/
def ChainForm.ofWord {X W : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (w : Word X W) : ChainForm X W :=
  ⟨.final w.op, [], fun _ ↦ Equiv.refl _, fun _ _ ↦ w⟩

/-- A completion rule for chain forms: for every source-only word from some system to `Y`, the
chain form of that word followed by the rest of a circuit from `Y` to `W`. -/
abbrev ChainCont (Y W : P → Type) : Type 1 :=
  ∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)], Word X Y → ChainForm X W

variable {W : P → Type} [∀ s, Fintype (W s)] [∀ s, DecidableEq (W s)]

/-- The chain form of the circuit `c` from `Z` to `Y`, after a source-only word `w` from some `X`
to `Z`, completed by the rule `k` for the rest of the circuit from `Y`. A local operation or a
pair source is appended to `w`; a pair effect `g` closes the piece `F = w` (read along
`g.configEquiv`) and starts the rest with the empty word; a composition treats its first part,
completed by the chain form of the second part. In the replacement words, the effect is replaced
by the insertion word `Word.insWord g m (κ 0)` and the rest runs beside the new stack
(`Word.framePairs`). Source:
`04-compression.tex`, lines 32–35 (allowed monomials) and 96–123 (the terms of the replaced
monomial). -/
def chainFormAux : {Z Y : P → Type} → [∀ s, Fintype (Z s)] → [∀ s, DecidableEq (Z s)] →
    PartyCircuit (ChainGate (P := P)) Z Y → ChainCont Y W → ChainCont Z W
  | _, _, _, _, .done _, k => fun _ _ _ w ↦ k w
  | Z, Y, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY (.inl g), k => fun _ _ _ w ↦
      k (w.comp (PartyCircuit.gate D hY g : Word Z Y))
  | _, Y, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr g), k => fun _ _ _ w ↦
      let rest := k (PartyCircuit.done Y)
      { chain := .effect g.leftBasis g.rightBasis (Config Y)
          (reindex g.configEquiv (Equiv.refl _) w.op) g.vector rest.chain
        effects := g.toPairSource :: rest.effects
        indexEquiv := fun m ↦ (Equiv.refl _).prodCongr (rest.indexEquiv m)
        replaceWord := fun m κ ↦
          w.comp ((Word.insWord g m (κ (0 : Fin (rest.chain.effectCount + 1)))).comp
            (Word.framePairs g.distinct g.leftBasis g.rightBasis m
              (rest.replaceWord m (Fin.tail κ)))) }
  | Z, Y, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, k => fun _ _ _ w ↦
      k (w.comp (PartyCircuit.localOp p hY A : Word Z Y))
  | Z, Y, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A, k => fun _ _ _ w ↦
      k (w.comp (PartyCircuit.localOps A : Word Z Y))
  | _, _, _, _, @PartyCircuit.comp _ _ _ M _ _ _ c c', k =>
      chainFormAux (Y := M) c (chainFormAux c' k)

/-! ### The chain form, constructor by constructor -/

section Rules

variable {Z Y : P → Type} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] (k : ChainCont Y W)
  {X : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The chain form of a composition: the first part, completed by the chain form of the
second. -/
@[simp] theorem chainFormAux_comp {M : P → Type} [∀ s, Fintype (M s)] [∀ s, DecidableEq (M s)]
    (c : PartyCircuit (ChainGate (P := P)) Z M) (c' : PartyCircuit (ChainGate (P := P)) M Y) :
    chainFormAux (.comp c c') k = chainFormAux c (chainFormAux c' k) :=
  rfl

/-- The chain form of the empty circuit after a word is the completion of that word. -/
@[simp] theorem chainFormAux_done (k' : ChainCont Z W) (w : Word X Z) :
    chainFormAux (.done Z) k' w = k' w :=
  rfl

/-- A local operation is appended to the current piece. -/
@[simp] theorem chainFormAux_localOp [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] (p : P)
    (hY : ∀ s ≠ p, Y s = Z s) (A : Matrix (Y p) (Z p) ℂ) (w : Word X Z) :
    chainFormAux (.localOp p hY A) k w = k (w.comp (PartyCircuit.localOp p hY A : Word _ _)) :=
  rfl

/-- Local operations at every party are appended to the current piece. -/
@[simp] theorem chainFormAux_localOps [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (A : ∀ p, Matrix (Y p) (Z p) ℂ) (w : Word X Z) :
    chainFormAux (.localOps A) k w = k (w.comp (PartyCircuit.localOps A : Word _ _)) :=
  rfl

/-- A pair source is appended to the current piece. -/
@[simp] theorem chainFormAux_source [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    {D : Finset P} (hY : ∀ s ∉ D, Y s = Z s) (g : SourceGate D Z Y) (w : Word X Z) :
    chainFormAux (.gate D hY (.inl g)) k w = k (w.comp (PartyCircuit.gate D hY g : Word _ _)) :=
  rfl

/-- A pair effect closes the current piece: the chain starts with the effect of `g` after the
piece read so far, and the effect list starts with `g`. -/
theorem chainFormAux_effect [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    {D : Finset P} (hY : ∀ s ∉ D, Y s = Z s) (g : PairEffectGate D Z Y) (w : Word X Z) :
    (chainFormAux (.gate D hY (.inr g)) k w).chain =
      .effect g.leftBasis g.rightBasis (Config Y) (reindex g.configEquiv (Equiv.refl _) w.op)
        g.vector (k (PartyCircuit.done Y)).chain ∧
    (chainFormAux (.gate D hY (.inr g)) k w).effects =
      g.toPairSource :: (k (PartyCircuit.done Y)).effects :=
  ⟨rfl, rfl⟩

end Rules

/-! ### Invariants of the chain form -/

section Invariants

/-- **The chain form evaluates to the operator**: when the completion rule `k` evaluates to
`R · op v` after every word `v`, the chain form of `c` after the word `w` evaluates to
`R · op c · op w`. -/
theorem eval_chainFormAux : {Z Y : P → Type} → [∀ s, Fintype (Z s)] → [∀ s, DecidableEq (Z s)] →
    [∀ s, Fintype (Y s)] →
    (c : PartyCircuit (ChainGate (P := P)) Z Y) → (k : ChainCont Y W) →
    (R : Matrix (Config W) (Config Y) ℂ) →
    (∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Y),
      (k w).chain.eval = R * w.op) →
    ∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z),
      (chainFormAux c k w).chain.eval = R * c.op chainEv * w.op
  | _, _, iZ, _, iY, .done _, _, R, hk, _, _, _, w => by
    obtain rfl : iZ = iY := Subsingleton.elim _ _
    rw [chainFormAux_done, hk, PartyCircuit.op_done, Matrix.mul_one]
  | _, _, _, _, iY, @PartyCircuit.gate _ _ _ _ i _ D hY (.inl g), k, R, hk, _, _, _, w => by
    obtain rfl : i = iY := Subsingleton.elim _ _
    rw [chainFormAux_source, hk, Word.op_comp, Matrix.mul_assoc]
    exact congrArg (fun M ↦ R * (M * w.op)) (Word.op_toChain (PartyCircuit.gate D hY g)).symm
  | _, Y, _, _, iY, @PartyCircuit.gate _ _ _ _ i _ D hY (.inr g), k, R, hk, _, _, _, w => by
    obtain rfl : i = iY := Subsingleton.elim _ _
    change (k (PartyCircuit.done Y)).chain.eval * effectMatrix g.vector (Config Y) *
      reindex g.configEquiv (Equiv.refl _) w.op = _
    rw [hk (PartyCircuit.done Y), ChainGate.op_gate_inr]
    simp only [Matrix.mul_assoc]
    exact congrArg (R * ·) ((Matrix.one_mul _).trans (submatrix_id_mul_right _ w.op id _).symm)
  | _, _, _, _, iY, @PartyCircuit.localOp _ _ _ _ i _ p hY A, k, R, hk, _, _, _, w => by
    obtain rfl : i = iY := Subsingleton.elim _ _
    rw [chainFormAux_localOp, hk, Word.op_comp, Matrix.mul_assoc]
    exact congrArg (fun M ↦ R * (M * w.op)) (Word.op_toChain (PartyCircuit.localOp p hY A)).symm
  | _, _, _, _, iY, @PartyCircuit.localOps _ _ _ _ i _ A, k, R, hk, _, _, _, w => by
    obtain rfl : i = iY := Subsingleton.elim _ _
    rw [chainFormAux_localOps, hk, Word.op_comp, Matrix.mul_assoc]
    exact congrArg (fun M ↦ R * (M * w.op)) (Word.op_toChain (PartyCircuit.localOps A)).symm
  | _, _, _, _, _, @PartyCircuit.comp _ _ _ M _ _ _ c c', k, R, hk, _, _, _, w => by
    rw [chainFormAux_comp, eval_chainFormAux c (chainFormAux c' k) (R * c'.op chainEv)
      (eval_chainFormAux c' k R hk) w, PartyCircuit.op_comp, Matrix.mul_assoc R]

/-- The chain form of an allowed circuit after an allowed word is allowed, when the completion
rule gives allowed chains after every allowed word. -/
theorem isAllowed_chainFormAux : {Z Y : P → Type} → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → {c : PartyCircuit (ChainGate (P := P)) Z Y} →
    c.IsAllowed chainEv ChainGate.IsAllowed → {k : ChainCont Y W} →
    (∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Y),
      w.IsAllowed → (k w).chain.IsAllowed) →
    ∀ {X : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {w : Word X Z},
      w.IsAllowed → (chainFormAux c k w).chain.IsAllowed
  | _, _, _, _, .done _, _, _, hk, _, _, _, _, hw => hk _ hw
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl _), hc, _, hk, _, _, _, _, hw =>
    hk _ (Word.IsAllowed.comp hw hc)
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr _), hc, _, hk, _, _, _, _, hw =>
    ⟨(l2_opNorm_reindex_le _ _ _).trans (PartyCircuit.norm_op_le_one _ hw), hc.2,
      hk _ Word.isAllowed_done⟩
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, hc, _, hk, _, _, _, _, hw =>
    hk _ (Word.IsAllowed.comp hw hc)
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, hc, _, hk, _, _, _, _, hw =>
    hk _ (Word.IsAllowed.comp hw hc)
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ _ _, hc, _, hk, _, _, _, _, hw =>
    isAllowed_chainFormAux hc.1 (fun _ _ _ _ hw' ↦ isAllowed_chainFormAux hc.2 hk hw') hw

/-- The replacement words of an allowed circuit after an allowed word are allowed, when those
given by the completion rule are allowed after every allowed word. -/
theorem isAllowed_replaceWord_chainFormAux : {Z Y : P → Type} → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → {c : PartyCircuit (ChainGate (P := P)) Z Y} →
    c.IsAllowed chainEv ChainGate.IsAllowed → {k : ChainCont Y W} →
    (∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Y),
      w.IsAllowed → ∀ m κ, ((k w).replaceWord m κ).IsAllowed) →
    ∀ {X : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] {w : Word X Z},
      w.IsAllowed → ∀ m κ, ((chainFormAux c k w).replaceWord m κ).IsAllowed
  | _, _, _, _, .done _, _, _, hk, _, _, _, _, hw => hk _ hw
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl _), hc, _, hk, _, _, _, _, hw =>
    hk _ (Word.IsAllowed.comp hw hc)
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr g), hc, _, hk, _, _, _, _, hw =>
    fun m _ ↦ Word.IsAllowed.comp hw (Word.IsAllowed.comp (Word.isAllowed_insWord g hc.2 m _)
      (Word.isAllowed_framePairs _ _ _ m (hk _ Word.isAllowed_done m _)))
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, hc, _, hk, _, _, _, _, hw =>
    hk _ (Word.IsAllowed.comp hw hc)
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, hc, _, hk, _, _, _, _, hw =>
    hk _ (Word.IsAllowed.comp hw hc)
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ _ _, hc, _, hk, _, _, _, _, hw =>
    isAllowed_replaceWord_chainFormAux hc.1
      (fun _ _ _ _ hw' ↦ isAllowed_replaceWord_chainFormAux hc.2 hk hw') hw

/-- The ideal content of the stacks of the chain form, read along the identification of its stack
registers, is the ideal content `stackIdxVector` of the stacks of its effects, when the same holds
for the completion rule after every word. -/
theorem stackVector_chainFormAux : {Z Y : P → Type} → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : PartyCircuit (ChainGate (P := P)) Z Y) →
    (k : ChainCont Y W) →
    (∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Y) (m : ℕ)
      (i : stackIdx m (k w).effects),
      (k w).chain.stackVector m (((k w).indexEquiv m).symm i) = stackIdxVector m (k w).effects i) →
    ∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z) (m : ℕ)
      (i : stackIdx m (chainFormAux c k w).effects),
      (chainFormAux c k w).chain.stackVector m (((chainFormAux c k w).indexEquiv m).symm i) =
        stackIdxVector m (chainFormAux c k w).effects i
  | _, _, _, _, .done _, _, hk, _, _, _, w => hk w
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl _), _, hk, _, _, _, _ => hk _
  | _, Y, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr g), _, hk, _, _, _, _ => fun m i ↦
    congrArg (tensorPower (Fin m) g.vector i.1 * ·) (hk (PartyCircuit.done Y) m i.2)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, hk, _, _, _, _ => hk _
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, hk, _, _, _, _ => hk _
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', k, hk, _, _, _, w =>
    stackVector_chainFormAux c _ (fun _ _ _ w' ↦ stackVector_chainFormAux c' k hk w') w

/-- One step of the replaced terms: the insertion word followed by the rest beside the new stack
is the term of the effect chain, read along the stacks. -/
private theorem reindex_effect_step {A₁ B₁ O A₂ S Z' X' F Q : Type} [Fintype S] [Fintype Z']
    [Fintype F] [DecidableEq F] [Fintype Q] [DecidableEq S] [Fintype A₂] (sc₁ : A₁ ≃ F × B₁)
    (E : B₁ ≃ O) (sc₂ : A₂ ≃ F × S) (gc : Z' ≃ Q × S)
    (R : Matrix O S ℂ) (I : Matrix F Q ℂ) (V : Matrix Z' X' ℂ) :
    reindex sc₁.symm sc₂.symm ((1 : Matrix F F ℂ) ⊗ₖ reindex E.symm (Equiv.refl S) R) *
        reindex sc₂.symm gc.symm (I ⊗ₖ (1 : Matrix S S ℂ)) * V =
      reindex (sc₁.trans ((Equiv.refl F).prodCongr E)).symm (Equiv.refl X')
        (((1 : Matrix F F ℂ) ⊗ₖ R) * (I ⊗ₖ (1 : Matrix S S ℂ)) * reindex gc (Equiv.refl X') V) := by
  have hV : V = (reindex gc (Equiv.refl X') V).submatrix gc id := by ext; simp
  simp only [reindex_apply, Equiv.symm_symm, submatrix_mul_equiv]
  conv_lhs => rw [hV]
  rw [submatrix_mul_equiv]
  ext y x
  simp [mul_apply, kroneckerMap_apply]
  rfl

/-- **The replacement words of the chain form are the replaced terms of its chain**, read along
the stacks of its effects and the identification of the stack registers, when the same holds for
the completion rule after every word. -/
theorem op_replaceWord_chainFormAux : {Z Y : P → Type} → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : PartyCircuit (ChainGate (P := P)) Z Y) →
    (k : ChainCont Y W) →
    (∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Y) (m : ℕ)
      (κ : Fin (k w).chain.effectCount → Fin m),
      ((k w).replaceWord m κ).op = reindex ((stackAppEquiv m (k w).effects W).trans
        ((Equiv.refl _).prodCongr ((k w).indexEquiv m).symm)).symm (Equiv.refl _)
        ((k w).chain.replaceTerm m κ)) →
    ∀ ⦃X : P → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z) (m : ℕ)
      (κ : Fin (chainFormAux c k w).chain.effectCount → Fin m),
      ((chainFormAux c k w).replaceWord m κ).op =
        reindex ((stackAppEquiv m (chainFormAux c k w).effects W).trans
          ((Equiv.refl _).prodCongr ((chainFormAux c k w).indexEquiv m).symm)).symm
          (Equiv.refl _) ((chainFormAux c k w).chain.replaceTerm m κ)
  | _, _, _, _, .done _, _, hk, _, _, _, w => hk w
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl _), _, hk, _, _, _, _ => hk _
  | _, Y, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr g), k, hk, _, _, _, w => fun m κ ↦ by
    have hr := hk (PartyCircuit.done Y) m (Fin.tail κ)
    change Word.op (w.comp ((Word.insWord g m _).comp (Word.framePairs g.distinct g.leftBasis
      g.rightBasis m ((k (PartyCircuit.done Y)).replaceWord m (Fin.tail κ))))) = _
    rw [Word.op_comp, Word.op_comp, Word.op_framePairs, Word.op_insWord, hr]
    change _ = reindex _ _ (reindex (Equiv.prodLeftComm _ _ _) (Equiv.refl _) _)
    rw [reindex_effect_step]
    ext y x
    rfl
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, hk, _, _, _, _ => hk _
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, hk, _, _, _, _ => hk _
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', k, hk, _, _, _, w =>
    op_replaceWord_chainFormAux c _ (fun _ _ _ w' ↦ op_replaceWord_chainFormAux c' k hk w') w

variable {Z Y : P → Type} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)]

/-- The chain form of a word `v` read as a circuit of sources and effects, after a word `w`, is
the completion of a single word `w'` with the operator `op v · op w` and the sources of `v`
followed by those of `w`, allowed when `w` and `v` are. -/
theorem chainFormAux_toChain : {Z Y : P → Type} → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (v : Word Z Y) → (k : ChainCont Y W) → {X : P → Type} →
    [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] → (w : Word X Z) →
    ∃ w' : Word X Y, chainFormAux v.toChain k w = k w' ∧ w'.op = v.op * w.op ∧
      w'.sources = v.sources ++ w.sources ∧ (w.IsAllowed → v.IsAllowed → w'.IsAllowed)
  | _, _, _, _, .done _, _, _, _, _, w =>
    ⟨w, rfl, (Matrix.one_mul _).symm, rfl, fun hw _ ↦ hw⟩
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g, _, _, _, _, w =>
    ⟨w.comp (PartyCircuit.gate D hY g), rfl, Word.op_comp _ _, rfl,
      fun hw hv ↦ Word.IsAllowed.comp hw hv⟩
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, _, _, _, _, w =>
    ⟨w.comp (PartyCircuit.localOp p hY A), rfl, Word.op_comp _ _, rfl,
      fun hw hv ↦ Word.IsAllowed.comp hw hv⟩
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A, _, _, _, _, w =>
    ⟨w.comp (PartyCircuit.localOps A), rfl, Word.op_comp _ _, rfl,
      fun hw hv ↦ Word.IsAllowed.comp hw hv⟩
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ a b, k, _, _, _, w => by
    obtain ⟨w₁, h₁, hop₁, hs₁, ha₁⟩ := chainFormAux_toChain a (chainFormAux (Word.toChain b) k) w
    obtain ⟨w₂, h₂, hop₂, hs₂, ha₂⟩ := chainFormAux_toChain b k w₁
    refine ⟨w₂, h₁.trans h₂, ?_, ?_, fun hw hv ↦ ha₂ (ha₁ hw hv.1) hv.2⟩
    · rw [hop₂, hop₁, Word.op_comp, Matrix.mul_assoc]
    · rw [hs₂, hs₁, Word.sources_comp, List.append_assoc]

end Invariants

/-! ### Constructors: pair effects and words followed by effects -/

section Constructors

variable {X Y Z W : P → Type}

omit [Fintype P] in
/-- One pair effect as a circuit of pair sources and pair effects. -/
def PairEffectGate.toChain [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] {D : Finset P}
    (g : PairEffectGate D X Y) : PartyCircuit (ChainGate (P := P)) X Y :=
  PartyCircuit.gate D g.outside (.inr g)

omit [Fintype P] in
/-- The circuit `rest ∘ ⟨η| ∘ w`: the word `w`, then the pair effect `g`, then the circuit
`rest`. -/
def Word.thenEffect [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] [∀ s, Fintype (Y s)]
    [∀ s, DecidableEq (Y s)] {D : Finset P} (w : Word X Z) (g : PairEffectGate D Z Y)
    (rest : PartyCircuit (ChainGate (P := P)) Y W) : PartyCircuit (ChainGate (P := P)) X W :=
  w.toChain.comp (g.toChain.comp rest)

/-- The operator of one pair effect, read among the gates of monomials, is its operator as a
pair effect. -/
theorem PairEffectGate.op_toChain [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] {D : Finset P} (g : PairEffectGate D X Y) :
    g.toChain.op chainEv = (PartyCircuit.gate D g.outside g).op PairEffectGate.ev :=
  (PartyCircuit.op_gate (G := ChainGate) chainEv D g.outside (.inr g)).trans
    (PartyCircuit.op_gate PairEffectGate.ev D g.outside g).symm

end Constructors

end QuantumCircuit.Party
