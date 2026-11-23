/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Monomial.ChainForm

/-!
# Monomials as effect chains, and their replaced terms as words

A monomial (`Monomial D X Y`, a party circuit on the parties of `D` whose gates are pair
sources and pair effects) is a chain `F_n E_n ⋯ E_1 F_0` of source-only pieces `F_i` and pair
effects `E_i = ⟨η_i| ⊗ 1`: an `EffectChain` on the configurations (`Monomial.toEffectChain`,
`Monomial.eval_toEffectChain`), its chain form (`QICLean.Circuit.Party.Monomial.ChainForm`). So
the error, count and coefficient bounds of `QICLean.Circuit.Party.Monomial.Elimination` apply.

The insertions are source-only words (`Word.insWord`), so each term of a replaced monomial is
the operator of a source-only word (`Monomial.op_replaceWord`), and the ideal content of the
stacks is prepared by pair sources (`Monomial.op_prepStack`). The identification of the effect
list of the chain form with `Monomial.effects` is `Monomial.chainEffects_eq`.

## Main definitions

* `QuantumCircuit.Party.Monomial.toEffectChain`, `chainEffects`, `replaceWord`, `stackEquiv`.

## Main results

* `QuantumCircuit.Party.Monomial.eval_toEffectChain` — the chain evaluates to the operator.
* `QuantumCircuit.Party.Monomial.op_replaceWord` — each term of a replaced monomial is the
  operator of an allowed source-only word.
* `QuantumCircuit.Party.Monomial.op_prepStack` — the stacks are prepared by pair sources.
* `QuantumCircuit.Party.Monomial.stackApp_of_notMem_effectParties` — the stacks are owned by the
  endpoint parties of the effects.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127.
-/

noncomputable section

open Matrix ManyBody EuclideanSpace CyclicInsertion
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [Fintype P] [DecidableEq P]

/-! ### Monomials -/

namespace Monomial

omit [Fintype P]

variable {D : Finset P} {X Y : ↥D → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- The chain form of a monomial: its chain form after the empty word, completed by the chain
form of a single word at the end. -/
def chainForm (M : Monomial D X Y) : ChainForm X Y :=
  chainFormAux M (fun _ _ _ w ↦ ChainForm.ofWord w) (PartyCircuit.done X)

/-- The monomial as a chain `F_n E_n ⋯ E_1 F_0` of source-only pieces and pair effects. -/
def toEffectChain (M : Monomial D X Y) : EffectChain (Config X) (Config Y) :=
  M.chainForm.chain

/-- The pair effects of the monomial as computed by the chain form (equal to
`Monomial.effects`, `chainEffects_eq`). -/
def chainEffects (M : Monomial D X Y) : List (PairSource ↥D) :=
  M.chainForm.effects

/-- The configurations of the stacks of the effects of a monomial in front of `T`: a
configuration of `T` and one of the stack registers of the effect chain. -/
def stackEquiv (M : Monomial D X Y) (m : ℕ) (T : ↥D → Type) :
    Config (stackApp m M.chainEffects T) ≃ Config T × M.toEffectChain.stackIndex m :=
  (stackAppEquiv m M.chainEffects T).trans
    ((Equiv.refl _).prodCongr (M.chainForm.indexEquiv m).symm)

/-- The terms of the replaced monomial as source-only words: the effect occurrence number `i`
is replaced by the insertion at position `κ i`, and its stack stays idle afterwards. Source:
`04-compression.tex`, lines 96–106 and 121–123. -/
def replaceWord (M : Monomial D X Y) (m : ℕ)
    (κ : Fin M.toEffectChain.effectCount → Fin m) : Word X (stackApp m M.chainEffects Y) :=
  M.chainForm.replaceWord m κ

/-! #### The effects of the chain form -/

section Effects

/-- The effects of the chain form of a circuit are its effects followed by those given by the
completion rule, when these do not depend on the word read before. -/
theorem effects_chainFormAux {W : ↥D → Type} [∀ s, Fintype (W s)] [∀ s, DecidableEq (W s)] :
    {Z Z' : ↥D → Type} → [∀ s, Fintype (Z s)] → [∀ s, DecidableEq (Z s)] →
    (c : Monomial D Z Z') → (k : ChainCont Z' W) → (E : List (PairSource ↥D)) →
    (∀ ⦃X : ↥D → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z'),
      (k w).effects = E) →
    ∀ {X : ↥D → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z),
      (chainFormAux c k w).effects = c.effects ++ E
  | _, _, _, _, .done _, _, _, hk, _, _, _, w => hk w
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl _), _, _, hk, _, _, _, _ => hk _
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr g), _, _, hk, _, _, _, _ =>
    congrArg (g.toPairSource :: ·) (hk _)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, _, hk, _, _, _, _ => hk _
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _, hk, _, _, _, _ => hk _
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', k, E, hk, _, _, _, w => by
    rw [chainFormAux_comp, effects_chainFormAux c _ (Monomial.effects c' ++ E)
      (fun _ _ _ w ↦ effects_chainFormAux c' k E hk w) w, effects_comp c c', List.append_assoc]

/-- The number of effects of the chain form of a circuit is its number of effects plus that
given by the completion rule, when this does not depend on the word read before. -/
theorem effectCount_chainFormAux {W : ↥D → Type} [∀ s, Fintype (W s)]
    [∀ s, DecidableEq (W s)] : {Z Z' : ↥D → Type} → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : Monomial D Z Z') → (k : ChainCont Z' W) → (n : ℕ) →
    (∀ ⦃X : ↥D → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z'),
      (k w).chain.effectCount = n) →
    ∀ {X : ↥D → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z),
      (chainFormAux c k w).chain.effectCount = c.effectCount + n
  | _, _, _, _, .done _, _, _, hk, _, _, _, w => (hk w).trans (Nat.zero_add _).symm
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inl _), _, _, hk, _, _, _, _ =>
    (hk _).trans (Nat.zero_add _).symm
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr _), _, _, hk, _, _, _, _ =>
    (congrArg (· + 1) (hk _)).trans (Nat.add_comm _ _)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ _ _ _, _, _, hk, _, _, _, _ =>
    (hk _).trans (Nat.zero_add _).symm
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ _, _, _, hk, _, _, _, _ =>
    (hk _).trans (Nat.zero_add _).symm
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', k, n, hk, _, _, _, w => by
    rw [chainFormAux_comp, effectCount_chainFormAux c _ (Monomial.effectCount c' + n)
      (fun _ _ _ w ↦ effectCount_chainFormAux c' k n hk w) w, effectCount_comp c c',
      Nat.add_assoc]

/-- The number of sources of the replacement words of the chain form: those of the word read so
far, those of the circuit, `m - 1` per effect of the circuit, and those added by the completion
rule. -/
theorem sourceCount_replaceWord_chainFormAux {W : ↥D → Type} [∀ s, Fintype (W s)]
    [∀ s, DecidableEq (W s)] (m : ℕ) : {Z Z' : ↥D → Type} → [∀ s, Fintype (Z s)] →
    [∀ s, DecidableEq (Z s)] → (c : Monomial D Z Z') → (k : ChainCont Z' W) → (N : ℕ) →
    (∀ ⦃X : ↥D → Type⦄ [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z') κ,
      ((k w).replaceWord m κ).sourceCount = w.sourceCount + N) →
    ∀ {X : ↥D → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (w : Word X Z) κ,
      ((chainFormAux c k w).replaceWord m κ).sourceCount =
        w.sourceCount + Monomial.sourceCount c + Monomial.effectCount c * (m - 1) + N
  | _, _, _, _, .done _, _, _, hk, _, _, _, w, κ => (hk w κ).trans (by
    change _ = w.sourceCount + 0 + 0 * (m - 1) + _
    omega)
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY (.inl g), _, _, hk, _, _, _, w, κ =>
    (hk _ κ).trans (by
      change (Word.sources (w.comp (PartyCircuit.gate D hY g))).length + _ =
        w.sources.length + 1 + 0 * (m - 1) + _
      rw [Word.sources_comp, List.length_append]
      change 1 + _ + _ = _
      omega)
  | _, Y, _, _, @PartyCircuit.gate _ _ _ _ _ _ _ _ (.inr g), k, _, hk, _, _, _, w, κ => by
    change (Word.sources (w.comp ((Word.insWord g m _).comp (Word.framePairs g.distinct
      g.leftBasis g.rightBasis m ((k (PartyCircuit.done Y)).replaceWord m (Fin.tail κ)))))).length =
      w.sourceCount + 0 + 1 * (m - 1) + _
    rw [Word.sources_comp, Word.sources_comp, Word.sources_framePairs, Word.sources_insWord,
      List.length_append, List.length_append, List.length_replicate]
    have h := hk (PartyCircuit.done Y) (Fin.tail κ)
    change ((k (PartyCircuit.done Y)).replaceWord m (Fin.tail κ)).sources.length = 0 + _ at h
    rw [h]
    change _ = w.sources.length + 0 + 1 * (m - 1) + _
    omega
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY A, _, _, hk, _, _, _, w, κ =>
    (hk _ κ).trans (by
      change (Word.sources (w.comp (PartyCircuit.localOp p hY A))).length + _ =
        w.sources.length + 0 + 0 * (m - 1) + _
      rw [Word.sources_comp, List.length_append]
      change 0 + _ + _ = _
      omega)
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ A, _, _, hk, _, _, _, w, κ =>
    (hk _ κ).trans (by
      change (Word.sources (w.comp (PartyCircuit.localOps A))).length + _ =
        w.sources.length + 0 + 0 * (m - 1) + _
      rw [Word.sources_comp, List.length_append]
      change 0 + _ + _ = _
      omega)
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c', k, N, hk, _, _, _, w, κ => by
    refine (sourceCount_replaceWord_chainFormAux m c _
      (Monomial.sourceCount c' + Monomial.effectCount c' * (m - 1) + N)
      (fun _ _ _ w' κ' ↦ (sourceCount_replaceWord_chainFormAux m c' k N hk w' κ').trans
        (by ring)) w κ).trans ?_
    rw [sourceCount_comp, effectCount_comp, Nat.add_mul]
    ring

end Effects

variable (M : Monomial D X Y)

/-- **The chain evaluates to the operator of the monomial.** -/
theorem eval_toEffectChain : M.toEffectChain.eval = M.op chainEv := by
  have h := eval_chainFormAux M (fun _ _ _ w ↦ ChainForm.ofWord w)
    (1 : Matrix (Config Y) (Config Y) ℂ)
    (fun _ _ _ w ↦ (Matrix.one_mul _).symm) (PartyCircuit.done X)
  exact h.trans ((congrArg (· * _) (Matrix.one_mul _)).trans (Matrix.mul_one _))

/-- The chain of an allowed monomial is allowed: its pieces are contractions and its effects
are normalized. -/
theorem isAllowed_toEffectChain (hM : M.IsAllowed chainEv ChainGate.IsAllowed) :
    M.toEffectChain.IsAllowed :=
  isAllowed_chainFormAux (k := fun _ _ _ w ↦ ChainForm.ofWord w) hM
    (fun _ _ _ _ hw ↦ PartyCircuit.norm_op_le_one _ hw)
    Word.isAllowed_done

/-- The effect list of the chain form is the list of effects of the monomial. -/
theorem chainEffects_eq : M.chainEffects = M.effects :=
  (effects_chainFormAux M _ [] (fun _ _ _ _ ↦ rfl) _).trans (List.append_nil _)

/-- The chain has as many effects as the monomial. -/
theorem effectCount_toEffectChain : M.toEffectChain.effectCount = M.effectCount :=
  effectCount_chainFormAux M _ 0 (fun _ _ _ _ ↦ rfl) _

/-- The endpoint parties of the pair effects of a monomial are those of the effects of its chain
form. -/
theorem effectParties_eq : M.effectParties = M.chainEffects.map fun e ↦ (e.left, e.right) := by
  rw [chainEffects_eq]; rfl

/-- The effects of an allowed monomial are normalized. -/
theorem norm_vector_of_mem_chainEffects (hM : M.IsAllowed chainEv ChainGate.IsAllowed) :
    ∀ e ∈ M.chainEffects, ‖e.vector‖ = 1 :=
  M.chainEffects_eq ▸ norm_vector_of_mem_effects hM

variable (m : ℕ)

/-- The replacement words of an allowed monomial are allowed. -/
theorem isAllowed_replaceWord (hM : M.IsAllowed chainEv ChainGate.IsAllowed)
    (κ : Fin M.toEffectChain.effectCount → Fin m) : (M.replaceWord m κ).IsAllowed :=
  isAllowed_replaceWord_chainFormAux (k := fun _ _ _ w ↦ ChainForm.ofWord w) hM
    (fun _ _ _ _ hw _ _ ↦ hw) Word.isAllowed_done m κ

/-- **Each term of a replaced monomial is source-only**: the term with insertion positions `κ`
is the operator of the source-only word `replaceWord`, read along `stackEquiv`. Source: Lemma 5.1,
`04-compression.tex`, lines 65–66 and 96–123. -/
theorem op_replaceWord (κ : Fin M.toEffectChain.effectCount → Fin m) :
    (M.replaceWord m κ).op =
      reindex (M.stackEquiv m Y).symm (Equiv.refl _) (M.toEffectChain.replaceTerm m κ) := by
  refine op_replaceWord_chainFormAux M (fun _ _ _ w ↦ ChainForm.ofWord w) (fun _ _ _ w m κ ↦ ?_)
    (PartyCircuit.done X) m κ
  ext y x
  change w.op y x = (prepMatrix (Equiv.prodComm (Config Y) Unit) (EuclideanSpace.single () 1) *
    w.op) (y, ()) x
  rw [prepMatrix_prodComm_mul_apply]
  simp

/-- A replacement word has the sources of the monomial and `m - 1` more sources per effect. -/
theorem sourceCount_replaceWord (κ : Fin M.toEffectChain.effectCount → Fin m) :
    (M.replaceWord m κ).sourceCount = M.sourceCount + M.effectCount * (m - 1) := by
  refine (sourceCount_replaceWord_chainFormAux m M (fun _ _ _ w ↦ ChainForm.ofWord w) 0
    (fun _ _ _ _ _ ↦ rfl) (PartyCircuit.done X) κ).trans ?_
  change 0 + _ + _ + 0 = _
  omega

variable (T : ↥D → Type) [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)]

/-- The stacks of an allowed monomial are prepared by an allowed word. -/
theorem isAllowed_prepStack (hM : M.IsAllowed chainEv ChainGate.IsAllowed) :
    (prepStack m M.chainEffects T).IsAllowed :=
  Party.isAllowed_prepStack m _ T (M.norm_vector_of_mem_chainEffects hM)

/-- **The stacks of a monomial are prepared by pair sources**: read along `stackEquiv`, the
word `prepStack` prepares the ideal content of the stacks of the effect chain behind the
input. -/
theorem op_prepStack :
    (prepStack m M.chainEffects T).op =
      reindex (M.stackEquiv m T).symm (Equiv.refl _)
        (prepMatrix (Equiv.prodComm (Config T) _) (M.toEffectChain.stackVector m)) := by
  rw [Party.op_prepStack]
  ext y x
  have hv := stackVector_chainFormAux M (fun _ _ _ w ↦ ChainForm.ofWord w)
    (fun _ _ _ _ _ _ ↦ rfl) (PartyCircuit.done X) m
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.refl_symm, Equiv.coe_refl,
    id, prepMatrix_apply, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, stackEquiv,
    Equiv.trans_apply]
  congr 1
  exact (hv _).symm

omit [∀ s, Fintype (T s)] [∀ s, DecidableEq (T s)] in
/-- **Ownership of the stacks of a monomial**: at a party that is no endpoint of an effect, the
stacked system has the basis of `T`. Source: Lemma 5.1, `04-compression.tex`, lines 67–68 and
100–103. -/
theorem stackApp_of_notMem_effectParties {s : ↥D}
    (h : ∀ e ∈ M.effectParties, s ≠ e.1 ∧ s ≠ e.2) : stackApp m M.chainEffects T s = T s := by
  refine stackApp_of_forall_ne m _ T fun e he ↦ h (e.left, e.right) ?_
  rw [effectParties_eq]
  exact List.mem_map_of_mem he

/-! #### The chain form of the constructors -/

section ChainOfConstructors

variable {Z W : ↥D → Type} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] [∀ s, Fintype (W s)]
  [∀ s, DecidableEq (W s)]

/-- A word read as a monomial has the chain of one piece, its operator. -/
theorem toEffectChain_toChain (w : Word X Y) :
    Monomial.toEffectChain (D := D) (Word.toChain w) = .final w.op := by
  obtain ⟨w', h, hop, -⟩ := chainFormAux_toChain w (fun _ _ _ w ↦ ChainForm.ofWord w)
    (PartyCircuit.done X)
  rw [toEffectChain, chainForm, h]
  exact congrArg EffectChain.final (hop.trans (Matrix.mul_one _))

/-- The chain of `rest ∘ ⟨η| ∘ w` is the effect `⟨η|` after the piece `w`, read along the
configurations of `g`, followed by the chain of `rest`. -/
theorem toEffectChain_thenEffect {E : Finset ↥D} (w : Word X Z) (g : PairEffectGate E Z Y)
    (rest : Monomial D Y W) :
    Monomial.toEffectChain (D := D) (Word.thenEffect w g rest) =
      .effect g.leftBasis g.rightBasis (Config Y) (reindex g.configEquiv (Equiv.refl _) w.op)
        g.vector rest.toEffectChain := by
  obtain ⟨w', h, hop, -⟩ := chainFormAux_toChain w
    (chainFormAux (PartyCircuit.comp g.toChain rest) fun _ _ _ w ↦ ChainForm.ofWord w)
    (PartyCircuit.done X)
  have hop' : w'.op = w.op := hop.trans (Matrix.mul_one _)
  rw [toEffectChain, chainForm, Word.thenEffect, chainFormAux_comp, h, ← hop']
  rfl

/-- The effects of `rest ∘ ⟨η| ∘ w` are the effect `g` followed by those of `rest`. -/
theorem chainEffects_thenEffect {E : Finset ↥D} (w : Word X Z) (g : PairEffectGate E Z Y)
    (rest : Monomial D Y W) :
    Monomial.chainEffects (D := D) (Word.thenEffect w g rest) =
      g.toPairSource :: rest.chainEffects := by
  rw [chainEffects_eq, chainEffects_eq, Word.thenEffect, effects_comp, effects_comp,
    Monomial.effects_toChain]
  rfl

omit [∀ s, Fintype (W s)] [∀ s, DecidableEq (W s)] in
/-- `rest ∘ ⟨η| ∘ w` is allowed when `w` and `rest` are and the vector of `g` is
normalized. -/
theorem isAllowed_thenEffect {E : Finset ↥D} {w : Word X Z} {g : PairEffectGate E Z Y}
    {rest : Monomial D Y W} (hw : w.IsAllowed) (hg : ‖g.vector‖ = 1)
    (hrest : rest.IsAllowed chainEv ChainGate.IsAllowed) :
    PartyCircuit.IsAllowed chainEv ChainGate.IsAllowed (Word.thenEffect w g rest) :=
  ⟨hw.toChain, ⟨(PairEffectGate.norm_ev_le g ()).trans hg.le, hg⟩, hrest⟩

end ChainOfConstructors

end Monomial

end QuantumCircuit.Party
