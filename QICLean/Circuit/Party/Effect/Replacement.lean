/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Basic
import QICLean.Circuit.Party.Source.Locations
import QICLean.Circuit.Party.Effect.GateReplacement

/-!
# Source-only replacement of an effect circuit, with retained auxiliary registers

Theorem 5.2 replaces every gate of an effect circuit — a gate
expansion `G = ∑_ξ c_ξ M_ξ` into allowed monomials on its cell `D` — by a prepared source gate:
Lemma 5.1 (`WeightedGate.partyPairEffectElimination`) turns the expansion into a weighted sum of
source-only words with stacks of `m` pair registers per pair effect, the common source
preparation (`Word.exists_preparedSourceGate`) turns that sum into one prepared gate, and the
common rescaling `(1 + δ)⁻¹` makes it a contraction within `2δ` of `G` followed by the
preparation of the stacks (`exists_prepared_effectReplacement`, in `Effect/GateReplacement`).

The stacks of a gate stay in the memory until the end: they are its *auxiliary registers*.
Here a register of a party is a factor of its basis, so the auxiliary registers of the whole
circuit form a system `auxiliary m c : P → Type`, and the replacement goes from `X` to
`fun p ↦ auxiliary m c p × Y p` (the auxiliary factor in front, the factors of earlier gates
first). It is a structural recursion on the effect circuit:

* a gate on `D` becomes its prepared gate followed by the relabelling that reads the stacks of
  the parties of `D` as their auxiliary factor (`gateRelabelEquiv`); the systems that change the
  bases on the cell only are `ManyBody.updateOn` (`gateOutSystem`, and the auxiliary factor of a
  gate, `PUnit` outside its cell);
* a composition of `c` and then `c'` becomes `replacement c`, then `replacement c'` beside the
  auxiliary factor of `c` (`SourceCircuit.frame`), then the regrouping of the two auxiliary
  factors;
* the empty circuit and local operations add the trivial auxiliary factor `Unit`.

The auxiliary vector `auxiliaryVector m c` is the product of the garbage vectors `Γ_m` of the
gates (`GateExpansion.inventoryVector`), read on the configurations of `auxiliary m c`.

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.gateAuxConfigEquiv`, `gateOutSystem`, `gateRelabelEquiv`.
* `QuantumCircuit.Party.EffectCircuit.auxiliary`, `auxiliaryVector`, `gatePrepared`,
  `replacement`; `QuantumCircuit.Party.SourceCircuit.ofLocalWord`.

## Main results

* `QuantumCircuit.Party.EffectCircuit.replacement_gate`, `replacement_comp`, … — the
  computation rules (`rfl`).
* `QuantumCircuit.Party.EffectCircuit.isAllowed_replacement`, `norm_auxiliaryVector`.
* `QuantumCircuit.Party.EffectCircuit.gatePrepared_eval`, `gatePrepared_spec` — the prepared
  gate of one gate is the rescaled replaced gate, within `2δ` of the gate followed by the
  preparation of its stacks.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2 `thm:compression`,
  `04-compression.tex`, lines 137–151 and 199–229; Lemma 5.1, lines 53–127.
-/

noncomputable section

open Matrix ManyBody EuclideanSpace
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

open GateExpansion

/-! ### The replacement of an effect circuit -/

variable {P : Type} [DecidableEq P]

namespace EffectCircuit

/-- The auxiliary registers of an effect circuit, a factor of the basis of every party: at a gate on
`D` its stack factors on the parties of `D` (`Unit` outside), at a composition the product of those
of the two parts, earlier first, and `Unit` at the empty circuit and the local operations. Source:
`04-compression.tex`, lines 199–217. -/
def auxiliary (m : ℕ) : {X Y : P → Type} → [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] →
    EffectCircuit X Y → P → Type
  | _, _, _, _, PartyCircuit.done _ => fun _ ↦ Unit
  | _, _, _, _, PartyCircuit.gate D _ g =>
    updateOn (fun _ ↦ PUnit) D (WeightedGate.auxFactor m g.terms)
  | _, _, _, _, PartyCircuit.localOp _ _ _ => fun _ ↦ Unit
  | _, _, _, _, PartyCircuit.localOps _ => fun _ ↦ Unit
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => fun p ↦ auxiliary m c p × auxiliary m c' p

/-- The auxiliary registers are finite. -/
instance instFintypeAuxiliary (m : ℕ) : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → (p : P) → Fintype (auxiliary m c p)
  | _, _, _, _, PartyCircuit.done _ => fun _ ↦ inferInstanceAs (Fintype Unit)
  | _, _, _, _, PartyCircuit.gate D _ g => fun s ↦
    inferInstanceAs (Fintype (updateOn (fun _ ↦ PUnit) D (WeightedGate.auxFactor m g.terms) s))
  | _, _, _, _, PartyCircuit.localOp _ _ _ => fun _ ↦ inferInstanceAs (Fintype Unit)
  | _, _, _, _, PartyCircuit.localOps _ => fun _ ↦ inferInstanceAs (Fintype Unit)
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => fun p ↦
    letI := instFintypeAuxiliary m c p
    letI := instFintypeAuxiliary m c' p
    inferInstanceAs (Fintype (auxiliary m c p × auxiliary m c' p))

/-- The auxiliary registers have decidable equality. -/
instance instDecidableEqAuxiliary (m : ℕ) : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) → (p : P) → DecidableEq (auxiliary m c p)
  | _, _, _, _, PartyCircuit.done _ => fun _ ↦ inferInstanceAs (DecidableEq Unit)
  | _, _, _, _, PartyCircuit.gate D _ g => fun s ↦
    inferInstanceAs
      (DecidableEq (updateOn (fun _ ↦ PUnit) D (WeightedGate.auxFactor m g.terms) s))
  | _, _, _, _, PartyCircuit.localOp _ _ _ => fun _ ↦ inferInstanceAs (DecidableEq Unit)
  | _, _, _, _, PartyCircuit.localOps _ => fun _ ↦ inferInstanceAs (DecidableEq Unit)
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => fun p ↦
    letI := instDecidableEqAuxiliary m c p
    letI := instDecidableEqAuxiliary m c' p
    inferInstanceAs (DecidableEq (auxiliary m c p × auxiliary m c' p))

section Rules

variable (m : ℕ) {X Y Z : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- The empty circuit has trivial auxiliary registers. -/
@[simp] theorem auxiliary_done : auxiliary m (PartyCircuit.done X : EffectCircuit X X) =
    fun _ ↦ Unit :=
  rfl

/-- The auxiliary registers of one gate are its stack factors on its cell. -/
@[simp] theorem auxiliary_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) :
    auxiliary m (PartyCircuit.gate D hY g : EffectCircuit X Y) =
      updateOn (fun _ ↦ PUnit) D (WeightedGate.auxFactor m g.terms) :=
  rfl

/-- A local operation has trivial auxiliary registers. -/
@[simp] theorem auxiliary_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s) (A : Matrix (Y p) (X p) ℂ) :
    auxiliary m (PartyCircuit.localOp p hY A : EffectCircuit X Y) = fun _ ↦ Unit :=
  rfl

/-- Local operations at every party have trivial auxiliary registers. -/
@[simp] theorem auxiliary_localOps (A : ∀ p, Matrix (Y p) (X p) ℂ) :
    auxiliary m (PartyCircuit.localOps A : EffectCircuit X Y) = fun _ ↦ Unit :=
  rfl

/-- The auxiliary registers of a composition are those of both parts, the first in front. -/
@[simp] theorem auxiliary_comp (c : EffectCircuit X Y) (c' : EffectCircuit Y Z) :
    auxiliary m (PartyCircuit.comp c c') = fun p ↦ auxiliary m c p × auxiliary m c' p :=
  rfl

end Rules

/-- The configurations of the auxiliary factor of one gate are the inventory of its replaced gate.
-/
def gateAuxConfigEquiv (m : ℕ) {D : Finset P} {X Y : P → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
    (g : WeightedGate D X Y) :
    Config (updateOn (fun _ ↦ PUnit) D (WeightedGate.auxFactor m g.terms)) ≃
      inventory m (WeightedGate.toGate g.terms) :=
  ((updateOnConfigEquiv _ D _).trans (Equiv.prodUnique _ _)).trans
    (WeightedGate.auxFactorConfigEquiv m g.terms)

/-- The auxiliary vector of an effect circuit: the product of the garbage vectors `Γ_m` of its
gates, read on the configurations of the auxiliary registers. Source: `04-compression.tex`, lines
103–112 and 210–217. -/
def auxiliaryVector [Fintype P] (m : ℕ) : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] →
    (c : EffectCircuit X Y) → EuclideanSpace ℂ (Config (auxiliary m c))
  | _, _, _, _, PartyCircuit.done _ => EuclideanSpace.single (fun _ ↦ ()) 1
  | _, _, _, _, PartyCircuit.gate _ _ g =>
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gateAuxConfigEquiv m g).symm
      (inventoryVector m (WeightedGate.toGate g.terms))
  | _, _, _, _, PartyCircuit.localOp _ _ _ => EuclideanSpace.single (fun _ ↦ ()) 1
  | _, _, _, _, PartyCircuit.localOps _ => EuclideanSpace.single (fun _ ↦ ()) 1
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' =>
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.arrowProdEquivProdArrow P _ _).symm
      (vecKron (auxiliaryVector m c) (auxiliaryVector m c'))

/-- Every auxiliary vector of an allowed circuit is normalized; local operations contribute the
scalar unit and impose no dimension bound. Source: `04-compression.tex`, lines 103–112 and 210–217.
-/
theorem norm_auxiliaryVector [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (c : EffectCircuit X Y) →
    c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed → (m : ℕ) → ‖c.auxiliaryVector m‖ = 1
  | _, _, _, _, PartyCircuit.done _, _, _ => (PiLp.norm_single _ _ _ _).trans norm_one
  | _, _, _, _, PartyCircuit.gate _ _ g, hw, m => by
    change ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (gateAuxConfigEquiv m g).symm
      (inventoryVector m (WeightedGate.toGate g.terms))‖ = 1
    exact (LinearIsometryEquiv.norm_map _ _).trans
      (norm_inventoryVector m _ (WeightedGate.isAllowed_toGate hw.2))
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, _ => (PiLp.norm_single _ _ _ _).trans norm_one
  | _, _, _, _, PartyCircuit.localOps _, _, _ => (PiLp.norm_single _ _ _ _).trans norm_one
  | _, _, _, _, PartyCircuit.comp c c', hw, m => by
    change ‖LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ _
      (vecKron (auxiliaryVector m c) (auxiliaryVector m c'))‖ = 1
    refine (LinearIsometryEquiv.norm_map _ _).trans ?_
    rw [norm_vecKron, norm_auxiliaryVector c hw.1 m, norm_auxiliaryVector c' hw.2 m, one_mul]

/-! #### The replaced gate on its cell -/

section Gate

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)]
  [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] {D : Finset P} {r : ℕ} {S δ : ℝ}

/-- The output system of the replaced gate: the output of the replaced gate on the cell, the output
of the gate outside. -/
abbrev gateOutSystem (m : ℕ) (g : WeightedGate D X Y) : P → Type :=
  updateOn Y D (WeightedGate.gateOut m g.terms)

/-- Outside the cell, the replaced gate keeps the input bases. -/
theorem gateOutSystem_of_notMem (m : ℕ) (hY : ∀ s ∉ D, Y s = X s) (g : WeightedGate D X Y) :
    ∀ s ∉ D, gateOutSystem m g s = X s :=
  fun s hs ↦ (updateOn_of_notMem hs).trans (hY s hs)

/-- The output basis of the replaced gate at a party is its auxiliary factor in front of the output
basis of the gate. -/
def gateRelabelEquiv (m : ℕ) (g : WeightedGate D X Y) (s : P) :
    updateOn (fun _ ↦ PUnit) D (WeightedGate.auxFactor m g.terms) s × Y s ≃
      gateOutSystem m g s :=
  if h : s ∈ D then
    ((Equiv.cast (updateOn_of_mem h)).prodCongr (Equiv.refl _)).trans
      ((WeightedGate.auxFactorEquiv m g.terms ⟨s, h⟩).symm.trans
        (Equiv.cast (updateOn_of_mem h)).symm)
  else
    (((Equiv.cast (updateOn_of_notMem h)).prodCongr (Equiv.refl _)).trans
      (Equiv.punitProd _)).trans (Equiv.cast (updateOn_of_notMem h)).symm

/-- On the cell, the relabelling of the replaced gate reads the auxiliary factor and the output
basis of the gate as the output of the replaced gate. -/
theorem cast_gateRelabelEquiv_of_mem (m : ℕ) (g : WeightedGate D X Y) (s : ↥D)
    (w : updateOn (fun _ ↦ PUnit) D (WeightedGate.auxFactor m g.terms) s × Y s) :
    Equiv.cast (updateOn_of_mem s.2) (gateRelabelEquiv m g s w) =
      (WeightedGate.auxFactorEquiv m g.terms s).symm
        (Equiv.cast (updateOn_of_mem s.2) w.1, w.2) := by
  simp [gateRelabelEquiv, s.2]
  rfl

/-- Outside the cell, the relabelling of the replaced gate drops the trivial auxiliary factor. -/
theorem cast_gateRelabelEquiv_of_notMem (m : ℕ) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) {v : P} (hv : v ∉ D)
    (w : updateOn (fun _ ↦ PUnit) D (WeightedGate.auxFactor m g.terms) v × Y v) :
    cast (gateOutSystem_of_notMem m hY g v hv) (gateRelabelEquiv m g v w) = cast (hY v hv) w.2 := by
  simp only [gateRelabelEquiv, hv, dite_false]
  exact cast_cast _ _ _

/-- The prepared gate replacing a gate of an allowed, expansion-bounded effect circuit, with the
stack length `stackLength r S δ`. Source: `04-compression.tex`, lines 199–212. -/
def gatePrepared (hδ : 0 < δ) (g : WeightedGate D X Y)
    (hw : ‖WeightedGate.ev g (GateFamily.UniqueOutcome.outcome g)‖ ≤ 1 ∧ WeightedGate.IsAllowed g)
    (hb : (∀ t ∈ g.terms, t.2.effectCount ≤ r) ∧ (g.terms.map fun t ↦ ‖t.1‖).sum ≤ S) :
    PreparedGate D X (gateOutSystem (stackLength r S δ) g) where
  ι := Fin (WeightedGate.wordList (stackLength r S δ) g.terms).length
  coeff := WeightedGate.replacementCoefficients (stackLength r S δ) δ g.terms
  gate := Classical.choose
    (WeightedGate.exists_prepared_effectReplacement_relabel hδ g.terms
      (fun t ht ↦ ⟨hw.2 t ht, hb.1 t ht⟩)
      ((congrArg norm (WeightedGate.ev_eq_gate_toGate g _)).symm.trans_le hw.1) hb.2
      (B' := fun s : ↥D ↦ gateOutSystem (stackLength r S δ) g s)
      fun s ↦ Equiv.cast (updateOn_of_mem s.2))

/-- **The matrix of the prepared gate of a gate**, read back on the cell along the identifications
of the output bases and along `gateEquiv`, is the rescaled replaced gate `(1 + δ)⁻¹ G'_m`. Source:
`04-compression.tex`, lines 210–212. -/
theorem gatePrepared_eval (hδ : 0 < δ) (g : WeightedGate D X Y)
    (hw : ‖WeightedGate.ev g (GateFamily.UniqueOutcome.outcome g)‖ ≤ 1 ∧ WeightedGate.IsAllowed g)
    (hb : (∀ t ∈ g.terms, t.2.effectCount ≤ r) ∧ (g.terms.map fun t ↦ ‖t.1‖).sum ≤ S) :
    reindex (WeightedGate.gateEquiv (stackLength r S δ) g.terms) (Equiv.refl _)
        (reindex (Equiv.piCongrRight fun s : ↥D ↦ Equiv.cast (updateOn_of_mem s.2)) (Equiv.refl _)
          (gatePrepared hδ g hw hb).gate.eval) =
      (((1 + δ)⁻¹ : ℝ) : ℂ) • replaceGate (stackLength r S δ) (WeightedGate.toGate g.terms) :=
  (Classical.choose_spec
    (WeightedGate.exists_prepared_effectReplacement_relabel hδ g.terms
      (fun t ht ↦ ⟨hw.2 t ht, hb.1 t ht⟩)
      ((congrArg norm (WeightedGate.ev_eq_gate_toGate g _)).symm.trans_le hw.1) hb.2
      (B' := fun s : ↥D ↦ gateOutSystem (stackLength r S δ) g s)
      fun s ↦ Equiv.cast (updateOn_of_mem s.2))).2.1

/-- The prepared gate of a gate is within `2 δ` of the gate followed by the preparation of its
stacks, read on the cell. Source: `04-compression.tex`, lines 210–212. -/
theorem gatePrepared_spec (hδ : 0 < δ) (g : WeightedGate D X Y)
    (hw : ‖WeightedGate.ev g (GateFamily.UniqueOutcome.outcome g)‖ ≤ 1 ∧ WeightedGate.IsAllowed g)
    (hb : (∀ t ∈ g.terms, t.2.effectCount ≤ r) ∧ (g.terms.map fun t ↦ ‖t.1‖).sum ≤ S) :
    ‖reindex (Equiv.piCongrRight fun s : ↥D ↦ Equiv.cast (updateOn_of_mem s.2)) (Equiv.refl _)
        (gatePrepared hδ g hw hb).gate.eval -
      (WeightedGate.prepGate (stackLength r S δ) g.terms).op *
        gate (WeightedGate.toGate g.terms)‖ ≤ 2 * δ :=
  (Classical.choose_spec
    (WeightedGate.exists_prepared_effectReplacement_relabel hδ g.terms
      (fun t ht ↦ ⟨hw.2 t ht, hb.1 t ht⟩)
      ((congrArg norm (WeightedGate.ev_eq_gate_toGate g _)).symm.trans_le hw.1) hb.2
      (B' := fun s : ↥D ↦ gateOutSystem (stackLength r S δ) g s)
      fun s ↦ Equiv.cast (updateOn_of_mem s.2))).2.2

end Gate

/-! #### The replacement -/

/-- **The source-only replacement**: every gate replaced by its prepared gate followed by the
relabelling that reads its stacks as its auxiliary factor, every later part run beside the auxiliary
registers of the earlier part. No evaluation or approximation identity is input data. Source:
`04-compression.tex`, lines 199–217. -/
def replacement {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] →
    [∀ p, DecidableEq (Y p)] → (c : EffectCircuit X Y) →
    c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed → IsExpansionBounded r S c →
      SourceCircuit X (fun p ↦ auxiliary (stackLength r S δ) c p × Y p)
  | X, _, _, _, _, _, PartyCircuit.done _, _, _ =>
    (PartyCircuit.relabel fun s ↦ Equiv.punitProd (X s) :
      SourceCircuit X fun p ↦ Unit × X p)
  | _, _, _, _, _, _, PartyCircuit.gate D hY g, hw, hb =>
    (PartyCircuit.gate D (gateOutSystem_of_notMem _ hY g) (gatePrepared hδ g hw hb)).comp
      (PartyCircuit.relabel (gateRelabelEquiv (stackLength r S δ) g))
  | X, Y, _, _, _, _, PartyCircuit.localOp p hY A, _, _ =>
    ((PartyCircuit.localOp p hY A).comp (PartyCircuit.relabel fun s ↦ Equiv.punitProd (Y s)) :
      SourceCircuit X fun p ↦ Unit × Y p)
  | X, Y, _, _, _, _, PartyCircuit.localOps A, _, _ =>
    ((PartyCircuit.localOps A).comp (PartyCircuit.relabel fun s ↦ Equiv.punitProd (Y s)) :
      SourceCircuit X fun p ↦ Unit × Y p)
  | _, _, _, _, _, _, PartyCircuit.comp c c', hw, hb =>
    (replacement hδ c hw.1 hb.1).comp
      ((SourceCircuit.frame (auxiliary (stackLength r S δ) c) (replacement hδ c' hw.2 hb.2)).comp
        (PartyCircuit.relabel fun _ ↦ Equiv.prodAssoc _ _ _))

section ReplacementRules

variable {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) {X Y Z : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The replacement of the empty circuit adds the trivial auxiliary factor. -/
theorem replacement_done
    (hw : (PartyCircuit.done X : EffectCircuit X X).IsAllowed WeightedGate.ev
      WeightedGate.IsAllowed)
    (hb : IsExpansionBounded r S (PartyCircuit.done X : EffectCircuit X X)) :
    replacement hδ (PartyCircuit.done X : EffectCircuit X X) hw hb =
      PartyCircuit.relabel fun s ↦ Equiv.punitProd (X s) :=
  rfl

/-- The replacement of one gate: its prepared gate, then the relabelling that reads its stacks as
its auxiliary factor. -/
theorem replacement_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : WeightedGate D X Y)
    (hw : ‖WeightedGate.ev g (GateFamily.UniqueOutcome.outcome g)‖ ≤ 1 ∧
      WeightedGate.IsAllowed g)
    (hb : (∀ t ∈ g.terms, t.2.effectCount ≤ r) ∧ (g.terms.map fun t ↦ ‖t.1‖).sum ≤ S) :
    replacement hδ (PartyCircuit.gate D hY g : EffectCircuit X Y) hw hb =
      (PartyCircuit.gate D (gateOutSystem_of_notMem _ hY g) (gatePrepared hδ g hw hb)).comp
        (PartyCircuit.relabel (gateRelabelEquiv (stackLength r S δ) g)) :=
  rfl

/-- The replacement of a local operation is the operation, then the trivial auxiliary factor. -/
theorem replacement_localOp (p : P) (hY : ∀ s ≠ p, Y s = X s) (A : Matrix (Y p) (X p) ℂ)
    (hw : (PartyCircuit.localOp p hY A : EffectCircuit X Y).IsAllowed WeightedGate.ev
      WeightedGate.IsAllowed)
    (hb : IsExpansionBounded r S (PartyCircuit.localOp p hY A : EffectCircuit X Y)) :
    replacement hδ (PartyCircuit.localOp p hY A : EffectCircuit X Y) hw hb =
      (PartyCircuit.localOp p hY A).comp (PartyCircuit.relabel fun s ↦ Equiv.punitProd (Y s)) :=
  rfl

/-- The replacement of local operations at every party is the operations, then the trivial auxiliary
factor. -/
theorem replacement_localOps (A : ∀ p, Matrix (Y p) (X p) ℂ)
    (hw : (PartyCircuit.localOps A : EffectCircuit X Y).IsAllowed WeightedGate.ev
      WeightedGate.IsAllowed)
    (hb : IsExpansionBounded r S (PartyCircuit.localOps A : EffectCircuit X Y)) :
    replacement hδ (PartyCircuit.localOps A : EffectCircuit X Y) hw hb =
      (PartyCircuit.localOps A).comp (PartyCircuit.relabel fun s ↦ Equiv.punitProd (Y s)) :=
  rfl

/-- The replacement of a composition: the first replacement, then the second beside the auxiliary
registers of the first, then the regrouping of the auxiliary registers. -/
theorem replacement_comp [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] (c : EffectCircuit X Y)
    (c' : EffectCircuit Y Z) (hw : (PartyCircuit.comp c c').IsAllowed WeightedGate.ev
      WeightedGate.IsAllowed) (hb : IsExpansionBounded r S (PartyCircuit.comp c c')) :
    replacement hδ (PartyCircuit.comp c c') hw hb =
      (replacement hδ c hw.1 hb.1).comp
        ((SourceCircuit.frame (auxiliary (stackLength r S δ) c)
          (replacement hδ c' hw.2 hb.2)).comp
          (PartyCircuit.relabel fun _ ↦ Equiv.prodAssoc _ _ _)) :=
  rfl

end ReplacementRules

/-- **The replacement is allowed**: its local operations are contractions (the prepared gates carry
their bounds). Source: `04-compression.tex`, lines 199–217. -/
theorem isAllowed_replacement {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] →
    [∀ p, DecidableEq (Y p)] → (c : EffectCircuit X Y) →
    (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) → (hb : IsExpansionBounded r S c) →
    (c.replacement hδ hw hb).IsAllowed PreparedGate.ev fun _ _ _ _ _ _ _ _ ↦ True
  | _, _, iF, iD, iF', iD', PartyCircuit.done _, _, _ => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    obtain rfl : iD' = iD := Subsingleton.elim _ _
    exact fun _ ↦ l2_opNorm_toMatrix_toPEquiv_le _
  | _, _, _, _, _, _, PartyCircuit.gate _ _ _, _, _ =>
    ⟨⟨PreparedGate.norm_ev_le_one _ _, trivial⟩, PartyCircuit.isAllowed_relabel _ _⟩
  | _, _, _, _, _, _, PartyCircuit.localOp _ _ _, hw, _ => ⟨hw, PartyCircuit.isAllowed_relabel _ _⟩
  | _, _, _, _, _, _, PartyCircuit.localOps _, hw, _ => ⟨hw, PartyCircuit.isAllowed_relabel _ _⟩
  | _, _, _, _, _, _, PartyCircuit.comp c c', hw, hb =>
    ⟨isAllowed_replacement hδ c hw.1 hb.1,
      PartyCircuit.isAllowed_frame _ _ PreparedGate.isCompatible_frame
        (fun _ _ _ _ _ _ _ _ h ↦ h) (isAllowed_replacement hδ c' hw.2 hb.2),
      PartyCircuit.isAllowed_relabel _ _⟩

/-- The replacement is a contraction. -/
theorem norm_op_replacement_le_one [Fintype P] {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) {X Y : P → Type}
    [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (c : EffectCircuit X Y) (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed)
    (hb : IsExpansionBounded r S c) : ‖(c.replacement hδ hw hb).op‖ ≤ 1 :=
  SourceCircuit.norm_op_le_one (isAllowed_replacement hδ c hw hb).isLocalContractive

end EffectCircuit

/-! ### Words without sources as source circuits -/

namespace SourceCircuit

/-- A word without sources as a source circuit of exact operations. Source: `04-compression.tex`,
lines 21–36 and 210–217. -/
def ofLocalWord : {X Y : P → Type} → (w : Word X Y) → w.sources = [] → SourceCircuit X Y
  | _, _, PartyCircuit.done X, _ => PartyCircuit.done X
  | _, _, PartyCircuit.gate _ _ _, h => absurd h (List.cons_ne_nil _ _)
  | _, _, PartyCircuit.localOp p hY A, _ => PartyCircuit.localOp p hY A
  | _, _, PartyCircuit.localOps A, _ => PartyCircuit.localOps A
  | _, _, PartyCircuit.comp w w', h =>
    PartyCircuit.comp (ofLocalWord w (List.append_eq_nil_iff.mp h).2)
      (ofLocalWord w' (List.append_eq_nil_iff.mp h).1)

/-- The conversion keeps the operator. -/
theorem op_ofLocalWord [Fintype P] : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] →
    (w : Word X Y) → (h : w.sources = []) → (ofLocalWord w h).op = w.op
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, PartyCircuit.gate _ _ _, h => absurd h (List.cons_ne_nil _ _)
  | _, _, _, _, PartyCircuit.localOp p hY A, _ =>
    (PartyCircuit.op_localOp _ p hY A).trans (PartyCircuit.op_localOp _ p hY A).symm
  | _, _, _, _, PartyCircuit.localOps A, _ =>
    (PartyCircuit.op_localOps _ A).trans (PartyCircuit.op_localOps _ A).symm
  | _, _, _, _, PartyCircuit.comp w w', h => by
    change PartyCircuit.op _ (PartyCircuit.comp (ofLocalWord w _) (ofLocalWord w' _)) = _
    rw [PartyCircuit.op_comp, Word.op_comp]
    exact congrArg₂ (· * ·) (op_ofLocalWord w' _) (op_ofLocalWord w _)

/-- Exact local operations stay allowed. -/
theorem isAllowed_ofLocalWord : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : Word X Y) → (h : w.sources = []) → w.IsAllowed →
      (ofLocalWord w h).IsAllowed PreparedGate.ev fun _ _ _ _ _ _ _ _ ↦ True
  | _, _, _, _, PartyCircuit.done _, _, _ => trivial
  | _, _, _, _, PartyCircuit.gate _ _ _, h, _ => absurd h (List.cons_ne_nil _ _)
  | _, _, _, _, PartyCircuit.localOp _ _ _, _, hw => hw
  | _, _, _, _, PartyCircuit.localOps _, _, hw => hw
  | _, _, _, _, PartyCircuit.comp w w', _, hw =>
    ⟨isAllowed_ofLocalWord w _ hw.1, isAllowed_ofLocalWord w' _ hw.2⟩

/-- A word without sources gives a source circuit without gates. -/
theorem numGates_ofLocalWord : {X Y : P → Type} → (w : Word X Y) → (h : w.sources = []) →
    (ofLocalWord w h).numGates = 0
  | _, _, PartyCircuit.done _, _ => rfl
  | _, _, PartyCircuit.gate _ _ _, h => absurd h (List.cons_ne_nil _ _)
  | _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, PartyCircuit.comp w w', _ =>
    congrArg₂ (· + ·) (numGates_ofLocalWord w _) (numGates_ofLocalWord w' _)

end SourceCircuit

end QuantumCircuit.Party
