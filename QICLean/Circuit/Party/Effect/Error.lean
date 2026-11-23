/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Effect.Replacement
import QICLean.Analysis.TraceNorm.SubnormalizedPureStateError
import QICLean.Channel.Dilation.ChronologicalGarbage

/-!
# Error of the source-only replacement, operators and physical densities

The *reference* of an effect circuit `c` is the circuit followed by the preparation of its
auxiliary vector: `|Γ⟩ ⊗ op c`, read along the pairing of configurations of the auxiliary
registers and the output (`EffectCircuit.referenceOp`). The source-only replacement is within
`2 δ` of the reference at every gate, so within `2 δ N` of it for a circuit of `N` gates
(`norm_replacement_sub_reference_le`, `eq:compression-effect-circuit-error`). Discarding the
normalized auxiliary vector does not change the physical density of the original circuit, so
the physical density of the replacement is within `4 δ N` of it in trace norm
(`rectangularTraceNorm_replacement_density_sub_le`).

## Main definitions

* `QuantumCircuit.Party.EffectCircuit.referenceOp`.
* `QuantumCircuit.Party.extendedReadout`,
  `QuantumCircuit.Party.EffectCircuit.originalPhysicalDensity`, `replacementPhysicalDensity`.

## Main results

* `QuantumCircuit.Party.EffectCircuit.norm_referenceOp_le_one`,
  `QuantumCircuit.Party.EffectCircuit.referenceOp_comp` — the reference of a composition.
* `QuantumCircuit.Party.EffectCircuit.referenceOp_gate`, `norm_gate_sub_reference_le` — one
  replaced gate.
* `QuantumCircuit.Party.EffectCircuit.norm_replacement_sub_reference_le` — the operator error.
* `QuantumCircuit.Party.EffectCircuit.rectangularTraceNorm_replacement_density_sub_le` — the
  density error.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
  `eq:compression-effect-circuit-error`, `04-compression.tex`, lines 199–229.
-/

noncomputable section

open Matrix ManyBody
open scoped Kronecker Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

open GateExpansion

variable {P : Type} [Fintype P] [DecidableEq P]

/-- Adding the trivial factor in front of every basis is the preparation of the unit vector of the
trivial system. -/
private theorem op_relabel_punitProd (Z : P → Type) [∀ p, Fintype (Z p)]
    [∀ p, DecidableEq (Z p)] :
    (PartyCircuit.relabel (G := PreparedGate) fun s ↦ Equiv.punitProd (Z s)).op PreparedGate.ev =
      prepMatrix (Equiv.arrowProdEquivProdArrow P (fun _ ↦ Unit) Z)
        (EuclideanSpace.single (fun _ ↦ ()) 1) := by
  rw [PartyCircuit.op_relabel]
  ext y x
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq,
    prepMatrix_apply]
  have h1 : (EuclideanSpace.single (fun _ ↦ ()) (1 : ℂ) :
      EuclideanSpace ℂ (Config fun _ : P ↦ Unit))
        ((Equiv.arrowProdEquivProdArrow P (fun _ ↦ Unit) Z) y).1 = 1 := by
    rw [show ((Equiv.arrowProdEquivProdArrow P (fun _ ↦ Unit) Z) y).1 = fun _ ↦ () from
      Subsingleton.elim _ _]
    simp
  rw [h1]
  exact if_congr (by simp [funext_iff, Equiv.arrowProdEquivProdArrow]) rfl rfl

/-- A matrix bounds its action on a vector by its operator norm (`Matrix.l2_opNorm_mulVec`, read on
`Matrix.toEuclideanLin`). -/
private theorem norm_toEuclideanLin_apply_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin A x‖ ≤ ‖A‖ * ‖x‖ :=
  A.l2_opNorm_mulVec x

/-- Reading the rows of a matrix along an equivalence does not increase its operator norm. -/
private theorem norm_submatrix_rows_le {m n m' : Type*} [Fintype m] [Fintype n] [Fintype m']
    [DecidableEq n] (M : Matrix m n ℂ) (e : m' ≃ m) : ‖M.submatrix e id‖ ≤ ‖M‖ :=
  l2_opNorm_reindex_le e.symm (Equiv.refl n) M

/-- The difference of two reindexed matrices beside an identity factor is bounded by the difference
of the matrices. -/
private theorem norm_reindex_one_kronecker_sub_le {a m n m' n' : Type*} [Finite a]
    [DecidableEq a]
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] [DecidableEq n] [DecidableEq n']
    (e : m' ≃ a × m) (f : n' ≃ a × n) (U V : Matrix m n ℂ) :
    ‖reindex e.symm f.symm ((1 : Matrix a a ℂ) ⊗ₖ U) -
        reindex e.symm f.symm ((1 : Matrix a a ℂ) ⊗ₖ V)‖ ≤ ‖U - V‖ := by
  have := Fintype.ofFinite a
  rw [show reindex e.symm f.symm ((1 : Matrix a a ℂ) ⊗ₖ U) -
      reindex e.symm f.symm ((1 : Matrix a a ℂ) ⊗ₖ V) =
        reindex e.symm f.symm ((1 : Matrix a a ℂ) ⊗ₖ U - (1 : Matrix a a ℂ) ⊗ₖ V) from rfl,
    show (1 : Matrix a a ℂ) ⊗ₖ U - (1 : Matrix a a ℂ) ⊗ₖ V = (1 : Matrix a a ℂ) ⊗ₖ (U - V) by
      ext; simp [mul_sub]]
  exact (l2_opNorm_reindex_le _ _ _).trans (l2_opNorm_one_kronecker_le _)

/-! ### The reference of an effect circuit -/

namespace EffectCircuit

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- The reference of an effect circuit: the circuit followed by the preparation of its auxiliary
vector, in front of the output. Source: `04-compression.tex`, lines 210–217. -/
def referenceOp (m : ℕ) (c : EffectCircuit X Y) :
    Matrix (Config fun p ↦ auxiliary m c p × Y p) (Config X) ℂ :=
  prepMatrix (Equiv.arrowProdEquivProdArrow P (auxiliary m c) Y) (c.auxiliaryVector m) *
    c.op WeightedGate.ev

/-- The reference of an allowed circuit is a contraction. Source: `04-compression.tex`, lines
210–217. -/
theorem norm_referenceOp_le_one (c : EffectCircuit X Y)
    (hc : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) (m : ℕ) :
    ‖c.referenceOp m‖ ≤ 1 :=
  l2_opNorm_mul_le_one _ _ ((norm_prepMatrix_le _ _).trans (norm_auxiliaryVector c hc m).le)
    (PartyCircuit.norm_op_le_one _ hc)

/-- The auxiliary vector of a composition is the product of those of its parts. -/
theorem auxiliaryVector_comp_apply (m : ℕ) {X Y Z : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (c : EffectCircuit X Y) (c' : EffectCircuit Y Z)
    (a : Config (auxiliary m (PartyCircuit.comp c c'))) :
    auxiliaryVector m (PartyCircuit.comp c c') a =
      auxiliaryVector m c (fun p ↦ (a p).1) * auxiliaryVector m c' (fun p ↦ (a p).2) :=
  rfl

/-- **The reference of a composition**: the reference of the first part, then the reference of the
second part beside the auxiliary registers of the first, then the regrouping of the auxiliary
registers. Source: `04-compression.tex`, lines 210–217. -/
theorem referenceOp_comp (m : ℕ) {X Y Z : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    [∀ p, Fintype (Z p)] [∀ p, DecidableEq (Z p)] (c : EffectCircuit X Y)
    (c' : EffectCircuit Y Z) :
    referenceOp m (PartyCircuit.comp c c') =
      (PartyCircuit.relabel (G := PreparedGate) fun _ ↦ Equiv.prodAssoc _ _ _).op
          PreparedGate.ev *
        (reindex (Equiv.arrowProdEquivProdArrow P (auxiliary m c)
            fun p ↦ auxiliary m c' p × Z p).symm
          (Equiv.arrowProdEquivProdArrow P (auxiliary m c) Y).symm
          ((1 : Matrix (Config (auxiliary m c)) (Config (auxiliary m c)) ℂ) ⊗ₖ
            referenceOp m c') * referenceOp m c) := by
  refine Eq.trans ?_ (PartyCircuit.op_relabel_mul _ _ _).symm
  ext w x
  rw [submatrix_apply, Matrix.mul_apply,
    ← (Equiv.arrowProdEquivProdArrow P (auxiliary m c) Y).symm.sum_comp, Fintype.sum_prod_type]
  simp only [referenceOp, prepMatrix_mul_apply, PartyCircuit.op_comp, reindex_apply,
    submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply, kroneckerMap_apply, one_apply,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [auxiliaryVector_comp_apply]
  exact (by intros; ring : ∀ a b A B : ℂ, a * b * (A * B) = b * A * (a * B)) _ _ _ _

/-- **The reference of one gate**: the gate followed by the preparation of its stacks, placed on the
cell, then the relabelling that reads the stacks as the auxiliary factor of the gate. Source:
`04-compression.tex`, lines 210–212. -/
theorem referenceOp_gate (m : ℕ) (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : WeightedGate D X Y) :
    referenceOp m (PartyCircuit.gate D hY g : EffectCircuit X Y) =
      (PartyCircuit.relabel (G := PreparedGate) (gateRelabelEquiv m g)).op PreparedGate.ev *
        placeBetween D (gateOutSystem_of_notMem m hY g)
          (reindex (Equiv.piCongrRight fun s : ↥D ↦ Equiv.cast (updateOn_of_mem s.2)).symm
            (Equiv.refl _)
            ((WeightedGate.prepGate m g.terms).op * gate (WeightedGate.toGate g.terms))) := by
  set e : ∀ s : ↥D, gateOutSystem m g s ≃ WeightedGate.gateOut m g.terms s :=
    fun s ↦ Equiv.cast (updateOn_of_mem s.2)
  refine Eq.trans ?_ (PartyCircuit.op_relabel_mul _ _ _).symm
  ext w x
  simp only [referenceOp, prepMatrix_mul_apply, submatrix_apply, id, placeBetween_apply,
    PartyCircuit.op_gate]
  by_cases h : ∀ (v : P) (hv : v ∉ D), cast (hY v hv)
      (((Equiv.arrowProdEquivProdArrow P (auxiliary m (PartyCircuit.gate D hY g)) Y) w).2 v) =
        x v
  · have h' : ∀ (v : P) (hv : v ∉ D), cast (gateOutSystem_of_notMem m hY g v hv)
        ((Equiv.piCongrRight (gateRelabelEquiv m g)) w v) = x v := fun v hv ↦
      (cast_gateRelabelEquiv_of_notMem m hY g hv (w v)).trans (h v hv)
    rw [ite_eq_left h]
    refine Eq.trans ?_ (ite_eq_left h').symm
    change _ = ((WeightedGate.prepGate m g.terms).op * gate (WeightedGate.toGate g.terms))
      (fun s ↦ e s (gateRelabelEquiv m g s (w s))) (fun v ↦ x v)
    rw [WeightedGate.op_prepGate, Matrix.reindex_symm_prepMatrix, prepMatrix_mul_apply,
      Equiv.trans_apply, WeightedGate.gateEquiv_apply]
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    rw [WeightedGate.ev_eq_gate_toGate]
    have hu : ∀ s : ↥D, (WeightedGate.auxFactorEquiv m g.terms s)
        ((Equiv.cast (updateOn_of_mem s.2)) ((gateRelabelEquiv m g s) (w s))) =
          (Equiv.cast (updateOn_of_mem s.2) (w s).1, (w s).2) := fun s ↦
      (congrArg (WeightedGate.auxFactorEquiv m g.terms s)
        (cast_gateRelabelEquiv_of_mem m g s (w s))).trans (Equiv.apply_symm_apply _ _)
    refine congrArg₂ (· * ·) ?_ ?_
    · exact congrArg (fun a ↦ (inventoryVector m (WeightedGate.toGate g.terms)).ofLp
        (WeightedGate.auxFactorConfigEquiv m g.terms a))
          (funext fun s ↦ (congrArg Prod.fst (hu s)).symm)
    · exact congrFun (congrArg _ (funext fun s ↦ (congrArg Prod.snd (hu s)).symm)) _
  · have h' : ¬ ∀ (v : P) (hv : v ∉ D), cast (gateOutSystem_of_notMem m hY g v hv)
        ((Equiv.piCongrRight (gateRelabelEquiv m g)) w v) = x v := fun h' ↦ h fun v hv ↦
      (cast_gateRelabelEquiv_of_notMem m hY g hv (w v)).symm.trans (h' v hv)
    exact ((congrArg (fun t ↦ _ * t) (ite_eq_right h)).trans
      (mul_zero _)).trans (ite_eq_right h').symm

/-- **One replaced gate is within `2 δ` of its reference.** Source: `04-compression.tex`, lines
199–212. -/
theorem norm_gate_sub_reference_le {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (D : Finset P)
    (hY : ∀ s ∉ D, Y s = X s) (g : WeightedGate D X Y)
    (hw : ‖WeightedGate.ev g (GateFamily.UniqueOutcome.outcome g)‖ ≤ 1 ∧
      WeightedGate.IsAllowed g)
    (hb : (∀ t ∈ g.terms, t.2.effectCount ≤ r) ∧ (g.terms.map fun t ↦ ‖t.1‖).sum ≤ S) :
    ‖(replacement hδ (PartyCircuit.gate D hY g : EffectCircuit X Y) hw hb).op -
      referenceOp (stackLength r S δ) (PartyCircuit.gate D hY g : EffectCircuit X Y)‖ ≤
        2 * δ := by
  set m := stackLength r S δ
  set e : ∀ s : ↥D, gateOutSystem m g s ≃ WeightedGate.gateOut m g.terms s :=
    fun s ↦ Equiv.cast (updateOn_of_mem s.2)
  set N := reindex (Equiv.piCongrRight e).symm (Equiv.refl _)
    ((WeightedGate.prepGate m g.terms).op * gate (WeightedGate.toGate g.terms))
  have hN : ‖(gatePrepared hδ g hw hb).gate.eval - N‖ ≤ 2 * δ := by
    refine le_trans (le_of_eq ?_) ((l2_opNorm_reindex_le (Equiv.piCongrRight e).symm
      (Equiv.refl _) _).trans (gatePrepared_spec hδ g hw hb))
    congr 1
    ext
    simp [N, e]
    rfl
  have href := referenceOp_gate m D hY g
  have hrep : (replacement hδ (PartyCircuit.gate D hY g : EffectCircuit X Y) hw hb).op =
      (PartyCircuit.relabel (G := PreparedGate) (gateRelabelEquiv m g)).op PreparedGate.ev *
        placeBetween D (gateOutSystem_of_notMem m hY g) (gatePrepared hδ g hw hb).gate.eval :=
    (PartyCircuit.op_comp _ _ _).trans (congrArg _ (PartyCircuit.op_gate _ _ _ _))
  rw [hrep, href]
  refine (le_of_eq (congrArg norm (Matrix.mul_sub _ _ _).symm)).trans ?_
  refine (le_of_eq (congrArg norm (PartyCircuit.op_relabel_mul _ _ _))).trans ?_
  refine (l2_opNorm_reindex_le (Equiv.piCongrRight (gateRelabelEquiv m g)).symm (Equiv.refl _)
    _).trans ?_
  rw [placeBetween_sub]
  exact (norm_placeBetween_le _ _).trans hN

/-- **The replacement is within `2 δ` per gate of the reference**: `‖op c' - |Γ⟩ ⊗ op c‖ ≤ 2 δ N`
for a circuit of `N` gates, every gate counted (`numGates`, gates on one party or none included).
Source: `eq:compression-effect-circuit-error`, `04-compression.tex`, lines 210–216. -/
theorem norm_replacement_sub_reference_le {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) : {X Y : P → Type} →
    [∀ p, Fintype (X p)] → [∀ p, DecidableEq (X p)] → [∀ p, Fintype (Y p)] →
    [∀ p, DecidableEq (Y p)] → (c : EffectCircuit X Y) →
    (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) → (hb : IsExpansionBounded r S c) →
    ‖(c.replacement hδ hw hb).op - c.referenceOp (stackLength r S δ)‖ ≤ 2 * δ * c.numGates
  | X, _, iF, iD, iF', iD', PartyCircuit.done _, hw, hb => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    obtain rfl : iD' = iD := Subsingleton.elim _ _
    have h : (replacement hδ (PartyCircuit.done X : EffectCircuit X X) hw hb).op =
        referenceOp (stackLength r S δ) (PartyCircuit.done X : EffectCircuit X X) :=
      (op_relabel_punitProd X).trans (Matrix.mul_one _).symm
    rw [h, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hδ.le) (Nat.cast_nonneg _)
  | _, _, _, _, iF', iD', @PartyCircuit.gate _ _ _ _ iF iD D hY g, hw, hb => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    obtain rfl : iD' = iD := Subsingleton.elim _ _
    refine (norm_gate_sub_reference_le hδ D hY g hw hb).trans_eq ?_
    change 2 * δ = 2 * δ * ((1 : ℕ) : ℝ)
    rw [Nat.cast_one, mul_one]
  | _, Y, _, _, iF', iD', @PartyCircuit.localOp _ _ _ _ iF iD p hY A, hw, hb => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    obtain rfl : iD' = iD := Subsingleton.elim _ _
    have h : (replacement hδ (PartyCircuit.localOp p hY A : EffectCircuit _ Y) hw hb).op =
        referenceOp (stackLength r S δ) (PartyCircuit.localOp p hY A : EffectCircuit _ Y) :=
      (PartyCircuit.op_comp _ _ _).trans (congrArg₂ (· * ·) (op_relabel_punitProd Y)
        ((PartyCircuit.op_localOp _ p hY A).trans (PartyCircuit.op_localOp _ p hY A).symm))
    rw [h, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hδ.le) (Nat.cast_nonneg _)
  | _, Y, _, _, iF', iD', @PartyCircuit.localOps _ _ _ _ iF iD A, hw, hb => by
    obtain rfl : iF' = iF := Subsingleton.elim _ _
    obtain rfl : iD' = iD := Subsingleton.elim _ _
    have h : (replacement hδ (PartyCircuit.localOps A : EffectCircuit _ Y) hw hb).op =
        referenceOp (stackLength r S δ) (PartyCircuit.localOps A : EffectCircuit _ Y) :=
      (PartyCircuit.op_comp _ _ _).trans (congrArg₂ (· * ·) (op_relabel_punitProd Y)
        ((PartyCircuit.op_localOps _ A).trans (PartyCircuit.op_localOps _ A).symm))
    rw [h, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hδ.le) (Nat.cast_nonneg _)
  | _, Z, _, _, _, _, @PartyCircuit.comp _ _ _ Y _ _ _ c c', hw, hb => by
    rw [referenceOp_comp]
    change ‖PartyCircuit.op PreparedGate.ev (PartyCircuit.comp (replacement hδ c hw.1 hb.1)
        (PartyCircuit.comp (SourceCircuit.frame _ (replacement hδ c' hw.2 hb.2))
          (PartyCircuit.relabel fun _ ↦ Equiv.prodAssoc _ _ _))) - _‖ ≤
        2 * δ * ((c.numGates + c'.numGates : ℕ) : ℝ)
    rw [PartyCircuit.op_comp, PartyCircuit.op_comp, Matrix.mul_assoc]
    refine (le_of_eq (congrArg norm (Matrix.mul_sub _ _ _).symm)).trans ?_
    rw [PartyCircuit.op_relabel_mul]
    refine (norm_submatrix_rows_le _ _).trans ?_
    have hF1 : ‖PartyCircuit.op PreparedGate.ev (SourceCircuit.frame
        (auxiliary (stackLength r S δ) c) (replacement hδ c' hw.2 hb.2))‖ ≤ 1 :=
      PartyCircuit.norm_op_le_one _ (PartyCircuit.isAllowed_frame _ _
        PreparedGate.isCompatible_frame (fun _ _ _ _ _ _ _ _ h ↦ h)
        (isAllowed_replacement hδ c' hw.2 hb.2))
    refine (Matrix.norm_mul_sub_mul_le _ _ _ _ hF1 (norm_referenceOp_le_one c hw.1 _)).trans ?_
    have h3 : ‖PartyCircuit.op PreparedGate.ev (SourceCircuit.frame
          (auxiliary (stackLength r S δ) c) (replacement hδ c' hw.2 hb.2)) -
        reindex (Equiv.arrowProdEquivProdArrow P (auxiliary (stackLength r S δ) c)
            fun p ↦ auxiliary (stackLength r S δ) c' p × Z p).symm
          (Equiv.arrowProdEquivProdArrow P (auxiliary (stackLength r S δ) c) Y).symm
          ((1 : Matrix (Config (auxiliary (stackLength r S δ) c))
            (Config (auxiliary (stackLength r S δ) c)) ℂ) ⊗ₖ
              referenceOp (stackLength r S δ) c')‖ ≤
        ‖(replacement hδ c' hw.2 hb.2).op - referenceOp (stackLength r S δ) c'‖ := by
      refine (le_of_eq (congrArg (fun M ↦ ‖M - reindex (Equiv.arrowProdEquivProdArrow P
          (auxiliary (stackLength r S δ) c) fun p ↦ auxiliary (stackLength r S δ) c' p × Z p).symm
          (Equiv.arrowProdEquivProdArrow P (auxiliary (stackLength r S δ) c) Y).symm
          ((1 : Matrix (Config (auxiliary (stackLength r S δ) c))
            (Config (auxiliary (stackLength r S δ) c)) ℂ) ⊗ₖ
              referenceOp (stackLength r S δ) c')‖)
        (SourceCircuit.op_frame (auxiliary (stackLength r S δ) c)
          (replacement hδ c' hw.2 hb.2)))).trans ?_
      exact norm_reindex_one_kronecker_sub_le _ _ _ _
    have h1 := norm_replacement_sub_reference_le hδ c hw.1 hb.1
    have h2 := norm_replacement_sub_reference_le hδ c' hw.2 hb.2
    push_cast
    linarith

end EffectCircuit

/-! ### Physical densities -/

variable {Phys Env : Type*} [Fintype Phys] [Fintype Env]

/-- The readout `K` of the output, with the auxiliary registers grouped into the environment.
Source: `04-compression.tex`, lines 223–227. -/
def extendedReadout {A Y : P → Type} [∀ p, Fintype (A p)] [∀ p, DecidableEq (A p)]
    [∀ p, Fintype (Y p)] (K : Matrix (Phys × Env) (Config Y) ℂ) :
    Matrix (Phys × (Env × Config A)) (Config fun p ↦ A p × Y p) ℂ :=
  reindex (Equiv.prodAssoc _ _ _)
    ((Equiv.arrowProdEquivProdArrow P A Y).trans (Equiv.prodComm _ _)).symm
    (K ⊗ₖ (1 : Matrix (Config A) (Config A) ℂ))

omit [Fintype Phys] [Fintype Env] in
/-- The extended readout of a product vector is the readout with the auxiliary vector appended. -/
theorem toEuclideanLin_extendedReadout_prepMatrix {A Y : P → Type} [∀ p, Fintype (A p)]
    [∀ p, DecidableEq (A p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (γ : EuclideanSpace ℂ (Config A))
    (v : EuclideanSpace ℂ (Config Y)) :
    Matrix.toEuclideanLin (extendedReadout K)
        (Matrix.toEuclideanLin (prepMatrix (Equiv.arrowProdEquivProdArrow P A Y) γ) v) =
      appendAuxiliaryVector (Matrix.toEuclideanLin K v) γ := by
  ext ⟨ph, en, a⟩
  simp only [Matrix.ofLp_toLpLin, Matrix.toLin'_apply, appendAuxiliaryVector, mulVec,
    dotProduct]
  rw [← (Equiv.arrowProdEquivProdArrow P A Y).symm.sum_comp, Fintype.sum_prod_type]
  simp only [extendedReadout, reindex_apply, submatrix_apply, Equiv.symm_symm,
    Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodComm_apply, Prod.swap_prod_mk,
    Equiv.prodAssoc_symm_apply, kroneckerMap_apply, one_apply, prepMatrix_apply, mul_ite,
    mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact Finset.sum_congr rfl fun y _ ↦ by ring

/-- The extended readout of a contraction is a contraction. -/
theorem norm_extendedReadout_le_one {A Y : P → Type} [∀ p, Fintype (A p)]
    [∀ p, DecidableEq (A p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1) : ‖extendedReadout (A := A) K‖ ≤ 1 :=
  (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_kronecker_one_le K).trans hK)

namespace EffectCircuit

variable {X Y : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- The physical density of the original circuit on the input `x`, subnormalization kept. Source:
`04-compression.tex`, lines 218–227. -/
def originalPhysicalDensity (c : EffectCircuit X Y) (K : Matrix (Phys × Env) (Config Y) ℂ)
    (x : EuclideanSpace ℂ (Config X)) : Matrix Phys Phys ℂ :=
  let y := Matrix.toEuclideanLin K (Matrix.toEuclideanLin (c.op WeightedGate.ev) x)
  partialTraceRight (euclideanOuterProduct y y)

/-- The physical density of the source-only replacement, its auxiliary registers and the environment
discarded. Source: `04-compression.tex`, lines 218–227. -/
def replacementPhysicalDensity {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (c : EffectCircuit X Y)
    (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) (hb : IsExpansionBounded r S c)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (x : EuclideanSpace ℂ (Config X)) :
    Matrix Phys Phys ℂ :=
  let y := Matrix.toEuclideanLin (extendedReadout (A := auxiliary (stackLength r S δ) c) K)
    (Matrix.toEuclideanLin (c.replacement hδ hw hb).op x)
  partialTraceRight (euclideanOuterProduct y y)

/-- **The physical density error of the replacement** is at most `4 δ N` in trace norm, `N` the
number of gates. The circuit, the auxiliary vector and the readout are explicit. Source:
`eq:compression-effect-circuit-error`, `04-compression.tex`, lines 199–229. -/
theorem rectangularTraceNorm_replacement_density_sub_le [DecidableEq Phys]
    {r : ℕ} {S δ : ℝ} (hδ : 0 < δ) (c : EffectCircuit X Y)
    (hw : c.IsAllowed WeightedGate.ev WeightedGate.IsAllowed) (hb : IsExpansionBounded r S c)
    (K : Matrix (Phys × Env) (Config Y) ℂ) (hK : ‖K‖ ≤ 1) (x : EuclideanSpace ℂ (Config X))
    (hx : ‖x‖ ≤ 1) :
    rectangularTraceNorm (c.replacementPhysicalDensity hδ hw hb K x -
      c.originalPhysicalDensity K x) ≤ 4 * δ * c.numGates := by
  set m := stackLength r S δ
  set R := (c.replacement hδ hw hb).op
  set E := extendedReadout (A := auxiliary m c) K
  set v := Matrix.toEuclideanLin (c.op WeightedGate.ev) x
  have hE : ‖E‖ ≤ 1 := norm_extendedReadout_le_one K hK
  have hle : ∀ {a b : ℝ}, a ≤ 1 → 0 ≤ b → b ≤ 1 → a * b ≤ 1 :=
    fun ha hb0 hb ↦ (mul_le_mul ha hb hb0 zero_le_one).trans_eq (one_mul 1)
  have hv : ‖Matrix.toEuclideanLin K v‖ ≤ 1 :=
    (norm_toEuclideanLin_apply_le K v).trans (hle hK (norm_nonneg _)
      ((norm_toEuclideanLin_apply_le _ x).trans
        (hle (PartyCircuit.norm_op_le_one _ hw) (norm_nonneg _) hx)))
  have hu : ‖Matrix.toEuclideanLin E (Matrix.toEuclideanLin R x)‖ ≤ 1 :=
    (norm_toEuclideanLin_apply_le E _).trans (hle hE (norm_nonneg _)
      ((norm_toEuclideanLin_apply_le _ x).trans
        (hle (norm_op_replacement_le_one hδ c hw hb) (norm_nonneg _) hx)))
  have key : Matrix.toEuclideanLin E (Matrix.toEuclideanLin (c.referenceOp m) x) =
      appendAuxiliaryVector (Matrix.toEuclideanLin K v) (c.auxiliaryVector m) := by
    rw [referenceOp, Matrix.toLpLin_mul 2 2 2, LinearMap.comp_apply]
    exact toEuclideanLin_extendedReadout_prepMatrix K _ v
  have herr : ‖Matrix.toEuclideanLin E (Matrix.toEuclideanLin R x) -
      appendAuxiliaryVector (Matrix.toEuclideanLin K v) (c.auxiliaryVector m)‖ ≤
        2 * δ * c.numGates := by
    rw [← key, ← map_sub, ← LinearMap.sub_apply, ← map_sub]
    refine (norm_toEuclideanLin_apply_le E _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) hE).trans
        ((norm_toEuclideanLin_apply_le _ x).trans ?_))
    exact (mul_le_of_le_one_right (norm_nonneg _) hx).trans
      (norm_replacement_sub_reference_le hδ c hw hb)
  have h := Matrix.rectangularTraceNorm_appendAuxiliaryVector_error_le_two
    (Matrix.toEuclideanLin K v) (c.auxiliaryVector m) _ (norm_auxiliaryVector c hw m) hv hu
  refine h.trans ?_
  linarith

end EffectCircuit

end QuantumCircuit.Party
