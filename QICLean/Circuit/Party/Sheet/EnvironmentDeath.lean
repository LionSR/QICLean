/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Sheet.EnvironmentBirth

/-!
# Death with a prescribed environment

Taking the adjoint of the distinct-party birth replaces its pair source by the
corresponding pair effect and reverses its local operations. The canonical map
is Hermitian, so the two circuits have the same operator in site coordinates.

Source: polynomial-PEPS, Lemma 6.5, `05-frames.tex`, lines 439–444.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party.Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [DecidableEq P]
  {q : ℕ} {S : Sheet ι P} {T E : Finset ι} {P₀ Q : P}

local notation "A" => RegionConfig (fun _ : ι ↦ Fin q) T
local notation "S'" => S.changeOwner T Q

variable (hTE : Disjoint T E) (hTP : ∀ x ∈ T, S.owner x = P₀)
  (hU : ∀ x ∉ T ∪ E, S.owner x = P₀) (hQP : Q ≠ P₀)

local notation "effect" σ =>
  PairEffectGate.ofAddPair hQP A A (WithLp.toLp 2 (SplittingData.s σ)) (S.system q)

/-- The death circuit applies the adjoints of the local birth matrices, then
the pair effect given by the splitting data. -/
noncomputable def environmentDeathChain
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    PartyCircuit (ChainGate (P := P)) ((S').system q) (S.system q) :=
  PartyCircuit.comp
    (PartyCircuit.localOps (fun r ↦ (environmentBirthFamily hTE hTP hU hQP σ r)ᴴ))
    (PartyCircuit.gate {Q, P₀} (effect σ).outside (.inr (effect σ)))

/-- The death circuit is the canonical birth operator read in the reverse
party bases. -/
theorem op_environmentDeathChain [Fintype P]
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentDeathChain hTE hTP hU hQP σ).op chainEv =
      reindex (blockConfigEquiv S.owner (fun _ ↦ Fin q)).symm
        (blockConfigEquiv (S').owner (fun _ ↦ Fin q)).symm
        (configBirthOp Finset.subset_union_left σ) := by
  have he : (PartyCircuit.gate {Q, P₀} (effect σ).outside
      (.inr (effect σ) : ChainGate _ _ _)).op chainEv =
        (Word.sourceAt hQP A A (WithLp.toLp 2 σ.s) (S.system q)).opᴴ := by
    have hconfig : (effect σ).configEquiv = addPairConfigEquiv hQP A A :=
      SourceGate.configEquiv_ofAddPair hQP A A (WithLp.toLp 2 σ.s) (S.system q)
    rw [ChainGate.op_gate_inr, Word.op_sourceAt, conjTranspose_prepMatrix, hconfig]
    rfl
  have h : (environmentDeathChain hTE hTP hU hQP σ).op chainEv =
      (environmentBirthWord hTE hTP hU hQP σ).opᴴ := by
    rw [environmentDeathChain, PartyCircuit.op_comp (P := P) (G := ChainGate), he,
      PartyCircuit.op_localOps, environmentBirthWord, Word.op_comp,
      show (Word.op (PartyCircuit.localOps (environmentBirthFamily hTE hTP hU hQP σ))) =
        piKronecker (environmentBirthFamily hTE hTP hU hQP σ) from PartyCircuit.op_localOps _ _,
      conjTranspose_mul, conjTranspose_piKronecker]
  rw [h, op_environmentBirthWord, conjTranspose_reindex,
    (configBirthOp_isHermitian Finset.subset_union_left σ).eq]

/-- The local operations and the pair effect of the death circuit are allowed. -/
theorem isAllowed_environmentDeathChain
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentDeathChain hTE hTP hU hQP σ).IsAllowed chainEv ChainGate.IsAllowed := by
  have hη := EuclideanSpace.norm_toLp_eq_one_of_star_dotProduct σ.star_s
  refine ⟨fun r ↦ ?_, (PairEffectGate.norm_ev_le _ ()).trans hη.le, hη⟩
  change ‖(environmentBirthFamily hTE hTP hU hQP σ r)ᴴ‖ ≤ 1
  rw [l2_opNorm_conjTranspose]
  exact (isAllowed_environmentBirthWord hTE hTP hU hQP σ).2 r

/-- The only parties acting in the death circuit are the two parties that
exchange ownership of the region. -/
theorem usesOnly_environmentDeathChain
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentDeathChain hTE hTP hU hQP σ).UsesOnly {P₀, Q} := by
  have h := usesOnly_environmentBirthWord hTE hTP hU hQP σ
  refine ⟨fun r hr ↦ ?_, h.1⟩
  obtain ⟨e, he⟩ := h.2 r hr
  refine ⟨e.symm, fun y x ↦ ?_⟩
  change (environmentBirthFamily hTE hTP hU hQP σ r)ᴴ y x = _
  rw [conjTranspose_apply, he]
  have hx : cast e x = y ↔ cast e.symm y = x := by
    constructor
    · intro h
      rw [← h, cast_cast, cast_eq]
    · intro h
      rw [← h, cast_cast, cast_eq]
  split_ifs <;> simp_all

/-- The death circuit has one gate, which is a pair effect. -/
theorem numGates_environmentDeathChain
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentDeathChain hTE hTP hU hQP σ).numGates = 1 :=
  rfl

/-- The death circuit has no pair sources. -/
theorem forallGate_isRight_environmentDeathChain
    (σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E)) :
    (environmentDeathChain hTE hTP hU hQP σ).ForallGate fun _ _ _ g ↦ Sum.isRight g :=
  ⟨trivial, rfl⟩

end QuantumCircuit.Party.Sheet
