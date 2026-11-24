/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Compression.PartialExpansion.Sources

/-!
# Substituted source vectors

The source vectors of a source circuit may be replaced at every source position and branch
label separately, keeping the order of the circuit and all remaining operations: the operator
with substituted vectors (`SourceCircuit.opWithSources`) and the branches of the partial
expansion with substituted vectors (`SourceCircuit.partialWithSources`), which keep every
untouched gate as a whole. The vectors of the gates give back the operator and the branches.
When no vector at an untouched gate is changed, the weighted sum of the substituted branches is
the substituted operator read on the affected parties and the exterior party
(`SourceCircuit.sum_coefficient_smul_op_partialWithSources`); this holds in particular when only
positions with an affected endpoint are substituted (`SourceCircuit.selectedSourceVectors`).

## Main definitions

* `QuantumCircuit.Party.PreparedSourceGate.branchWithSources`.
* `QuantumCircuit.Party.SourceCircuit.opWithSources`,
  `QuantumCircuit.Party.SourceCircuit.partialWithSources`,
  `QuantumCircuit.Party.SourceCircuit.selectedSourceVectors`.

## Main results

* `QuantumCircuit.Party.SourceCircuit.opWithSources_original`,
  `QuantumCircuit.Party.SourceCircuit.partialWithSources_original`.
* `QuantumCircuit.Party.SourceCircuit.sum_coefficient_smul_op_partialWithSources`,
  `QuantumCircuit.Party.SourceCircuit.sum_coefficient_smul_op_partialWithSources_selected`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 233–267 and 338–381 (equation `eq:compression-subset-expansion`).

Adapted from TNLean, `TNLean/Lattice/Compression/SourceCircuitSubstitution.lean` at commit
`a05f5d6d0a` (Apache-2.0). Changes: the operators are matrices; the frame and swap cases are
gone.
-/

open Matrix ManyBody

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

namespace PreparedSourceGate

variable [Fintype P] {ι : Type} [Fintype ι] {c : ι → ℂ} {X Y : P → Type} [∀ p, Fintype (X p)]
  [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]

/-- The branch of a label with prescribed vectors prepared in the slots of the gate, followed by
its remaining word. Source: Theorem 5.2, `04-compression.tex`, lines 233–267 and 338–355. -/
def branchWithSources (G : PreparedSourceGate c X Y) (ξ : ι)
    (η : ∀ i, EuclideanSpace ℂ (G.bases.left i × G.bases.right i)) : Word X Y :=
  (SourceInventory.prepareSlots G.slots G.bases η X).comp (G.remaining ξ)

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- With the vectors of the gate, the branch is the branch of the gate. -/
@[simp] theorem branchWithSources_vector (G : PreparedSourceGate c X Y) (ξ : ι) :
    G.branchWithSources ξ (G.vector ξ) = G.branchWord ξ :=
  rfl

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- The sources of a branch with prescribed vectors are the slots with these vectors. -/
theorem sources_branchWithSources (G : PreparedSourceGate c X Y) (ξ : ι)
    (η : ∀ i, EuclideanSpace ℂ (G.bases.left i × G.bases.right i)) :
    (G.branchWithSources ξ η).sources = SourceInventory.ofSlots G.slots G.bases η := by
  rw [branchWithSources, Word.sources_comp, G.remaining_sources,
    SourceInventory.sources_prepareSlots, List.nil_append]

end PreparedSourceGate

namespace SourceCircuit

variable [Fintype P]

/-- The operator of a source circuit with the vectors `η e ξ` at every position `e` and label
`ξ` of its gate; no norm condition is imposed on them. Source: Theorem 5.2, `04-compression.tex`,
lines 338–355. -/
noncomputable def opWithSources : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) → Matrix (Config Y) (Config X) ℂ
  | _, _, _, _, PartyCircuit.done _ => fun _ ↦ 1
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g => fun η ↦
    placeBetween D hY (∑ ξ, g.coeff ξ • (g.gate.branchWithSources ξ fun i ↦ η ⟨(), i⟩ ξ).op)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY U => fun _ ↦
    SourceCircuit.op (PartyCircuit.localOp p hY U)
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ U => fun _ ↦ piKronecker U
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => fun η ↦
    opWithSources c' (fun e ↦ η ⟨Sum.inr e.1, e.2⟩) * opWithSources c fun e ↦ η ⟨Sum.inl e.1, e.2⟩

variable (A : P → Bool)

/-- The branches of the partial expansion with the vectors `η e ξ` prepared at the touched gates;
untouched gates stay whole. Source: Theorem 5.2, `04-compression.tex`, lines 351–381. -/
noncomputable def partialWithSources : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) → Choices A w →
      Word (blockSystem (affectedOwner A) X) (blockSystem (affectedOwner A) Y)
  | _, _, _, _, PartyCircuit.done _ => fun _ _ ↦ PartyCircuit.done _
  | _, _, _, _, @PartyCircuit.gate _ _ _ _ _ _ D hY g => fun η ξ ↦
    if h : PreparedGate.IsTouched A D then
      Word.coarsen (affectedOwner A) (Word.onCell D hY
        (g.gate.branchWithSources (choiceLabel A hY g h ξ)
          fun i ↦ η ⟨(), i⟩ (choiceLabel A hY g h ξ)))
    else
      PartyCircuit.localOp none (blockSystem_eq_of_not_isTouched h hY)
        (subregionPlaceBetween (subset_blockPreimage_of_not_isTouched h) hY g.gate.eval)
  | _, _, _, _, @PartyCircuit.localOp _ _ _ _ _ _ p hY U => fun _ _ ↦
    Word.coarsen (affectedOwner A) (PartyCircuit.localOp p hY U : Word _ _)
  | _, _, _, _, @PartyCircuit.localOps _ _ _ _ _ _ U => fun _ _ ↦
    Word.coarsen (affectedOwner A) (PartyCircuit.localOps U : Word _ _)
  | _, _, _, _, @PartyCircuit.comp _ _ _ _ _ _ _ c c' => fun η ξ ↦
    PartyCircuit.comp (partialWithSources c (fun e ↦ η ⟨Sum.inl e.1, e.2⟩) ξ.1)
      (partialWithSources c' (fun e ↦ η ⟨Sum.inr e.1, e.2⟩) ξ.2)

/-! #### Computation rules -/

variable {X Y Z : P → Type} [∀ p, Fintype (X p)] [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)]
  [∀ p, DecidableEq (Y p)]

/-- The substituted operator of a composition is the product of those of its parts. -/
@[simp] theorem opWithSources_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (η : ∀ e : sourceLocations (PartyCircuit.comp w w'),
      branchLabels (PartyCircuit.comp w w') e.1 →
        EuclideanSpace ℂ (leftBasis (PartyCircuit.comp w w') e ×
          rightBasis (PartyCircuit.comp w w') e)) :
    opWithSources (PartyCircuit.comp w w') η =
      opWithSources w' (fun e ↦ η ⟨Sum.inr e.1, e.2⟩) *
        opWithSources w fun e ↦ η ⟨Sum.inl e.1, e.2⟩ :=
  rfl

/-- The substituted operator of a gate: the weighted sum of its branches with the prescribed
vectors, placed on its cell. -/
theorem opWithSources_gate (D : Finset P) (hY : ∀ s ∉ D, Y s = X s) (g : PreparedGate D X Y)
    (η : ∀ e : sourceLocations (PartyCircuit.gate D hY g : SourceCircuit X Y),
      branchLabels (PartyCircuit.gate D hY g : SourceCircuit X Y) e.1 →
        EuclideanSpace ℂ (leftBasis (PartyCircuit.gate D hY g : SourceCircuit X Y) e ×
          rightBasis (PartyCircuit.gate D hY g : SourceCircuit X Y) e)) :
    opWithSources (PartyCircuit.gate D hY g : SourceCircuit X Y) η =
      placeBetween D hY (∑ ξ, g.coeff ξ • (g.gate.branchWithSources ξ fun i ↦ η ⟨(), i⟩ ξ).op) :=
  rfl

/-- The substituted branch of a composition is the composition of those of its parts. -/
@[simp] theorem partialWithSources_comp (w : SourceCircuit X Y) (w' : SourceCircuit Y Z)
    (η : ∀ e : sourceLocations (PartyCircuit.comp w w'),
      branchLabels (PartyCircuit.comp w w') e.1 →
        EuclideanSpace ℂ (leftBasis (PartyCircuit.comp w w') e ×
          rightBasis (PartyCircuit.comp w w') e))
    (ξ : Choices A (PartyCircuit.comp w w')) :
    partialWithSources A (PartyCircuit.comp w w') η ξ =
      PartyCircuit.comp (partialWithSources A w (fun e ↦ η ⟨Sum.inl e.1, e.2⟩) ξ.1)
        (partialWithSources A w' (fun e ↦ η ⟨Sum.inr e.1, e.2⟩) ξ.2) :=
  rfl

/-- At an untouched gate the substituted branch is the whole gate, whatever the vectors. -/
theorem partialWithSources_gate_of_not_isTouched (D : Finset P) (hY : ∀ s ∉ D, Y s = X s)
    (g : PreparedGate D X Y) (h : ¬ PreparedGate.IsTouched A D)
    (η : ∀ e : sourceLocations (PartyCircuit.gate D hY g : SourceCircuit X Y),
      branchLabels (PartyCircuit.gate D hY g : SourceCircuit X Y) e.1 →
        EuclideanSpace ℂ (leftBasis (PartyCircuit.gate D hY g : SourceCircuit X Y) e ×
          rightBasis (PartyCircuit.gate D hY g : SourceCircuit X Y) e))
    (ξ : Choices A (PartyCircuit.gate D hY g : SourceCircuit X Y)) :
    partialWithSources A (PartyCircuit.gate D hY g : SourceCircuit X Y) η ξ =
      partialWord A (PartyCircuit.gate D hY g : SourceCircuit X Y) ξ :=
  (dite_eq_right h).trans (partialWord_gate_of_not_isTouched A D hY g h ξ).symm

/-! ### The vectors of the gates -/

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **The vectors of the gates give the operator back.** Source: Theorem 5.2,
`04-compression.tex`, lines 338–355. -/
theorem opWithSources_original : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) → opWithSources w w.sourceVectorAt = w.op
  | _, _, _, _, PartyCircuit.done _ => (PartyCircuit.op_done _).symm
  | _, _, _, _, PartyCircuit.gate _ _ _ => (SourceCircuit.op_gate _ _ _).symm
  | _, _, _, _, PartyCircuit.localOp _ _ _ => rfl
  | _, _, _, _, PartyCircuit.localOps _ => (PartyCircuit.op_localOps _ _).symm
  | _, _, _, _, PartyCircuit.comp c c' => by
    rw [opWithSources_comp]
    exact (congrArg₂ (· * ·) (opWithSources_original c') (opWithSources_original c)).trans
      (PartyCircuit.op_comp _ _ _).symm

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **The vectors of the gates give the branches back.** Source: Theorem 5.2,
`04-compression.tex`, lines 351–381. -/
theorem partialWithSources_original : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) → (ξ : Choices A w) →
      partialWithSources A w w.sourceVectorAt ξ = partialWord A w ξ
  | _, _, _, _, PartyCircuit.done _, _ => rfl
  | _, _, _, _, PartyCircuit.gate _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOp _ _ _, _ => rfl
  | _, _, _, _, PartyCircuit.localOps _, _ => rfl
  | _, _, _, _, PartyCircuit.comp c c', ξ =>
    congrArg₂ PartyCircuit.comp (partialWithSources_original c ξ.1)
      (partialWithSources_original c' ξ.2)

/-! ### The weighted sum of the substituted branches -/

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- **Substitutions at the touched gates commute with summing back the untouched gates**: when no
vector at an untouched gate is changed, the weighted sum of the substituted branches is the
substituted operator read on the affected parties and the exterior party. Source: Theorem 5.2,
`04-compression.tex`, lines 351–381. -/
theorem sum_coefficient_smul_op_partialWithSources : {X Y : P → Type} → [∀ p, Fintype (X p)] →
    [∀ p, DecidableEq (X p)] → (w : SourceCircuit X Y) →
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e)) →
    (∀ e ξ, ¬ IsTouched A w e.1 → η e ξ = w.sourceVectorAt e ξ) →
      ∑ ξ, coefficient A w ξ • Word.op (partialWithSources A w η ξ) =
        reindex (blockConfigEquiv (affectedOwner A) Y).symm
          (blockConfigEquiv (affectedOwner A) X).symm (opWithSources w η)
  | _, _, _, _, PartyCircuit.done X, _, _ => by
    change ∑ _ξ : Unit, (1 : ℂ) • Word.op (PartyCircuit.done _) = _
    rw [Fintype.sum_unique, one_smul, Word.op, PartyCircuit.op_done]
    ext
    simp [opWithSources, one_apply]
  | _, _, _, _, PartyCircuit.gate D hY g, η, hη => by
    by_cases h : PreparedGate.IsTouched A D
    · rw [opWithSources_gate]
      let e : Choices A (PartyCircuit.gate D hY g : SourceCircuit _ _) ≃ g.ι :=
        Equiv.cast (ite_eq_left h)
      refine (Fintype.sum_equiv e _
        (fun i ↦ g.coeff i • reindex (blockConfigEquiv (affectedOwner A) _).symm
          (blockConfigEquiv (affectedOwner A) _).symm
          (placeBetween D hY (g.gate.branchWithSources i fun j ↦ η ⟨(), j⟩ i).op))
        fun ξ ↦ ?_).trans ?_
      · simp only [coefficient_gate, dite_eq_left h]
        change _ • Word.op (dite _ _ _) = _
        rw [dite_eq_left h, Word.op_coarsen, Word.op_onCell]
        rfl
      · ext a b
        simp only [placeBetween_sum, placeBetween_smul, Matrix.sum_apply, Matrix.smul_apply,
          reindex_apply, submatrix_apply]
    · obtain rfl : η = sourceVectorAt (PartyCircuit.gate D hY g : SourceCircuit _ _) :=
        funext fun e ↦ funext fun ξ ↦ hη e ξ h
      rw [opWithSources_original]
      exact sum_coefficient_smul_op_partialWord A _
  | _, _, _, _, PartyCircuit.localOp p hY U, _, _ => by
    change ∑ _ξ : Unit, (1 : ℂ) • Word.op (Word.coarsen (affectedOwner A)
      (PartyCircuit.localOp p hY U : Word _ _)) = _
    rw [Fintype.sum_unique, one_smul, Word.op_coarsen]
    rfl
  | _, _, _, _, PartyCircuit.localOps U, _, _ => by
    change ∑ _ξ : Unit, (1 : ℂ) • Word.op (Word.coarsen (affectedOwner A)
      (PartyCircuit.localOps U : Word _ _)) = _
    rw [Fintype.sum_unique, one_smul, Word.op_coarsen, Word.op, PartyCircuit.op_localOps]
    rfl
  | _, _, _, _, PartyCircuit.comp c c', η, hη => by
    have key : ∑ ξ, coefficient A (PartyCircuit.comp c c') ξ •
          Word.op (partialWithSources A (PartyCircuit.comp c c') η ξ) =
        (∑ ξ', coefficient A c' ξ' •
            Word.op (partialWithSources A c' (fun e ↦ η ⟨Sum.inr e.1, e.2⟩) ξ')) *
          ∑ ξ, coefficient A c ξ •
            Word.op (partialWithSources A c (fun e ↦ η ⟨Sum.inl e.1, e.2⟩) ξ) := by
      simp only [Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
        Finset.smul_sum, smul_smul]
      refine (Fintype.sum_prod_type _).trans
        (Finset.sum_congr rfl fun ξ _ ↦ Finset.sum_congr rfl fun ξ' _ ↦ ?_)
      exact congrArg ((coefficient A c ξ * coefficient A c' ξ') • ·) (Word.op_comp _ _)
    rw [key, sum_coefficient_smul_op_partialWithSources c _ fun e ξ h ↦ hη ⟨Sum.inl e.1, e.2⟩ ξ h,
      sum_coefficient_smul_op_partialWithSources c' _ fun e ξ h ↦ hη ⟨Sum.inr e.1, e.2⟩ ξ h,
      reindex_apply, reindex_apply, submatrix_mul_equiv, reindex_apply, opWithSources_comp]

open Classical in
/-- Vectors replaced at the positions of a set `S` and kept elsewhere. Source: Theorem 5.2,
`04-compression.tex`, lines 342–355. -/
noncomputable def selectedSourceVectors (w : SourceCircuit X Y) (S : Finset w.sourceLocations)
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e))
    (e : w.sourceLocations) (ξ : w.branchLabels e.1) :
    EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e) :=
  if e ∈ S then η e ξ else w.sourceVectorAt e ξ

omit [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)] in
/-- When every position of `S` has an affected endpoint, the substitutions at `S` sum back over
the untouched gates. Source: Theorem 5.2, `04-compression.tex`, lines 342–381. -/
theorem sum_coefficient_smul_op_partialWithSources_selected (w : SourceCircuit X Y)
    (S : Finset w.sourceLocations)
    (η : ∀ e : w.sourceLocations, w.branchLabels e.1 →
      EuclideanSpace ℂ (w.leftBasis e × w.rightBasis e))
    (hS : ∀ e ∈ S, A (w.endpoints e).1 = true ∨ A (w.endpoints e).2 = true) :
    ∑ ξ, coefficient A w ξ • Word.op (partialWithSources A w (selectedSourceVectors w S η) ξ) =
      reindex (blockConfigEquiv (affectedOwner A) Y).symm
        (blockConfigEquiv (affectedOwner A) X).symm
        (opWithSources w (selectedSourceVectors w S η)) := by
  classical
  refine sum_coefficient_smul_op_partialWithSources A w _ fun e ξ he ↦ ?_
  have : e ∉ S := fun heS ↦ he (isTouched_of_source_endpoint A w e (hS e heS))
  simp only [selectedSourceVectors, this, ite_false]

end SourceCircuit

end QuantumCircuit.Party
