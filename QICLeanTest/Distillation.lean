/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Model.Distillation
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Regression tests and strict transitive axiom guards for
`QICLean.Channel.Entanglement.BipartiteCopies` and `QICLean.Circuit.Model.Distillation`.

Covers:
* Empty protocol class behavior (`minDistillationError = ⊤`, never `0`; `E_D = 0`).
* Local copy discard (`keepFirstBellPair`, `keepCopySepOp`) on multi-copy Bell targets.
* Concrete zero-distillation instantiations for `|00⟩⟨00|` and the maximally mixed two-qubit
  state under both `IsSeparableTPChannel` and `IsBipartiteFiniteRoundLOCC`.
* Non-vacuity: rate `0` is achievable for unit-trace states, and `1 ≤ E_D^{SEP}(|Ω₂⟩⟨Ω₂|)`.
* Strict transitive axiom guard (only `propext`, `Classical.choice`, `Quot.sound`).
-/

open Matrix QuantumInfo QuantumCircuit
open scoped BigOperators ComplexOrder Kronecker NNReal ENNReal

namespace DistillationTest

/-! ## Empty protocol class sanity checks -/

/-- The empty bipartite protocol class. -/
def EmptyProtocolClass : BipartiteProtocolClass :=
  fun {_ _ _ _ _ _ _ _ _ _ _ _} _ ↦ False

/-- For an empty protocol class, `minDistillationError` is `⊤` (never spuriously `0`). -/
theorem empty_class_error_is_top (n k : ℕ) :
    minDistillationError EmptyProtocolClass (Matrix.omegaProj 2) n k = ⊤ :=
  minDistillationError_eq_top_of_empty EmptyProtocolClass (Matrix.omegaProj 2) n k
    (fun _ h ↦ h)

/-- For an empty protocol class, no rate is achievable and `E_D = 0`. -/
theorem empty_class_ed_is_zero :
    distillableEntanglement EmptyProtocolClass (Matrix.omegaProj 2) = 0 := by
  rw [distillableEntanglement_eq_zero_iff]
  rintro r _ ⟨Λ, hP, -⟩
  obtain ⟨_, hfalse⟩ := hP.exists
  exact hfalse

/-! ## Local copy discard on multi-copy Bell targets -/

/-- Keeping the first pair of 3 Bell pairs produces `Matrix.omegaProj 2`. -/
theorem keepFirstBellPair_three :
    (keepFirstBellPair (k := 3) (by decide)).map (bellPairTarget 3) = Matrix.omegaProj 2 :=
  keepFirstBellPair_map_bellPairTarget (k := 3) (by decide)

/-! ## Concrete product states: `|00⟩⟨00|` and maximally mixed two-qubit state -/

/-- Single-qubit computational basis projector `|0⟩⟨0|`. -/
def qubitZeroProj : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.single 0 0 1

theorem qubitZeroProj_posSemidef : qubitZeroProj.PosSemidef := by
  have h : qubitZeroProj = qubitZeroProjᴴ * qubitZeroProj := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [qubitZeroProj, Matrix.mul_apply, Matrix.single_apply]
  rw [h]
  exact posSemidef_conjTranspose_mul_self _

theorem qubitZeroProj_trace : qubitZeroProj.trace = 1 := by
  simp [qubitZeroProj, Matrix.trace, Matrix.diag, Matrix.single_apply]

/-- `|00⟩⟨00|` has zero distillable entanglement under both `IsSeparableTPChannel` and
`IsBipartiteFiniteRoundLOCC`, while rate `0` is achievable under `IsSeparableTPChannel`. -/
theorem product_zero_zero_distillation :
    let ρ := qubitZeroProj ⊗ₖ qubitZeroProj
    distillableEntanglement IsSeparableTPChannel ρ = 0 ∧
      distillableEntanglement IsBipartiteFiniteRoundLOCC ρ = 0 ∧
      IsAchievableDistillationRate IsSeparableTPChannel ρ 0 := by
  intro ρ
  have hsep : distillableEntanglement IsSeparableTPChannel ρ = 0 :=
    distillableEntanglement_kronecker_eq_zero
      isTracePreservingClass_isSeparableTPChannel
      isContainedInSeparable_isSeparableTPChannel
      qubitZeroProj_posSemidef qubitZeroProj_posSemidef
      qubitZeroProj_trace qubitZeroProj_trace
  have hlocc : distillableEntanglement IsBipartiteFiniteRoundLOCC ρ = 0 :=
    le_antisymm
      ((distillableEntanglement_isBipartiteFiniteRoundLOCC_le_isSeparableTPChannel ρ).trans
        hsep.le)
      zero_le
  have htr : ρ.trace = 1 := by
    rw [Matrix.trace_kronecker, qubitZeroProj_trace, mul_one]
  exact ⟨hsep, hlocc, isAchievableDistillationRate_zero_isSeparableTPChannel htr⟩

/-- Single-qubit maximally mixed state `(1 / 2) • 1`. -/
noncomputable def qubitMaxMixed : Matrix (Fin 2) (Fin 2) ℂ :=
  ((2 : ℝ)⁻¹ : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem qubitMaxMixed_posSemidef : qubitMaxMixed.PosSemidef :=
  Matrix.PosSemidef.one.smul (by positivity)

theorem qubitMaxMixed_trace : qubitMaxMixed.trace = 1 := by
  rw [qubitMaxMixed, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin]
  norm_num

/-- The maximally mixed two-qubit state has zero distillable entanglement under
`IsSeparableTPChannel` and `IsBipartiteFiniteRoundLOCC`. -/
theorem max_mixed_two_qubit_distillation :
    let ρ := qubitMaxMixed ⊗ₖ qubitMaxMixed
    distillableEntanglement IsSeparableTPChannel ρ = 0 ∧
      distillableEntanglement IsBipartiteFiniteRoundLOCC ρ = 0 := by
  intro ρ
  have hsep : distillableEntanglement IsSeparableTPChannel ρ = 0 :=
    distillableEntanglement_kronecker_eq_zero
      isTracePreservingClass_isSeparableTPChannel
      isContainedInSeparable_isSeparableTPChannel
      qubitMaxMixed_posSemidef qubitMaxMixed_posSemidef
      qubitMaxMixed_trace qubitMaxMixed_trace
  have hlocc : distillableEntanglement IsBipartiteFiniteRoundLOCC ρ = 0 :=
    le_antisymm
      ((distillableEntanglement_isBipartiteFiniteRoundLOCC_le_isSeparableTPChannel ρ).trans
        hsep.le)
      zero_le
  exact ⟨hsep, hlocc⟩

/-! ## Non-vacuity: Bell pair has positive distillable entanglement -/

/-- `Matrix.omegaProj 2` has `E_D^{SEP} ≥ 1` and in particular `E_D^{SEP} ≠ 0`. -/
theorem omegaProj_two_positive_ed :
    (1 : ℝ≥0∞) ≤ distillableEntanglement IsSeparableTPChannel (Matrix.omegaProj 2) ∧
      distillableEntanglement IsSeparableTPChannel (Matrix.omegaProj 2) ≠ 0 := by
  have h1 := one_le_distillableEntanglement_omegaProj_two
  refine ⟨h1, ?_⟩
  intro h0
  rw [h0] at h1
  exact not_le_of_gt zero_lt_one h1

/-! ## Strict transitive axiom guard -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``QuantumInfo.bipartiteCopies,
      ``QuantumInfo.bipartiteCopies_apply,
      ``QuantumInfo.bipartiteCopies_kronecker,
      ``QuantumInfo.conjTranspose_bipartiteCopies,
      ``QuantumInfo.trace_bipartiteCopies,
      ``QuantumInfo.trace_bipartiteCopies_eq_one,
      ``QuantumInfo.bipartiteCopies_posSemidef,
      ``QuantumInfo.bellPairTarget,
      ``QuantumInfo.trace_bellPairTarget,
      ``QuantumInfo.splitCopyEquiv,
      ``QuantumInfo.keepCopyKraus,
      ``QuantumInfo.isTP_keepCopyKraus,
      ``QuantumInfo.keepCopyKraus_op_apply,
      ``QuantumInfo.keepCopySepOp,
      ``QuantumInfo.keepCopySepOp_toKrausFamily,
      ``QuantumInfo.isTP_keepCopySepOp,
      ``QuantumInfo.rectangularTraceNorm_keepCopySepOp_map_le,
      ``QuantumInfo.keepCopySepOp_map_apply,
      ``QuantumInfo.keepCopySepOp_map_bipartiteCopies,
      ``QuantumInfo.keepCopySepOp_map_bipartiteCopies_of_trace_eq_one,
      ``QuantumInfo.keepCopySepOp_map_bellPairTarget,
      ``QuantumInfo.rectangularTraceNorm_keepCopySepOp_sub_omegaProj_le,
      ``QuantumInfo.keepFirstBellPair,
      ``QuantumInfo.isTP_keepFirstBellPair,
      ``QuantumInfo.keepFirstBellPair_map_bellPairTarget,
      ``QuantumInfo.rectangularTraceNorm_keepFirstBellPair_sub_omegaProj_le,
      ``QuantumCircuit.ClassLe,
      ``QuantumCircuit.IsTracePreservingClass,
      ``QuantumCircuit.IsContainedInSeparable,
      ``QuantumCircuit.IsSeparableTPChannel,
      ``QuantumCircuit.isTracePreservingClass_isSeparableTPChannel,
      ``QuantumCircuit.isContainedInSeparable_isSeparableTPChannel,
      ``QuantumCircuit.IsBipartiteFiniteRoundLOCC,
      ``QuantumCircuit.classLe_isBipartiteFiniteRoundLOCC_isSeparableTPChannel,
      ``QuantumCircuit.minDistillationError,
      ``QuantumCircuit.minDistillationError_eq_top_of_empty,
      ``QuantumCircuit.minDistillationError_le_of_mem,
      ``QuantumCircuit.IsAchievableDistillationRate,
      ``QuantumCircuit.distillableEntanglement,
      ``QuantumCircuit.IsAchievableDistillationRate.mono,
      ``QuantumCircuit.distillableEntanglement_mono,
      ``QuantumCircuit.distillableEntanglement_isBipartiteFiniteRoundLOCC_le_isSeparableTPChannel,
      ``QuantumCircuit.le_distillableEntanglement_of_achievable,
      ``QuantumCircuit.distillableEntanglement_eq_zero_iff,
      ``QuantumCircuit.tendsto_minDistillationError_of_achievable,
      ``QuantumCircuit.isAchievableDistillationRate_of_tendsto_minDistillationError,
      ``QuantumCircuit.isAchievableDistillationRate_iff_tendsto_minDistillationError,
      ``QuantumCircuit.HasUniformBellOverlapCap,
      ``QuantumCircuit.one_sub_le_rectangularTraceNorm_sub_bellPairTarget_of_uniformBellOverlapCap,
      ``QuantumCircuit.not_isAchievableDistillationRate_of_uniformBellOverlapCap,
      ``QuantumCircuit.distillableEntanglement_eq_zero_of_uniformBellOverlapCap,
      ``QuantumCircuit.distillableEntanglement_eq_zero_of_classLe_isSeparableTPChannel,
      ``QuantumCircuit.distillableEntanglement_isBipartiteFiniteRoundLOCC_eq_zero_of_uniformBellOverlapCap,
      ``QuantumCircuit.hasUniformBellOverlapCap_kronecker_half,
      ``QuantumCircuit.distillableEntanglement_kronecker_eq_zero,
      ``QuantumCircuit.isAchievableDistillationRate_zero_isSeparableTPChannel,
      ``QuantumCircuit.isAchievableDistillationRate_one_omegaProj_two,
      ``QuantumCircuit.one_le_distillableEntanglement_omegaProj_two,
      ``empty_class_error_is_top,
      ``empty_class_ed_is_zero,
      ``keepFirstBellPair_three,
      ``product_zero_zero_distillation,
      ``max_mixed_two_qubit_distillation,
      ``omegaProj_two_positive_ed] do
    let axs ← Lean.collectAxioms decl
    unless axs.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axs}"
    Lean.logInfo m!"{decl}: {axs}"

end DistillationTest
