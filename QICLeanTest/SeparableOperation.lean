/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Entanglement.SeparableOperation
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Product-Kraus operation regressions

Check rectangular sandwiches, identity, composition order, shared (not independent)
outcomes, and the distinction between unrestricted CP maps and TP/TNI operations.
The semantic computations unfold definitions rather than restating the migrated lemmas.
Every audited declaration must exist and have only standard kernel axioms transitively.
-/

open Matrix QuantumInfo
open scoped Kronecker ComplexOrder MatrixOrder

namespace SeparableOperationTest

theorem rectangular_sandwich (L : Matrix (Fin 3) (Fin 2) ℂ)
    (R : Matrix (Fin 2) (Fin 1) ℂ)
    (ρ : Matrix (Fin 2 × Fin 1) (Fin 2 × Fin 1) ℂ) :
    (SeparableOperation.single L R).map ρ = (L ⊗ₖ R) * ρ * (L ⊗ₖ R)ᴴ := by
  simp [SeparableOperation.map, KrausFamily.map_apply, SeparableOperation.single,
    SeparableOperation.toKrausFamily]

theorem identity_map (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    (SeparableOperation.id (Fin 2) (Fin 3)).map ρ = ρ := by
  simp [SeparableOperation.id, SeparableOperation.map, KrausFamily.map_apply,
    SeparableOperation.single, SeparableOperation.toKrausFamily]

-- Arbitrary noncommuting local factors detect reversal of the composition order.
theorem composition_order (L R U V : Matrix (Fin 2) (Fin 2) ℂ)
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    ((SeparableOperation.single U V).comp (SeparableOperation.single L R)).map ρ =
      ((U * L) ⊗ₖ (V * R)) * ρ * ((U * L) ⊗ₖ (V * R))ᴴ := by
  dsimp [SeparableOperation.map, KrausFamily.map_apply, SeparableOperation.comp,
    SeparableOperation.single, SeparableOperation.toKrausFamily]
  rw [Fintype.sum_prod_type]
  simp

-- Two common outcomes give two copies, not the four from independent sums.
def repeatedIdentity : SeparableOperation (Fin 2) (Fin 2) (Fin 2) (Fin 2) :=
  ⟨Bool, fun _ ↦ 1, fun _ ↦ 1⟩

theorem shared_outcomes (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    repeatedIdentity.map ρ = ρ + ρ := by
  dsimp [repeatedIdentity, SeparableOperation.map, KrausFamily.map_apply,
    SeparableOperation.toKrausFamily]
  simp [two_mul]

theorem unnormalized_cp : IsKrausCP repeatedIdentity.map :=
  repeatedIdentity.isKrausCP_map

theorem identity_tp : (SeparableOperation.id (Fin 2) (Fin 3)).IsTP := by
  change (SeparableOperation.id (Fin 2) (Fin 3)).toKrausFamily.effect = 1
  dsimp [KrausFamily.effect, SeparableOperation.id, SeparableOperation.single,
    SeparableOperation.toKrausFamily]
  rw [Fintype.sum_unique]
  simp

theorem identity_tni : (SeparableOperation.id (Fin 2) (Fin 3)).IsTraceNonincreasing :=
  KrausFamily.IsTP.isTraceNonincreasing identity_tp

theorem identity_trace (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    ((SeparableOperation.id (Fin 2) (Fin 3)).map ρ).trace = ρ.trace :=
  KrausFamily.trace_map identity_tp ρ

-- The empty outcome set is permitted: the zero branch is TNI but not TP.
def emptyBranch : SeparableOperation (Fin 2) (Fin 3) (Fin 1) (Fin 2) :=
  ⟨Empty, Empty.elim, Empty.elim⟩

theorem empty_map (ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) :
    emptyBranch.map ρ = 0 := by
  simp [emptyBranch, SeparableOperation.map, KrausFamily.map_apply,
    SeparableOperation.toKrausFamily]

theorem empty_effect : emptyBranch.toKrausFamily.effect = 0 := by
  exact Finset.sum_empty

theorem empty_tni : emptyBranch.IsTraceNonincreasing := by
  change emptyBranch.toKrausFamily.effect ≤ 1
  rw [empty_effect]
  exact zero_le_one

theorem empty_not_tp : ¬ emptyBranch.IsTP := by
  change ¬ emptyBranch.toKrausFamily.effect = 1
  rw [empty_effect]
  exact zero_ne_one

theorem empty_trace_le {ρ : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ}
    (hρ : ρ.PosSemidef) : (emptyBranch.map ρ).trace ≤ ρ.trace :=
  KrausFamily.trace_map_le empty_tni hρ

end SeparableOperationTest

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``QuantumInfo.SeparableOperation,
      ``QuantumInfo.SeparableOperation.toKrausFamily,
      ``QuantumInfo.SeparableOperation.toKrausFamily_op,
      ``QuantumInfo.SeparableOperation.single, ``QuantumInfo.SeparableOperation.id,
      ``QuantumInfo.SeparableOperation.map, ``QuantumInfo.SeparableOperation.map_apply,
      ``QuantumInfo.SeparableOperation.map_single,
      ``QuantumInfo.SeparableOperation.map_kronecker,
      ``QuantumInfo.SeparableOperation.map_id,
      ``QuantumInfo.SeparableOperation.isKrausCP_map,
      ``QuantumInfo.SeparableOperation.IsTP,
      ``QuantumInfo.SeparableOperation.IsTraceNonincreasing,
      ``KrausFamily.IsTP.isTraceNonincreasing,
      ``KrausFamily.trace_map,
      ``KrausFamily.trace_map_le,
      ``QuantumInfo.SeparableOperation.comp,
      ``QuantumInfo.SeparableOperation.toKrausFamily_comp_op,
      ``QuantumInfo.SeparableOperation.map_comp,
      ``QuantumInfo.SeparableOperation.map_comp_eq,
      ``SeparableOperationTest.rectangular_sandwich,
      ``SeparableOperationTest.identity_map, ``SeparableOperationTest.composition_order,
      ``SeparableOperationTest.shared_outcomes, ``SeparableOperationTest.unnormalized_cp,
      ``SeparableOperationTest.identity_tp, ``SeparableOperationTest.identity_tni,
      ``SeparableOperationTest.identity_trace, ``SeparableOperationTest.empty_map,
      ``SeparableOperationTest.empty_effect, ``SeparableOperationTest.empty_tni,
      ``SeparableOperationTest.empty_not_tp,
      ``SeparableOperationTest.empty_trace_le] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
