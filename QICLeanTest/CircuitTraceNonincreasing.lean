/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Core.Channel
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Regressions for rectangular, branching, lossy and empty circuit semantics. -/

open Matrix ManyBody QuantumCircuit
open scoped ComplexOrder MatrixOrder

namespace CircuitTraceNonincreasingTest

private def geometry (S : Type) : Geometry S where
  Cell := Empty
  cell := Empty.elim
  cost := Empty.elim

private def onsiteLayer {α β : Type} (K : KrausFamily α β) :
    Layer (geometry Unit) KrausGate (fun _ ↦ α) (fun _ ↦ β) where
  cells := ∅
  pairwiseDisjoint := by simp
  gate b := False.elim (Finset.notMem_empty _ b.2)
  onsite _ := K

private theorem onsiteLayer_forall {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {K : KrausFamily α β} (h : K.IsTraceNonincreasing) :
    (onsiteLayer K).Forall KrausGate.ev KrausFamily.IsTraceNonincreasing :=
  ⟨fun b ↦ False.elim (Finset.notMem_empty _ b.2), fun _ ↦ h⟩

-- Rectangular dimensions are arbitrary, including empty input or output bases.
example {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {K : KrausFamily α β} (h : K.IsTraceNonincreasing) :
    ((Circuit.ofLayer (onsiteLayer K)).krausFamily KrausGate.ev).IsTraceNonincreasing :=
  Circuit.isTraceNonincreasing_krausFamily _ _ ⟨onsiteLayer_forall h, fun _ ↦ trivial⟩

private def filter : KrausFamily Bool Bool :=
  KrausFamily.single (diagonal fun b ↦ if b then 0 else 1)

private theorem filter_effect : filter.effect = diagonal (fun b ↦ if b then 0 else 1) := by
  rw [filter, KrausFamily.effect_single, diagonal_conjTranspose, diagonal_mul_diagonal]
  congr 1
  funext b
  cases b <;> simp

private theorem filter_tni : filter.IsTraceNonincreasing := by
  rw [KrausFamily.IsTraceNonincreasing, filter_effect, Matrix.le_iff]
  have he : (1 : Matrix Bool Bool ℂ) - diagonal (fun b ↦ if b then 0 else 1) =
      diagonal (fun b ↦ if b then 1 else 0) := by
    ext a b
    cases a <;> cases b <;> simp
  rw [he]
  exact Matrix.PosSemidef.diagonal (fun b ↦ by cases b <;> simp)

-- A nonzero, genuinely lossy operation: one basis state survives and the other is removed.
example : ¬filter.IsTP := by
  intro h
  have he := congrFun (congrFun h true) true
  rw [filter_effect] at he
  simp at he

example : filter.map (diagonal fun b ↦ if b then 0 else 1) ≠ 0 := by
  intro h
  have he := congrFun (congrFun h false) false
  simp [filter, KrausFamily.map_apply, KrausFamily.single] at he

example : ((Circuit.ofLayer (onsiteLayer filter)).krausFamily KrausGate.ev).IsTraceNonincreasing :=
  Circuit.isTraceNonincreasing_krausFamily _ _
    ⟨onsiteLayer_forall filter_tni, fun _ ↦ trivial⟩

-- Complete positivity needs no normalization, even for the rectangular examples above.
example {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (K : KrausFamily α β) : IsKrausCP K.map :=
  Matrix.rectangularKrausMap_isKrausCP K.op

private def emptyFamily (α β : Type) : KrausFamily α β := ⟨Empty, Empty.elim⟩

private theorem emptyFamily_tni (α β : Type) [Fintype α] [DecidableEq α] [Fintype β] :
    (emptyFamily α β).IsTraceNonincreasing := by
  change (∑ i : Empty, (Empty.elim i : Matrix β α ℂ)ᴴ * Empty.elim i) ≤ 1
  simp

private theorem measure_tp : (KrausFamily.measure Bool).IsTP := by
  change (∑ i : Bool, (Matrix.single i i (1 : ℂ))ᴴ * Matrix.single i i 1) = 1
  simp only [conjTranspose_single, star_one, single_mul_single_same, mul_one]
  exact sum_single_one

-- A measurement followed by a surviving identity branch or a branch with no outcomes.
private noncomputable def branchCircuit : Circuit (geometry Unit) KrausGate (fun _ ↦ Bool) (fun _ ↦ Bool) := by
  classical
  exact Circuit.step (onsiteLayer (KrausFamily.measure Bool)) fun i ↦
    if (i.2 ⟨(), by simp [onsiteLayer]⟩ : Bool) = true then
      Circuit.ofLayer (onsiteLayer (emptyFamily Bool Bool))
    else Circuit.done _

private theorem branchCircuit_tni :
    branchCircuit.Forall KrausGate.ev KrausFamily.IsTraceNonincreasing := by
  refine ⟨onsiteLayer_forall measure_tp.isTraceNonincreasing, ?_⟩
  intro i
  dsimp [branchCircuit]
  split
  · exact ⟨onsiteLayer_forall (emptyFamily_tni Bool Bool), fun _ ↦ trivial⟩
  · trivial

example : (branchCircuit.krausFamily KrausGate.ev).IsTraceNonincreasing :=
  branchCircuit.isTraceNonincreasing_krausFamily _ branchCircuit_tni

example {ρ : Matrix (Config (fun _ : Unit ↦ Bool)) (Config (fun _ : Unit ↦ Bool)) ℂ}
    (hρ : ρ.PosSemidef) : (branchCircuit.map KrausGate.ev ρ).trace ≤ ρ.trace :=
  branchCircuit.trace_map_le _ branchCircuit_tni hρ

example : ((onsiteLayer (emptyFamily Bool Empty)).krausFamily KrausGate.ev).IsTraceNonincreasing :=
  Layer.isTraceNonincreasing_krausFamily _ _ (onsiteLayer_forall (emptyFamily_tni Bool Empty))

example : ((onsiteLayer (emptyFamily Empty Bool)).krausFamily KrausGate.ev).IsTraceNonincreasing :=
  Layer.isTraceNonincreasing_krausFamily _ _ (onsiteLayer_forall (emptyFamily_tni Empty Bool))

-- No sites: the empty product is the identity on the singleton configuration basis.
example (L : Layer (geometry Empty) KrausGate (fun _ ↦ Bool) (fun _ ↦ Bool))
    (h : L.Forall KrausGate.ev KrausFamily.IsTraceNonincreasing) : L.dual KrausGate.ev 1 ≤ 1 :=
  L.dual_one_le _ h

end CircuitTraceNonincreasingTest

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Matrix.prod_le_one, ``KrausFamily.trace_map_le,
      ``QuantumCircuit.Layer.blockEffect_le_one, ``QuantumCircuit.Layer.effect_apply_eq_prod,
      ``QuantumCircuit.Layer.isTraceNonincreasing_krausFamily, ``QuantumCircuit.Layer.dual_one_le,
      ``QuantumCircuit.Circuit.dual_one_le_of_forall,
      ``QuantumCircuit.Circuit.isTraceNonincreasing_krausFamily,
      ``QuantumCircuit.Circuit.trace_map_le] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
