/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Model.LOCC
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Finite-round LOCC and branchwise factorization regressions

Test singleton-cell party extraction (with both gate cells and onsite families), adaptive
classical feed-forward (measurement on Alice followed by outcome-conditioned operation on Bob),
rectangular dimension change, unnormalized (trace-nonincreasing) branchwise factorization, and
exact agreement with `QuantumInfo.SeparableOperation`. Every audited declaration must exist and
use only standard kernel axioms transitively.
-/

open Matrix ManyBody QuantumCircuit QuantumInfo
open scoped Kronecker ComplexOrder MatrixOrder

namespace LOCCTest

/-! ### 1. Multipartite layer with both a singleton gate cell and onsite families -/

/-- Three-party system: qubits on parties 0, 1 and a qutrit on party 2. -/
def triSys : Fin 3 → Type
  | ⟨0, _⟩ => Fin 2
  | ⟨1, _⟩ => Fin 2
  | ⟨2, _⟩ => Fin 3

instance : (p : Fin 3) → Fintype (triSys p)
  | ⟨0, _⟩ => inferInstanceAs (Fintype (Fin 2))
  | ⟨1, _⟩ => inferInstanceAs (Fintype (Fin 2))
  | ⟨2, _⟩ => inferInstanceAs (Fintype (Fin 3))

instance : (p : Fin 3) → DecidableEq (triSys p)
  | ⟨0, _⟩ => inferInstanceAs (DecidableEq (Fin 2))
  | ⟨1, _⟩ => inferInstanceAs (DecidableEq (Fin 2))
  | ⟨2, _⟩ => inferInstanceAs (DecidableEq (Fin 3))

/-- A layer on `Geometry.sites (Fin 3)` with a singleton gate on party `0` (measurement) and
onsite identity families on parties `1, 2`. -/
def triLayer : Layer (Geometry.sites (Fin 3)) KrausGate triSys triSys :=
  Layer.single (Γ := Geometry.sites (Fin 3)) (G := KrausGate) (0 : Fin 3)
    (KrausFamily.measure (RegionConfig triSys {0}))

theorem triLayer_factorizes (i : triLayer.Index) :
    triLayer.kraus KrausGate.ev i = Matrix.piKronecker (triLayer.siteKraus KrausGate.ev i) :=
  triLayer.kraus_eq_piKronecker_siteKraus KrausGate.ev i

theorem triLayer_depth_zero : triLayer.depth = 0 :=
  triLayer.depth_sites

/-! ### 2. Adaptive 2-step bipartite LOCC protocol with genuine classical feed-forward -/

/-- Bipartite qubit system: `false` = Alice, `true` = Bob. -/
abbrev twoQubit : Bool → Type := fun _ ↦ Fin 2

/-- Output system where Alice discards her qubit to `PUnit` and Bob keeps his qubit. -/
abbrev bobOnly : Bool → Type
  | false => PUnit
  | true => Fin 2

instance : (b : Bool) → Fintype (bobOnly b)
  | false => inferInstanceAs (Fintype PUnit)
  | true => inferInstanceAs (Fintype (Fin 2))

instance : (b : Bool) → DecidableEq (bobOnly b)
  | false => inferInstanceAs (DecidableEq PUnit)
  | true => inferInstanceAs (DecidableEq (Fin 2))

/-- Pauli X on a qubit. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

theorem pauliX_mem_unitaryGroup : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- Round 1: Alice measures her qubit via a singleton gate cell `{false}`; Bob does nothing. -/
def aliceMeasureLayer : Layer (Geometry.sites Bool) KrausGate twoQubit twoQubit :=
  Layer.single (Γ := Geometry.sites Bool) (G := KrausGate) false
    (KrausFamily.measure (RegionConfig twoQubit {false}))

/-- Extract Alice's classical outcome bit from `aliceMeasureLayer.Index`. -/
def aliceOutcome (i : aliceMeasureLayer.Index) : Fin 2 :=
  (i.1 ⟨false, Finset.mem_singleton_self false⟩ : RegionConfig twoQubit {false})
    ⟨false, Finset.mem_singleton_self false⟩

/-- Round 2 (conditioned on Alice's outcome `m`): Alice discards her qubit; Bob applies `1` if
`m = 0` and `pauliX` if `m = 1`. -/
def bobCorrectLayer (m : Fin 2) : Layer (Geometry.sites Bool) KrausGate twoQubit bobOnly where
  cells := ∅
  pairwiseDisjoint := by simp
  gate b := absurd b.2 (Finset.notMem_empty _)
  onsite s := match s.1 with
    | false => KrausFamily.discard (Fin 2)
    | true => KrausFamily.single (if m = 0 then (1 : Matrix (Fin 2) (Fin 2) ℂ) else pauliX)

/-- Full adaptive LOCC circuit: measure Alice, feed forward outcome to Bob, discard Alice. -/
def adaptiveFeedForward : Circuit (Geometry.sites Bool) KrausGate twoQubit bobOnly :=
  Circuit.step aliceMeasureLayer fun i ↦ Circuit.ofLayer (bobCorrectLayer (aliceOutcome i))

theorem adaptiveFeedForward_depth_zero : adaptiveFeedForward.depth = 0 :=
  adaptiveFeedForward.depth_sites

theorem adaptiveFeedForward_forall_isTP :
    adaptiveFeedForward.Forall KrausGate.ev KrausFamily.IsTP := by
  refine ⟨⟨fun b ↦ ?_, fun s ↦ ?_⟩, fun i ↦ ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _),
    fun s ↦ ?_⟩, fun _ ↦ trivial⟩⟩
  · obtain ⟨b, hb'⟩ := b
    obtain rfl : b = false := Finset.mem_singleton.mp hb'
    exact KrausFamily.isUnitaryOrMeasurement_measure.isTP
  · exact (KrausFamily.isUnitary_single (one_mem _)).isTP
  · obtain ⟨b, hb⟩ := s
    cases b
    · exact KrausFamily.isTP_discard (Fin 2)
    · dsimp [bobCorrectLayer]
      split_ifs
      · exact (KrausFamily.isUnitary_single (one_mem _)).isTP
      · exact (KrausFamily.isUnitary_single pauliX_mem_unitaryGroup).isTP

theorem adaptiveFeedForward_isFiniteRoundLOCC :
    IsFiniteRoundLOCC Bool (adaptiveFeedForward.map KrausGate.ev) :=
  isFiniteRoundLOCC_iff.mpr ⟨adaptiveFeedForward, adaptiveFeedForward_forall_isTP, rfl⟩

theorem adaptiveFeedForward_toSeparableOperation_isTP :
    (adaptiveFeedForward.toSeparableOperation KrausGate.ev).IsTP :=
  adaptiveFeedForward.isTP_toSeparableOperation KrausGate.ev adaptiveFeedForward_forall_isTP

theorem adaptiveFeedForward_map_agrees
    (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    (adaptiveFeedForward.toSeparableOperation KrausGate.ev).map ρ =
      (adaptiveFeedForward.map KrausGate.ev
        (ρ.submatrix (boolConfigEquiv twoQubit) (boolConfigEquiv twoQubit))).submatrix
        (boolConfigEquiv bobOnly).symm (boolConfigEquiv bobOnly).symm :=
  adaptiveFeedForward.toSeparableOperation_map KrausGate.ev ρ

/-! ### 3. Unnormalized (trace-nonincreasing, non-TP) circuit still factorizes -/

/-- A trace-nonincreasing (empty-index) local Kraus family on a qubit. -/
def emptyLocalFamily : KrausFamily (Fin 2) (Fin 2) :=
  ⟨Empty, Empty.elim⟩

theorem emptyLocalFamily_isTraceNonincreasing : emptyLocalFamily.IsTraceNonincreasing := by
  change emptyLocalFamily.effect ≤ 1
  have h0 : emptyLocalFamily.effect = 0 := Finset.sum_empty
  rw [h0]
  exact zero_le_one

/-- A bipartite circuit with an empty-index local family on Alice: TNI, not TP. -/
def tniCircuit : Circuit (Geometry.sites Bool) KrausGate twoQubit twoQubit :=
  Circuit.ofLayer (Layer.ofOnsite fun b ↦
    match b with
    | false => emptyLocalFamily
    | true => KrausFamily.single 1)

theorem tniCircuit_forall_tni :
    tniCircuit.Forall KrausGate.ev KrausFamily.IsTraceNonincreasing := by
  refine ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun s ↦ ?_⟩, fun _ ↦ trivial⟩
  obtain ⟨b, hb⟩ := s
  cases b
  · exact emptyLocalFamily_isTraceNonincreasing
  · exact (KrausFamily.isUnitary_single (one_mem _)).isTP.isTraceNonincreasing

theorem tniCircuit_toSeparableOperation_tni :
    (tniCircuit.toSeparableOperation KrausGate.ev).IsTraceNonincreasing :=
  tniCircuit.isTraceNonincreasing_toSeparableOperation KrausGate.ev tniCircuit_forall_tni

end LOCCTest

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``QuantumCircuit.singletonRegionConfigEquiv,
      ``QuantumCircuit.Layer.mem_biUnion_sites_iff,
      ``QuantumCircuit.Layer.siteKraus,
      ``QuantumCircuit.Layer.kraus_eq_piKronecker_siteKraus,
      ``QuantumCircuit.Circuit.partyKraus,
      ``QuantumCircuit.Circuit.partyKraus_done,
      ``QuantumCircuit.Circuit.partyKraus_step,
      ``QuantumCircuit.Circuit.kraus_eq_piKronecker_partyKraus,
      ``QuantumCircuit.Layer.depth_sites,
      ``QuantumCircuit.Circuit.depth_sites,
      ``QuantumCircuit.boolConfigEquiv,
      ``QuantumCircuit.submatrix_boolConfigEquiv_piKronecker,
      ``QuantumCircuit.Circuit.toSeparableOperation,
      ``QuantumCircuit.Circuit.toSeparableOperation_op,
      ``QuantumCircuit.Circuit.toSeparableOperation_toKrausFamily,
      ``QuantumCircuit.Circuit.toSeparableOperation_map,
      ``QuantumCircuit.Circuit.map_eq_submatrix_toSeparableOperation_map,
      ``QuantumCircuit.Circuit.isTP_toSeparableOperation,
      ``QuantumCircuit.Circuit.isTraceNonincreasing_toSeparableOperation,
      ``QuantumCircuit.IsFiniteRoundLOCC,
      ``QuantumCircuit.IsBoundedRoundLOCC,
      ``QuantumCircuit.isFiniteRoundLOCC_iff,
      ``QuantumCircuit.IsAdaptiveProtocol.id,
      ``QuantumCircuit.IsAdaptiveProtocol.comp,
      ``QuantumCircuit.IsFiniteRoundLOCC.step,
      ``QuantumCircuit.IsAdaptiveProtocol.isKrausCPTP,
      ``QuantumCircuit.IsBoundedRoundLOCC.id,
      ``QuantumCircuit.IsBoundedRoundLOCC.mono,
      ``QuantumCircuit.IsBoundedRoundLOCC.comp,
      ``QuantumCircuit.IsBoundedRoundLOCC.isFiniteRoundLOCC,
      ``QuantumCircuit.isFiniteRoundLOCC_iff_exists_isBoundedRoundLOCC,
      ``QuantumCircuit.IsFiniteRoundLOCC.exists_separableOperation,
      ``LOCCTest.triLayer_factorizes,
      ``LOCCTest.triLayer_depth_zero,
      ``LOCCTest.adaptiveFeedForward_depth_zero,
      ``LOCCTest.adaptiveFeedForward_forall_isTP,
      ``LOCCTest.adaptiveFeedForward_isFiniteRoundLOCC,
      ``LOCCTest.adaptiveFeedForward_toSeparableOperation_isTP,
      ``LOCCTest.adaptiveFeedForward_map_agrees,
      ``LOCCTest.tniCircuit_forall_tni,
      ``LOCCTest.tniCircuit_toSeparableOperation_tni] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
