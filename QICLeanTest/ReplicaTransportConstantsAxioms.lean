/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.FiniteFamily

/-! Require the replica-transport estimates at the named constants to use only standard
axioms. -/

open TensorPower.ReplicaTransport in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Entropy.conditionalMovement_norm_le_explicit,
      ``Entropy.regionalMovement_norm_le_explicit,
      ``TensorPower.relativePin_explicit,
      ``TensorPower.relativePin_regionalMovementEta_explicit,
      ``relativePinBoundAt,
      ``splitSkewBoundAt,
      ``TransportData.exists_entropyGain_le_exactDerivative_of_relativePinBoundAt,
      ``TransportData.exists_energy_le_of_splitSkewBoundAt,
      ``transport_of_relativePinBoundAt_of_splitSkewBoundAt,
      ``transport_of_splitSkewBoundAt,
      ``transport_explicit,
      ``transport_finite_family_explicit,
      ``transportThreshold_eq,
      ``transportEntropyConst_eq,
      ``transportEntropyExponent_eq,
      ``transportEnergyConst_eq,
      ``transportEnergyExponent_eq] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
