/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.IrreducibleSchwarz
import QICLean.Channel.Peripheral.CyclicGroupKraus
import QICLean.Channel.Peripheral.CyclicDecomposition.PeripheralUnitary
import Lean.Util.CollectAxioms

/-! Traverse actual kernel proof bodies, including opaque values, for Wolf Theorem 6.6. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[``SchwarzMap.wolf_theorem_6_6,
    ``SchwarzMap.exists_posDef_traceAdjoint_stationaryState,
    ``Kraus.peripheralEigenvalues_eq_range_primitiveRoot,
    ``Kraus.peripheralEigenvalues_mul_mem_of_irreducible_unital_of_adjoint_fixedPoint,
    ``Kraus.fixed_eq_scalar_of_irreducible_unital,
    ``Kraus.exists_peripheral_unitary_of_irreducible_schwarz,
    ``Kraus.map_powers_of_peripheral_unitary,
    ``Kraus.exists_normalized_peripheral_unitary_of_irreducible_schwarz]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut todo := roots
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut opaqueDecls : NameSet := {}
  while !todo.isEmpty do
    let name := todo.back!
    todo := todo.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Missing kernel declaration in proof dependency closure: {name}"
    if info.isUnsafe then
      throwError "Unsafe declaration reachable from theorem: {name}"
    match info with
    | .axiomInfo _ =>
      axioms := axioms.insert name
      unless allowed.contains name do
        throwError "Unexpected axiom reachable from theorem: {name}"
    | .opaqueInfo _ => opaqueDecls := opaqueDecls.insert name
    | _ => pure ()
    todo := todo ++ info.type.getUsedConstants
    if let some value := info.value? (allowOpaque := true) then
      todo := todo ++ value.getUsedConstants
  logInfo m!"DEPENDENCY AUDIT: {seen.size} kernel declarations; axioms {axioms.toArray}; "
    ++ m!"{opaqueDecls.size} opaque definitions with checked values"
