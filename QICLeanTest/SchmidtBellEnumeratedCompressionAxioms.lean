/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellEnumeratedCompression
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit compression of the band product and original prevector under enumeration. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[``FiniteProduct.replicaMetric_compressed_bandProduct_enumerate_C,
    ``FiniteProduct.schmidtBellSitePrevector_compressed_enumerate_C]
  for decl in declarations do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
