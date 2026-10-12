/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.RootCompression
import QICLean.Representation.BellPinnedCompressedPowers
import QICLean.Representation.ReplicaSymmetricMeanTreeProduct
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Audit the common product identity and its three applications in symmetric coordinates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.listProd_ofFn_intertwine,
    ``TensorPower.ReplicaTransport.TransportData.rootPath_compressed_bandProduct,
    ``TensorPower.replicaMetric_compressed_bandProduct_bellPin_rpow,
    ``TensorPower.replicaMetric_symProj_meanTree_eq_product]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
