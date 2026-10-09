/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.OrthonormalMatrixNorm
import QICLean.Channel.PartialTraceBlocks
import QICLean.Channel.PartialTraceBasisInvariance
import QICLean.Probability.MatrixTraceNormIntegrability
import QICLean.Probability.ComplexGaussian.SourceTransportExpansion
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Kernel dependencies of compression-coordinate identities

Check the imported coordinate, block, integrability and source-expansion results.
Every named declaration must exist, and every transitive axiom dependency must be
one of `propext`, `Classical.choice` and `Quot.sound`. A declaration may use any
subset of these axioms, including the empty set.
-/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  for decl in #[``ContinuousLinearMap.norm_toMatrix_orthonormal,
      ``Matrix.eq_sum_single_kronecker_submatrix,
      ``Matrix.rectangularTraceNorm_le_sum_submatrix,
      ``Matrix.submatrix_partialTraceRight,
      ``Matrix.integral_rectangularTraceNorm_le_sum_submatrix,
      ``Matrix.rectangularTraceNorm_partialTraceRight_isometries,
      ``OrthonormalBasis.tensorProduct_basisChange,
      ``OrthonormalBasis.tensorProduct_rankOne_basisChange,
      ``OrthonormalBasis.rectangularTraceNorm_partialTrace_sum_rankOne_basis_eq,
      ``ProbabilityTheory.integrable_rectangularTraceNorm_sum,
      ``ProbabilityTheory.integrable_rectangularTraceNorm_sum_of_memLp_two,
      ``QICLean.ComplexGaussian.sourceTransport_eq_sum_rankOne] do
    unless env.contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
