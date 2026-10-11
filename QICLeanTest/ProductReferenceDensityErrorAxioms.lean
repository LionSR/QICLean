/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ProductReferenceDensityError
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Fail closed unless every new theorem exists and uses only the standard
trusted Lean axioms. The collected sets are also written to the CI log. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``Matrix.rectangularTraceNorm_reindex,
      ``Matrix.partialTraceRight_tensorVector_eq_smul,
      ``Matrix.rectangularTraceNorm_product_reference_sub_le,
      ``Matrix.rectangularTraceNorm_partialTraceRight_sub_product_reference_le,
      ``Matrix.rectangularTraceNorm_partialTraceRight_sub_product_reference_le_of_norm_sub_le,
      ``Matrix.rectangularTraceNorm_sub_pure_le_of_product_reference,
      ``Matrix.one_sub_le_norm_of_product_reference,
      ``Matrix.trace_deficit_partialTraceRight_le_of_product_reference] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
