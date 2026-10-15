import QICLean.Entropy.FiniteProductConditionalSum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``FiniteProduct.mutualInformation_union_biUnion_le_of_conditional] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
