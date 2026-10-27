import QICLean.Analysis.ViableSubspaceSchmidtRank
import Lean.Util.CollectAxioms

/-! The public viable-subspace approximation theorems use only the standard
logical foundations. Their transitive proof dependencies are checked here. -/

run_cmd do
  let decls := #[
    ``Submodule.IsViable.exists_unit_mem_prodExt_schmidtRank_le,
    ``Submodule.IsViable.one_sub_le_kyFanNorm,
    ``Submodule.IsViable.exists_unit_schmidtRank_le_of_equiv]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing viable-subspace approximation declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
