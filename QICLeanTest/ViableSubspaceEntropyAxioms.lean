import QICLean.Analysis.ViableSubspaceBootstrap
import QICLean.Analysis.ProbabilityEntropyRankTails
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Analysis.ViableSubspaceEntropy
import Lean.Elab.Command
import Lean.Util.CollectAxioms

run_cmd do
  let env ← Lean.getEnv
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``Submodule.viable_enlargement_of_close_improving_target,
      ``Entropy.probabilityEntropy_le_of_cubic_dyadic_rank_tail_bounds,
      ``Submodule.euclideanTensorEquiv_symm_comm,
      ``Submodule.unit_cut_spectral_probability,
      ``Submodule.actualRegionSplit_marginal_and_entropy] do
    unless env.contains decl do
      throwError "Missing public entropy declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.size == expected.size && axioms.all (expected.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
