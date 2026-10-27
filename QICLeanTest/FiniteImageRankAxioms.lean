/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceBootstrap
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Dimension of finite image spans, including an empty family and the zero subspace. -/

open scoped BigOperators

namespace Submodule

section

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

example (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S]
    (A : Fin 0 → E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (↥((⨆ i, S.map (A i)) : Submodule 𝕜 F)) ≤ 0 := by
  simpa using finrank_iSup_map_le_card_mul S A

example (A : Fin 2 → E →ₗ[𝕜] F) :
    Module.finrank 𝕜 (↥((⨆ i, (⊥ : Submodule 𝕜 E).map (A i)) : Submodule 𝕜 F)) ≤ 0 := by
  simpa using finrank_iSup_map_le_card_mul (⊥ : Submodule 𝕜 E) A

example (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] (D : ℕ)
    (A : Fin (D ^ 2) → E →L[𝕜] F) :
    Module.finrank 𝕜 (↥((⨆ i, S.map (A i).toLinearMap) : Submodule 𝕜 F)) ≤
      D ^ 2 * Module.finrank 𝕜 S := by
  simpa only [Fintype.card_fin] using
    (finrank_iSup_map_le_card_mul S (fun i ↦ (A i).toLinearMap))

end

end Submodule

run_cmd do
  let env ← Lean.getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Submodule.finrank_iSup_map_le_card_mul,
      ``Submodule.IsViable.map_of_tensor_decomposition,
      ``Submodule.IsViable.spectralProjector,
      ``Submodule.exists_isViable_finrank_le_half,
      ``Submodule.viable_enlargement_of_close_improving_target] do
    unless env.contains decl do
      throwError "Missing finite-image dimension declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected foundations for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
