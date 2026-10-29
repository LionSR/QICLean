/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace

/-!
# Dimensions of mutually approximating subspaces

If one subspace approximates another with squared projection loss below one,
the approximating subspace has at least the dimension of the other. Thus two
nested subspaces that approximate a third in opposite directions coincide.
Every intermediate subspace retains both approximation estimates.

These finite-dimensional consequences of ALVV, arXiv:1602.08828v2, Lemma `l:2`,
lines 449–465, give the dimension comparison used in the proof of Theorem
`t:ais`, line 1020. They impose no one-dimensional or nonzero-space condition.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- A subspace approximated with error below one has no larger dimension than
its approximating subspace. This is a finite-dimensional consequence of ALVV,
arXiv:1602.08828v2, Lemma `l:2`, lines 449–465. -/
theorem IsCloseTo.finrank_le {δ : ℝ} {U T : Submodule 𝕜 E}
    (h : IsCloseTo δ U T) (hδ : δ < 1) :
    Module.finrank 𝕜 T ≤ Module.finrank 𝕜 U := by
  let f : U →ₗ[𝕜] T := T.orthogonalProjectionOnto.toLinearMap.comp U.subtype
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨u, hu, hut, _⟩ := h.exists_mem_starProjection_eq hδ t.property
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    change T.starProjection u = (t : E)
    exact hut
  exact LinearMap.finrank_le_finrank_of_surjective hf

/-- If two nested subspaces approximate a third in opposite directions with
errors below one, then they coincide. Every intermediate subspace is the same
space and retains both approximation bounds. This supplies the dimension step
for the hard-truncation argument in ALVV, arXiv:1602.08828v2, proof of
Theorem `t:ais`, line 1020; no Hamiltonian conclusion is asserted here. -/
theorem eq_and_isCloseTo_of_le {δ δ' : ℝ} {U V G : Submodule 𝕜 E}
    (hUV : U ≤ V) (hUG : IsCloseTo δ U G) (hGV : IsCloseTo δ' G V)
    (hδ : δ < 1) (hδ' : δ' < 1) :
    U = V ∧ ∀ W : Submodule 𝕜 E, U ≤ W → W ≤ V →
      W = U ∧ IsCloseTo δ W G ∧ IsCloseTo δ' G W := by
  have hdim : Module.finrank 𝕜 V ≤ Module.finrank 𝕜 U :=
    (hGV.finrank_le hδ').trans (hUG.finrank_le hδ)
  have hEq : U = V := Submodule.eq_of_le_of_finrank_le hUV hdim
  refine ⟨hEq, ?_⟩
  intro W hUW hWV
  have hWU : W = U := le_antisymm (hWV.trans (le_of_eq hEq.symm)) hUW
  refine ⟨hWU, ?_, ?_⟩
  · simpa only [hWU] using hUG
  · simpa only [hWU, hEq] using hGV

end Submodule
