/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspace

/-!
# Closeness from inclusion of subspaces

A subspace containing a target has zero projection loss on that target.
It is therefore close to the target at every nonnegative error parameter.
This includes self-closeness as the equality case. Closeness is also
monotone in its error parameter. These are supporting
projection identities for ALVV, arXiv:1602.08828v2, Lemma `l:close`,
lines 484–489, and the short-region alternatives to Theorems `t:ais`
and `t:aisgapless`, lines 1010–1041.
-/

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Closeness is monotone in the parameter: a `δ`-close subspace is `δ'`-close for `δ ≤ δ'`. -/
theorem IsCloseTo.of_le {δ δ' : ℝ} {U T : Submodule 𝕜 E} (h : IsCloseTo δ U T) (hδ : δ ≤ δ') :
    IsCloseTo δ' U T := by
  rw [isCloseTo_iff] at h ⊢
  intro t ht
  refine le_trans ?_ (h t ht)
  nlinarith [sq_nonneg ‖t‖]

/-- Inclusion gives closeness at every nonnegative error parameter.
In particular a target is close to itself. Auxiliary to ALVV,
arXiv:1602.08828v2, Lemma `l:close`, lines 484–489. -/
theorem isCloseTo_of_le {delta : ℝ} {U T : Submodule 𝕜 E}
    (hdelta : 0 ≤ delta) (hTU : T ≤ U) : IsCloseTo delta U T := by
  apply isCloseTo_iff.mpr
  intro x hx
  rw [U.starProjection_eq_self_iff.mpr (hTU hx)]
  exact mul_le_of_le_one_left (sq_nonneg _) (by linarith only [hdelta])

end Submodule
