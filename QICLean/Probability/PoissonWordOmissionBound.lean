/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordTelescope
import Mathlib.Analysis.Normed.Group.Basic

/-!
# A norm bound for omitted chronological maps

Contractive linear maps preserve the norm bound through every full suffix.
The chronological omission identity therefore bounds the discrepancy by the
sum of one-map defects on the actual retained prefixes. The sum counts each
original omitted occurrence separately.

This is the pointwise comparison preceding the expectation estimate in
OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, `09-amplification.tex`, lines 203–209, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators

namespace PoissonWord

variable {ι 𝕜 V : Type*} [Semiring 𝕜]
  [SeminormedAddCommGroup V] [Module 𝕜 V]

/-- The discrepancy of full and retained chronological actions is bounded
by the sum of omitted-map defects on the retained prefixes. Auxiliary to
`09-amplification.tex`, lines 203–209. -/
theorem norm_foldl_sub_partitionWords_fst_le_sum
    (E : ι → V →ₗ[𝕜] V) (hE : ∀ i y, ‖E i y‖ ≤ ‖y‖)
    (p : ι → Prop) [DecidablePred p] (w : Word ι) (x : V) :
    let act : List ι → V → V :=
      fun xs y ↦ xs.foldl (fun z i ↦ E i z) y
    let retained : Word ι → V :=
      fun u ↦ act ((List.ofFn (partitionWords p u).1.2).map Subtype.val) x
    ‖act (List.ofFn w.2) x - retained w‖ ≤
      ∑ j : Fin w.1, if p (w.2 j) then 0 else
        ‖E (w.2 j) (retained (take w j)) - retained (take w j)‖ := by
  dsimp only
  have hact (xs : List ι) (y : V) :
      ‖xs.foldl (fun z i ↦ E i z) y‖ ≤ ‖y‖ := by
    exact List.foldlRecOn (motive := fun z : V ↦ ‖z‖ ≤ ‖y‖) xs
      (fun z i ↦ E i z) le_rfl (fun z hz i _ ↦ (hE i z).trans hz)
  rw [foldl_sub_partitionWords_fst_eq_sum E p w x]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro j _
  by_cases hp : p (w.2 j)
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    exact hact _ _

end PoissonWord
