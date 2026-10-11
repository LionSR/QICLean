/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.PoissonWordOmissionBound
import QICLean.Probability.PoissonWordRealOccupation

/-!
# Expected norm of omissions in chronological products

The maps are applied in the original order of each Poissonized word. Removing
the letters outside a fixed retained alphabet changes the output by at most
the sum of the corresponding defects on the earlier retained prefixes. The
expected sum is the time integral of those defects under the actual retained
word law. Each defect is bounded by twice the norm of the initial vector.

This is the algebraic and probabilistic comparison used before the spatial
estimate in OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `09-amplification.tex`, lines 203–209, source revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace PoissonWord

variable {ι 𝕜 V : Type*} [Fintype ι] [Semiring 𝕜]
  [SeminormedAddCommGroup V] [Module 𝕜 V]

/-- The expected discrepancy is bounded by the time integral of omitted-map
defects on the actual retained word. No normalization of the initial vector,
nonempty alphabet, or independence hypothesis is required. Auxiliary to the
area-law manuscript, `09-amplification.tex`, lines 203–209. -/
theorem integral_norm_sub_retained_le
    (E : ι → V →ₗ[𝕜] V) (hE : ∀ i y, ‖E i y‖ ≤ ‖y‖)
    (p : ι → Prop) [DecidablePred p] (T : ℝ≥0) (x : V) :
    let act : List ι → V → V :=
      fun xs y ↦ xs.foldl (fun z i ↦ E i z) y
    let retained : Word {i // p i} → V :=
      fun u ↦ act ((List.ofFn u.2).map Subtype.val) x
    (∫ w : Word ι,
        ‖act (List.ofFn w.2) x - retained (partitionWords p w).1‖
        ∂measure ι T) ≤
      ∫ s : ℝ in Set.Ioc 0 (T : ℝ),
        ∑ i ∈ Finset.univ.filter (fun i ↦ ¬p i),
          ∫ u : Word {i // p i}, ‖E i (retained u) - retained u‖
            ∂measure {i // p i} (Real.toNNReal s) := by
  dsimp only
  have hact (xs : List ι) (y : V) :
      ‖xs.foldl (fun z i ↦ E i z) y‖ ≤ ‖y‖ :=
    List.foldlRecOn (motive := fun z : V ↦ ‖z‖ ≤ ‖y‖) xs
      (fun z i ↦ E i z) le_rfl (fun z hz i _ ↦ (hE i z).trans hz)
  let R (u : Word {i // p i}) : V :=
    ((List.ofFn u.2).map Subtype.val).foldl (fun z i ↦ E i z) x
  let F (u : Word {i // p i}) (i : ι) : ℝ := ‖E i (R u) - R u‖
  have hF (u : Word {i // p i}) (i : ι) : F u i ≤ ‖x‖ + ‖x‖ :=
    (norm_sub_le (E i (R u)) (R u)).trans
      (add_le_add ((hE i (R u)).trans (hact _ x)) (hact _ x))
  let L (w : Word ι) : ℝ :=
    ‖(List.ofFn w.2).foldl (fun z i ↦ E i z) x - R (partitionWords p w).1‖
  have hL (w : Word ι) : L w ≤ ‖x‖ + ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add (hact _ x) (hact _ x))
  have hleft : Integrable L (measure ι T) :=
    integrable_of_nonneg_le_const T L (fun _ ↦ norm_nonneg _) hL
  have hsum := integrable_sum_omitted_partition_prefix p T F
    (fun _ _ ↦ norm_nonneg _) hF
  have hpoint (w : Word ι) : L w ≤
      ∑ j : Fin w.1, if p (w.2 j) then 0 else
        F (partitionWords p (take w j)).1 (w.2 j) :=
    norm_foldl_sub_partitionWords_fst_le_sum E hE p w x
  exact (integral_mono hleft hsum hpoint).trans_eq
    (integral_sum_omitted_partition_prefix p T F (fun _ _ ↦ norm_nonneg _) hF)

end PoissonWord
