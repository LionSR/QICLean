/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaPinnedLeafExpectation
import QICLean.Analysis.MeanTreeUniformExpectation

/-!
# The actual pinned band product and its inverse-power estimate

The same weighted mean tree is evaluated separately in each band, and the
resulting roots are multiplied in band order. The manuscript's nesting
across all statuses makes different bands commute. The existing finite-tree
factorization therefore identifies this actual product with the tree whose
inputs are the corresponding ordered products.

Positivity, cross-band commutation, and leaf expectation bounds are derived
from the actual replica metrics and region relations. The final overlap
estimate takes only the actual cutoff conditions and a unit test vector;
no leaf-positivity, commutation, or operator-bound certificate is assumed.
The original full-system label weights are retained throughout.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, `comparator:nesting`,
  `comparator:pinned-metric`, and lines 367–381; `06-transport.tex`,
  Lemma 7.1, `transport:means` and `transport:vector-jensen`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
open scoped Matrix.Norms.L2Operator InnerProductSpace MatrixOrder ComplexOrder

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)]
variable {J : Type*}

/-- Actual cross-status nesting identifies the ordered product of band roots
with the same weighted tree evaluated on the actual ordered leaf products.
Both positivity and the cross-band commutations are derived internally.

Source: area-law manuscript, `06-transport.tex`, Lemma 7.1,
`transport:means`; `07-comparators.tex`, lines 367–375. -/
theorem replicaPinnedTree_eval_eq_prod {t : ℝ} (ht : 0 ≤ t) (k K : ℕ)
    (U Y : J → Fin K → Finset F)
    (hdisj : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h)
    (T : Matrix.MeanTree J) :
    let D := fun j g ↦ ((replicaMetric ι t k (U j g))⁻¹ *
      (replicaMetric ι t k (U j g ∪ Y j g))⁻¹ * replicaMetric ι t k (Y j g)) ^ 2
    T.eval (fun j ↦ (List.ofFn (D j)).prod) =
      (List.ofFn fun g ↦ T.eval (D · g)).prod := by
  intro D
  obtain ⟨hD, hcomm⟩ := replicaPinnedBands_posDef_commute ι ht k K U Y hdisj hnest
  exact T.eval_listProd_ofFn hD hcomm

variable [Finite J]

/-- The actual ordered product of band roots satisfies the inverse-power
Cauchy–Schwarz bound obtained from the derived cutoff estimates and the two
Jensen inequalities. No positivity, commutation, or leaf estimate is supplied.
The vector u is arbitrary; only the test vector φ is normalized.

Source: area-law manuscript, `07-comparators.tex`, lines 367–381. -/
theorem exists_replicaPinnedTree_inverse_norm_bound {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k K : ℕ) (U Y : J → Fin K → Finset F),
      (∀ j g, Disjoint (U j g) (Y j g)) →
      (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
      ∀ (T : Matrix.MeanTree J) (a : ℝ)
        (φ u : EuclideanSpace ℂ (Config k ι)), ‖φ‖ = 1 →
        (∀ j g, toEuclideanLin (labelCutoff (subsystemPerm k ι (U j g)) a) φ = φ ∧
          toEuclideanLin (labelCutoff (subsystemPerm k ι (U j g ∪ Y j g)) a) φ = φ) →
        ∀ s : ℝ, 2 * s ∈ Set.Icc (0 : ℝ) 1 →
        let D := fun j g ↦ ((replicaMetric ι t k (U j g))⁻¹ *
          (replicaMetric ι t k (U j g ∪ Y j g))⁻¹ * replicaMetric ι t k (Y j g)) ^ 2
        ‖inner ℂ φ u‖ ^ 2 ≤
          (((k : ℝ) + 2) ^ (C * (K : ℝ)) * Real.exp (4 * t * (K : ℝ) * a)) ^
            (2 * s) *
          ‖toEuclideanLin (((List.ofFn fun g ↦ T.eval (D · g)).prod) ^ (-s)) u‖ ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_replicaPinnedLeaf_expectation_le ι ht
  refine ⟨C, hC0, ?_⟩
  intro k K U Y hdisj hnest T a φ u hφ hcuts s hs D
  let L : ℝ := ((k : ℝ) + 2) ^ (C * (K : ℝ)) * Real.exp (4 * t * (K : ℝ) * a)
  have hL : 0 < L := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  have hpos (j : J) : (List.ofFn (D j)).prod.PosDef :=
    posDef_replicaPinnedLeaf ι ht.le k K (U j) (Y j) (hdisj j) (hnest j j)
  have hleaf (j : J) :
      (inner ℂ φ (toEuclideanLin (List.ofFn (D j)).prod φ)).re ≤ L := by
    simpa only [hφ, one_pow, mul_one] using
      hC k K (U j) (Y j) (hdisj j) (hnest j j) a φ (hcuts j)
  have h := T.norm_inner_sq_le_rpow_mul_inverse_norm_sq hpos φ u hφ hL hs hleaf
  rw [replicaPinnedTree_eval_eq_prod ι ht.le k K U Y hdisj hnest T] at h
  exact h

end TensorPower
