/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSymmetricMetricFloor
import QICLean.Representation.ReplicaTransport.SymmetricMetric
import QICLean.Analysis.OperatorMean.FiniteTree

/-!
# Uniform floors for symmetric band metrics and their mean trees

The symmetric band metric is the existing partition metric on complete
symmetric copies, extended by the identity on their orthogonal complement.
A single polynomial exponent bounds these matrices below, uniformly in the
copy number and the partition. Monotonicity gives the same floor for any
finite mean tree of such matrices.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
`05-replicas.tex`, equations `replicas:leaf-metric` and
`replicas:leaf-floor`, lines 452–465; `06-transport.tex`,
`transport:band-metric`, lines 251–258, and `transport:means`, lines 40–62;
`07-comparators.tex`, lines 603–621.
-/

-- The proofs have been checked with the native dependency revision.
-- Verification of the ordinary module and declaration links remains pending.

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V]
  (n : V → ℕ) [∀ v, NeZero (n v)]

/-- The identity extension of every actual partition metric has one
polynomial floor, with the exponent chosen before the copy number or the
partition. OpenAI, `05-replicas.tex`, `replicas:leaf-floor`, lines 452–465;
`06-transport.tex`, `transport:band-metric`, lines 251–258. -/
theorem exists_symBandMetric_floor {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (π : PYF V), π.IsPartition →
      ((k : ℝ) + 2) ^ (-C) •
        (1 : Matrix (Config k fun v => Fin (n v))
          (Config k fun v => Fin (n v)) ℂ) ≤ symBandMetric n t k π := by
  obtain ⟨C, hC, hbound⟩ :=
    TensorPower.exists_replicaMetric_symmetric_floor (fun v => Fin (n v)) ht
  refine ⟨C, hC, ?_⟩
  rintro k π ⟨hPY, hPF, hYF, hcover⟩
  have hfloor := (hbound k π.P π.Y π.F hPY hPF hYF hcover).2.2.2.2
  change _ ≤
    symProj (copyPerm (Entropy.SiteConfig n) k) * bandMetric n t k π *
      symProj (copyPerm (Entropy.SiteConfig n) k) +
        (1 - symProj (copyPerm (Entropy.SiteConfig n) k)) at hfloor
  rw [mul_assoc, ← (commute_symProj_bandMetric (n := n) t k π).eq,
    ← mul_assoc, symProj_mul_symProj] at hfloor
  simpa only [symBandMetric, RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hfloor

/-- Every finite mean tree of actual symmetric partition metrics has a
polynomial floor uniform in its copy number, partitions and interpolation
parameters. The exponent is chosen before the label type and tree.
OpenAI, `06-transport.tex`, `transport:means`, lines 40–62, and
`07-comparators.tex`, lines 603–621.
-/
theorem exists_meanTree_symBandMetric_floor {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) {J : Type*} (π : J → PYF V),
      (∀ j, (π j).IsPartition) → ∀ T : Matrix.MeanTree J,
      ((k : ℝ) + 2) ^ (-C) •
        (1 : Matrix (Config k fun v => Fin (n v))
          (Config k fun v => Fin (n v)) ℂ) ≤
            T.eval (fun j => symBandMetric n t k (π j)) := by
  obtain ⟨C, hC, hfloor⟩ := exists_symBandMetric_floor n ht
  refine ⟨C, hC, ?_⟩
  intro k J π hπ T
  have hc : 0 < ((k : ℝ) + 2) ^ (-C) :=
    Real.rpow_pos_of_pos (by positivity) (-C)
  have hI : (((k : ℝ) + 2) ^ (-C) •
      (1 : Matrix (Config k fun v => Fin (n v))
        (Config k fun v => Fin (n v)) ℂ)).PosDef := PosDef.one.smul hc
  simpa only [T.eval_const hI] using
    T.eval_mono (fun _ => hI) (fun j => hfloor k (π j) (hπ j))

end TensorPower.ReplicaTransport
