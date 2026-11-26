/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Metric.SymmetricMetricFloor
import QICLean.ManyBody.Replica.BandMetric.SymmetricMetric
import QICLean.Analysis.OperatorMean.FiniteTree
import QICLean.Channel.OperatorMean.NormDerivative
import QICLean.ManyBody.Replica.BandMetric.Energy

/-!
# Uniform floors for symmetric band metrics and their mean trees

The symmetric band metric is the existing partition metric on complete
symmetric copies, extended by the identity on their orthogonal complement.
A single polynomial exponent bounds these matrices below, uniformly in the
copy number and the partition. Monotonicity gives the same floor for any
finite mean tree of such matrices.

It also contains the following results.

* `TensorPower.ReplicaTransport.exists_rootPath_scalar_floor`,
  `TensorPower.ReplicaTransport.exists_rootPath_log_filteredNormSq_bound`: polynomial floors and
  normalization bounds for transport roots.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
`05-replicas.tex`, equations `replicas:leaf-metric` and
`replicas:leaf-floor`, lines 452–465; `06-transport.tex`,
`transport:band-metric`, lines 251–258, and `transport:means`, lines 40–62;
`07-comparators.tex`, lines 603–621.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

section SymmetricMetricFloor

-- The proofs have been checked with the native dependency revision.
-- Verification of the ordinary module and declaration links remains pending.


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
    symProj (copyPerm (∀ v, Fin (n v)) k) * bandMetric n t k π *
      symProj (copyPerm (∀ v, Fin (n v)) k) +
        (1 - symProj (copyPerm (∀ v, Fin (n v)) k)) at hfloor
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

/-- A fixed number of commuting band factors has a polynomial lower bound
uniform over all finite mean trees, copy counts, partitions and parameters.
Auxiliary product estimate for OpenAI, `05-replicas.tex`, `replicas:leaf-floor`,
lines 452--465, and `06-transport.tex`, `transport:means`, lines 40--62. -/
theorem exists_meanTree_symBandMetric_prod_floor {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K k : ℕ) {J : Type*} (π : J → Fin K → PYF V),
      (∀ j g, (π j g).IsPartition) →
      (∀ j, (List.ofFn fun g => symBandMetric n t k (π j g)).Pairwise
        fun A B => Commute A B) → ∀ T : Matrix.MeanTree J,
      ((k : ℝ) + 2) ^ (-(C * (K : ℝ))) •
        (1 : Matrix (Config k fun v => Fin (n v))
          (Config k fun v => Fin (n v)) ℂ) ≤
            T.eval (fun j => (List.ofFn fun g => symBandMetric n t k (π j g)).prod) := by
  classical
  obtain ⟨C, hC, hfloor⟩ := exists_symBandMetric_floor n ht
  refine ⟨C, hC, ?_⟩
  intro K k J π hπ hcomm T
  have hleaf : ∀ j, (((k : ℝ) + 2) ^ (-C)) ^ K •
      (1 : Matrix (Config k fun v => Fin (n v))
        (Config k fun v => Fin (n v)) ℂ) ≤
      (List.ofFn fun g => symBandMetric n t k (π j g)).prod := fun j => by
    simpa only [List.length_ofFn] using Matrix.pow_smul_one_le_list_prod
      (Real.rpow_nonneg (by positivity) (-C))
      (List.forall_mem_ofFn_iff.mpr fun g => hfloor k (π j g) (hπ j g))
      (hcomm j)
  have hinput : ∀ j, ((k : ℝ) + 2) ^ (-(C * (K : ℝ))) •
      (1 : Matrix (Config k fun v => Fin (n v))
        (Config k fun v => Fin (n v)) ℂ) ≤
      (List.ofFn fun g => symBandMetric n t k (π j g)).prod := fun j => by
    simpa only [← Real.rpow_mul_natCast (show 0 ≤ (k : ℝ) + 2 by positivity),
      neg_mul] using hleaf j
  have hI : (((k : ℝ) + 2) ^ (-(C * (K : ℝ))) •
      (1 : Matrix (Config k fun v => Fin (n v))
        (Config k fun v => Fin (n v)) ℂ)).PosDef :=
    PosDef.one.smul (Real.rpow_pos_of_pos (by positivity) _)
  simpa only [T.eval_const hI] using T.eval_mono (fun _ => hI) hinput

end TensorPower.ReplicaTransport

end SymmetricMetricFloor

section RootMetricFloor

/-!
## Polynomial floors and normalization bounds for transport roots

Fix the physical dimensions and a positive band exponent. One constant gives
a polynomial lower bound for every admissible transport root whose band
metrics commute. The constant is independent of the number of bands, the
history and choice sets, the transport data, the copy count and the parameter.
The root is formed from the given terminal inputs and interpolation tree.
For every prevector of norm at most one, the same floor yields a logarithmic
upper bound for its squared filtered norm, with the constant chosen before
these data and the vector.

### References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
`05-replicas.tex`, `replicas:leaf-floor`, lines 452--465;
`06-transport.tex`, `transport:means`, lines 40--62 and 257--286;
`07-comparators.tex`, lines 603--621.
-/

universe uH uC
namespace TensorPower.ReplicaTransport
variable {V : Type*} [Fintype V] [DecidableEq V]
  (n : V → ℕ) [∀ v, NeZero (n v)]

/-- One polynomial exponent bounds every literal transport root, before the
band count, history and choice types, transport data, copy count or parameter.
OpenAI, `05-replicas.tex`, `replicas:leaf-floor`, lines 452--465;
`06-transport.tex`, `transport:means`, lines 40--62 and 257--286. -/
theorem exists_rootPath_scalar_floor {t : ℝ} (ht : 0 < t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (K : ℕ) {H : Type uH} [DecidableEq H]
      {C : H → Type uC} [∀ h, DecidableEq (C h)] (D : TransportData V K H C),
      D.IsAdmissible → ∀ (k : ℕ), D.CrossBandCommute n t k → ∀ (q : ℝ),
      ((k : ℝ) + 2) ^ (-(C₀ * (K : ℝ))) •
        (1 : Matrix (Config k fun v => Fin (n v))
          (Config k fun v => Fin (n v)) ℂ) ≤ D.rootPath n t k q := by
  classical
  obtain ⟨C₀, hC₀, hfloor⟩ := exists_meanTree_symBandMetric_prod_floor n ht
  refine ⟨C₀, hC₀, ?_⟩
  intro K H instH C instC D hD k hcomm q
  have hleafComm : ∀ j, (List.ofFn fun g => symBandMetric n t k (D.leafPart j g)).Pairwise
      fun A B => Commute A B := fun j => List.pairwise_ofFn.mpr fun g g' hgg' =>
    ((D.crossBandCommute_iff (n := n) t k).mp hcomm) j j g g' (ne_of_lt hgg')
  simpa only [← D.input_eq_prod (n := n) t k, TransportData.rootPath] using
    hfloor K k D.leafPart (D.isPartition_leafPart hD) hleafComm
      (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one q))

/-- A common logarithmic bound for the squared filtered norm of every transport
root, with the exponent chosen before the transport data and copy count.
Auxiliary normalization estimate for OpenAI, `07-comparators.tex`, lines 603--621. -/
theorem exists_rootPath_log_filteredNormSq_bound {t : ℝ} (ht : 0 < t) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (K : ℕ) {H : Type uH} [DecidableEq H]
      {C : H → Type uC} [∀ h, DecidableEq (C h)] (D : TransportData V K H C),
      D.IsAdmissible → ∀ (k : ℕ), D.CrossBandCommute n t k → ∀ (q : ℝ)
      (pre : Config k (fun v => Fin (n v)) → ℂ),
      ‖(EuclideanSpace.equiv (Config k fun v => Fin (n v)) ℂ).symm pre‖ ≤ 1 →
      Real.log (Matrix.Transport.filteredNormSq (D.rootPath n t k q) pre) ≤
        (C₀ * (K : ℝ) / 2) * Real.log ((k : ℝ) + 2) := by
  obtain ⟨C₀, hC₀, hfloor⟩ := exists_rootPath_scalar_floor n ht
  refine ⟨C₀, hC₀, ?_⟩
  intro K H instH C instC D hD k hcomm q pre hpre
  have hM : (D.rootPath n t k q).PosDef :=
    MeanTree.posDef_eval (D.posDef_input hD ht.le hcomm) _
  exact Matrix.Transport.log_filteredNormSq_le_of_rpow_floor hM
    (mul_nonneg hC₀ (Nat.cast_nonneg K))
    (by linarith [Nat.cast_nonneg (α := ℝ) k]) (hfloor K D hD k hcomm q) pre hpre

end TensorPower.ReplicaTransport

end RootMetricFloor
