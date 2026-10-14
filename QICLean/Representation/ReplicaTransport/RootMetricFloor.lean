/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Analysis.Transport.MetricFloor
import QICLean.Representation.ReplicaTransport.Energy
import QICLean.Representation.ReplicaTransport.SymmetricMetricFloor

/-!
# Polynomial floors and normalization bounds for transport roots

Fix the physical dimensions and a positive band exponent. One constant gives
a polynomial lower bound for every admissible transport root whose band
metrics commute. The constant is independent of the number of bands, the
history and choice sets, the transport data, the copy count and the parameter.
The root is formed from the given terminal inputs and interpolation tree.
For every prevector of norm at most one, the same floor yields a logarithmic
upper bound for its squared filtered norm, with the constant chosen before
these data and the vector.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September
24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:
`05-replicas.tex`, `replicas:leaf-floor`, lines 452--465;
`06-transport.tex`, `transport:means`, lines 40--62 and 257--286;
`07-comparators.tex`, lines 603--621.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

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
