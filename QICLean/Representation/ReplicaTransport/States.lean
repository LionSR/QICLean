/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Setup
import QICLean.Analysis.Transport.Derivative

/-!
# Metrics, transport states and the exact derivative for replica histories

For admissible finite data with cross-band commutation, the old and new metrics are
positive definite, the transport states `σ_{j,u}` are density matrices on the symmetric
subspace `𝒮_k`, and the exact derivative of the area-law paper, Proposition 7.4
(display `transport:exact-derivative`, `06-transport.tex` lines 402--408), holds for the
replica root `M(p)`.

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator unitInterval
open Matrix Set PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ} [∀ v, NeZero (n v)]

/-- A band metric of a partition is positive definite (`06-transport.tex` line 256). -/
theorem posDef_bandMetric {π : PYF V} (hπ : π.IsPartition) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (bandMetric n t k π).PosDef := by
  sorry

/-- A valid move of a partition gives a partition. -/
theorem Move.isPartition_apply {π : PYF V} (hπ : π.IsPartition) {m : Move V}
    (hm : m.IsValid π) : (m.apply π).IsPartition := by
  sorry

namespace TransportData

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)

/-- Every terminal partition is a partition. -/
theorem isPartition_leafPart (hD : D.IsAdmissible) (j : Σ h, Option (C h)) (g : Fin K) :
    (D.leafPart j g).IsPartition := by
  sorry

/-- The terminal inputs are positive definite. -/
theorem posDef_input (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) (j : Σ h, Option (C h)) :
    (D.input n t k j).PosDef := by
  sorry

/-- The terminal inputs commute with every copy permutation. -/
theorem commute_permOp_input {t : ℝ} (k : ℕ) (s : Equiv.Perm (Fin k))
    (j : Σ h, Option (C h)) :
    Commute (permOp (copyPerm (SiteConfig n) k) s) (D.input n t k j) := by
  sorry

/-- Every terminal weight is positive for `0 < p < 1`. -/
theorem weight_tree_pos (hD : D.IsAdmissible) {p : ℝ} (hp : p ∈ Ioo 0 1)
    (j : Σ h, Option (C h)) : 0 < (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).weight j := by
  sorry

/-- The transport states are density matrices on `𝒮_k` (`06-transport.tex` line 491). -/
theorem posSemidef_state (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ)
    (j : Σ h, Option (C h)) (u : ℝ) : (D.state n t k pre p j u).PosSemidef := by
  sorry

theorem trace_state (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ≠ 0) {p : ℝ} (hp : p ∈ Ioo 0 1) (j : Σ h, Option (C h)) (u : ℝ) :
    (D.state n t k pre p j u).trace = 1 := by
  sorry

theorem symProj_mul_state (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ∈ symmetricSubspace k (fun v => Fin (n v))) (p : ℝ)
    (j : Σ h, Option (C h)) (u : ℝ) :
    symProj (copyPerm (SiteConfig n) k) * D.state n t k pre p j u = D.state n t k pre p j u := by
  sorry

/-- **Exact derivative for replica histories** (area-law paper, Proposition 7.4, display
`transport:exact-derivative`, `06-transport.tex` lines 402--408). -/
theorem hasDerivAt_exactDerivative (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ≠ 0) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    HasDerivAt (fun q => -Real.log (Transport.filteredNormSq (D.rootPath n t k q) pre))
      (D.exactDerivative n t k pre p) p := by
  have hA : ∀ h, (D.oldMetric n t k h).PosDef := fun h => D.posDef_input hD ht hcomm ⟨h, none⟩
  have hA' : ∀ h c, (D.newMetric n t k h c).PosDef := fun h c =>
    D.posDef_input hD ht hcomm ⟨h, some c⟩
  exact Transport.hasDerivAt_neg_log_filteredNormSq hA hA' hD.histWeight_pos hp hpre

end TransportData

end TensorPower.ReplicaTransport
