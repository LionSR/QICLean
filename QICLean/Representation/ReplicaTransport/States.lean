/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Setup
import QICLean.Analysis.Transport.Derivative
import QICLean.Analysis.Transport.Commutant

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

omit [Fintype V] [DecidableEq V] [∀ v, NeZero (n v)] in
/-- A matrix commuting with an invertible matrix commutes with its inverse. -/
theorem commute_inv_of_commute {m : Type*} [Fintype m] [DecidableEq m] {A A' B : Matrix m m ℂ}
    (hA : A * A' = 1) (hA' : A' * A = 1) (h : Commute A B) : Commute A B⁻¹ := by
  have hB : A' * B * A = B := by
    rw [Matrix.mul_assoc, ← h.eq, ← Matrix.mul_assoc, hA', Matrix.one_mul]
  have hi : B⁻¹ = A' * B⁻¹ * A := by
    conv_lhs => rw [← hB]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hA,
      Matrix.inv_eq_right_inv hA', Matrix.mul_assoc]
  change A * B⁻¹ = B⁻¹ * A
  conv_lhs => rw [hi]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.one_mul]

/-- A band metric of a partition is positive definite (`06-transport.tex` line 256). -/
theorem posDef_bandMetric {π : PYF V} (hπ : π.IsPartition) {t : ℝ} (ht : 0 ≤ t) (k : ℕ) :
    (bandMetric n t k π).PosDef := by
  obtain ⟨hPY, hPF, hYF, -⟩ := hπ
  have hR := posDef_leafRoot (n := n) ht k hPY hPF hYF
  rw [bandMetric, leafMetric, pow_two]
  exact hR.mul_of_commute hR (Commute.refl _)

/-- A valid move of a partition gives a partition. -/
theorem Move.isPartition_apply {π : PYF V} (hπ : π.IsPartition) {m : Move V}
    (hm : m.IsValid π) : (m.apply π).IsPartition := by
  obtain ⟨hPY, hPF, hYF, hU⟩ := hπ
  rw [Finset.disjoint_left] at hPY hPF hYF
  cases m with
  | stay => exact ⟨Finset.disjoint_left.mpr hPY, Finset.disjoint_left.mpr hPF,
      Finset.disjoint_left.mpr hYF, hU⟩
  | toP x =>
    have hx : x ⊆ π.Y := hm
    refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_,
      Finset.disjoint_left.mpr ?_, ?_⟩
    · intro a ha hb
      simp only [Move.apply, Finset.mem_union, Finset.mem_sdiff] at ha hb
      rcases ha with ha | ha
      · exact hPY ha hb.1
      · exact hb.2 ha
    · intro a ha hb
      simp only [Move.apply, Finset.mem_union] at ha hb
      rcases ha with ha | ha
      · exact hPF ha hb
      · exact hYF (hx ha) hb
    · intro a ha hb
      simp only [Move.apply, Finset.mem_sdiff] at ha hb
      exact hYF ha.1 hb
    · rw [← hU]
      ext a
      simp only [Move.apply, Finset.mem_union, Finset.mem_sdiff]
      have := @hx a
      tauto
  | toF x =>
    have hx : x ⊆ π.Y := hm
    refine ⟨Finset.disjoint_left.mpr ?_, Finset.disjoint_left.mpr ?_,
      Finset.disjoint_left.mpr ?_, ?_⟩
    · intro a ha hb
      simp only [Move.apply, Finset.mem_sdiff] at ha hb
      exact hPY ha hb.1
    · intro a ha hb
      simp only [Move.apply, Finset.mem_union] at ha hb
      rcases hb with hb | hb
      · exact hPF ha hb
      · exact hPY ha (hx hb)
    · intro a ha hb
      simp only [Move.apply, Finset.mem_union, Finset.mem_sdiff] at ha hb
      rcases hb with hb | hb
      · exact hYF ha.1 hb
      · exact ha.2 hb
    · rw [← hU]
      ext a
      simp only [Move.apply, Finset.mem_union, Finset.mem_sdiff]
      have := @hx a
      tauto

namespace TransportData

variable {K : ℕ} {H : Type*} [Fintype H] [DecidableEq H] {C : H → Type*}
  [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)] (D : TransportData V K H C)

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- Every terminal partition is a partition. -/
theorem isPartition_leafPart (hD : D.IsAdmissible) (j : Σ h, Option (C h)) (g : Fin K) :
    (D.leafPart j g).IsPartition := by
  obtain ⟨h, _ | c⟩ := j
  · exact hD.old_isPartition h g
  · exact Move.isPartition_apply (hD.old_isPartition h g) (hD.move_isValid h c g)

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- The terminal inputs are positive definite. -/
theorem posDef_input (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) (j : Σ h, Option (C h)) :
    (D.input n t k j).PosDef := by
  have key : (List.ofFn fun g => bandMetric n t k (D.leafPart j g)).prod.PosDef :=
    MeanTree.posDef_listProd_ofFn (fun g => posDef_bandMetric (D.isPartition_leafPart hD j g) ht k)
      (fun g g' hgg' => hcomm j j g g' hgg')
  obtain ⟨h, _ | c⟩ := j
  · exact key
  · exact key

omit [∀ v, NeZero (n v)] [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)]
  [∀ h, DecidableEq (C h)] in
/-- The terminal inputs commute with every copy permutation. -/
theorem commute_permOp_input {t : ℝ} (k : ℕ) (s : Equiv.Perm (Fin k))
    (j : Σ h, Option (C h)) :
    Commute (permOp (copyPerm (SiteConfig n) k) s) (D.input n t k j) := by
  have hband : ∀ π : PYF V,
      Commute (permOp (copyPerm (SiteConfig n) k) s) (bandMetric n t k π) := by
    intro π
    have hW : ∀ Q : Finset V, Commute (permOp (copyPerm (SiteConfig n) k) s)
        (replicaMetric (fun v => Fin (n v)) t k Q) := fun Q =>
      commute_copyPerm_labelObservable (n := n) k Q _ s
    have hWi : ∀ Q : Finset V, Commute (permOp (copyPerm (SiteConfig n) k) s)
        (replicaMetric (fun v => Fin (n v)) t k Q)⁻¹ := fun Q =>
      commute_inv_of_commute (permOp_mul_inv_self _ s) (permOp_inv_mul_self _ s) (hW Q)
    exact (((hWi _).mul_right (hWi _)).mul_right (hW _)).pow_right 2
  have key : Commute (permOp (copyPerm (SiteConfig n) k) s)
      (List.ofFn fun g => bandMetric n t k (D.leafPart j g)).prod :=
    Commute.list_prod_right _ _ fun y hy => by
      obtain ⟨g, rfl⟩ := List.mem_ofFn.mp hy
      exact hband _
  obtain ⟨h, _ | c⟩ := j
  · exact key
  · exact key

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- Every terminal weight is positive for `0 < p < 1`. -/
theorem weight_tree_pos (hD : D.IsAdmissible) {p : ℝ} (hp : p ∈ Ioo 0 1)
    (j : Σ h, Option (C h)) : 0 < (D.tree (projIcc (0 : ℝ) 1 zero_le_one p)).weight j := by
  have hp' : ((projIcc (0 : ℝ) 1 zero_le_one p : I) : ℝ) = p :=
    congrArg Subtype.val (projIcc_of_mem _ (Ioo_subset_Icc_self hp))
  obtain ⟨h, _ | c⟩ := j
  · rw [tree, MeanTree.weight_interpTree_old, hp']
    exact mul_pos (by linarith [hp.2]) (hD.histWeight_pos h)
  · rw [tree, MeanTree.weight_interpTree_new, hp']
    exact mul_pos (mul_pos hp.1 (hD.histWeight_pos h)) (hD.choiceWeight_pos h c)

omit [Fintype H] [∀ h, Fintype (C h)] in
/-- The transport states are density matrices on `𝒮_k` (`06-transport.tex` line 491). -/
theorem posSemidef_state (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ)
    (j : Σ h, Option (C h)) (u : ℝ) : (D.state n t k pre p j u).PosSemidef :=
  Transport.posSemidef_transportState (D.posDef_input hD ht hcomm) _ _ _

omit [Fintype H] [∀ h, Fintype (C h)] in
theorem trace_state (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ≠ 0) {p : ℝ} (hp : p ∈ Ioo 0 1) (j : Σ h, Option (C h)) (u : ℝ) :
    (D.state n t k pre p j u).trace = 1 := by
  rw [state, Transport.trace_transportState (D.posDef_input hD ht hcomm)
    (D.weight_tree_pos hD hp j).ne']
  exact Transport.star_dotProduct_filteredVector
    (MeanTree.posDef_eval (D.posDef_input hD ht hcomm) _) hpre

omit [Fintype H] [∀ h, Fintype (C h)] in
theorem symProj_mul_state (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k) {pre : Config k (fun v => Fin (n v)) → ℂ}
    (hpre : pre ∈ symmetricSubspace k (fun v => Fin (n v))) (p : ℝ)
    (j : Σ h, Option (C h)) (u : ℝ) :
    symProj (copyPerm (SiteConfig n) k) * D.state n t k pre p j u = D.state n t k pre p j u := by
  have hIn := D.posDef_input hD ht hcomm
  have hP : ∀ j, Commute (symProj (copyPerm (SiteConfig n) k)) (D.input n t k j) := fun j =>
    (Commute.sum_left _ _ _ fun s _ => D.commute_permOp_input k s j).smul_left _
  exact Transport.mul_transportState hIn hP (Transport.mulVec_filteredVector
    (MeanTree.posDef_eval hIn _) (MeanTree.commute_eval_right hIn hP _)
    (symProj_mulVec_of_mem _ hpre)) j u

omit [∀ h, Fintype (C h)] in
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
