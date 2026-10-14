/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.States

/-!
# Original one-site labels under replica transport

Each original one-site label projector commutes with the terminal metrics.
The terminal labels, history tree, conditional trees and ordered products
are those of the supplied transport data.

Source: the area-law paper, `05-replicas.tex`, Lemma 6.1(2), lines 101–103
and 168–181; `06-transport.tex`, lines 388–401; `07-comparators.tex`,
lines 421–443.
-/

noncomputable section

open Matrix PermutationRepresentation

namespace TensorPower.ReplicaTransport.TransportData

variable {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ)
variable {K : ℕ} {H : Type*} {C : H → Type*} (D : TransportData V K H C)

/-- Every terminal metric commutes with each original one-site label projector.
No partition, positive-dimension or sign assumption is needed for this
commutation identity. Area-law paper, Lemma 6.1(2), `05-replicas.tex`,
lines 101–103; `06-transport.tex`, lines 388–401. -/
theorem commute_labelProj_singleton_input (t : ℝ) (k : ℕ) (a : V)
    (ell : IrrepLabel (Equiv.Perm (Fin k))) (j : Σ h, Option (C h)) :
    Commute (labelProj (subsystemPerm k (fun v => Fin (n v)) {a}) ell)
      (D.input n t k j) := by
  classical
  have key : Commute (labelProj (subsystemPerm k (fun v => Fin (n v)) {a}) ell)
      (List.ofFn fun g => symBandMetric n t k (D.leafPart j g)).prod :=
    Commute.list_prod_right _ _ fun y hy =>
      (List.mem_ofFn.mp hy).elim fun g hg =>
        hg ▸ commute_labelProj_singleton_symBandMetric (n := n) t k (D.leafPart j g) a ell
  rcases j with ⟨h, _ | c⟩
  all_goals exact key

variable [∀ v, NeZero (n v)] [DecidableEq H] [∀ h, DecidableEq (C h)]

/-- Filtering by the replica root preserves each one-site label of the
initial vector. Area-law paper, `05-replicas.tex`, Lemma 6.1(2), lines
101–103 and 168–181; `06-transport.tex`, lines 388–401;
`07-comparators.tex`, lines 421–443. -/
theorem labelProj_singleton_mulVec_filteredVector
    (hD : D.IsAdmissible) {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    (hcomm : D.CrossBandCommute n t k)
    {pre : Config k (fun v => Fin (n v)) → ℂ}
    (a : V) (ell : IrrepLabel (Equiv.Perm (Fin k)))
    (hlabel : labelProj (subsystemPerm k (fun v => Fin (n v)) {a}) ell *ᵥ pre = pre)
    (p : ℝ) :
    labelProj (subsystemPerm k (fun v => Fin (n v)) {a}) ell *ᵥ
        Matrix.Transport.filteredVector (D.rootPath n t k p) pre =
      Matrix.Transport.filteredVector (D.rootPath n t k p) pre := by
  classical
  exact Transport.mulVec_filteredVector
    (MeanTree.posDef_eval (D.posDef_input hD ht hcomm) _)
    (MeanTree.commute_eval_right (D.posDef_input hD ht hcomm)
      (fun j => D.commute_labelProj_singleton_input n t k a ell j) _) hlabel

end TensorPower.ReplicaTransport.TransportData
