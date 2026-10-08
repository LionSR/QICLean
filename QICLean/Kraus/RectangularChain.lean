/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.OrderedRectangular

/-!
# Ordered rectangular Kraus products

Successive Kraus matrices may have different input and output dimensions. Their ordered
matrix product and the corresponding ordered channel act on the actual endpoint spaces.
The transfer of the product equals the composition of the successive site transfers.

## References

* Wolf, *Quantum Channels & Operations*, Chapter 2, composition of Kraus representations.
-/

open Matrix
open scoped BigOperators

namespace Matrix

/-- Relabeling the input and output of a rectangular Kraus family by equal dimensions
preserves its channel property. No ambient-space extension is involved. -/
theorem isKrausCPTP_rectangularKrausMap_finCast {d a b a' b' : ℕ}
    (ha : a = a') (hb : b = b')
    (A : Fin d → Matrix (Fin a') (Fin b') ℂ)
    (hA : IsKrausCPTP (rectangularKrausMap A)) :
    IsKrausCPTP (rectangularKrausMap
      (fun i => (A i).submatrix (Fin.cast ha) (Fin.cast hb))) := by
  subst a'
  subst b'
  exact hA

end Matrix

namespace Kraus

/-- Ordered multiplication on the actual bond spaces of a rectangular chain. -/
def rectangularEval {d : ℕ} : {n : ℕ} → (b : ℕ → ℕ) →
    (∀ i : Fin n, Fin d → Matrix (Fin (b i.val)) (Fin (b (i.val + 1))) ℂ) →
    (Fin n → Fin d) → Matrix (Fin (b 0)) (Fin (b n)) ℂ
  | 0, _, _, _ => 1
  | _n + 1, b, A, s => A ⟨0, Nat.succ_pos _⟩ (s ⟨0, Nat.succ_pos _⟩) *
      rectangularEval (fun i => b (i + 1)) (fun i => A i.succ) (fun i => s i.succ)

/-- The ordered composition of the actual rectangular transfer maps. -/
noncomputable def rectangularTransfer {d : ℕ} : {n : ℕ} → (b : ℕ → ℕ) →
    (∀ i : Fin n, Fin d → Matrix (Fin (b i.val)) (Fin (b (i.val + 1))) ℂ) →
    (Matrix (Fin (b n)) (Fin (b n)) ℂ →ₗ[ℂ]
      Matrix (Fin (b 0)) (Fin (b 0)) ℂ)
  | 0, _, _ => LinearMap.id
  | _n + 1, b, A => (Matrix.rectangularKrausMap (A ⟨0, Nat.succ_pos _⟩)).comp
      (rectangularTransfer (fun i => b (i + 1)) (fun i => A i.succ))

/-- The actual rectangular product has exactly the ordered site transfer map. -/
theorem rectangularTransfer_apply {d n : ℕ} (b : ℕ → ℕ)
    (A : ∀ i : Fin n, Fin d → Matrix (Fin (b i.val)) (Fin (b (i.val + 1))) ℂ)
    (X : Matrix (Fin (b n)) (Fin (b n)) ℂ) :
    rectangularTransfer b A X = ∑ s, rectangularEval b A s * X * (rectangularEval b A s)ᴴ := by
  induction n generalizing b with
  | zero => simp [rectangularTransfer, rectangularEval, Finset.univ_unique]
  | succ n ih =>
    rw [rectangularTransfer, LinearMap.comp_apply, ih]
    simp only [map_sum, Matrix.rectangularKrausMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_comm, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin d)).sum_comp,
      Fintype.sum_prod_type]
    congr 1
    funext i
    apply Finset.sum_congr rfl
    intro s _
    dsimp only [rectangularEval, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rfl

/-- The recursive rectangular Kraus transfer equals the ordered interval of the actual
site channels. This identifies two descriptions of the same finite composition. -/
theorem rectangularTransfer_eq_channelInterval {d n : ℕ} (b : ℕ → ℕ)
    (A : ∀ i : Fin n, Fin d → Matrix (Fin (b i.val)) (Fin (b (i.val + 1))) ℂ)
    (E : ∀ i, Matrix (Fin (b (i + 1))) (Fin (b (i + 1))) ℂ →ₗ[ℂ]
      Matrix (Fin (b i)) (Fin (b i)) ℂ)
    (hE : ∀ i : Fin n, E i.val = Matrix.rectangularKrausMap (A i)) :
    rectangularTransfer b A = Matrix.channelInterval E 0 n (Nat.zero_le n) := by
  induction n generalizing b with
  | zero => simp [rectangularTransfer]
  | succ n ih =>
    have htail := ih (fun i => b (i + 1)) (fun i => A i.succ)
      (fun i => E (i + 1)) (fun i => hE i.succ)
    have hshift (m : ℕ) :
        Matrix.channelInterval (D := fun i => b (i + 1)) (fun i => E (i + 1))
          0 m (Nat.zero_le m) =
        Matrix.channelInterval E 1 (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) := by
      induction m with
      | zero => simp
      | succ m hm =>
        rw [Matrix.channelInterval_succ (D := fun i => b (i + 1))
          (fun i => E (i + 1)) (Nat.zero_le m), hm,
          Matrix.channelInterval_succ E (Nat.succ_le_succ (Nat.zero_le m))]
    rw [rectangularTransfer, htail, hshift n, ← hE ⟨0, Nat.succ_pos n⟩]
    exact Matrix.channelInterval_succ_left E (Nat.succ_le_succ (Nat.zero_le n))

end Kraus
