/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# Controlled elements of a ring

For an idempotent `p` of a ring and an element `x`, the controlled element is
`C(p, x) = p x + (1 - p)`: it acts as `x` on the range of `p` and as the identity on the range
of `1 - p`. This file develops the algebra of these elements:

* `C(p, x) C(p, y) = C(p, x y)` when `p` commutes with `x` (`QuantumCircuit.ctrlElem_mul`);
* conjugation by an invertible element commuting with `p` acts on the second argument
  (`QuantumCircuit.conj_ctrlElem`);
* for commuting idempotents `p₁`, `p₂` and invertible `v`, `w` commuting with them,
  `C(p₁ p₂, v w v⁻¹ w⁻¹) = C(p₁, v) C(p₂, w) C(p₁, v⁻¹) C(p₂, w⁻¹)`
  (`QuantumCircuit.ctrlElem_commutator`), which replaces a control by the product of two
  idempotents with controls by each of them.

The commutator identity is the algebraic step in the decomposition of a gate of constant size
into elementary gates in arXiv:2307.01696 (caption of Fig. 1 and paragraph "The sequential-RG
circuit").

The declarations are ported from the section on controlled elements of a ring of
`TNLean/Circuit/Gates/Controlled.lean` at commit
`4150a33bacefe5ca311874b20cc4b90237fa447e` (Apache-2.0), with statements and names unchanged.
-/

namespace QuantumCircuit

variable {R : Type*} [Ring R]

/-- The controlled element `C(p, x) = p x + (1 - p)`. -/
def ctrlElem (p x : R) : R := p * x + (1 - p)

theorem ctrlElem_one (p : R) : ctrlElem p 1 = 1 := by
  simp [ctrlElem]

theorem ctrlElem_ctrlElem (p₁ p₂ w : R) :
    ctrlElem p₁ (ctrlElem p₂ w) = ctrlElem (p₁ * p₂) w := by
  simp only [ctrlElem]; noncomm_ring

/-- For `p` idempotent and commuting with `x`, `C(p, x) C(p, y) = C(p, x y)`. -/
theorem ctrlElem_mul {p x y : R} (hp : IsIdempotentElem p) (hx : Commute p x) :
    ctrlElem p x * ctrlElem p y = ctrlElem p (x * y) := by
  have h1 : p * x * (p * y) = p * (x * y) := by
    rw [mul_assoc, ← mul_assoc x p y, ← hx.eq, mul_assoc, ← mul_assoc p p, hp.eq]
  have h2 : p * x * (1 - p) = 0 := by
    rw [mul_assoc, mul_sub, mul_one, ← hx.eq, mul_sub, ← mul_assoc p p x, hp.eq, sub_self]
  have h3 : (1 - p) * (p * y) = 0 := by
    rw [← mul_assoc, hp.one_sub_mul_self, zero_mul]
  have h4 : (1 - p) * (1 - p) = 1 - p := by
    rw [sub_mul, one_mul, hp.mul_one_sub_self, sub_zero]
  calc ctrlElem p x * ctrlElem p y
      = p * x * (p * y) + p * x * (1 - p) + (1 - p) * (p * y) + (1 - p) * (1 - p) := by
        simp only [ctrlElem]; noncomm_ring
    _ = ctrlElem p (x * y) := by rw [h1, h2, h3, h4, ctrlElem]; abel

/-- Conjugating a controlled element by an invertible element commuting with the control. -/
theorem conj_ctrlElem {p v v' : R} (w : R) (hv : Commute p v) (hvv : v * v' = 1) :
    v * ctrlElem p w * v' = ctrlElem p (v * w * v') := by
  have h : p * v * v' = p := by rw [mul_assoc, hvv, mul_one]
  calc v * ctrlElem p w * v' = v * p * w * v' + v * v' - v * p * v' := by
        simp only [ctrlElem]; noncomm_ring
    _ = ctrlElem p (v * w * v') := by
        rw [← hv.eq, h, hvv, ctrlElem]; noncomm_ring

theorem commute_ctrlElem {p q x : R} (hpq : Commute p q) (hpx : Commute p x) :
    Commute p (ctrlElem q x) :=
  (hpq.mul_right hpx).add_right ((Commute.one_right p).sub_right hpq)

/-- **Controlled commutators.** For commuting idempotents `p₁`, `p₂` and elements `v`, `w`
with right inverses `v'`, `w'`, where `p₁` commutes with `v`, `w` and `p₂` with `v`, `v'`, `w`,
`C(p₁ p₂, v w v' w') = C(p₁, v) C(p₂, w) C(p₁, v') C(p₂, w')`. -/
theorem ctrlElem_commutator {p₁ p₂ v v' w w' : R} (hp₁ : IsIdempotentElem p₁)
    (hp₂ : IsIdempotentElem p₂) (h12 : Commute p₁ p₂) (h1v : Commute p₁ v)
    (h1w : Commute p₁ w) (h2v : Commute p₂ v) (h2v' : Commute p₂ v')
    (h2w : Commute p₂ w) (hvv : v * v' = 1) (hww : w * w' = 1) :
    ctrlElem p₁ v * ctrlElem p₂ w * ctrlElem p₁ v' * ctrlElem p₂ w' =
      ctrlElem (p₁ * p₂) (v * w * v' * w') := by
  set A := ctrlElem p₁ v
  set A' := ctrlElem p₁ v'
  have hAA : A * A' = 1 := by rw [ctrlElem_mul hp₁ h1v, hvv, ctrlElem_one]
  have h2A : Commute p₂ A := commute_ctrlElem h12.symm h2v
  have h2A' : Commute p₂ A' := commute_ctrlElem h12.symm h2v'
  -- `A w A' = p₁ (v w v') + (1 - p₁) w`.
  have hAw : A * w * A' = p₁ * (v * w * v') + (1 - p₁) * w := by
    have e1 : p₁ * v * w * (p₁ * v') = p₁ * (v * w * v') := by
      rw [mul_assoc (p₁ * v) w, ← mul_assoc w p₁, ← h1w.eq, mul_assoc p₁ w v', ← mul_assoc,
        mul_assoc p₁ v p₁, ← h1v.eq, ← mul_assoc p₁ p₁, hp₁.eq]
      simp only [mul_assoc]
    have e2 : p₁ * v * w * (1 - p₁) = 0 := by
      rw [mul_sub, mul_one, mul_assoc (p₁ * v) w p₁, ← h1w.eq, ← mul_assoc, mul_assoc p₁ v p₁,
        ← h1v.eq, ← mul_assoc p₁ p₁, hp₁.eq, sub_self]
    have e3 : (1 - p₁) * w * (p₁ * v') = 0 := by
      rw [mul_assoc (1 - p₁) w, ← mul_assoc w p₁, ← h1w.eq, mul_assoc, ← mul_assoc (1 - p₁),
        hp₁.one_sub_mul_self, zero_mul]
    have e4 : (1 - p₁) * w * (1 - p₁) = (1 - p₁) * w := by
      rw [mul_assoc, mul_sub, mul_one, ← h1w.eq, mul_sub, ← mul_assoc (1 - p₁) p₁ w,
        hp₁.one_sub_mul_self, zero_mul, sub_zero]
    calc A * w * A' = p₁ * v * w * (p₁ * v') + p₁ * v * w * (1 - p₁) +
          (1 - p₁) * w * (p₁ * v') + (1 - p₁) * w * (1 - p₁) := by
          simp only [A, A', ctrlElem]; noncomm_ring
      _ = p₁ * (v * w * v') + (1 - p₁) * w := by rw [e1, e2, e3, e4]; abel
  have hAwA : A * w * A' * w' = ctrlElem p₁ (v * w * v' * w') := by
    rw [hAw, add_mul, mul_assoc (1 - p₁), hww, mul_one, mul_assoc p₁, ctrlElem]
  have h2u : Commute p₂ (A * w * A') := (h2A.mul_right h2w).mul_right h2A'
  calc A * ctrlElem p₂ w * A' * ctrlElem p₂ w'
      = ctrlElem p₂ (A * w * A') * ctrlElem p₂ w' := by rw [conj_ctrlElem w h2A hAA]
    _ = ctrlElem p₂ (ctrlElem p₁ (v * w * v' * w')) := by
        rw [ctrlElem_mul hp₂ h2u, hAwA]
    _ = ctrlElem (p₁ * p₂) (v * w * v' * w') := by rw [ctrlElem_ctrlElem, h12.eq]

end QuantumCircuit
