/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.LocalExtr

/-!
# Finite-coordinate prerequisites for Nowosad's extremum theorem

This file records the source-facing finite-coordinate infrastructure needed for
Yamagami's use of Nowosad's Theorem 1.8.  For a real linear operator `T` on
`Fin d → ℝ`, the functional is

`functional T x = ∑ i, (T x) i / x i`.

Nowosad's original statement is oriented toward local minima.  Yamagami's
Theorem 1 uses the corresponding local-maximum form.  The passage is exactly
`T ↦ -T`, since `functional (-T) = -functional T`; it is made explicit below.

The file also discharges two finite-dimensional specializations used in the
source proof: every coordinate linear operator is continuous, and every point
derivation of the coordinate algebra vanishes.  The latter is proved directly
from the coordinate idempotent, replacing the Singer--Wermer step in the
general Banach-algebra argument.

This is only prerequisite infrastructure.  It does not claim Nowosad's
Laurent-algebra constancy theorem or Yamagami's Lemma 3.
-/

open scoped BigOperators

namespace Nowosad

variable {d : ℕ}

/-- The strictly positive part of the real coordinate algebra. -/
def positiveDomain : Set (Fin d → ℝ) :=
  {x | ∀ i, 0 < x i}

/-- The finite-coordinate specialization of Nowosad's functional
`x ↦ φ (x⁻¹ T(x))`, for the sum-of-coordinates positive functional `φ`. -/
noncomputable def functional
    (T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) : ℝ :=
  ∑ i, (T x) i / x i

/-- Negating the operator negates Nowosad's functional. -/
@[simp] theorem functional_neg
    (T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) :
    functional (-T) x = -functional T x := by
  simp only [functional, LinearMap.neg_apply, Pi.neg_apply, neg_div]
  rw [Finset.sum_neg_distrib]

/-- Nowosad's functional is invariant under a nonzero scalar rescaling of its
coordinate argument. -/
theorem functional_smul
    (T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (c : ℝ) (x : Fin d → ℝ)
    (hc : c ≠ 0) :
    functional T (c • x) = functional T x := by
  simp only [functional, LinearMap.map_smul, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact mul_div_mul_left _ _ hc

/-- Explicit sign bridge from Nowosad's local-minimum orientation to the
local-maximum orientation used by Yamagami. -/
theorem isLocalMinOn_functional_neg_iff_isLocalMaxOn
    (T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (a : Fin d → ℝ) :
    IsLocalMinOn (functional (-T)) (positiveDomain (d := d)) a ↔
      IsLocalMaxOn (functional T) (positiveDomain (d := d)) a := by
  constructor
  · intro h
    simpa using h.neg
  · intro h
    rw [show functional (-T) = fun x ↦ -functional T x by
      funext x
      exact functional_neg T x]
    exact h.neg

/-- A linear operator on the finite coordinate space is automatically a
bounded linear operator for the Euclidean norm. -/
noncomputable def continuousLinearMap
    (T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ⟨T, T.continuous_of_finiteDimensional⟩

@[simp] theorem continuousLinearMap_apply
    (T : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) :
    continuousLinearMap T x = T x :=
  rfl

/-- A point derivation at coordinate `i`: the coordinate evaluation is the
character appearing in the Leibniz rule. -/
def IsPointDerivationAt
    (D : (Fin d → ℝ) →ₗ[ℝ] ℝ) (i : Fin d) : Prop :=
  ∀ x y, D (x * y) = x i * D y + y i * D x

/-- Every point derivation on the finite coordinate algebra vanishes.  The
proof uses the coordinate idempotent directly, which is the finite-coordinate
specialization of the derivation-vanishing step in Nowosad's argument. -/
theorem pointDerivation_eq_zero
    (D : (Fin d → ℝ) →ₗ[ℝ] ℝ) (i : Fin d)
    (hD : IsPointDerivationAt D i) :
    D = 0 := by
  apply LinearMap.ext
  intro x
  let e : Fin d → ℝ := Pi.single i 1
  have hei : e i = 1 := by simp [e]
  have hee : e * e = e := by
    ext j
    simp [e, Pi.single_apply]
  have hDe_formula := hD e e
  have hDe : D e = 0 := by
    rw [hee, hei] at hDe_formula
    linarith
  have hex : e * x = x i • e := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [e, smul_eq_mul]
    · simp [e, smul_eq_mul, hji]
  have hDx_formula := hD e x
  rw [hex, D.map_smul, hDe, smul_zero, hei, one_mul, mul_zero, add_zero] at hDx_formula
  simpa using hDx_formula.symm

end Nowosad
