/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Data.EReal.Basic

/-!
# Conic programs and weak duality

This file defines the primal and dual conic programs in Wolf's convention and proves weak
duality. The source is Wolf, *Quantum Channels & Operations*, Chapter 4,
`Notes/WolfNoteTexSource/ch04_convex_structure.tex`, lines 39--71, especially equations
`conic-primal` and `conic-dual`.

The optimization values lie in `EReal`. Thus an infeasible primal problem has value `+∞`, an
infeasible dual problem has value `-∞`, a primal problem unbounded below has value `-∞`, and a
dual problem unbounded above has value `+∞`.

No strong-duality or attainment assertion is made here.
-/

noncomputable section

open Set

namespace ConicProgram

variable {V V' : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']

local instance : CompleteSpace V := FiniteDimensional.complete ℝ V
local instance : CompleteSpace V' := FiniteDimensional.complete ℝ V'

/-- The feasible set of Wolf's primal problem
`inf {<c, x> | x ∈ K, T x = b}`.

Source: Wolf, Chapter 4, equation `conic-primal`, lines 39--48. -/
def primalFeasible (K : ProperCone ℝ V) (T : V →ₗ[ℝ] V') (b : V') : Set V :=
  {x | x ∈ K ∧ T x = b}

/-- The feasible set of Wolf's dual problem
`sup {<b, y> | c - T† y ∈ K*}`, where `K*` is the inner dual cone.

The adjoint is the continuous-linear adjoint of the automatically continuous map `T`.
Source: Wolf, Chapter 4, equation `conic-dual` and the definition of `K*`, lines 61--70. -/
def dualFeasible (K : ProperCone ℝ V) (T : V →ₗ[ℝ] V') (c : V) : Set V' :=
  {y | c - T.toContinuousLinearMap.adjoint y ∈ ProperCone.innerDual (K : Set V)}

/-- The extended-real value `C_p` of Wolf's primal problem.

The infimum over an empty feasible set is `+∞`; an objective unbounded below has infimum `-∞`.
Source: Wolf, Chapter 4, equation `conic-primal`, lines 39--48. -/
def primalValue (K : ProperCone ℝ V) (T : V →ₗ[ℝ] V') (c : V) (b : V') : EReal :=
  ⨅ x : primalFeasible K T b, ((inner ℝ c (x : V) : ℝ) : EReal)

/-- The extended-real value `C_d` of Wolf's dual problem.

The supremum over an empty feasible set is `-∞`; an objective unbounded above has supremum `+∞`.
Source: Wolf, Chapter 4, equation `conic-dual`, lines 61--65. -/
def dualValue (K : ProperCone ℝ V) (T : V →ₗ[ℝ] V') (c : V) (b : V') : EReal :=
  ⨆ y : dualFeasible K T c, ((inner ℝ b (y : V') : ℝ) : EReal)

/-- **Pointwise weak duality.** Every dual-feasible objective value is at most every
primal-feasible objective value.

Source: Wolf, Chapter 4, weak-duality sentence after equation `conic-dual`, line 71. -/
theorem weak_duality_pointwise {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'}
    {x : V} {y : V'} (hx : x ∈ primalFeasible K T b) (hy : y ∈ dualFeasible K T c) :
    inner ℝ b y ≤ inner ℝ c x := by
  change x ∈ K ∧ T x = b at hx
  change c - T.toContinuousLinearMap.adjoint y ∈ ProperCone.innerDual (K : Set V) at hy
  have hdual : 0 ≤ inner ℝ x (c - T.toContinuousLinearMap.adjoint y) :=
    (ProperCone.mem_innerDual.mp hy) hx.1
  have hbound : inner ℝ x (T.toContinuousLinearMap.adjoint y) ≤ inner ℝ x c :=
    sub_nonneg.mp (by simpa only [inner_sub_right] using hdual)
  rw [← hx.2]
  change inner ℝ (T.toContinuousLinearMap x) y ≤ inner ℝ c x
  rw [← T.toContinuousLinearMap.adjoint_inner_right]
  exact hbound.trans_eq (real_inner_comm x c).symm

/-- **Weak duality for optimal values:** Wolf's extended-real dual value is at most the
extended-real primal value, `C_d ≤ C_p`.

Because the values use complete-lattice infima and suprema in `EReal`, this statement also covers
infeasible and unbounded problems with the documented conventions.
Source: Wolf, Chapter 4, weak-duality sentence after equation `conic-dual`, line 71. -/
theorem weak_duality {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} :
    dualValue K T c b ≤ primalValue K T c b := by
  refine iSup_le fun y => ?_
  refine le_iInf fun x => ?_
  exact EReal.coe_le_coe (weak_duality_pointwise x.property y.property)

end ConicProgram
