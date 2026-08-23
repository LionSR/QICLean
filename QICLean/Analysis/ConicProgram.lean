/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Data.EReal.Basic

/-!
# Conic programs, strict feasibility, and weak duality

This file defines the primal and dual conic programs in Wolf's convention, their strict-feasibility
and optimizer predicates, and proves weak duality. The source is Wolf, *Quantum Channels &
Operations*, Chapter 4, `Notes/WolfNoteTexSource/ch04_convex_structure.tex`, lines 39--78,
especially equations `conic-primal` and `conic-dual`.

The optimization values lie in `EReal`. Thus an infeasible primal problem has value `+∞`, an
infeasible dual problem has value `-∞`, a primal problem unbounded below has value `-∞`, and a
dual problem unbounded above has value `+∞`.

The strict-feasibility and optimizer predicates deliberately keep value equality separate from
attainment. No Slater strong-duality assertion is made here: Wolf's claim at lines 72--78 needs a
finiteness or opposite-feasibility condition for its attainment clause.
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

/-- Wolf's primal problem is strictly feasible when the affine constraint meets the interior of
the cone.

Source: Wolf, Chapter 4, lines 72--75. -/
def IsPrimalStrictlyFeasible (K : ProperCone ℝ V) (T : V →ₗ[ℝ] V') (b : V') : Prop :=
  ∃ x ∈ interior (K : Set V), T x = b

/-- Wolf's dual problem is strictly feasible when one of its slack vectors belongs to the interior
of the dual cone.

Source: Wolf, Chapter 4, lines 75--78. -/
def IsDualStrictlyFeasible (K : ProperCone ℝ V) (T : V →ₗ[ℝ] V') (c : V) : Prop :=
  ∃ y, c - T.toContinuousLinearMap.adjoint y ∈
    interior (ProperCone.innerDual (K : Set V) : Set V)

/-- A feasible point at which Wolf's primal infimum is attained.

Source: Wolf, Chapter 4, equations `conic-primal` and the attainment discussion at lines 72--78. -/
def IsPrimalOptimizer (K : ProperCone ℝ V) (T : V →ₗ[ℝ] V') (c : V) (b : V')
    (x : V) : Prop :=
  x ∈ primalFeasible K T b ∧
    ∀ z ∈ primalFeasible K T b, inner ℝ c x ≤ inner ℝ c z

/-- A feasible point at which Wolf's dual supremum is attained.

Source: Wolf, Chapter 4, equations `conic-dual` and the attainment discussion at lines 72--78. -/
def IsDualOptimizer (K : ProperCone ℝ V) (T : V →ₗ[ℝ] V') (c : V) (b : V')
    (y : V') : Prop :=
  y ∈ dualFeasible K T c ∧
    ∀ z ∈ dualFeasible K T c, inner ℝ b z ≤ inner ℝ b y

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- Primal strict feasibility implies ordinary primal feasibility. -/
theorem IsPrimalStrictlyFeasible.feasible {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {b : V'}
    (h : IsPrimalStrictlyFeasible K T b) : (primalFeasible K T b).Nonempty := by
  obtain ⟨x, hx, hTx⟩ := h
  exact ⟨x, interior_subset hx, hTx⟩

/-- Dual strict feasibility implies ordinary dual feasibility. -/
theorem IsDualStrictlyFeasible.feasible {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V}
    (h : IsDualStrictlyFeasible K T c) : (dualFeasible K T c).Nonempty := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y, ?_⟩
  change c - T.toContinuousLinearMap.adjoint y ∈ ProperCone.innerDual (K : Set V)
  exact interior_subset hy

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

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- A primal optimizer realizes the extended-real primal value as a finite real value. -/
theorem primalValue_eq_of_isPrimalOptimizer {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'}
    {c : V} {b : V'} {x : V} (hx : IsPrimalOptimizer K T c b x) :
    primalValue K T c b = (inner ℝ c x : EReal) := by
  apply le_antisymm
  · exact iInf_le_of_le ⟨x, hx.1⟩ le_rfl
  · refine le_iInf fun z ↦ ?_
    exact EReal.coe_le_coe (hx.2 z z.property)

/-- A dual optimizer realizes the extended-real dual value as a finite real value. -/
theorem dualValue_eq_of_isDualOptimizer {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'}
    {c : V} {b : V'} {y : V'} (hy : IsDualOptimizer K T c b y) :
    dualValue K T c b = (inner ℝ b y : EReal) := by
  apply le_antisymm
  · refine iSup_le fun z ↦ ?_
    exact EReal.coe_le_coe (hy.2 z z.property)
  · exact le_iSup_of_le ⟨y, hy.1⟩ le_rfl

/-- A primal-dual feasible pair with equal objective values attains both extrema. This separates
the zero-gap certificate from the existence statement in Slater's theorem.

Source: Wolf, Chapter 4, lines 71--78. -/
theorem optimizers_of_feasible_of_objectives_eq {K : ProperCone ℝ V}
    {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {x : V} {y : V'}
    (hx : x ∈ primalFeasible K T b) (hy : y ∈ dualFeasible K T c)
    (hxy : inner ℝ c x = inner ℝ b y) :
    IsPrimalOptimizer K T c b x ∧ IsDualOptimizer K T c b y := by
  constructor
  · refine ⟨hx, fun z hz ↦ ?_⟩
    rw [hxy]
    exact weak_duality_pointwise hz hy
  · refine ⟨hy, fun z hz ↦ ?_⟩
    rw [← hxy]
    exact weak_duality_pointwise hx hz

/-- A zero-gap feasible pair gives equality of Wolf's extended-real primal and dual values, while
also supplying optimizers on both sides. -/
theorem values_eq_of_feasible_of_objectives_eq {K : ProperCone ℝ V}
    {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {x : V} {y : V'}
    (hx : x ∈ primalFeasible K T b) (hy : y ∈ dualFeasible K T c)
    (hxy : inner ℝ c x = inner ℝ b y) :
    primalValue K T c b = dualValue K T c b := by
  obtain ⟨hxopt, hyopt⟩ := optimizers_of_feasible_of_objectives_eq hx hy hxy
  rw [primalValue_eq_of_isPrimalOptimizer hxopt, dualValue_eq_of_isDualOptimizer hyopt,
    hxy]

end ConicProgram
