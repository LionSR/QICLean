/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.EReal.Basic

/-!
# Conic programs and corrected Slater duality

This file defines the primal and dual conic programs in Wolf's convention, their strict-feasibility
and optimizer predicates, weak duality, and the corrected finite-dimensional Slater theorem. The
source is Wolf, *Quantum Channels &
Operations*, Chapter 4, `Notes/WolfNoteTexSource/ch04_convex_structure.tex`, lines 39--78,
especially equations `conic-primal` and `conic-dual`.

The optimization values lie in `EReal`. Thus an infeasible primal problem has value `+∞`, an
infeasible dual problem has value `-∞`, a primal problem unbounded below has value `-∞`, and a
dual problem unbounded above has value `+∞`.

The strict-feasibility and optimizer predicates keep value equality separate from attainment.
Wolf's claim at lines 72--78 is false without a finiteness or opposite-feasibility condition. The
theorems below restore the missing hypothesis: primal strict feasibility together with a finite
primal value gives dual attainment and equality of values, and the dual statement is analogous.
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
section SlaterSeparation

variable {W Z : Type*}
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

local instance : CompleteSpace W := FiniteDimensional.complete ℝ W
local instance : CompleteSpace Z := FiniteDimensional.complete ℝ Z

/-- The lifted map used in the finite-dimensional separation proof. Its codomain is restricted to
the range of `A`, so the map is surjective without requiring `A` itself to be surjective. -/
private def slaterLift (A : W →ₗ[ℝ] Z) (d : W) : W × ℝ →ₗ[ℝ] A.range × ℝ :=
  (A.rangeRestrict.comp (LinearMap.fst ℝ W ℝ)).prod
    ((innerₛₗ ℝ d).comp (LinearMap.fst ℝ W ℝ) + LinearMap.snd ℝ W ℝ)

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ Z] in
@[simp]
private theorem slaterLift_apply (A : W →ₗ[ℝ] Z) (d : W) (x : W) (r : ℝ) :
    slaterLift A d (x, r) =
      (⟨A x, LinearMap.mem_range_self A x⟩, inner ℝ d x + r) :=
  rfl

omit [FiniteDimensional ℝ W] [FiniteDimensional ℝ Z] in
private theorem slaterLift_surjective (A : W →ₗ[ℝ] Z) (d : W) :
    Function.Surjective (slaterLift A d) := by
  rintro ⟨z, r⟩
  obtain ⟨x, hx⟩ := z.property
  refine ⟨(x, r - inner ℝ d x), ?_⟩
  ext
  · exact hx
  · simp [slaterLift]

omit [FiniteDimensional ℝ Z] in
/-- The separation argument underlying both corrected Slater theorems. The cone need not be
closed. In particular, the proof never assumes that a linear image of a closed cone is closed. -/
private theorem exists_dual_of_strictlyFeasible_of_isGLB
    (C : PointedCone ℝ W) (A : W →ₗ[ℝ] Z) (d : W) (r : Z) (p : ℝ)
    (hstrict : ∃ x ∈ interior (C : Set W), A x = r)
    (hp : IsGLB ((fun x : W ↦ inner ℝ d x) '' {x | x ∈ C ∧ A x = r}) p) :
    ∃ y : Z, (∀ x ∈ C, inner ℝ (A x) y ≤ inner ℝ d x) ∧ inner ℝ r y = p := by
  obtain ⟨x₀, hx₀, hAx₀⟩ := hstrict
  let D : Set (A.range × ℝ) :=
    slaterLift A d '' ((C : Set W) ×ˢ Set.Ici 0)
  have hD_convex : Convex ℝ D := by
    exact (C.convex.prod (convex_Ici (0 : ℝ))).linear_image (slaterLift A d)
  have hL_open : IsOpenMap (slaterLift A d) :=
    LinearMap.isOpenMap_of_finiteDimensional _ (slaterLift_surjective A d)
  have hx₀_one : (x₀, (1 : ℝ)) ∈ interior ((C : Set W) ×ˢ Set.Ici 0) := by
    rw [interior_prod_eq, interior_Ici]
    exact ⟨hx₀, by simp⟩
  have ha₀ : slaterLift A d (x₀, 1) ∈ interior D :=
    hL_open.image_interior_subset _ ⟨_, hx₀_one, rfl⟩
  have hD_interior : (interior D).Nonempty := ⟨_, ha₀⟩
  let rA : A.range := ⟨r, ⟨x₀, hAx₀⟩⟩
  let q : A.range × ℝ := (rA, p)
  have hq_not_interior : q ∉ interior D := by
    intro hq
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior q hq
    have hnear : (rA, p - ε / 2) ∈ Metric.ball q ε := by
      rw [Metric.mem_ball, dist_prod_same_left, Real.dist_eq]
      have hdiff : p - ε / 2 - p = -(ε / 2) := by ring
      rw [hdiff, abs_neg, abs_of_pos (by positivity)]
      linarith
    have hbelow : (rA, p - ε / 2) ∈ D := interior_subset (hball hnear)
    obtain ⟨⟨x, s⟩, ⟨hxC, hs⟩, hxs⟩ := hbelow
    have hAx : A x = r := by
      have := congr_arg (fun z : A.range × ℝ ↦ (z.1 : Z)) hxs
      simpa [rA] using this
    have hobj : inner ℝ d x + s = p - ε / 2 := by
      have := congr_arg Prod.snd hxs
      simpa using this
    have hp_le : p ≤ inner ℝ d x :=
      hp.1 ⟨x, ⟨hxC, hAx⟩, rfl⟩
    change 0 ≤ s at hs
    have hx_le : inner ℝ d x ≤ p - ε / 2 := by linarith
    linarith
  let S : Set ℝ := (fun x : W ↦ inner ℝ d x) '' {x | x ∈ C ∧ A x = r}
  change IsGLB S p at hp
  have hS_nonempty : S.Nonempty := by
    exact ⟨inner ℝ d x₀, ⟨x₀, ⟨interior_subset hx₀, hAx₀⟩, rfl⟩⟩
  have hp_closure : p ∈ closure S := hp.mem_closure hS_nonempty
  let g : ℝ → A.range × ℝ := fun t ↦ (rA, t)
  have hg_continuous : Continuous g := by fun_prop
  have hg_mapsTo : MapsTo g S D := by
    rintro t ⟨x, ⟨hxC, hAx⟩, rfl⟩
    refine ⟨(x, 0), ⟨hxC, by simp⟩, ?_⟩
    ext
    · exact hAx
    · simp [g, slaterLift]
  have hq_closure : q ∈ closure D := by
    exact map_mem_closure hg_continuous hp_closure hg_mapsTo
  obtain ⟨f, hf_ne, hfD⟩ :=
    geometric_hahn_banach_of_nonempty_interior_point hD_convex hq_not_interior hD_interior
  have hzero_D : (0 : A.range × ℝ) ∈ D := by
    refine ⟨(0, 0), ⟨by simp, by simp⟩, ?_⟩
    exact (slaterLift A d).map_zero
  have hD_smul {t : ℝ} (ht : 0 ≤ t) {z : A.range × ℝ} (hz : z ∈ D) : t • z ∈ D := by
    obtain ⟨⟨x, s⟩, ⟨hxC, hs⟩, rfl⟩ := hz
    refine ⟨t • (x, s), ?_, ?_⟩
    · refine ⟨C.smul_mem ht hxC, ?_⟩
      change 0 ≤ t * s
      exact mul_nonneg ht hs
    · exact (slaterLift A d).map_smul t (x, s)
  have hfD_closure : ∀ z ∈ closure D, f z ≤ f q := by
    exact closure_minimal hfD (isClosed_Iic.preimage f.continuous)
  have htwo_q : (2 : ℝ) • q ∈ closure D := by
    exact map_mem_closure (continuous_const_smul (2 : ℝ)) hq_closure
      (fun _ hz ↦ hD_smul (by norm_num) hz)
  have hfq_nonneg : 0 ≤ f q := by simpa using hfD 0 hzero_D
  have hfq_nonpos : f q ≤ 0 := by
    have := hfD_closure _ htwo_q
    simp only [map_smul] at this
    change 2 * f q ≤ f q at this
    linarith
  have hfq : f q = 0 := le_antisymm hfq_nonpos hfq_nonneg
  have hfD_nonpos : ∀ z ∈ D, f z ≤ 0 := by
    intro z hz
    simpa [hfq] using hfD z hz
  let α : ℝ := f (0, 1)
  have hvertical : (0, 1) ∈ D := by
    refine ⟨(0, 1), ⟨by simp, by simp⟩, ?_⟩
    rw [slaterLift_apply]
    ext <;> simp
  have hα_nonpos : α ≤ 0 := hfD_nonpos _ hvertical
  have hα_ne : α ≠ 0 := by
    intro hα
    have hf_eq_of_fst_eq {z w : A.range × ℝ} (hzw : z.1 = w.1) : f z = f w := by
      calc
        f z = f (z.1, 0) + f (0, z.2) := by
          rw [← map_add]
          congr 1
          ext <;> simp
        _ = f (z.1, 0) := by
          have hz : (0, z.2) = z.2 • ((0, 1) : A.range × ℝ) := by ext <;> simp
          rw [hz, map_smul, show f (0, 1) = 0 by exact hα]
          simp
        _ = f (w.1, 0) := by rw [hzw]
        _ = f (w.1, 0) + f (0, w.2) := by
          have hw : (0, w.2) = w.2 • ((0, 1) : A.range × ℝ) := by ext <;> simp
          rw [hw, map_smul, show f (0, 1) = 0 by exact hα]
          simp
        _ = f w := by
          rw [← map_add]
          congr 1
          ext <;> simp
    have hfirst : (slaterLift A d (x₀, 1)).1 = q.1 := by
      ext
      simpa [q, rA] using hAx₀
    have hfa₀ : f (slaterLift A d (x₀, 1)) = 0 :=
      (hf_eq_of_fst_eq hfirst).trans hfq
    have himage_open : IsOpen (f '' interior D) :=
      f.isOpenMap_of_ne_zero hf_ne _ isOpen_interior
    have himage_subset : f '' interior D ⊆ Set.Iic 0 := by
      rintro _ ⟨z, hz, rfl⟩
      exact hfD_nonpos z (interior_subset hz)
    have hzero_interior : (0 : ℝ) ∈ interior (Set.Iic 0) :=
      interior_maximal himage_subset himage_open ⟨_, ha₀, hfa₀⟩
    rw [interior_Iic] at hzero_interior
    change (0 : ℝ) < 0 at hzero_interior
    exact (lt_irrefl 0) hzero_interior
  have hα_neg : α < 0 := lt_of_le_of_ne hα_nonpos hα_ne
  let fA : StrongDual ℝ A.range :=
    f.comp (ContinuousLinearMap.inl ℝ A.range ℝ)
  let _ : CompleteSpace A.range := FiniteDimensional.complete ℝ A.range
  let u : A.range := (InnerProductSpace.toDual ℝ A.range).symm fA
  have hf_decomp (z : A.range) (t : ℝ) : f (z, t) = inner ℝ u z + α * t := by
    calc
      f (z, t) = f (z, 0) + f (0, t) := by
        rw [← map_add]
        congr 1
        ext <;> simp
      _ = fA z + t • f (0, 1) := by
        change f (z, 0) + f (0, t) = f (z, 0) + t • f (0, 1)
        congr 1
        have ht : (0, t) = t • ((0, 1) : A.range × ℝ) := by ext <;> simp
        rw [ht, map_smul]
      _ = inner ℝ u z + α * t := by
        rw [← InnerProductSpace.toDual_symm_apply]
        simp [u, fA, α, mul_comm]
  let scale : ℝ := -α
  have hscale_pos : 0 < scale := by simp [scale, hα_neg]
  have hscale_ne : scale ≠ 0 := ne_of_gt hscale_pos
  let y : Z := scale⁻¹ • (u : Z)
  refine ⟨y, ?_, ?_⟩
  · intro x hxC
    have hxD : slaterLift A d (x, 0) ∈ D := by
      exact ⟨(x, 0), ⟨hxC, by simp⟩, rfl⟩
    have hsep := hfD_nonpos _ hxD
    rw [slaterLift_apply, hf_decomp] at hsep
    simp only [add_zero] at hsep
    let Ax : A.range := ⟨A x, LinearMap.mem_range_self A x⟩
    have hraw : inner ℝ (u : Z) (A x) ≤ scale * inner ℝ d x := by
      change inner ℝ (u : Z) (A x) + α * inner ℝ d x ≤ 0 at hsep
      dsimp [scale]
      linarith
    have hinner : inner ℝ (A x) (u : Z) = inner ℝ u Ax := by
      rw [real_inner_comm]
      rfl
    calc
      inner ℝ (A x) y = scale⁻¹ * inner ℝ (A x) (u : Z) := by
        simp [y, inner_smul_right]
      _ = scale⁻¹ * inner ℝ u Ax := by rw [hinner]
      _ ≤ inner ℝ d x := (inv_mul_le_iff₀ hscale_pos).2 (by simpa [Ax] using hraw)
  · have hq_eq : inner ℝ u rA + α * p = 0 := by
      have h := hfq
      change f (rA, p) = 0 at h
      rwa [hf_decomp] at h
    have hraw : inner ℝ (u : Z) r = scale * p := by
      change inner ℝ (u : Z) r + α * p = 0 at hq_eq
      dsimp [scale]
      linarith
    have hinner : inner ℝ r (u : Z) = inner ℝ (u : Z) r := real_inner_comm _ _
    calc
      inner ℝ r y = scale⁻¹ * inner ℝ r (u : Z) := by
        simp [y, inner_smul_right]
      _ = scale⁻¹ * inner ℝ (u : Z) r := by rw [hinner]
      _ = p := by
        rw [hraw, ← mul_assoc, inv_mul_cancel₀ hscale_ne, one_mul]

end SlaterSeparation

section Slater

/-- A real greatest lower bound of a nonempty family gives the corresponding finite infimum in
the extended reals. -/
private theorem ereal_iInf_eq_of_isGLB {I : Type*} [Nonempty I] (f : I → ℝ) (p : ℝ)
    (hp : IsGLB (Set.range f) p) : (⨅ i, (f i : EReal)) = (p : EReal) := by
  have hb : BddBelow (Set.range f) := hp.bddBelow
  have hb' : BddBelow (Set.range fun i ↦ (f i : WithTop ℝ)) := by
    refine ⟨(p : WithTop ℝ), ?_⟩
    rintro _ ⟨i, rfl⟩
    exact WithTop.coe_le_coe.mpr (hp.1 (Set.mem_range_self i))
  change (⨅ i, ((f i : WithTop ℝ) : WithBot (WithTop ℝ))) =
    ((p : WithTop ℝ) : WithBot (WithTop ℝ))
  calc
    (⨅ i, ((f i : WithTop ℝ) : WithBot (WithTop ℝ))) =
        ((↑(⨅ i, (f i : WithTop ℝ)) : WithBot (WithTop ℝ))) :=
      (WithBot.coe_iInf (fun i ↦ (f i : WithTop ℝ)) hb').symm
    _ = ((↑(⨅ i, f i) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      exact congrArg (fun z : WithTop ℝ ↦ (z : WithBot (WithTop ℝ)))
        (WithTop.coe_iInf hb).symm
    _ = ((p : WithTop ℝ) : WithBot (WithTop ℝ)) := by rw [hp.ciInf_eq]

/-- A real least upper bound of a nonempty family gives the corresponding finite supremum in the
extended reals. -/
private theorem ereal_iSup_eq_of_isLUB {I : Type*} [Nonempty I] (f : I → ℝ) (p : ℝ)
    (hp : IsLUB (Set.range f) p) : (⨆ i, (f i : EReal)) = (p : EReal) := by
  have hb : BddAbove (Set.range f) := hp.bddAbove
  have hb' : BddAbove (Set.range fun i ↦ (f i : WithTop ℝ)) := OrderTop.bddAbove _
  change (⨆ i, ((f i : WithTop ℝ) : WithBot (WithTop ℝ))) =
    ((p : WithTop ℝ) : WithBot (WithTop ℝ))
  calc
    (⨆ i, ((f i : WithTop ℝ) : WithBot (WithTop ℝ))) =
        ((↑(⨆ i, (f i : WithTop ℝ)) : WithBot (WithTop ℝ))) :=
      (WithBot.coe_iSup hb').symm
    _ = ((↑(⨆ i, f i) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
      exact congrArg (fun z : WithTop ℝ ↦ (z : WithBot (WithTop ℝ)))
        (WithTop.coe_iSup f hb).symm
    _ = ((p : WithTop ℝ) : WithBot (WithTop ℝ)) := by rw [hp.ciSup_eq]

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- A finite extended-real infimum of a nonempty real family is its real greatest lower bound. -/
private theorem isGLB_of_ereal_iInf_eq {I : Type*} [Nonempty I] (f : I → ℝ) (p : ℝ)
    (hp : (⨅ i, (f i : EReal)) = (p : EReal)) : IsGLB (Set.range f) p := by
  constructor
  · rintro _ ⟨i, rfl⟩
    apply EReal.coe_le_coe_iff.mp
    rw [← hp]
    exact iInf_le _ i
  · intro a ha
    apply EReal.coe_le_coe_iff.mp
    rw [← hp]
    refine le_iInf fun i ↦ ?_
    exact EReal.coe_le_coe (ha (Set.mem_range_self i))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- A finite extended-real supremum of a nonempty real family is its real least upper bound. -/
private theorem isLUB_of_ereal_iSup_eq {I : Type*} [Nonempty I] (f : I → ℝ) (p : ℝ)
    (hp : (⨆ i, (f i : EReal)) = (p : EReal)) : IsLUB (Set.range f) p := by
  constructor
  · rintro _ ⟨i, rfl⟩
    apply EReal.coe_le_coe_iff.mp
    rw [← hp]
    exact le_iSup (fun i ↦ (f i : EReal)) i
  · intro a ha
    apply EReal.coe_le_coe_iff.mp
    rw [← hp]
    refine iSup_le fun i ↦ ?_
    exact EReal.coe_le_coe (ha (Set.mem_range_self i))

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- A real greatest lower bound realizes Wolf's extended-real primal value. This is the finite
primal-optimum hypothesis used below; it does not assert that the infimum is attained. -/
theorem primalValue_eq_coe_of_isGLB {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'}
    {c : V} {b : V'} {p : ℝ}
    (hp : IsGLB ((fun x : V ↦ inner ℝ c x) '' primalFeasible K T b) p) :
    primalValue K T c b = (p : EReal) := by
  let _ : Nonempty (primalFeasible K T b) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hp_all : ∀ a : ℝ, a ≤ p := by
      intro a
      apply hp.2
      rintro _ ⟨x, hx, rfl⟩
      exact False.elim (@IsEmpty.false (primalFeasible K T b) h ⟨x, hx⟩)
    exact (not_le_of_gt (lt_add_one p)) (hp_all (p + 1))
  apply ereal_iInf_eq_of_isGLB
  have hrange :
      Set.range (fun x : primalFeasible K T b ↦ inner ℝ c (x : V)) =
        (fun x : V ↦ inner ℝ c x) '' primalFeasible K T b := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange]
  exact hp

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ V'] in
/-- For a nonempty primal feasible set, saying that Wolf's extended-real primal value is the real
number `p` is exactly saying that `p` is the greatest lower bound of the real objective values. -/
theorem primalValue_eq_coe_iff_isGLB {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'}
    {c : V} {b : V'} {p : ℝ} (hfeasible : (primalFeasible K T b).Nonempty) :
    primalValue K T c b = (p : EReal) ↔
      IsGLB ((fun x : V ↦ inner ℝ c x) '' primalFeasible K T b) p := by
  let _ : Nonempty (primalFeasible K T b) := hfeasible.to_subtype
  have hrange :
      Set.range (fun x : primalFeasible K T b ↦ inner ℝ c (x : V)) =
        (fun x : V ↦ inner ℝ c x) '' primalFeasible K T b := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  constructor
  · intro hp
    rw [← hrange]
    exact isGLB_of_ereal_iInf_eq _ p hp
  · exact primalValue_eq_coe_of_isGLB

/-- A real least upper bound realizes Wolf's extended-real dual value. This is the finite
dual-optimum hypothesis used below; it does not assert that the supremum is attained. -/
theorem dualValue_eq_coe_of_isLUB {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'}
    {c : V} {b : V'} {p : ℝ}
    (hp : IsLUB ((fun y : V' ↦ inner ℝ b y) '' dualFeasible K T c) p) :
    dualValue K T c b = (p : EReal) := by
  let _ : Nonempty (dualFeasible K T c) := by
    by_contra h
    rw [not_nonempty_iff] at h
    have hp_all : ∀ a : ℝ, p ≤ a := by
      intro a
      apply hp.2
      rintro _ ⟨y, hy, rfl⟩
      exact False.elim (@IsEmpty.false (dualFeasible K T c) h ⟨y, hy⟩)
    exact (not_le_of_gt (sub_one_lt p)) (hp_all (p - 1))
  apply ereal_iSup_eq_of_isLUB
  have hrange :
      Set.range (fun y : dualFeasible K T c ↦ inner ℝ b (y : V')) =
        (fun y : V' ↦ inner ℝ b y) '' dualFeasible K T c := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  rw [hrange]
  exact hp

/-- For a nonempty dual feasible set, saying that Wolf's extended-real dual value is the real
number `p` is exactly saying that `p` is the least upper bound of the real objective values. -/
theorem dualValue_eq_coe_iff_isLUB {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'}
    {c : V} {b : V'} {p : ℝ} (hfeasible : (dualFeasible K T c).Nonempty) :
    dualValue K T c b = (p : EReal) ↔
      IsLUB ((fun y : V' ↦ inner ℝ b y) '' dualFeasible K T c) p := by
  let _ : Nonempty (dualFeasible K T c) := hfeasible.to_subtype
  have hrange :
      Set.range (fun y : dualFeasible K T c ↦ inner ℝ b (y : V')) =
        (fun y : V' ↦ inner ℝ b y) '' dualFeasible K T c := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  constructor
  · intro hp
    rw [← hrange]
    exact isLUB_of_ereal_iSup_eq _ p hp
  · exact dualValue_eq_coe_of_isLUB

/-- The dual conic problem written as a primal cone constraint. The first coordinate is free and
the second coordinate is the dual slack. -/
private def dualAsPrimalCone (K : ProperCone ℝ V) :
    PointedCone ℝ (WithLp 2 (V' × V)) where
  carrier := {w | w.snd ∈ ProperCone.innerDual (K : Set V)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change x.snd ∈ ProperCone.innerDual (K : Set V) at hx
    change y.snd ∈ ProperCone.innerDual (K : Set V) at hy
    change (x + y).snd ∈ ProperCone.innerDual (K : Set V)
    simpa using (ProperCone.innerDual (K : Set V)).add_mem hx hy
  smul_mem' := by
    intro a x hx
    change x.snd ∈ ProperCone.innerDual (K : Set V) at hx
    change (a : ℝ) • x.snd ∈ ProperCone.innerDual (K : Set V)
    exact (ProperCone.innerDual (K : Set V)).smul_mem hx a.property

/-- The equality map `(y, z) ↦ T† y + z` for the dual problem written as a primal problem. -/
private def dualAsPrimalMap (T : V →ₗ[ℝ] V') : WithLp 2 (V' × V) →ₗ[ℝ] V :=
  (T.toContinuousLinearMap.adjoint.toLinearMap.coprod LinearMap.id).comp
    (WithLp.linearEquiv 2 ℝ (V' × V)).toLinearMap

@[simp]
private theorem dualAsPrimalMap_apply (T : V →ₗ[ℝ] V') (w : WithLp 2 (V' × V)) :
    dualAsPrimalMap T w = T.toContinuousLinearMap.adjoint w.fst + w.snd :=
  rfl

/-- **Primal Slater attainment, corrected.** If Wolf's primal problem is strictly feasible and
has the finite real optimum `p`, then the dual supremum is attained at objective value `p`.

The finite-optimum hypothesis is necessary: primal strict feasibility alone permits an unbounded
primal problem with an empty dual feasible set.
Source: Wolf, Chapter 4, lines 72--75, with the missing finiteness hypothesis restored. -/
theorem exists_isDualOptimizer_of_isPrimalStrictlyFeasible_of_isGLB
    {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {p : ℝ}
    (hstrict : IsPrimalStrictlyFeasible K T b)
    (hp : IsGLB ((fun x : V ↦ inner ℝ c x) '' primalFeasible K T b) p) :
    ∃ y : V', IsDualOptimizer K T c b y ∧ inner ℝ b y = p := by
  obtain ⟨y, hybound, hyobj⟩ :=
    exists_dual_of_strictlyFeasible_of_isGLB K.toPointedCone T c b p
      (by simpa [IsPrimalStrictlyFeasible] using hstrict)
      (by simpa [primalFeasible] using hp)
  have hyfeasible : y ∈ dualFeasible K T c := by
    change c - T.toContinuousLinearMap.adjoint y ∈ ProperCone.innerDual (K : Set V)
    refine ProperCone.mem_innerDual.mpr fun x hxK ↦ ?_
    rw [inner_sub_right, T.toContinuousLinearMap.adjoint_inner_right, ← real_inner_comm x c]
    exact sub_nonneg.mpr (hybound x hxK)
  refine ⟨y, ⟨hyfeasible, ?_⟩, hyobj⟩
  intro z hz
  rw [hyobj]
  apply hp.2
  rintro _ ⟨x, hx, rfl⟩
  exact weak_duality_pointwise hx hz

/-- **Primal Slater strong duality, corrected.** Under primal strict feasibility and a finite
real primal optimum, Wolf's extended-real primal and dual values are equal. Attainment is supplied
separately by `exists_isDualOptimizer_of_isPrimalStrictlyFeasible_of_isGLB`. -/
theorem values_eq_of_isPrimalStrictlyFeasible_of_isGLB
    {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {p : ℝ}
    (hstrict : IsPrimalStrictlyFeasible K T b)
    (hp : IsGLB ((fun x : V ↦ inner ℝ c x) '' primalFeasible K T b) p) :
    primalValue K T c b = dualValue K T c b := by
  obtain ⟨y, hyopt, hyobj⟩ :=
    exists_isDualOptimizer_of_isPrimalStrictlyFeasible_of_isGLB hstrict hp
  rw [primalValue_eq_coe_of_isGLB hp, dualValue_eq_of_isDualOptimizer hyopt, hyobj]

/-- **Dual Slater attainment, corrected.** If Wolf's dual problem is strictly feasible and has
the finite real optimum `p`, then the primal infimum is attained at objective value `p`.

The finite-optimum hypothesis is necessary: dual strict feasibility alone does not imply that the
primal feasible set is nonempty.
Source: Wolf, Chapter 4, lines 75--78, with the missing finiteness hypothesis restored. -/
theorem exists_isPrimalOptimizer_of_isDualStrictlyFeasible_of_isLUB
    {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {p : ℝ}
    (hstrict : IsDualStrictlyFeasible K T c)
    (hp : IsLUB ((fun y : V' ↦ inner ℝ b y) '' dualFeasible K T c) p) :
    ∃ x : V, IsPrimalOptimizer K T c b x ∧ inner ℝ c x = p := by
  let C : PointedCone ℝ (WithLp 2 (V' × V)) := dualAsPrimalCone K
  let A : WithLp 2 (V' × V) →ₗ[ℝ] V := dualAsPrimalMap T
  let d : WithLp 2 (V' × V) := WithLp.toLp 2 (-b, 0)
  have hstrict' : ∃ w ∈ interior (C : Set (WithLp 2 (V' × V))), A w = c := by
    obtain ⟨y₀, hy₀⟩ := hstrict
    let z₀ : V := c - T.toContinuousLinearMap.adjoint y₀
    refine ⟨WithLp.toLp 2 (y₀, z₀), ?_, ?_⟩
    · let e : WithLp 2 (V' × V) ≃ₜ V' × V := WithLp.homeomorphProd 2 V' V
      have hC : (C : Set (WithLp 2 (V' × V))) =
          e ⁻¹' (Set.univ ×ˢ (ProperCone.innerDual (K : Set V) : Set V)) := by
        ext w
        constructor
        · intro hw
          change w.snd ∈ ProperCone.innerDual (K : Set V) at hw
          change e w ∈ Set.univ ×ˢ (ProperCone.innerDual (K : Set V) : Set V)
          exact ⟨Set.mem_univ _, hw⟩
        · intro hw
          have hw' : e w ∈
              Set.univ ×ˢ (ProperCone.innerDual (K : Set V) : Set V) := hw
          change w.snd ∈ ProperCone.innerDual (K : Set V)
          exact hw'.2
      rw [hC, ← e.preimage_interior, interior_prod_eq, interior_univ]
      exact ⟨Set.mem_univ _, hy₀⟩
    · simp [A, z₀, dualAsPrimalMap]
  have hGLB :
      IsGLB ((fun w : WithLp 2 (V' × V) ↦ inner ℝ d w) ''
        {w | w ∈ C ∧ A w = c}) (-p) := by
    constructor
    · rintro _ ⟨w, ⟨hwC, hAw⟩, rfl⟩
      have hz : w.snd ∈ ProperCone.innerDual (K : Set V) := by
        exact hwC
      have hy : w.fst ∈ dualFeasible K T c := by
        change c - T.toContinuousLinearMap.adjoint w.fst ∈
          ProperCone.innerDual (K : Set V)
        have heq : c - T.toContinuousLinearMap.adjoint w.fst = w.snd := by
          change T.toContinuousLinearMap.adjoint w.fst + w.snd = c at hAw
          rw [← hAw]
          abel
        rw [heq]
        exact hz
      have hle := hp.1 ⟨w.fst, hy, rfl⟩
      have hdw : inner ℝ d w = -inner ℝ b w.fst := by
        rw [WithLp.prod_inner_apply]
        simp [d]
      change -p ≤ inner ℝ d w
      rw [hdw]
      linarith
    · intro a ha
      have hupper : p ≤ -a := by
        apply hp.2
        rintro _ ⟨y, hy, rfl⟩
        let z : V := c - T.toContinuousLinearMap.adjoint y
        let w : WithLp 2 (V' × V) := WithLp.toLp 2 (y, z)
        have hwC : w ∈ C := by
          change z ∈ ProperCone.innerDual (K : Set V)
          change c - T.toContinuousLinearMap.adjoint y ∈
            ProperCone.innerDual (K : Set V) at hy
          exact hy
        have hAw : A w = c := by
          simp [A, w, z, dualAsPrimalMap]
        have hle := ha ⟨w, ⟨hwC, hAw⟩, rfl⟩
        have hdw : inner ℝ d w = -inner ℝ b y := by
          rw [WithLp.prod_inner_apply]
          simp [d, w]
        change a ≤ inner ℝ d w at hle
        rw [hdw] at hle
        linarith
      linarith
  obtain ⟨x, hxbound, hxobj⟩ :=
    exists_dual_of_strictlyFeasible_of_isGLB C A d c (-p) hstrict' hGLB
  have hTx : T (-x) = b := by
    let y : V' := T x + b
    let w : WithLp 2 (V' × V) := WithLp.toLp 2 (y, 0)
    have hyC : w ∈ C := by simp [C, dualAsPrimalCone, w]
    have hbound := hxbound w hyC
    have hbound' : inner ℝ (T.toContinuousLinearMap.adjoint y) x ≤
        inner ℝ (-b) y := by
      simpa [A, d, w, dualAsPrimalMap, WithLp.prod_inner_apply] using hbound
    rw [T.toContinuousLinearMap.adjoint_inner_left, inner_neg_left] at hbound'
    have hself_nonpos : inner ℝ y y ≤ 0 := by
      dsimp [y]
      rw [inner_add_right]
      dsimp [y] at hbound'
      rw [real_inner_comm (T x + b) b] at hbound'
      linarith
    have hy_zero : y = 0 := inner_self_eq_zero.mp (le_antisymm hself_nonpos real_inner_self_nonneg)
    rw [map_neg]
    exact neg_eq_of_add_eq_zero_right hy_zero
  have hxK : -x ∈ K := by
    have hdouble : -x ∈
        ProperCone.innerDual (ProperCone.innerDual (K : Set V) : Set V) := by
      refine ProperCone.mem_innerDual.mpr fun z hz ↦ ?_
      let w : WithLp 2 (V' × V) := WithLp.toLp 2 (0, z)
      have hzC : w ∈ C := by
        change z ∈ ProperCone.innerDual (K : Set V)
        exact hz
      have hbound := hxbound w hzC
      have hbound' : inner ℝ z x ≤ 0 := by
        simpa [A, d, w, dualAsPrimalMap, WithLp.prod_inner_apply] using hbound
      simpa [inner_neg_right] using neg_nonneg.mpr hbound'
    rw [ProperCone.innerDual_innerDual K] at hdouble
    exact hdouble
  have hxfeasible : -x ∈ primalFeasible K T b := ⟨hxK, hTx⟩
  have hxobj' : inner ℝ c (-x) = p := by
    rw [inner_neg_right]
    linarith
  refine ⟨-x, ⟨hxfeasible, ?_⟩, hxobj'⟩
  intro z hz
  rw [hxobj']
  apply hp.2
  rintro _ ⟨y, hy, rfl⟩
  exact weak_duality_pointwise hz hy

/-- **Dual Slater strong duality, corrected.** Under dual strict feasibility and a finite real
dual optimum, Wolf's extended-real primal and dual values are equal. Attainment is supplied
separately by `exists_isPrimalOptimizer_of_isDualStrictlyFeasible_of_isLUB`. -/
theorem values_eq_of_isDualStrictlyFeasible_of_isLUB
    {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {p : ℝ}
    (hstrict : IsDualStrictlyFeasible K T c)
    (hp : IsLUB ((fun y : V' ↦ inner ℝ b y) '' dualFeasible K T c) p) :
    primalValue K T c b = dualValue K T c b := by
  obtain ⟨x, hxopt, hxobj⟩ :=
    exists_isPrimalOptimizer_of_isDualStrictlyFeasible_of_isLUB hstrict hp
  rw [primalValue_eq_of_isPrimalOptimizer hxopt, dualValue_eq_coe_of_isLUB hp, hxobj]

/-- **Primal Slater attainment in Wolf's value notation.** If the primal problem is strictly
feasible and its extended-real value is the finite real number `p`, then the dual optimum is
attained at value `p`. -/
theorem exists_isDualOptimizer_of_isPrimalStrictlyFeasible_of_primalValue_eq_coe
    {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {p : ℝ}
    (hstrict : IsPrimalStrictlyFeasible K T b)
    (hvalue : primalValue K T c b = (p : EReal)) :
    ∃ y : V', IsDualOptimizer K T c b y ∧ inner ℝ b y = p := by
  apply exists_isDualOptimizer_of_isPrimalStrictlyFeasible_of_isGLB hstrict
  exact (primalValue_eq_coe_iff_isGLB hstrict.feasible).mp hvalue

/-- **Primal Slater strong duality in Wolf's value notation.** If the primal problem is strictly
feasible and its extended-real value is finite, then the primal and dual values are equal. -/
theorem values_eq_of_isPrimalStrictlyFeasible_of_primalValue_eq_coe
    {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {p : ℝ}
    (hstrict : IsPrimalStrictlyFeasible K T b)
    (hvalue : primalValue K T c b = (p : EReal)) :
    primalValue K T c b = dualValue K T c b := by
  apply values_eq_of_isPrimalStrictlyFeasible_of_isGLB hstrict
  exact (primalValue_eq_coe_iff_isGLB hstrict.feasible).mp hvalue

/-- **Dual Slater attainment in Wolf's value notation.** If the dual problem is strictly feasible
and its extended-real value is the finite real number `p`, then the primal optimum is attained at
value `p`. -/
theorem exists_isPrimalOptimizer_of_isDualStrictlyFeasible_of_dualValue_eq_coe
    {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {p : ℝ}
    (hstrict : IsDualStrictlyFeasible K T c)
    (hvalue : dualValue K T c b = (p : EReal)) :
    ∃ x : V, IsPrimalOptimizer K T c b x ∧ inner ℝ c x = p := by
  apply exists_isPrimalOptimizer_of_isDualStrictlyFeasible_of_isLUB hstrict
  exact (dualValue_eq_coe_iff_isLUB hstrict.feasible).mp hvalue

/-- **Dual Slater strong duality in Wolf's value notation.** If the dual problem is strictly
feasible and its extended-real value is finite, then the primal and dual values are equal. -/
theorem values_eq_of_isDualStrictlyFeasible_of_dualValue_eq_coe
    {K : ProperCone ℝ V} {T : V →ₗ[ℝ] V'} {c : V} {b : V'} {p : ℝ}
    (hstrict : IsDualStrictlyFeasible K T c)
    (hvalue : dualValue K T c b = (p : EReal)) :
    primalValue K T c b = dualValue K T c b := by
  apply values_eq_of_isDualStrictlyFeasible_of_isLUB hstrict
  exact (dualValue_eq_coe_iff_isLUB hstrict.feasible).mp hvalue

end Slater

end ConicProgram
