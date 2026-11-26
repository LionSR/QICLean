/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import QICLean.Analysis.Topology.NearestKronecker
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A local section for the action of local unitaries

The unitary part `Q(X) = X (X† X)^{-1/2}` of an invertible complex matrix is
continuous, commutes with left multiplication by unitaries, fixes unitaries and
sends a Kronecker product `A ⊗ B` of invertible matrices to `Q(A) ⊗ Q(B)`.

Fix a unitary `u₀` on a bipartite space. For `u` near the orbit of `u₀` under the
local unitaries `x ⊗ y`, the gauge `g(u) = Q(N(u u₀†))`, built from the nearest
Kronecker product `N` of `QICLean/Analysis/Topology/NearestKronecker.lean`, is a product of
local unitaries, and `σ(u) = g(u)† u` is a continuous map on an open set
containing the orbit, invariant under the local unitaries, with `σ(u)` in the
orbit of `u`.

This is step 3 of the cross-section construction that replaces the slice theorem
of Montgomery and Yang in arXiv:1703.09188, proof of Corollary `coruvSF`,
lines 942--947; see the note
https://sirui-lu.com/TNLean/paper-gaps/mpu_standard_form_path_cross_section.pdf.

## Main declarations

* `Matrix.unitaryPart`: the unitary part `Q(X)` of a matrix.
* `Matrix.continuousOn_unitaryPart`, `Matrix.unitaryPart_mem_unitaryGroup`,
  `Matrix.unitaryPart_unitary_mul`, `Matrix.unitaryPart_kronecker`.
* `Matrix.localSection`: the local section `σ`, defined on
  `Matrix.localSectionDomain`.
* `Matrix.continuousOn_localSection`, `Matrix.localSection_kronecker_mul`,
  `Matrix.exists_localSection_eq_kronecker_mul`,
  `Matrix.kronecker_mul_mem_localSectionDomain`.

Moved from TNLean, `TNLean/Algebra/KroneckerLocalSection.lean`
at commit `49b78ed821` (Apache-2.0).
* `exists_continuousOn_Icc_lift`, `Matrix.exists_continuous_lift_of_continuous_mod_localUnitary`:
  lifting paths that are continuous modulo local unitaries.
-/

section KroneckerLocalSection

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder Kronecker

namespace Matrix

/-! ### The unitary part of a matrix -/

section UnitaryPart

variable {p : Type*} [Fintype p] [DecidableEq p]

/-- The inverse square root `(X† X)^{-1/2}` of the Gram matrix, by the real
continuous functional calculus.

Source: the factor `(N†N)^{-1/2}` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def invSqrtGram (X : Matrix p p ℂ) : Matrix p p ℂ :=
  cfc (fun t : ℝ ↦ (Real.sqrt t)⁻¹) (star X * X)

/-- The unitary part `Q(X) = X (X† X)^{-1/2}` of a matrix.

Source: the map `Q` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def unitaryPart (X : Matrix p p ℂ) : Matrix p p ℂ :=
  X * invSqrtGram X

private theorem spectrum_star_mul_self_pos {X : Matrix p p ℂ} (hX : IsUnit X) {t : ℝ}
    (ht : t ∈ spectrum ℝ (star X * X)) : 0 < t :=
  (CStarAlgebra.isStrictlyPositive_iff_isSelfAdjoint_and_spectrum_pos.mp
    ((hX.star.mul hX).isStrictlyPositive (star_mul_self_nonneg X))).2 t ht

private theorem continuousOn_inv_sqrt :
    ContinuousOn (fun t : ℝ ↦ (Real.sqrt t)⁻¹) (Set.Ioi 0) :=
  Real.continuous_sqrt.continuousOn.inv₀ fun _ ht ↦ (Real.sqrt_pos.mpr ht).ne'

theorem isSelfAdjoint_invSqrtGram (X : Matrix p p ℂ) : IsSelfAdjoint (invSqrtGram X) :=
  cfc_predicate _ _

private theorem invSqrtGram_mul_star_mul_self_mul {X : Matrix p p ℂ} (hX : IsUnit X) :
    invSqrtGram X * (star X * X) * invSqrtGram X = 1 := by
  have hG : IsSelfAdjoint (star X * X) := IsSelfAdjoint.star_mul_self X
  have hc := continuousOn_inv_sqrt.mono fun t (ht : t ∈ spectrum ℝ (star X * X)) ↦
    spectrum_star_mul_self_pos hX ht
  rw [invSqrtGram]
  nth_rw 2 [← cfc_id' ℝ (star X * X) hG]
  rw [← cfc_mul (fun t : ℝ ↦ (Real.sqrt t)⁻¹) (fun t : ℝ ↦ t) _ hc continuousOn_id,
    ← cfc_mul (fun t : ℝ ↦ (Real.sqrt t)⁻¹ * t) (fun t : ℝ ↦ (Real.sqrt t)⁻¹) _
      (hc.mul continuousOn_id) hc,
    ← cfc_one ℝ (star X * X) hG]
  refine cfc_congr fun t ht ↦ ?_
  have h0 := spectrum_star_mul_self_pos hX ht
  have hs : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt h0.le
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr h0).ne'
  rw [Pi.one_apply]
  field_simp
  rw [Real.sq_sqrt h0.le]

/-- The unitary part of an invertible matrix is unitary. -/
theorem unitaryPart_mem_unitaryGroup {X : Matrix p p ℂ} (hX : IsUnit X) :
    unitaryPart X ∈ unitaryGroup p ℂ := by
  have hs : star (unitaryPart X) * unitaryPart X = 1 := by
    rw [unitaryPart, star_mul, (isSelfAdjoint_invSqrtGram X).star_eq, Matrix.mul_assoc,
      ← Matrix.mul_assoc (star X), ← Matrix.mul_assoc]
    exact invSqrtGram_mul_star_mul_self_mul hX
  exact (Matrix.mem_unitaryGroup_iff').mpr hs

/-- The unitary part is continuous on the invertible matrices. -/
theorem continuousOn_unitaryPart :
    ContinuousOn (unitaryPart : Matrix p p ℂ → Matrix p p ℂ) {X | IsUnit X} := by
  have hs : Set.Ioi (0 : ℝ) ∈ nhdsSet (⋃ X ∈ {X : Matrix p p ℂ | IsUnit X},
      spectrum ℝ (star X * X)) := by
    rw [isOpen_Ioi.mem_nhdsSet]
    simp only [Set.iUnion_subset_iff]
    exact fun X hX t ht ↦ spectrum_star_mul_self_pos hX ht
  have hinv : ContinuousOn invSqrtGram {X : Matrix p p ℂ | IsUnit X} :=
    ContinuousOn.cfc_of_mem_nhdsSet _ hs (by fun_prop)
      (fun X _ ↦ IsSelfAdjoint.star_mul_self X) continuousOn_inv_sqrt
  exact continuousOn_id.mul hinv

/-- **Equivariance of the unitary part.** For a unitary `U`, `Q(U X) = U Q(X)`. -/
theorem unitaryPart_unitary_mul {U : Matrix p p ℂ} (hU : U ∈ unitaryGroup p ℂ)
    (X : Matrix p p ℂ) : unitaryPart (U * X) = U * unitaryPart X := by
  have : star (U * X) * (U * X) = star X * X := by
    rw [star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star U), Unitary.star_mul_self_of_mem hU,
      Matrix.one_mul]
  rw [unitaryPart, unitaryPart, invSqrtGram, invSqrtGram, this, Matrix.mul_assoc]

/-- A unitary matrix is its own unitary part. -/
theorem unitaryPart_of_mem_unitaryGroup {U : Matrix p p ℂ} (hU : U ∈ unitaryGroup p ℂ) :
    unitaryPart U = U := by
  rcases isEmpty_or_nonempty p with hp | hp
  · exact Subsingleton.elim _ _
  rw [unitaryPart, invSqrtGram, Unitary.star_mul_self_of_mem hU, cfc_congr (g := fun _ ↦ 1)
    (fun t ht ↦ ?_), cfc_const_one ℝ (1 : Matrix p p ℂ), Matrix.mul_one]
  rw [spectrum.one_eq] at ht
  simp [Set.mem_singleton_iff.mp ht]

/-- The inverse square root of the Gram matrix is the square root of the inverse
Gram matrix. -/
private theorem invSqrtGram_eq_sqrt {X : Matrix p p ℂ} (hX : IsUnit X) :
    invSqrtGram X = CFC.sqrt (star X * X)⁻¹ := by
  have hG : IsSelfAdjoint (star X * X) := IsSelfAdjoint.star_mul_self X
  have hc := continuousOn_inv_sqrt.mono fun t (ht : t ∈ spectrum ℝ (star X * X)) ↦
    spectrum_star_mul_self_pos hX ht
  have hpos : (star X * X).PosDef :=
    IsStrictlyPositive.posDef ((hX.star.mul hX).isStrictlyPositive (star_mul_self_nonneg X))
  have hnn : 0 ≤ invSqrtGram X := cfc_nonneg fun t ht ↦
    inv_nonneg.mpr (Real.sqrt_nonneg t)
  symm
  rw [CFC.sqrt_eq_iff _ _ hpos.inv.posSemidef.nonneg hnn, invSqrtGram,
    ← cfc_mul _ _ _ hc hc]
  obtain ⟨u, hu⟩ := hpos.isUnit
  rw [← hu, ← Matrix.coe_units_inv, ← cfc_inv_id (R := ℝ) u (hu ▸ hG)]
  refine cfc_congr fun t ht ↦ ?_
  have h0 := spectrum_star_mul_self_pos hX (hu ▸ ht)
  rw [← mul_inv, Real.mul_self_sqrt h0.le]

/-- **The unitary part of a Kronecker product.** For invertible `A` and `B`,
`Q(A ⊗ B) = Q(A) ⊗ Q(B)`. -/
theorem unitaryPart_kronecker {q : Type*} [Fintype q] [DecidableEq q]
    {A : Matrix p p ℂ} {B : Matrix q q ℂ} (hA : IsUnit A) (hB : IsUnit B) :
    unitaryPart (A ⊗ₖ B) = unitaryPart A ⊗ₖ unitaryPart B := by
  have hAB : IsUnit (A ⊗ₖ B) := by
    rw [isUnit_iff_isUnit_det, det_kronecker]
    exact ((isUnit_iff_isUnit_det A).mp hA).pow _ |>.mul (((isUnit_iff_isUnit_det B).mp hB).pow _)
  have hpA : (star A * A).PosDef :=
    IsStrictlyPositive.posDef ((hA.star.mul hA).isStrictlyPositive (star_mul_self_nonneg A))
  have hpB : (star B * B).PosDef :=
    IsStrictlyPositive.posDef ((hB.star.mul hB).isStrictlyPositive (star_mul_self_nonneg B))
  rw [unitaryPart, unitaryPart, unitaryPart, mul_kronecker_mul, invSqrtGram_eq_sqrt hAB,
    invSqrtGram_eq_sqrt hA, invSqrtGram_eq_sqrt hB]
  congr 1
  have hstar : star (A ⊗ₖ B) * (A ⊗ₖ B) = (star A * A) ⊗ₖ (star B * B) := by
    rw [star_eq_conjTranspose, conjTranspose_kronecker, ← mul_kronecker_mul,
      star_eq_conjTranspose, star_eq_conjTranspose]
  rw [hstar, inv_kronecker, CFC.sqrt_eq_iff _ _
    (hpA.inv.posSemidef.kronecker hpB.inv.posSemidef).nonneg
    ((nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).kronecker
      (nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))).nonneg,
    ← mul_kronecker_mul, CFC.sqrt_mul_sqrt_self _ hpA.inv.posSemidef.nonneg,
    CFC.sqrt_mul_sqrt_self _ hpB.inv.posSemidef.nonneg]

end UnitaryPart

/-! ### The local section -/

section LocalSection

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable (a b : ℝ) (u₀ : Matrix (m × n) (m × n) ℂ)

/-- The local gauge `g(u) = Q(N(u u₀†))`.

Source: the gauge `g(u)` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def localGauge (u : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  unitaryPart (nearestKronecker a b (u * star u₀))

/-- The local section `σ(u) = g(u)† u`.

Source: the section `σ` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
noncomputable def localSection (u : Matrix (m × n) (m × n) ℂ) : Matrix (m × n) (m × n) ℂ :=
  star (localGauge a b u₀ u) * u

/-- The domain of the local section: `u u₀†` lies in the gap set of the nearest
Kronecker product, and `N(u u₀†)` is invertible.

Source: the open set `W` of step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
def localSectionDomain : Set (Matrix (m × n) (m × n) ℂ) :=
  {u | u * star u₀ ∈ kroneckerGapSet a b ∧ IsUnit (nearestKronecker a b (u * star u₀))}

theorem isOpen_localSectionDomain : IsOpen (localSectionDomain a b u₀) := by
  have hc : Continuous fun u : Matrix (m × n) (m × n) ℂ ↦ u * star u₀ :=
    continuous_id.mul continuous_const
  have hdet : Continuous fun u : Matrix (m × n) (m × n) ℂ ↦
      (nearestKronecker a b (u * star u₀)).det :=
    ((continuous_nearestKronecker a b).comp hc).matrix_det
  have hunit : {u : Matrix (m × n) (m × n) ℂ | IsUnit (nearestKronecker a b (u * star u₀))} =
      (fun u ↦ (nearestKronecker a b (u * star u₀)).det) ⁻¹' {0}ᶜ := by
    ext u
    simp [isUnit_iff_isUnit_det]
  change IsOpen ((fun u : Matrix (m × n) (m × n) ℂ ↦ u * star u₀) ⁻¹' kroneckerGapSet a b ∩
    {u | IsUnit (nearestKronecker a b (u * star u₀))})
  rw [hunit]
  exact ((isOpen_kroneckerGapSet a b).preimage hc).inter (isOpen_compl_singleton.preimage hdet)

theorem continuousOn_localSection :
    ContinuousOn (localSection a b u₀) (localSectionDomain a b u₀) := by
  have hc : Continuous fun u : Matrix (m × n) (m × n) ℂ ↦ nearestKronecker a b (u * star u₀) :=
    (continuous_nearestKronecker a b).comp (continuous_id.mul continuous_const)
  have hg : ContinuousOn (localGauge a b u₀) (localSectionDomain a b u₀) :=
    continuousOn_unitaryPart.comp hc.continuousOn fun _ hu ↦ hu.2
  exact (continuous_star.comp_continuousOn hg).mul continuousOn_id

variable (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ))

private theorem kronecker_mem_unitaryGroup :
    (x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ) ∈ unitaryGroup (m × n) ℂ :=
  kronecker_mem_unitary x.2 y.2

/-- **Invariance of the local section.** `σ((x ⊗ y) u) = σ(u)` for unitaries `x`
and `y`.

Source: the invariance of `σ` in step 3 of the cross-section construction for
arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
theorem localSection_kronecker_mul (u : Matrix (m × n) (m × n) ℂ) :
    localSection a b u₀ (((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u) =
      localSection a b u₀ u := by
  rw [localSection, localSection, localGauge, localGauge, Matrix.mul_assoc,
    nearestKronecker_kronecker_mul, unitaryPart_unitary_mul (kronecker_mem_unitaryGroup x y),
    star_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (star _) _ u,
    Unitary.star_mul_self_of_mem (kronecker_mem_unitaryGroup x y), Matrix.one_mul]

/-- The domain of the local section is invariant under the local unitaries. -/
theorem kronecker_mul_mem_localSectionDomain_iff (u : Matrix (m × n) (m × n) ℂ) :
    ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u ∈ localSectionDomain a b u₀ ↔
      u ∈ localSectionDomain a b u₀ := by
  have hU := kronecker_mem_unitaryGroup x y
  simp only [localSectionDomain, Set.mem_ofPred_eq, Matrix.mul_assoc,
    kronecker_mul_mem_kroneckerGapSet_iff, nearestKronecker_kronecker_mul]
  refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun h ↦ (Unitary.isUnit_coe (U := ⟨_, hU⟩)).mul h⟩
  have := (Unitary.isUnit_coe (U := ⟨_, Unitary.star_mem hU⟩)).mul h
  rwa [← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hU, Matrix.one_mul] at this

/-- **The local section stays in the orbit.** For `u` in the domain, `σ(u)` is
`(x ⊗ y) u` for some unitaries `x` and `y`, provided `0 < a < b`.

Source: step 3 of the cross-section construction for arXiv:1703.09188,
Corollary `coruvSF`, lines 942--947. -/
theorem exists_localSection_eq_kronecker_mul (ha : 0 < a) (hab : a < b)
    {u : Matrix (m × n) (m × n) ℂ} (hu : u ∈ localSectionDomain a b u₀) :
    ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
      localSection a b u₀ u = ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u := by
  rcases isEmpty_or_nonempty m with hm | hm
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, 1, Subsingleton.elim _ _⟩
  obtain ⟨A, B, -, -, hAB⟩ := exists_eq_kronecker_nearestKronecker ha hab hu.1
  have hunit := hu.2
  rw [hAB, isUnit_iff_isUnit_det, det_kronecker] at hunit
  have hA : IsUnit A := by
    rw [isUnit_iff_isUnit_det]
    exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_left hunit)
  have hB : IsUnit B := by
    rw [isUnit_iff_isUnit_det]
    exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hunit)
  refine ⟨⟨star (unitaryPart A), Unitary.star_mem (unitaryPart_mem_unitaryGroup hA)⟩,
    ⟨star (unitaryPart B), Unitary.star_mem (unitaryPart_mem_unitaryGroup hB)⟩, ?_⟩
  rw [localSection, localGauge, hAB, unitaryPart_kronecker hA hB, star_eq_conjTranspose,
    conjTranspose_kronecker]
  rfl

private theorem kronecker_mul_mul_star_eq {u₀ : Matrix (m × n) (m × n) ℂ}
    (hu₀ : u₀ ∈ unitaryGroup (m × n) ℂ) :
    ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u₀ * star u₀ =
      (x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ) := by
  rw [Matrix.mul_assoc, Unitary.mul_star_self_of_mem hu₀, Matrix.mul_one]

section Orbit

variable {a b} {u₀} (hapos : 0 < a) (hab : a < b) (hbc : b < Fintype.card m * Fintype.card n)
  (hu₀ : u₀ ∈ unitaryGroup (m × n) ℂ)
include hapos hab hbc hu₀

/-- **The orbit of the base point lies in the domain.** For a unitary `u₀`, every
`(x ⊗ y) u₀` lies in the domain of the local section, provided
`0 < a < b < |m| |n|`. -/
theorem kronecker_mul_mem_localSectionDomain :
    ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u₀ ∈ localSectionDomain a b u₀ := by
  rw [localSectionDomain, Set.mem_ofPred_eq, kronecker_mul_mul_star_eq x y hu₀,
    nearestKronecker_kronecker_of_unitary hapos hab hbc]
  exact ⟨kronecker_mem_kroneckerGapSet hapos hab hbc x y,
    Unitary.isUnit_coe (U := ⟨_, kronecker_mem_unitaryGroup x y⟩)⟩

/-- **The local section fixes the base point.** For a unitary `u₀`,
`σ((x ⊗ y) u₀) = u₀`, provided `0 < a < b < |m| |n|`. -/
theorem localSection_kronecker_mul_self :
    localSection a b u₀ (((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u₀) = u₀ := by
  rw [localSection_kronecker_mul, localSection, localGauge, Unitary.mul_star_self_of_mem hu₀,
    nearestKronecker_one hapos hab hbc, unitaryPart_of_mem_unitaryGroup (one_mem _), star_one,
    Matrix.one_mul]

end Orbit

end LocalSection

end Matrix

end KroneckerLocalSection

section KroneckerPathLifting

/-!
## Lifting paths that are continuous modulo local unitaries

Let `u : [0, 1] → U(ℓ r)` be continuous modulo the local unitaries: for every `p`
and `ε > 0` there is `δ > 0` such that for `|q - p| < δ` some product `x ⊗ y` of
unitaries gives `‖u(q) - (x ⊗ y) u(p)‖ < ε`. Then there is a continuous
`û : [0, 1] → U(ℓ r)` with `û(p)` in the orbit of `u(p)` for every `p`.

The proof uses the local sections of `QICLean/Analysis/Topology/KroneckerLocalSection.lean`:
near each `p`, the map `q ↦ σ_p(u(q))` is a continuous lift, because `σ_p` is
invariant under the local unitaries. A Lebesgue number for the cover of `[0, 1]`
by these neighbourhoods divides `[0, 1]` into finitely many intervals, each
carrying a local lift, and neighbouring lifts are matched at the junctions by
constant local unitaries. No continuity of `u` itself is used.

This is step 4 of the cross-section construction that replaces the slice theorem
of Montgomery and Yang in arXiv:1703.09188, proof of Corollary `coruvSF`,
lines 942--947; see the note
https://sirui-lu.com/TNLean/paper-gaps/mpu_standard_form_path_cross_section.pdf.

### Main statements

* `exists_continuousOn_Icc_lift`: local lifts on `[0, 1]`, matched by constant
  group elements, glue to a lift on `[0, 1]`, for any group action by
  homeomorphisms.
* `Matrix.exists_continuous_lift_of_continuous_mod_localUnitary`: the path
  lifting theorem.

Moved from TNLean, `TNLean/Algebra/KroneckerPathLifting.lean`
at commit `49b78ed821` (Apache-2.0).
-/

open Set Filter Topology Metric

/-! ### Gluing local lifts along `[0, 1]` -/

section Gluing

variable {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- Gluing a lift on `[0, t]` to a lift on `[t, t']` by a constant group element. -/
private theorem glue_lift {f : ℝ → X} {t t' : ℝ} (htt' : t ≤ t') {L L' : ℝ → X}
    (hL : ContinuousOn L (Icc 0 t)) (hLf : ∀ q ∈ Icc 0 t, ∃ g : G, L q = g • f q)
    (hL' : ContinuousOn L' (Icc t t')) (hL'f : ∀ q ∈ Icc t t', ∃ g : G, L' q = g • f q)
    (ht : 0 ≤ t) :
    ∃ L'' : ℝ → X, ContinuousOn L'' (Icc 0 t') ∧ ∀ q ∈ Icc 0 t', ∃ g : G, L'' q = g • f q := by
  obtain ⟨g₁, hg₁⟩ := hLf t ⟨ht, le_rfl⟩
  obtain ⟨g₂, hg₂⟩ := hL'f t ⟨le_rfl, htt'⟩
  set c : G := g₁ * g₂⁻¹
  have hc : L t = c • L' t := by rw [hg₁, hg₂, smul_smul, mul_assoc, inv_mul_cancel, mul_one]
  classical
  refine ⟨fun q ↦ if q ≤ t then L q else c • L' q, ?_, fun q hq ↦ ?_⟩
  · have hunion : Icc 0 t' = Icc 0 t ∪ Icc t t' := (Icc_union_Icc_eq_Icc ht htt').symm
    rw [hunion]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact hL.congr fun q hq ↦ by simp only [hq.2, ↓reduceIte]
    · refine ((continuous_const_smul c).comp_continuousOn hL').congr fun q hq ↦ ?_
      rcases hq.1.lt_or_eq with h | h
      · simp only [not_le.mpr h, ↓reduceIte, Function.comp_apply]
      · simp only [← h, le_refl, ↓reduceIte, hc, Function.comp_apply]
  · by_cases hqt : q ≤ t
    · simp only [hqt, ↓reduceIte]
      exact hLf q ⟨hq.1, hqt⟩
    · simp only [hqt, ↓reduceIte]
      obtain ⟨g, hg⟩ := hL'f q ⟨(not_le.mp hqt).le, hq.2⟩
      exact ⟨c * g, by rw [hg, smul_smul]⟩

/-- **Gluing local lifts.** Suppose every point of `[0, 1]` has a neighbourhood
carrying a continuous map `L` with `L q` in the orbit of `f q`. Then there is a
map, continuous on `[0, 1]`, whose value at every `q ∈ [0, 1]` lies in the orbit
of `f q`. The function `f` itself need not be continuous.

Source: the Lebesgue number argument of step 4 of the cross-section construction
for arXiv:1703.09188, Corollary `coruvSF`, lines 942--947. -/
theorem exists_continuousOn_Icc_lift {f : ℝ → X}
    (hloc : ∀ p ∈ Icc (0 : ℝ) 1, ∃ U ∈ 𝓝 p, ∃ L : ℝ → X,
      ContinuousOn L U ∧ ∀ q ∈ U, ∃ g : G, L q = g • f q) :
    ∃ L : ℝ → X, ContinuousOn L (Icc 0 1) ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∃ g : G, L q = g • f q := by
  choose! U hU L hL hLf using hloc
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric (c := fun p : Icc (0 : ℝ) 1 ↦
      interior (U p)) isCompact_Icc (fun _ ↦ isOpen_interior)
    (fun p hp ↦ mem_iUnion.mpr ⟨⟨p, hp⟩, mem_interior_iff_mem_nhds.mpr (hU p hp)⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have hn0 : (0 : ℝ) < n + 1 := by positivity
  -- Every interval `[k/(n+1), (k+1)/(n+1)]` with `k ≤ n` lies in some `U p`.
  have hstep : ∀ k : ℕ, k ≤ n → ∃ p ∈ Icc (0 : ℝ) 1,
      Icc ((k : ℝ) / (n + 1)) ((k + 1 : ℝ) / (n + 1)) ⊆ U p := by
    intro k hk
    have hk0 : (k : ℝ) / (n + 1) ∈ Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, (div_le_one hn0).mpr ?_⟩
      exact_mod_cast hk.trans (Nat.le_succ n)
    obtain ⟨⟨p, hp⟩, hp'⟩ := hball _ hk0
    refine ⟨p, hp, fun q hq ↦ interior_subset (hp' ?_)⟩
    rw [mem_ball, Real.dist_eq, abs_lt]
    have h1 : q - (k : ℝ) / (n + 1) ≤ 1 / (n + 1) := by
      have := hq.2
      rw [add_div] at this
      linarith
    constructor <;> linarith [hq.1]
  -- Induction on the number of intervals.
  have hind : ∀ k : ℕ, k ≤ n + 1 → ∃ L : ℝ → X, ContinuousOn L (Icc 0 ((k : ℝ) / (n + 1))) ∧
      ∀ q ∈ Icc (0 : ℝ) ((k : ℝ) / (n + 1)), ∃ g : G, L q = g • f q := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ ↦ f 0, continuousOn_const, fun q hq ↦ ⟨1, ?_⟩⟩
      have : q = 0 := by simp only [Nat.cast_zero, zero_div] at hq; exact le_antisymm hq.2 hq.1
      rw [this, one_smul]
    | succ k ih =>
      intro hk
      obtain ⟨L₀, hL₀, hL₀f⟩ := ih (by omega)
      obtain ⟨p, hp, hsub⟩ := hstep k (by omega)
      have htt' : (k : ℝ) / (n + 1) ≤ (k + 1 : ℝ) / (n + 1) :=
        div_le_div_of_nonneg_right (by linarith) hn0.le
      have := glue_lift (G := G) htt' hL₀ hL₀f ((hL p hp).mono hsub)
        (fun q hq ↦ hLf p hp q (hsub hq)) (by positivity)
      simpa only [Nat.cast_succ] using this
  obtain ⟨L₀, hL₀, hL₀f⟩ := hind (n + 1) le_rfl
  have : ((n + 1 : ℕ) : ℝ) / (n + 1) = 1 := by push_cast; exact div_self hn0.ne'
  rw [this] at hL₀ hL₀f
  exact ⟨L₀, hL₀, hL₀f⟩

end Gluing

/-! ### Lifting paths of unitaries -/

namespace Matrix

open scoped Matrix.Norms.L2Operator Kronecker

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The local unitaries `x ⊗ y` acting by left multiplication. -/
@[reducible] private noncomputable def localUnitaryAction :
    MulAction (unitary (Matrix m m ℂ) × unitary (Matrix n n ℂ)) (Matrix (m × n) (m × n) ℂ) where
  smul g v := ((g.1 : Matrix m m ℂ) ⊗ₖ (g.2 : Matrix n n ℂ)) * v
  one_smul v := by
    change ((1 : Matrix m m ℂ) ⊗ₖ (1 : Matrix n n ℂ)) * v = v
    rw [one_kronecker_one, Matrix.one_mul]
  mul_smul g h v := by
    change (((g.1 : Matrix m m ℂ) * (h.1 : Matrix m m ℂ)) ⊗ₖ
      ((g.2 : Matrix n n ℂ) * (h.2 : Matrix n n ℂ))) * v = _
    rw [mul_kronecker_mul, Matrix.mul_assoc]
    rfl

variable {a b : ℝ} (hapos : 0 < a) (hab : a < b) (hbc : b < Fintype.card m * Fintype.card n)
include hapos hab hbc

omit hapos hab hbc in
/-- **The local section is continuous along a path continuous modulo local
unitaries.** If `f(q₀)` lies in the domain of the local section `σ`, then `f(q)`
lies in the domain for `q` near `q₀`, and `q ↦ σ(f(q))` is continuous at `q₀`. -/
private theorem eventually_mem_and_continuousAt {u₀ : Matrix (m × n) (m × n) ℂ}
    {f : ℝ → Matrix (m × n) (m × n) ℂ}
    (hf : ∀ t, ∀ ε > 0, ∃ δ > 0, ∀ s, dist s t < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖f s - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * f t‖ < ε)
    {q₀ : ℝ} (hq₀ : f q₀ ∈ localSectionDomain a b u₀) :
    (∀ᶠ q in 𝓝 q₀, f q ∈ localSectionDomain a b u₀) ∧
      ContinuousAt (fun q ↦ localSection a b u₀ (f q)) q₀ := by
  have hopen := isOpen_localSectionDomain a b u₀
  have hσ : ContinuousAt (localSection a b u₀) (f q₀) :=
    (continuousOn_localSection a b u₀).continuousAt (hopen.mem_nhds hq₀)
  -- Moving `f s` back by the inverse local unitary lands near `f q₀`.
  have hback : ∀ η > 0, ∃ δ > 0, ∀ s, dist s q₀ < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        dist (((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * f s) (f q₀) < η := by
    intro η hη
    obtain ⟨δ, hδ, hfδ⟩ := hf q₀ η hη
    refine ⟨δ, hδ, fun s hs ↦ ?_⟩
    obtain ⟨x, y, hxy⟩ := hfδ s hs
    have hV := kronecker_mem_unitary x.2 y.2
    have hstar : ((star x : unitary (Matrix m m ℂ)) ⊗ₖ (star y : unitary (Matrix n n ℂ)) :
        Matrix (m × n) (m × n) ℂ) = star ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) := by
      rw [star_eq_conjTranspose, conjTranspose_kronecker]
      rfl
    refine ⟨star x, star y, ?_⟩
    have hk : ((star x : unitary (Matrix m m ℂ)) ⊗ₖ (star y : unitary (Matrix n n ℂ)) :
        Matrix (m × n) (m × n) ℂ) * f s - f q₀ =
        star ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) *
          (f s - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * f q₀) := by
      rw [hstar, Matrix.mul_sub, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem hV,
        Matrix.one_mul]
    rw [dist_eq_norm, hk]
    exact lt_of_eq_of_lt (CStarRing.norm_coe_unitary_mul ⟨_, Unitary.star_mem hV⟩ _) hxy
  constructor
  · obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hopen _ hq₀
    obtain ⟨δ, hδ, hδ'⟩ := hback η hη
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun s hs ↦ ?_⟩
    obtain ⟨x, y, hxy⟩ := hδ' s hs
    exact (kronecker_mul_mem_localSectionDomain_iff a b u₀ x y (f s)).mp (hball hxy)
  · refine Metric.continuousAt_iff.mpr fun ε hε ↦ ?_
    obtain ⟨η, hη, hση⟩ := Metric.continuousAt_iff.mp hσ ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hback η hη
    refine ⟨δ, hδ, fun s hs ↦ ?_⟩
    obtain ⟨x, y, hxy⟩ := hδ' s hs
    have := hση hxy
    rwa [localSection_kronecker_mul] at this

omit hapos hab hbc in
/-- A path continuous modulo local unitaries on `[0, 1]`, extended to `ℝ` by
projection, stays continuous modulo local unitaries. -/
private theorem continuous_mod_projIcc {u : unitInterval → Matrix (m × n) (m × n) ℂ}
    (hcont : ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, dist q p < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖u q - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p‖ < ε) :
    ∀ t, ∀ ε > 0, ∃ δ > 0, ∀ s, dist s t < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖u (projIcc 0 1 zero_le_one s) -
          ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u (projIcc 0 1 zero_le_one t)‖ < ε := by
  intro t ε hε
  obtain ⟨δ, hδ, h⟩ := hcont (projIcc 0 1 zero_le_one t) ε hε
  refine ⟨δ, hδ, fun s hs ↦ h _ ?_⟩
  have := (LipschitzWith.projIcc (zero_le_one' ℝ)).dist_le_mul s t
  simp only [NNReal.coe_one, one_mul] at this
  exact this.trans_lt hs

/-- The path lifting theorem for fixed cutoffs `0 < a < b < |m| |n|`. -/
private theorem exists_continuous_lift_aux
    (u : unitInterval → Matrix (m × n) (m × n) ℂ) (hu : ∀ p, u p ∈ unitaryGroup (m × n) ℂ)
    (hcont : ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, dist q p < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖u q - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p‖ < ε) :
    ∃ û : unitInterval → Matrix (m × n) (m × n) ℂ, Continuous û ∧
      ∀ p, ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        û p = ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p := by
  let := localUnitaryAction (m := m) (n := n)
  have : ContinuousConstSMul (unitary (Matrix m m ℂ) × unitary (Matrix n n ℂ))
      (Matrix (m × n) (m × n) ℂ) := ⟨fun g ↦ continuous_const.mul continuous_id⟩
  set f : ℝ → Matrix (m × n) (m × n) ℂ := fun t ↦ u (projIcc 0 1 zero_le_one t) with hfdef
  have hf := continuous_mod_projIcc hcont
  have hloc : ∀ p ∈ Icc (0 : ℝ) 1, ∃ U ∈ 𝓝 p, ∃ L : ℝ → Matrix (m × n) (m × n) ℂ,
      ContinuousOn L U ∧ ∀ q ∈ U, ∃ g : unitary (Matrix m m ℂ) × unitary (Matrix n n ℂ),
        L q = g • f q := by
    intro p _
    have hp : f p ∈ localSectionDomain a b (f p) := by
      have := kronecker_mul_mem_localSectionDomain (u₀ := f p) 1 1 hapos hab hbc (hu _)
      simpa only [OneMemClass.coe_one, one_kronecker_one, Matrix.one_mul] using this
    let U := {q | f q ∈ localSectionDomain a b (f p)}
    have hUopen : IsOpen U := isOpen_iff_mem_nhds.mpr fun q hq ↦
      (eventually_mem_and_continuousAt hf hq).1
    refine ⟨U, hUopen.mem_nhds hp, fun q ↦ localSection a b (f p) (f q), fun q hq ↦
      (eventually_mem_and_continuousAt hf hq).2.continuousWithinAt,
      fun q hq ↦ ?_⟩
    obtain ⟨x, y, hxy⟩ := exists_localSection_eq_kronecker_mul a b (f p) hapos hab hq
    exact ⟨(x, y), hxy⟩
  obtain ⟨L, hL, hLf⟩ := exists_continuousOn_Icc_lift hloc
  refine ⟨fun p ↦ L p, hL.comp_continuous continuous_subtype_val fun p ↦ p.2, fun p ↦ ?_⟩
  obtain ⟨g, hg⟩ := hLf p p.2
  refine ⟨g.1, g.2, ?_⟩
  change L p = ((g.1 : Matrix m m ℂ) ⊗ₖ (g.2 : Matrix n n ℂ)) * u p
  rw [hg]
  change ((g.1 : Matrix m m ℂ) ⊗ₖ (g.2 : Matrix n n ℂ)) *
    u (projIcc 0 1 zero_le_one (p : ℝ)) = _
  rw [projIcc_val]

omit hapos hab hbc in
/-- **Lifting paths continuous modulo local unitaries.** Let `u : [0, 1] → U(ℓ r)`
be continuous modulo the local unitaries: for every `p` and `ε > 0` there is
`δ > 0` such that for `|q - p| < δ` some unitaries `x` and `y` give
`‖u(q) - (x ⊗ y) u(p)‖ < ε`. Then some continuous `û` on `[0, 1]` has
`û(p) = (x ⊗ y) u(p)` for unitaries `x`, `y` depending on `p`. Nothing is assumed
about the regularity of `u` itself.

Source: arXiv:1703.09188, proof of Corollary `coruvSF`, lines 942--947, where this
step is obtained from the slice theorem of Montgomery and Yang; here it follows
from the direct cross-section construction of this file and its imports (see the module
documentation). -/
theorem exists_continuous_lift_of_continuous_mod_localUnitary
    (u : unitInterval → Matrix (m × n) (m × n) ℂ) (hu : ∀ p, u p ∈ unitaryGroup (m × n) ℂ)
    (hcont : ∀ p, ∀ ε > 0, ∃ δ > 0, ∀ q, dist q p < δ →
      ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        ‖u q - ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p‖ < ε) :
    ∃ û : unitInterval → Matrix (m × n) (m × n) ℂ, Continuous û ∧
      ∀ p, ∃ (x : unitary (Matrix m m ℂ)) (y : unitary (Matrix n n ℂ)),
        û p = ((x : Matrix m m ℂ) ⊗ₖ (y : Matrix n n ℂ)) * u p := by
  rcases isEmpty_or_nonempty (m × n) with hmn | hmn
  · exact ⟨u, continuous_of_const fun _ _ ↦ Subsingleton.elim _ _,
      fun p ↦ ⟨1, 1, Subsingleton.elim _ _⟩⟩
  have hc : (0 : ℝ) < Fintype.card m * Fintype.card n := by
    have := Fintype.card_pos (α := m × n)
    rw [Fintype.card_prod] at this
    exact_mod_cast this
  exact exists_continuous_lift_aux (a := (Fintype.card m * Fintype.card n : ℝ) / 3)
    (b := 2 * (Fintype.card m * Fintype.card n : ℝ) / 3) (by positivity) (by linarith)
    (by linarith) u hu hcont

end Matrix

end KroneckerPathLifting
