/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Norm.NeumannInverse
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Basic

/-!
# Range projectors of injective finite-dimensional maps

For an injective map \(T\) with finite-dimensional Hilbert domain and complete
Hilbert codomain, this file develops the inverse Gram operator
\((T^\dagger T)^{-1}\), identifies it with the canonical and ring inverses, and
records the range-projector formula
\[
  P_{\operatorname{ran} T}=T(T^\dagger T)^{-1}T^\dagger.
\]
It also derives the quantitative bound
\(\lVert(T^\dagger T)^{-1}\rVert\le(1-a)^{-1}\) from
\(\lVert 1-T^\dagger T\rVert\le a<1\),
and the exact norm identities
\(\lVert T(T^\dagger T)^{-1}\rVert
= \sqrt{\lVert(T^\dagger T)^{-1}\rVert}\)
and
\(\lVert(T^\dagger T)^{-1} T^\dagger\rVert
= \sqrt{\lVert(T^\dagger T)^{-1}\rVert}\).
For a continuous family of injective maps out of a fixed finite-dimensional Hilbert space, the
orthogonal projections onto their ranges vary continuously, by continuity of inversion at units
of a Banach algebra (`ContinuousLinearMap.continuous_injectiveRangeProjector`). The continuity
results were moved from TNLean, `TNLean/Algebra/InjectiveRangeProjectorContinuity.lean` at commit
`49b78ed821` (Apache-2.0).

Moved from TNLean, `TNLean/MPS/ParentHamiltonian/BulkObservable/GroundSpaceCompressionNorm.lean`,
`TNLean/MPS/ParentHamiltonian/BulkObservable/GroundSpaceCrossCompressionNorm.lean` at commit
`021ba0bd19` (Apache-2.0).
-/


namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The continuous inverse of the Gram endomorphism of an injective
finite-dimensional continuous linear map. -/
noncomputable def inverseGram (T : E →L[𝕜] F) (hT : Function.Injective T) : E →L[𝕜] E :=
  LinearMap.toContinuousLinearMap <|
    (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
      ((T.adjoint_comp_self_injective_iff).2 hT)).symm.toLinearMap

/-- The inverse Gram operator is a left inverse of the Gram operator. -/
@[simp]
theorem inverseGram_comp_adjoint_comp_self (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    (inverseGram T hT).comp (T.adjoint.comp T) = ContinuousLinearMap.id 𝕜 E := by
  ext x
  exact (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
    ((T.adjoint_comp_self_injective_iff).2 hT)).symm_apply_apply x

/-- The inverse Gram operator is a right inverse of the Gram operator. -/
@[simp]
theorem adjoint_comp_self_comp_inverseGram (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    (T.adjoint.comp T).comp (inverseGram T hT) = ContinuousLinearMap.id 𝕜 E := by
  ext x
  exact (LinearEquiv.ofInjectiveEndo (T.adjoint.comp T).toLinearMap
    ((T.adjoint_comp_self_injective_iff).2 hT)).apply_symm_apply x

/-- The inverse Gram operator agrees with the inverse operation on continuous linear maps. -/
theorem inverseGram_eq_inverse (T : E →L[𝕜] F) (hT : Function.Injective T) :
    inverseGram T hT = (T.adjoint.comp T).inverse := by
  symm
  exact ContinuousLinearMap.inverse_eq
    (adjoint_comp_self_comp_inverseGram T hT)
    (inverseGram_comp_adjoint_comp_self T hT)

/-- The inverse Gram operator agrees with the ring-theoretic inverse. -/
theorem inverseGram_eq_ringInverse (T : E →L[𝕜] F) (hT : Function.Injective T) :
    inverseGram T hT = Ring.inverse (T.adjoint.comp T) := by
  rw [ContinuousLinearMap.ringInverse_eq_inverse]
  exact inverseGram_eq_inverse T hT

/-- If the Gram operator is within norm \(a<1\) of the identity, then its inverse
has norm at most \((1-a)^{-1}\). The denominator is the Neumann inverse bound. -/
theorem norm_inverseGram_le_of_norm_one_sub_adjoint_comp_self_le
    (T : E →L[𝕜] F) (hT : Function.Injective T) {a : ℝ}
    (ha : ‖1 - T.adjoint.comp T‖ ≤ a) (ha_lt_one : a < 1) :
    ‖inverseGram T hT‖ ≤ (1 - a)⁻¹ := by
  cases subsingleton_or_nontrivial E with
  | inl hE =>
      let : Subsingleton E := hE
      have hzero : inverseGram T hT = 0 := Subsingleton.elim _ _
      rw [hzero, norm_zero]
      exact inv_nonneg.mpr (sub_nonneg.mpr ha_lt_one.le)
  | inr hE =>
      let : Nontrivial E := hE
      rw [inverseGram_eq_ringInverse]
      simpa only [sub_sub_cancel] using
        NormedRing.norm_inverse_one_sub_le (1 - T.adjoint.comp T) ha ha_lt_one

/-- The inverse Gram operator is symmetric (and hence self-adjoint). -/
theorem inverseGram_isSymmetric (T : E →L[𝕜] F) (hT : Function.Injective T) :
    ((inverseGram T hT : E →L[𝕜] E) : E →ₗ[𝕜] E).IsSymmetric := by
  have h_gram_adj : (T.adjoint.comp T).adjoint = T.adjoint.comp T := by
    simp [adjoint_comp, adjoint_adjoint]
  have h_right_inv : (T.adjoint.comp T).comp (inverseGram T hT) =
      ContinuousLinearMap.id 𝕜 E := adjoint_comp_self_comp_inverseGram T hT
  intro x y
  calc
    inner 𝕜 ((inverseGram T hT) x) y =
        inner 𝕜 ((inverseGram T hT) x)
          (((T.adjoint.comp T).comp (inverseGram T hT)) y) := by
      rw [h_right_inv, ContinuousLinearMap.id_apply]
    _ = inner 𝕜 ((inverseGram T hT) x)
        ((T.adjoint.comp T) ((inverseGram T hT) y)) := rfl
    _ = inner 𝕜 ((T.adjoint.comp T).adjoint ((inverseGram T hT) x))
        ((inverseGram T hT) y) := by rw [adjoint_inner_left]
    _ = inner 𝕜 ((T.adjoint.comp T) ((inverseGram T hT) x))
        ((inverseGram T hT) y) := by rw [h_gram_adj]
    _ = inner 𝕜 x ((inverseGram T hT) y) := by
      have hx : (T.adjoint.comp T) ((inverseGram T hT) x) = x :=
        calc
          (T.adjoint.comp T) ((inverseGram T hT) x) =
              ((T.adjoint.comp T).comp (inverseGram T hT)) x := rfl
          _ = x := by rw [h_right_inv, ContinuousLinearMap.id_apply]
      rw [hx]

/-- The norm identity
\(\lVert T \circ (T^\dagger T)^{-1}\rVert = \sqrt{\lVert(T^\dagger T)^{-1}\rVert}\)
for an injective map \(T\) with finite-dimensional domain. -/
theorem norm_T_comp_inverseGram_eq_sqrt (T : E →L[𝕜] F) (hT : Function.Injective T) :
    ‖T.comp (inverseGram T hT)‖ = Real.sqrt ‖inverseGram T hT‖ := by
  have h_sa_adj : (inverseGram T hT).adjoint = inverseGram T hT :=
    (inverseGram_isSymmetric T hT).clm_adjoint_eq
  set S := T.comp (inverseGram T hT)
  have hS_adj : S.adjoint = (inverseGram T hT).adjoint.comp T.adjoint :=
    adjoint_comp _ _
  have h_sq : ‖S‖ ^ 2 = ‖inverseGram T hT‖ := by
    calc
      ‖S‖ ^ 2 = ‖S‖ * ‖S‖ := by ring
      _ = ‖S.adjoint.comp S‖ := by rw [norm_adjoint_comp_self S]
      _ = ‖(((inverseGram T hT).adjoint).comp T.adjoint).comp S‖ := by rw [hS_adj]
      _ = ‖((inverseGram T hT).comp T.adjoint).comp
            (T.comp (inverseGram T hT))‖ := by rw [h_sa_adj]
      _ = ‖(inverseGram T hT).comp
            ((T.adjoint.comp T).comp (inverseGram T hT))‖ := by
        simp [ContinuousLinearMap.comp_assoc]
      _ = ‖(inverseGram T hT).comp (ContinuousLinearMap.id 𝕜 E)‖ := by
        rw [adjoint_comp_self_comp_inverseGram T hT]
      _ = ‖inverseGram T hT‖ := by simp
  have h_nonneg : 0 ≤ ‖S‖ := norm_nonneg _
  calc
    ‖S‖ = Real.sqrt (‖S‖ ^ 2) := by rw [Real.sqrt_sq h_nonneg]
    _ = Real.sqrt ‖inverseGram T hT‖ := by rw [h_sq]

/-- The norm identity
\(\lVert(T^\dagger T)^{-1} \circ T^\dagger\rVert = \sqrt{\lVert(T^\dagger T)^{-1}\rVert}\)
for an injective map \(T\) with finite-dimensional domain. -/
theorem norm_inverseGram_comp_adjoint_eq_sqrt (T : E →L[𝕜] F) (hT : Function.Injective T) :
    ‖(inverseGram T hT).comp T.adjoint‖ = Real.sqrt ‖inverseGram T hT‖ := by
  have h_sa_adj : (inverseGram T hT).adjoint = inverseGram T hT :=
    (inverseGram_isSymmetric T hT).clm_adjoint_eq
  calc
    ‖(inverseGram T hT).comp T.adjoint‖ =
        ‖(T.comp (inverseGram T hT)).adjoint‖ := by
      simp [adjoint_comp, h_sa_adj]
    _ = ‖T.comp (inverseGram T hT)‖ :=
      LinearIsometryEquiv.norm_map (adjoint (𝕜 := 𝕜) (E := E) (F := F)) _
    _ = Real.sqrt ‖inverseGram T hT‖ := norm_T_comp_inverseGram_eq_sqrt T hT

/-- The continuous range projector written through the inverse Gram operator. -/
noncomputable def injectiveRangeProjector (T : E →L[𝕜] F)
    (hT : Function.Injective T) : F →L[𝕜] F :=
  T.comp ((inverseGram T hT).comp T.adjoint)

/-- The continuous inverse-Gram formula is exactly the orthogonal projector
onto the range of an injective finite-dimensional map. -/
theorem injectiveRangeProjector_eq_starProjection (T : E →L[𝕜] F)
    (hT : Function.Injective T) :
    injectiveRangeProjector T hT = T.range.starProjection := by
  ext x
  symm
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact ⟨inverseGram T hT (T.adjoint x), rfl⟩
  · rw [Submodule.mem_orthogonal']
    intro _ hy
    obtain ⟨y, rfl⟩ := hy
    change inner 𝕜 (x - injectiveRangeProjector T hT x) (T y) = 0
    rw [← T.adjoint_inner_left y (x - injectiveRangeProjector T hT x)]
    suffices T.adjoint (x - injectiveRangeProjector T hT x) = 0 by rw [this, inner_zero_left]
    rw [map_sub, injectiveRangeProjector, comp_apply, comp_apply]
    change T.adjoint x - (T.adjoint.comp T)
      (inverseGram T hT (T.adjoint x)) = 0
    have hGram :
        (T.adjoint.comp T) (inverseGram T hT (T.adjoint x)) = T.adjoint x := by
      change ((T.adjoint.comp T).comp (inverseGram T hT)) (T.adjoint x) = T.adjoint x
      rw [adjoint_comp_self_comp_inverseGram]
      rfl
    rw [hGram, sub_self]

/-- Exact residual identity for three injective maps with a common factorization.
If \(C=T\circ J₁=L\circ J₂\), the difference of the range projectors of \(T\) and \(L\),
after composition, factors through the mixed-Gram residual
\[
  T^†L-(T^†T)J₁(C^†C)^{-1}J₂^†(L^†L).
\]
This identity is purely algebraic and does not assert a norm bound. -/
theorem injectiveRangeProjector_comp_sub_of_factorizations
    {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G]
      [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]
      [CompleteSpace H]
    (T : E →L[𝕜] F) (L : G →L[𝕜] F) (C : H →L[𝕜] F)
    (J₁ : H →L[𝕜] E) (J₂ : H →L[𝕜] G)
    (hT : Function.Injective T) (hL : Function.Injective L)
    (hC : Function.Injective C)
    (hTC : T.comp J₁ = C) (hLC : L.comp J₂ = C) :
    (injectiveRangeProjector T hT).comp (injectiveRangeProjector L hL) -
        injectiveRangeProjector C hC =
      T.comp ((inverseGram T hT).comp
        ((T.adjoint.comp L -
          (T.adjoint.comp T).comp (J₁.comp ((inverseGram C hC).comp
            (J₂.adjoint.comp (L.adjoint.comp L))))).comp
          ((inverseGram L hL).comp L.adjoint))) := by
  have hLCadj : J₂.adjoint.comp L.adjoint = C.adjoint := by
    rw [← ContinuousLinearMap.adjoint_comp, hLC]
  have hTGram (x : E) :
      inverseGram T hT (T.adjoint (T x)) = x := by
    exact congrArg (fun Q : E →L[𝕜] E => Q x)
      (inverseGram_comp_adjoint_comp_self T hT)
  have hLGram (x : G) :
      L.adjoint (L (inverseGram L hL x)) = x := by
    exact congrArg (fun Q : G →L[𝕜] G => Q x)
      (adjoint_comp_self_comp_inverseGram L hL)
  have hsecond :
      T.comp ((inverseGram T hT).comp
        (((T.adjoint.comp T).comp (J₁.comp ((inverseGram C hC).comp
          (J₂.adjoint.comp (L.adjoint.comp L))))).comp
            ((inverseGram L hL).comp L.adjoint))) =
        C.comp ((inverseGram C hC).comp C.adjoint) := by
    ext x
    simp only [comp_apply, hTGram, hLGram]
    rw [show J₂.adjoint (L.adjoint x) = C.adjoint x by
      exact congrArg (fun Q : F →L[𝕜] H => Q x) hLCadj]
    exact congrArg (fun Q : H →L[𝕜] F =>
      Q (inverseGram C hC (C.adjoint x))) hTC
  rw [injectiveRangeProjector, injectiveRangeProjector, injectiveRangeProjector]
  simp only [comp_sub, sub_comp]
  rw [hsecond]
  simp only [comp_assoc]

/-! ### Continuity of range projectors -/

/-- A family of maps out of a finite coordinate Hilbert space is continuous
when its values on every coordinate vector are continuous. -/
theorem continuous_of_euclideanSingle
    {X F ι : Type*} [TopologicalSpace X] [Finite ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : X → EuclideanSpace ℂ ι →L[ℂ] F)
    (h : ∀ i, Continuous fun x => T x (EuclideanSpace.single i 1)) :
    Continuous T := by
  have := Fintype.ofFinite ι
  refine continuous_clm_apply.2 fun y => ?_
  have hy : (fun x => T x y) =
      fun x => ∑ i, y i • T x (EuclideanSpace.single i 1) := by
    funext x
    conv_lhs => rw [← (EuclideanSpace.basisFun ι ℂ).sum_repr y]
    simp [map_sum, map_smul]
  rw [hy]
  exact continuous_finsetSum _ fun i _ => (h i).const_smul _

/-- At an injective finite-dimensional map, the orthogonal range projector is
continuous even if nearby maps have not been supplied with injectivity proofs.
Injectivity persists in a neighborhood by openness. -/
theorem continuousAt_range_starProjection_of_injective
    {X 𝕜 E F : Type*} [TopologicalSpace X] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : X → E →L[𝕜] F) {x₀ : X} (hT : ContinuousAt T x₀)
    (hInj : Function.Injective (T x₀)) :
    ContinuousAt (fun x => (T x).range.starProjection) x₀ := by
  have hAdj : ContinuousAt (fun x => (T x).adjoint) x₀ :=
    ContinuousLinearMap.adjoint.continuous.continuousAt.comp hT
  have hGram := hAdj.clm_comp hT
  let u : (E →L[𝕜] E)ˣ :=
    ⟨(T x₀).adjoint.comp (T x₀), inverseGram (T x₀) hInj,
      adjoint_comp_self_comp_inverseGram (T x₀) hInj,
      inverseGram_comp_adjoint_comp_self (T x₀) hInj⟩
  have hInv : ContinuousAt (fun x => Ring.inverse ((T x).adjoint.comp (T x))) x₀ :=
    (NormedRing.inverse_continuousAt u).comp'
      (f := fun x => (T x).adjoint.comp (T x)) hGram
  have hProj := hT.clm_comp (hInv.clm_comp hAdj)
  have hEv : ∀ᶠ x in nhds x₀, Function.Injective (T x) :=
    hT.eventually (ContinuousLinearMap.isOpen_injective.mem_nhds hInj)
  apply hProj.congr_of_eventuallyEq
  filter_upwards [hEv] with x hx
  rw [← injectiveRangeProjector_eq_starProjection (T x) hx]
  simp only [injectiveRangeProjector, inverseGram_eq_ringInverse]

/-- The orthogonal range projector of a continuous family of injective
finite-dimensional maps depends continuously on the parameter. -/
theorem continuous_injectiveRangeProjector
    {X 𝕜 E F : Type*} [TopologicalSpace X] [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (T : X → E →L[𝕜] F) (hT : Continuous T)
    (hInj : ∀ x, Function.Injective (T x)) :
    Continuous fun x => injectiveRangeProjector (T x) (hInj x) := by
  have hRange : Continuous fun x => (T x).range.starProjection :=
    continuous_iff_continuousAt.mpr fun x =>
      continuousAt_range_starProjection_of_injective T hT.continuousAt (hInj x)
  convert hRange using 1
  funext x
  exact injectiveRangeProjector_eq_starProjection (T x) (hInj x)

end ContinuousLinearMap

section

open Filter

open scoped Topology InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- Compression to the range of an injective map is controlled by the inverse Gram operator
and the pullback of the compressed operator. -/
theorem norm_starProjection_comp_le_inverseGram (T : E →L[𝕜] F)
    (hT : Function.Injective T) (X : F →L[𝕜] F) :
    ‖T.range.starProjection.comp (X.comp T.range.starProjection)‖ ≤
      ‖inverseGram T hT‖ * ‖T.adjoint.comp (X.comp T)‖ := by
  rw [← injectiveRangeProjector_eq_starProjection T hT]
  change ‖(T.comp (inverseGram T hT)).comp
    ((T.adjoint.comp (X.comp T)).comp ((inverseGram T hT).comp T.adjoint))‖ ≤ _
  refine le_trans (opNorm_comp_le _ _) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _)) ?_
  rw [norm_T_comp_inverseGram_eq_sqrt, norm_inverseGram_comp_adjoint_eq_sqrt,
    ← mul_assoc, mul_right_comm (Real.sqrt ‖inverseGram T hT‖),
    Real.mul_self_sqrt (norm_nonneg _)]

/-- The defect of scalar compression is controlled by the corresponding defect of the pulled
back operator relative to the Gram operator. -/
theorem norm_starProjection_comp_sub_smul_le_inverseGram (T : E →L[𝕜] F)
    (hT : Function.Injective T) (X : F →L[𝕜] F) (c : 𝕜) :
    ‖T.range.starProjection.comp (X.comp T.range.starProjection) -
        c • T.range.starProjection‖ ≤
      ‖inverseGram T hT‖ * ‖T.adjoint.comp (X.comp T) - c • (T.adjoint.comp T)‖ := by
  have h := norm_starProjection_comp_le_inverseGram T hT (X - c • ContinuousLinearMap.id 𝕜 F)
  simpa only [sub_comp, comp_sub, smul_comp, comp_smul, id_comp,
    Submodule.starProjection_comp_starProjection_of_le le_rfl] using h

/-- Eventual injectivity and a bound for the inverse Gram operators transfer
convergence of scalar pullback defects to convergence of the compressed operators.
The Hilbert spaces may vary with the index, and the filter is arbitrary. -/
theorem tendsto_starProjection_comp_sub_smul_zero_of_inverseGram_bound
    {ι : Type*} {l : Filter ι} {𝕜 : Type*} [RCLike 𝕜]
    {E F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
    [∀ i, CompleteSpace (F i)]
    (T : (i : ι) → E i →L[𝕜] F i)
    (X : (i : ι) → F i →L[𝕜] F i) (c : ι → 𝕜) {C : ℝ}
    (hBound : ∀ᶠ i in l, ∃ hT : Function.Injective (T i),
      ‖inverseGram (T i) hT‖ ≤ C)
    (hDefect : Tendsto (fun i =>
      ‖(T i).adjoint.comp ((X i).comp (T i)) -
        c i • ((T i).adjoint.comp (T i))‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖(T i).range.starProjection.comp ((X i).comp (T i).range.starProjection) -
        c i • (T i).range.starProjection‖) l (𝓝 0) := by
  have hUpper : Tendsto (fun i => C *
      ‖(T i).adjoint.comp ((X i).comp (T i)) -
        c i • ((T i).adjoint.comp (T i))‖) l (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hDefect
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hUpper
  filter_upwards [hBound] with i hi
  obtain ⟨hT, hi⟩ := hi
  exact (norm_starProjection_comp_sub_smul_le_inverseGram (T i) hT (X i) (c i)).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg _))

omit [CompleteSpace E] in
/-- Compression controls the action of an observable on a unit ground vector. -/
theorem norm_starProjection_apply_sub_smul_le_compression
    (G : Submodule 𝕜 E) (X : E →L[𝕜] E) (c : 𝕜)
    (v : E) (hv : v ∈ G) (hUnit : ‖v‖ = 1) :
    ‖G.starProjection (X v) - c • v‖ ≤
      ‖G.starProjection.comp (X.comp G.starProjection) - c • G.starProjection‖ := by
  simpa only [sub_apply, ContinuousLinearMap.comp_apply,
    smul_apply, G.starProjection_eq_self_iff.mpr hv, hUnit, mul_one] using
      (G.starProjection.comp (X.comp G.starProjection) - c • G.starProjection).le_opNorm v

omit [CompleteSpace E] in
/-- Scalar compression bounds the deviation of the expectation on a unit vector. -/
theorem norm_inner_sub_scalar_le_compression
    (G : Submodule 𝕜 E) (X : E →L[𝕜] E) (c : 𝕜)
    (v : E) (hv : v ∈ G) (hUnit : ‖v‖ = 1) :
    ‖⟪v, X v⟫_𝕜 - c‖ ≤
      ‖G.starProjection.comp (X.comp G.starProjection) - c • G.starProjection‖ := by
  have hInner : ⟪v, G.starProjection (X v) - c • v⟫_𝕜 = ⟪v, X v⟫_𝕜 - c := by
    simp only [inner_sub_right, inner_smul_right,
      ← G.inner_starProjection_left_eq_right, G.starProjection_eq_self_iff.mpr hv,
      inner_self_eq_norm_sq_to_K, hUnit, RCLike.ofReal_one, one_pow, mul_one]
  have hBound : ‖⟪v, X v⟫_𝕜 - c‖ ≤ ‖G.starProjection (X v) - c • v‖ := by
    simpa only [hInner, hUnit, one_mul] using
      norm_inner_le_norm (𝕜 := 𝕜) v (G.starProjection (X v) - c • v)
  exact hBound.trans (norm_starProjection_apply_sub_smul_le_compression G X c v hv hUnit)

end ContinuousLinearMap

end

section

open Filter

open scoped Topology

namespace ContinuousLinearMap

variable {𝕜 E G F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [FiniteDimensional 𝕜 G] [CompleteSpace G]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- The compression between two injective ranges is controlled by their inverse
Gram operators and the rectangular pullback of the observable. -/
theorem norm_starProjection_comp_starProjection_le_inverseGram
    (T : E →L[𝕜] F) (S : G →L[𝕜] F)
    (hT : Function.Injective T) (hS : Function.Injective S) (X : F →L[𝕜] F) :
    ‖T.range.starProjection.comp (X.comp S.range.starProjection)‖ ≤
      Real.sqrt ‖inverseGram T hT‖ * ‖T.adjoint.comp (X.comp S)‖ *
        Real.sqrt ‖inverseGram S hS‖ := by
  rw [← injectiveRangeProjector_eq_starProjection T hT,
    ← injectiveRangeProjector_eq_starProjection S hS]
  change ‖(T.comp (inverseGram T hT)).comp
    ((T.adjoint.comp (X.comp S)).comp ((inverseGram S hS).comp S.adjoint))‖ ≤ _
  refine le_trans (opNorm_comp_le _ _) ?_
  refine le_trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _)) ?_
  rw [norm_T_comp_inverseGram_eq_sqrt, norm_inverseGram_comp_adjoint_eq_sqrt, mul_assoc]

/-- Eventual inverse Gram bounds transfer decay of the rectangular pullback
to operator-norm decay of the cross compression. The Hilbert spaces may vary
with the index and the filter is arbitrary. -/
theorem tendsto_starProjection_comp_starProjection_zero_of_inverseGram_bounds
    {ι : Type*} {l : Filter ι} {𝕜 : Type*} [RCLike 𝕜]
    {E G F : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
    [∀ i, FiniteDimensional 𝕜 (E i)] [∀ i, CompleteSpace (E i)]
    [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]
    [∀ i, FiniteDimensional 𝕜 (G i)] [∀ i, CompleteSpace (G i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
    [∀ i, CompleteSpace (F i)]
    (T : (i : ι) → E i →L[𝕜] F i) (S : (i : ι) → G i →L[𝕜] F i)
    (X : (i : ι) → F i →L[𝕜] F i) {C D : ℝ}
    (hT : ∀ᶠ i in l, ∃ hInj : Function.Injective (T i), ‖inverseGram (T i) hInj‖ ≤ C)
    (hS : ∀ᶠ i in l, ∃ hInj : Function.Injective (S i), ‖inverseGram (S i) hInj‖ ≤ D)
    (hCross : Tendsto (fun i => ‖(T i).adjoint.comp ((X i).comp (S i))‖) l (𝓝 0)) :
    Tendsto (fun i =>
      ‖(T i).range.starProjection.comp ((X i).comp (S i).range.starProjection)‖) l (𝓝 0) := by
  have hUpper : Tendsto (fun i => Real.sqrt C *
      ‖(T i).adjoint.comp ((X i).comp (S i))‖ * Real.sqrt D) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      ((tendsto_const_nhds (x := Real.sqrt C)).mul hCross).mul_const (Real.sqrt D)
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hUpper
  filter_upwards [hT, hS] with i hiT hiS
  obtain ⟨hInjT, hiT⟩ := hiT
  obtain ⟨hInjS, hiS⟩ := hiS
  refine (norm_starProjection_comp_starProjection_le_inverseGram
    (T i) (S i) hInjT hInjS (X i)).trans ?_
  gcongr

end ContinuousLinearMap

end
