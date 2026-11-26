/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.NormNum

/-!
# Operators applied independently on the fibers of a finite product

A Euclidean vector indexed by `I × S`, for a finite spectator set `S`, is a family of vectors
indexed by `I`, its fibers `x (·, s)`. An operator `G` from `ℓ²(I)` to `ℓ²(J)` applied to every
fiber gives an operator from `ℓ²(I × S)` to `ℓ²(J × S)`, the operator `G ⊗ 1_S`. This extension
preserves sums, scalar multiples, composition, adjoints, symmetry, positivity, operator order and
orthogonal projections; its kernel and range consist of the families whose fibers lie in the
kernel and range of `G`; its range projection is the extension of the range projection of `G`;
and its operator norm is at most that of `G`, with equality for a nonempty spectator set. Inner
products and squared norms split as sums over the fibers. Empty coordinate sets are allowed
throughout.

Finite spectator coordinates of this kind appear in the projection estimates of Nachtergaele,
arXiv:cond-mat/9410110, Lemma `commutation`, lines 2442--2531.

Moved from TNLean (Apache-2.0) at commit `49b78ed821`: the definitions and lemmas of
`TNLean/MPS/ParentHamiltonian/Martingale/SpectatorMaps.lean`, the declarations of
`TNLean/MPS/ParentHamiltonian/Martingale/SpectatorOrder.lean`, and the fiber lemmas of
`TNLean/MPS/ParentHamiltonian/Martingale/SpectatorGapEquivalence.lean`, merged with
`TNLean/Algebra/EuclideanFiberwiseMap.lean` and `TNLean/Algebra/EuclideanFiberwiseProjection.lean`.
Changes: TNLean had two definitions of this operator, `ContinuousLinearMap.rightFiberwiseMap`
(spectator on the right, one coordinate set `I`) and `EuclideanSpace.fiberwiseMap` (spectator on
the left, source `I` and target `J`). They are merged into `ContinuousLinearMap.rightFiberwiseMap`
with source `I` and target `J`; the results stated for `EuclideanSpace.fiberwiseMap` are restated
for it, and the scalar field is `ℂ`.

## Main definitions

* `ContinuousLinearMap.rightFiber` — the fiber `x (·, s)` of a vector on `I × S`.
* `ContinuousLinearMap.rightFiberwiseMap` — an operator applied independently on every fiber.
* `ContinuousLinearMap.singleRightFiber` — a vector supported on one fiber.

## Main results

* `ContinuousLinearMap.rightFiberwiseMap_comp`, `ContinuousLinearMap.rightFiberwiseMap_adjoint` —
  composition and adjoints.
* `ContinuousLinearMap.inner_eq_sum_inner_rightFiber`,
  `ContinuousLinearMap.norm_sq_eq_sum_norm_sq_rightFiber` — inner products and norms split over
  the fibers.
* `ContinuousLinearMap.norm_rightFiberwiseMap_le`, `ContinuousLinearMap.norm_rightFiberwiseMap`
  — the operator norm.
* `ContinuousLinearMap.isPositive_rightFiberwiseMap`, `ContinuousLinearMap.rightFiberwiseMap_mono`
  — positivity and order; `LinearIsometryEquiv.conj_le_conj_iff` — unitary conjugation preserves
  and reflects the order.
* `ContinuousLinearMap.ker_starProjection_rightFiberwiseMap`,
  `ContinuousLinearMap.rightFiberwiseMap_range_starProjection` — kernel and range projections.
* `ContinuousLinearMap.norm_sum_rightFiberwiseMap_range_starProjection_sub_iSup_le` — adding
  spectator coordinates does not increase the error between a sum of range projections and the
  projection onto their joint span.

Moved from TNLean,
`TNLean/MPS/Symmetry/MPOSymmetry/MixedPath/Gap/MixedEndpointCoreHamiltonianSpectators.lean` at
commit `021ba0bd19` (Apache-2.0).
-/

open scoped BigOperators ComplexOrder InnerProductSpace

namespace ContinuousLinearMap

variable {I J K S : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype S]

/-- The vector on `I` obtained by fixing the spectator coordinate `s`. -/
noncomputable def rightFiber (x : EuclideanSpace ℂ (I × S)) (s : S) :
    EuclideanSpace ℂ I :=
  WithLp.toLp 2 fun i => x (i, s)

omit [Fintype I] [Fintype S] in
/-- Coordinates of a fiber. -/
theorem rightFiber_apply (x : EuclideanSpace ℂ (I × S)) (s : S) (i : I) :
    rightFiber x s i = x (i, s) := rfl

/-- Apply the same operator independently at every value of a finite spectator coordinate on
the right. The source and target coordinate sets may differ. -/
noncomputable def rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    EuclideanSpace ℂ (I × S) →L[ℂ] EuclideanSpace ℂ (J × S) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun p => G (rightFiber x p.2) p.1
      map_add' := by
        intro x y
        apply PiLp.ext
        rintro ⟨j, s⟩
        change (G (rightFiber (x + y) s)) j = _
        rw [show rightFiber (x + y) s = rightFiber x s + rightFiber y s by
          apply PiLp.ext
          intro i
          rfl, map_add]
        rfl
      map_smul' := by
        intro c x
        apply PiLp.ext
        rintro ⟨j, s⟩
        change (G (rightFiber (c • x) s)) j = _
        rw [show rightFiber (c • x) s = c • rightFiber x s by
          apply PiLp.ext
          intro i
          rfl, map_smul]
        rfl }

/-- Fiberwise extension applies the base operator on the selected fiber. -/
@[simp] theorem rightFiberwiseMap_apply_apply
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (I × S)) (j : J) (s : S) :
    rightFiberwiseMap (S := S) G x (j, s) = G (rightFiber x s) j := rfl

/-- Taking a fiber after extension recovers the base operator on that fiber. -/
@[simp] theorem rightFiber_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (I × S)) (s : S) :
    rightFiber (rightFiberwiseMap (S := S) G x) s = G (rightFiber x s) := by
  apply PiLp.ext
  intro j
  rfl

/-- Fiberwise extension preserves addition. -/
theorem rightFiberwiseMap_add
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    rightFiberwiseMap (S := S) (G + H) =
      rightFiberwiseMap (S := S) G + rightFiberwiseMap (S := S) H := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

/-- Fiberwise extension preserves subtraction. -/
theorem rightFiberwiseMap_sub
    (G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    rightFiberwiseMap (S := S) (G - H) =
      rightFiberwiseMap (S := S) G - rightFiberwiseMap (S := S) H := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

/-- The fiberwise extension of the zero operator is zero. -/
@[simp] theorem rightFiberwiseMap_zero :
    rightFiberwiseMap (I := I) (J := J) (S := S) 0 = 0 := by
  apply ContinuousLinearMap.coe_injective
  ext x p
  rfl

/-- Fiberwise extension commutes with scalar multiplication of the base operator. -/
theorem rightFiberwiseMap_smul
    (c : ℂ) (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    rightFiberwiseMap (S := S) (c • G) = c • rightFiberwiseMap (S := S) G := by
  rfl

/-- Fiberwise extension preserves finite sums. -/
theorem rightFiberwiseMap_sum {ι : Type*} (s : Finset ι)
    (G : ι → EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    rightFiberwiseMap (S := S) (∑ i ∈ s, G i) =
      ∑ i ∈ s, rightFiberwiseMap (S := S) (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, rightFiberwiseMap_add, ih]

/-- Fiberwise extension preserves composition. -/
theorem rightFiberwiseMap_comp
    (G : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ K)
    (H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    (rightFiberwiseMap (S := S) G).comp (rightFiberwiseMap (S := S) H) =
      rightFiberwiseMap (S := S) (G.comp H) := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨k, s⟩
  rfl

/-- The fiberwise extension of the identity is the identity. -/
theorem rightFiberwiseMap_id :
    rightFiberwiseMap (S := S) (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ I)) =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (I × S)) := by
  rfl

/-- A vector lies in the kernel of a fiberwise operator exactly when every fiber lies in the
kernel of the base operator. -/
theorem mem_ker_rightFiberwiseMap_iff
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (I × S)) :
    x ∈ LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap ↔
      ∀ s, rightFiber x s ∈ LinearMap.ker G.toLinearMap := by
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx s
    apply PiLp.ext
    intro j
    have hj := congrArg (fun y : EuclideanSpace ℂ (J × S) => y (j, s)) hx
    exact hj
  · intro hx
    apply PiLp.ext
    rintro ⟨j, s⟩
    change G (rightFiber x s) j = 0
    exact congrArg (fun y : EuclideanSpace ℂ J => y j) (hx s)

/-! ### Inner products and norms -/

/-- The inner product is the sum of the inner products of the fibers. -/
theorem inner_eq_sum_inner_rightFiber (x y : EuclideanSpace ℂ (I × S)) :
    ⟪x, y⟫_ℂ = ∑ s, ⟪rightFiber x s, rightFiber y s⟫_ℂ := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [PiLp.inner_apply]
  rfl

/-- The squared norm is the sum of the squared norms of the fibers. -/
theorem norm_sq_eq_sum_norm_sq_rightFiber (x : EuclideanSpace ℂ (I × S)) :
    ‖x‖ ^ 2 = ∑ s, ‖rightFiber x s‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [EuclideanSpace.norm_sq_eq]
  rfl

/-- The quadratic form of a fiberwise operator is the sum of its quadratic forms on the fibers.
-/
theorem inner_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (I × S)) (y : EuclideanSpace ℂ (J × S)) :
    ⟪rightFiberwiseMap (S := S) G x, y⟫_ℂ =
      ∑ s : S, ⟪G (rightFiber x s), rightFiber y s⟫_ℂ := by
  simp only [inner_eq_sum_inner_rightFiber, rightFiber_rightFiberwiseMap]

/-- The adjoint of a fiberwise operator is the fiberwise extension of the adjoint. -/
theorem rightFiberwiseMap_adjoint
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    (rightFiberwiseMap (S := S) G).adjoint = rightFiberwiseMap (S := S) G.adjoint := by
  refine ContinuousLinearMap.ext fun y => ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, inner_eq_sum_inner_rightFiber,
    inner_eq_sum_inner_rightFiber]
  simp only [rightFiber_rightFiberwiseMap, ContinuousLinearMap.adjoint_inner_left]

/-- Fiberwise extension preserves symmetry. -/
theorem isSymmetric_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsSymmetric) :
    (rightFiberwiseMap (S := S) G).toLinearMap.IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, inner_eq_sum_inner_rightFiber,
    rightFiber_rightFiberwiseMap]
  exact Finset.sum_congr rfl fun s _ => hG (rightFiber x s) (rightFiber y s)

/-- Fiberwise extension preserves orthogonal projections. -/
theorem isSymmetricProjection_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsSymmetricProjection) :
    (rightFiberwiseMap (S := S) G).toLinearMap.IsSymmetricProjection := by
  refine ⟨?_, isSymmetric_rightFiberwiseMap G hG.isSymmetric⟩
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  rintro ⟨i, s⟩
  change G (G (rightFiber x s)) i = G (rightFiber x s) i
  have hs := LinearMap.congr_fun hG.isIdempotentElem.eq (rightFiber x s)
  exact congrArg (fun y : EuclideanSpace ℂ I => y i) hs

/-- Fiberwise extension preserves positivity. -/
theorem isPositive_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hG : G.toLinearMap.IsPositive) :
    (rightFiberwiseMap (S := S) G).toLinearMap.IsPositive := by
  refine ⟨isSymmetric_rightFiberwiseMap G hG.isSymmetric, fun x ↦ ?_⟩
  simpa only [ContinuousLinearMap.coe_coe, inner_rightFiberwiseMap, map_sum] using
    (Finset.sum_nonneg fun (s : S) (_ : s ∈ Finset.univ) ↦ hG.2 (rightFiber x s))

/-- Fiberwise extension preserves the order of operators. -/
theorem rightFiberwiseMap_mono
    {G H : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I}
    (h : G.toLinearMap ≤ H.toLinearMap) :
    (rightFiberwiseMap (S := S) G).toLinearMap ≤
      (rightFiberwiseMap (S := S) H).toLinearMap := by
  apply LinearMap.le_def.mpr
  simpa only [rightFiberwiseMap_sub, toLinearMap_sub] using
    (isPositive_rightFiberwiseMap (S := S) (H - G) h)

/-- Fiberwise extension does not increase the operator norm. The statement also covers an empty
spectator type. -/
theorem norm_rightFiberwiseMap_le
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    ‖rightFiberwiseMap (S := S) G‖ ≤ ‖G‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun x ↦ ?_
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg G) (norm_nonneg x)),
    mul_pow, norm_sq_eq_sum_norm_sq_rightFiber, norm_sq_eq_sum_norm_sq_rightFiber,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun s _ => ?_
  rw [rightFiber_rightFiberwiseMap, ← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg G) (norm_nonneg _))).mpr
    (G.le_opNorm _)

/-- A vector supported at one spectator coordinate. -/
noncomputable def singleRightFiber (s : S) (x : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × S) := by
  classical
  exact WithLp.toLp 2 fun p => if p.2 = s then x p.1 else 0

omit [Fintype I] [Fintype S] in
/-- Taking a fiber of a vector supported at one spectator coordinate gives the original vector
at that coordinate and zero elsewhere. -/
@[simp] theorem rightFiber_singleRightFiber [DecidableEq S]
    (s t : S) (x : EuclideanSpace ℂ I) :
    rightFiber (singleRightFiber s x) t = if t = s then x else 0 := by
  classical
  by_cases h : t = s <;> apply PiLp.ext <;> intro i <;>
    simp [rightFiber, singleRightFiber, h]

/-- A vector supported on one spectator fiber has the norm of that fiber. -/
theorem norm_singleRightFiber (s : S) (x : EuclideanSpace ℂ I) :
    ‖singleRightFiber s x‖ = ‖x‖ := by
  classical
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_sum_norm_sq_rightFiber,
    Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    simp [hts]
  · simp

/-- A fiberwise operator preserves support on a single spectator coordinate. -/
@[simp] theorem rightFiberwiseMap_singleRightFiber
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (s : S) (x : EuclideanSpace ℂ I) :
    rightFiberwiseMap (S := S) G (singleRightFiber s x) = singleRightFiber s (G x) := by
  classical
  apply PiLp.ext
  rintro ⟨j, t⟩
  rw [rightFiberwiseMap_apply_apply, rightFiber_singleRightFiber]
  by_cases h : t = s <;> simp [singleRightFiber, h]

/-- On a nonempty spectator space, fiberwise extension preserves the operator norm exactly. -/
theorem norm_rightFiberwiseMap [Nonempty S]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    ‖rightFiberwiseMap (S := S) G‖ = ‖G‖ := by
  apply le_antisymm (norm_rightFiberwiseMap_le G)
  let s : S := Classical.choice ‹Nonempty S›
  refine ContinuousLinearMap.opNorm_le_bound G (norm_nonneg _) fun x ↦ ?_
  calc
    ‖G x‖ = ‖rightFiberwiseMap (S := S) G (singleRightFiber s x)‖ := by
      rw [rightFiberwiseMap_singleRightFiber, norm_singleRightFiber]
    _ ≤ ‖rightFiberwiseMap (S := S) G‖ * ‖singleRightFiber s x‖ :=
      (rightFiberwiseMap (S := S) G).le_opNorm _
    _ = ‖rightFiberwiseMap (S := S) G‖ * ‖x‖ := by
      rw [norm_singleRightFiber]

/-- Conjugation by a surjective linear isometry preserves the operator norm. -/
theorem norm_conj_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ E] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (G : E →L[ℂ] E) :
    ‖U.toLinearIsometry.toContinuousLinearMap.comp
        (G.comp U.symm.toLinearIsometry.toContinuousLinearMap)‖ = ‖G‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg G) fun x ↦ ?_
    calc
      ‖U (G (U.symm x))‖ = ‖G (U.symm x)‖ := U.norm_map _
      _ ≤ ‖G‖ * ‖U.symm x‖ := G.le_opNorm _
      _ = ‖G‖ * ‖x‖ := by rw [U.symm.norm_map]
  · let C := U.toLinearIsometry.toContinuousLinearMap.comp
        (G.comp U.symm.toLinearIsometry.toContinuousLinearMap)
    refine ContinuousLinearMap.opNorm_le_bound G (norm_nonneg C) fun x ↦ ?_
    calc
      ‖G x‖ = ‖U (G x)‖ := (U.norm_map _).symm
      _ = ‖C (U x)‖ := by
        dsimp only [C, ContinuousLinearMap.comp_apply]
        change ‖U (G x)‖ = ‖U (G (U.symm (U x)))‖
        rw [LinearIsometryEquiv.symm_apply_apply]
      _ ≤ ‖C‖ * ‖U x‖ := C.le_opNorm _
      _ = ‖C‖ * ‖x‖ := by rw [U.norm_map]

/-! ### Kernels, ranges and projections -/

/-- The kernel projection of a fiberwise operator is the fiberwise extension of the base kernel
projection. -/
theorem ker_starProjection_rightFiberwiseMap
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap).starProjection.toLinearMap =
      (rightFiberwiseMap (S := S)
        (LinearMap.ker G.toLinearMap).starProjection).toLinearMap := by
  let U := LinearMap.ker G.toLinearMap
  apply LinearMap.IsSymmetricProjection.ext
    (Submodule.isSymmetricProjection_starProjection _)
    (isSymmetricProjection_rightFiberwiseMap _
      (Submodule.isSymmetricProjection_starProjection U))
  ext x
  constructor
  · intro hx
    rw [Submodule.range_starProjection] at hx
    refine ⟨x, ?_⟩
    apply PiLp.ext
    rintro ⟨i, s⟩
    change U.starProjection (rightFiber x s) i = x (i, s)
    have hs := (mem_ker_rightFiberwiseMap_iff G x).mp hx s
    exact congrArg (fun y : EuclideanSpace ℂ I => y i)
      (U.starProjection_eq_self_iff.mpr hs)
  · rintro ⟨y, rfl⟩
    rw [Submodule.range_starProjection]
    apply (mem_ker_rightFiberwiseMap_iff G _).mpr
    intro s
    change U.starProjection (rightFiber y s) ∈ U
    exact Submodule.starProjection_apply_mem U _

/-- Orthogonality to the kernel of a fiberwise operator is equivalent to orthogonality to the
base kernel on every fiber. -/
theorem mem_orthogonal_ker_rightFiberwiseMap_iff
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (I × S)) :
    x ∈ (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap)ᗮ ↔
      ∀ s, rightFiber x s ∈ (LinearMap.ker G.toLinearMap)ᗮ := by
  have hProjection :
      (LinearMap.ker (rightFiberwiseMap (S := S) G).toLinearMap).starProjection x =
        rightFiberwiseMap (S := S) (LinearMap.ker G.toLinearMap).starProjection x :=
    LinearMap.congr_fun (ker_starProjection_rightFiberwiseMap (S := S) G) x
  rw [← Submodule.starProjection_apply_eq_zero_iff, hProjection]
  change x ∈ LinearMap.ker
    (rightFiberwiseMap (S := S) (LinearMap.ker G.toLinearMap).starProjection).toLinearMap ↔ _
  rw [mem_ker_rightFiberwiseMap_iff]
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    Submodule.starProjection_apply_eq_zero_iff]

/-- A family belongs to the range of a fiberwise operator exactly when each fiber belongs to the
range of the base operator. -/
theorem mem_range_rightFiberwiseMap_iff (T : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (J × S)) :
    x ∈ (rightFiberwiseMap (S := S) T).range ↔ ∀ s, rightFiber x s ∈ T.range := by
  constructor
  · rintro ⟨y, rfl⟩ s
    exact ⟨rightFiber y s, (rightFiber_rightFiberwiseMap T y s).symm⟩
  · intro hx
    choose y hy using hx
    refine ⟨WithLp.toLp 2 (fun p : I × S => y p.2 p.1), ?_⟩
    ext ⟨j, s⟩
    change T (WithLp.toLp 2 (fun i => y s i)) j = x (j, s)
    exact congrArg (fun z : EuclideanSpace ℂ J => z j) (hy s)

/-- A family is orthogonal to the range of a fiberwise operator exactly when each fiber is
orthogonal to the range of the base operator. -/
theorem mem_orthogonal_range_rightFiberwiseMap_iff
    (T : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J)
    (x : EuclideanSpace ℂ (J × S)) :
    x ∈ (rightFiberwiseMap (S := S) T).rangeᗮ ↔ ∀ s, rightFiber x s ∈ T.rangeᗮ := by
  rw [ContinuousLinearMap.orthogonal_range, rightFiberwiseMap_adjoint]
  simp only [ContinuousLinearMap.orthogonal_range]
  exact mem_ker_rightFiberwiseMap_iff T.adjoint x

/-- The orthogonal projection onto the range of a fiberwise operator is the fiberwise extension
of the range projection of the base operator. -/
theorem rightFiberwiseMap_range_starProjection
    (T : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ J) :
    (rightFiberwiseMap (S := S) T).range.starProjection =
      rightFiberwiseMap (S := S) T.range.starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [mem_range_rightFiberwiseMap_iff]
    intro s
    rw [rightFiber_rightFiberwiseMap]
    exact T.range.starProjection_apply_mem _
  · rw [mem_orthogonal_range_rightFiberwiseMap_iff]
    intro s
    have h : rightFiber (x - rightFiberwiseMap (S := S) T.range.starProjection x) s =
        rightFiber x s - T.range.starProjection (rightFiber x s) := by
      rw [← rightFiber_rightFiberwiseMap]
      rfl
    rw [h]
    exact T.range.sub_starProjection_mem_orthogonal _

/-- The joint span of the ranges of fiberwise operators is the range of the fiberwise extension
of the projection onto the joint span of the base ranges. The family of operators may have
varying finite domains and need not be finite. -/
theorem iSup_range_rightFiberwiseMap_eq
    {ι : Type*} {I : ι → Type*} [∀ j, Fintype (I j)]
    (T : (j : ι) → EuclideanSpace ℂ (I j) →L[ℂ] EuclideanSpace ℂ J) :
    (⨆ j, (rightFiberwiseMap (S := S) (T j)).range) =
      (rightFiberwiseMap (S := S) (⨆ j, (T j).range).starProjection).range := by
  have hOrth : (⨆ j, (rightFiberwiseMap (S := S) (T j)).range)ᗮ =
      (rightFiberwiseMap (S := S) (⨆ j, (T j).range).starProjection).rangeᗮ := by
    ext x
    simp only [← Submodule.iInf_orthogonal, Submodule.mem_iInf,
      mem_orthogonal_range_rightFiberwiseMap_iff, Submodule.range_starProjection]
    exact forall_comm
  simpa only [Submodule.orthogonal_orthogonal] using
    congrArg (fun W : Submodule ℂ (EuclideanSpace ℂ (J × S)) => Wᗮ) hOrth

/-- The projection onto the joint span of the ranges of fiberwise operators is the fiberwise
extension of the projection onto the joint span of the base ranges. -/
theorem rightFiberwiseMap_iSup_range_starProjection
    {ι : Type*} {I : ι → Type*} [∀ j, Fintype (I j)]
    (T : (j : ι) → EuclideanSpace ℂ (I j) →L[ℂ] EuclideanSpace ℂ J) :
    (⨆ j, (rightFiberwiseMap (S := S) (T j)).range).starProjection =
      rightFiberwiseMap (S := S) (⨆ j, (T j).range).starProjection := by
  rw [iSup_range_rightFiberwiseMap_eq, rightFiberwiseMap_range_starProjection]
  simp only [Submodule.range_starProjection]

/-- Adding finite spectator coordinates does not increase the error between a finite sum of
range projections and the projection onto their joint span. -/
theorem norm_sum_rightFiberwiseMap_range_starProjection_sub_iSup_le
    {ι : Type*} [Fintype ι] {I : ι → Type*} [∀ j, Fintype (I j)]
    (T : (j : ι) → EuclideanSpace ℂ (I j) →L[ℂ] EuclideanSpace ℂ J) :
    ‖(∑ j, (rightFiberwiseMap (S := S) (T j)).range.starProjection) -
      (⨆ j, (rightFiberwiseMap (S := S) (T j)).range).starProjection‖ ≤
      ‖(∑ j, (T j).range.starProjection) - (⨆ j, (T j).range).starProjection‖ := by
  simp only [rightFiberwiseMap_range_starProjection, rightFiberwiseMap_iSup_range_starProjection]
  rw [← rightFiberwiseMap_sum, ← rightFiberwiseMap_sub]
  exact norm_rightFiberwiseMap_le _

end ContinuousLinearMap

/-- A change of orthonormal coordinates preserves and reflects the order of operators. -/
theorem LinearIsometryEquiv.conj_le_conj_iff
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (G H : E →ₗ[ℂ] E) :
    U.toLinearEquiv.conj G ≤ U.toLinearEquiv.conj H ↔ G ≤ H := by
  rw [LinearMap.le_def, ← _root_.map_sub U.toLinearEquiv.conj H G]
  simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.le_def] using!
    (LinearMap.isPositive_linearIsometryEquiv_conj_iff (T := H - G) U)

section

open scoped Matrix InnerProductSpace BigOperators

namespace ContinuousLinearMap

variable {I S : Type*} [Fintype I] [Fintype S]

/-- An operator and its independent extension over a nonempty finite spectator space have the
same eigenvalues. -/
theorem hasEigenvalue_rightFiberwiseMap_iff [Nonempty S]
    (G : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) (μ : ℂ) :
    Module.End.HasEigenvalue (rightFiberwiseMap (S := S) G).toLinearMap μ ↔
      Module.End.HasEigenvalue G.toLinearMap μ := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    obtain ⟨s, hs⟩ : ∃ s, rightFiber x s ≠ 0 := by
      by_contra! hzero
      refine hx.2 (PiLp.ext fun ⟨i, t⟩ ↦ ?_)
      simpa only [rightFiber_apply, PiLp.zero_apply] using congrArg (fun y ↦ y i) (hzero t)
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := rightFiber x s) ⟨?_, hs⟩
    rw [Module.End.mem_eigenspace_iff]
    refine PiLp.ext fun i ↦ ?_
    simpa [rightFiber_apply] using congrArg (fun y ↦ y (i, s)) hx.apply_eq_smul
  · intro h
    obtain ⟨x, hx⟩ := h.exists_hasEigenvector
    let s : S := Classical.choice ‹Nonempty S›
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := singleRightFiber s x) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, ContinuousLinearMap.coe_coe,
        rightFiberwiseMap_singleRightFiber]
      have hGx : G x = μ • x := hx.apply_eq_smul
      refine PiLp.ext fun p ↦ ?_
      by_cases hp : p.2 = s <;> simp [singleRightFiber, hp, hGx]
    · intro h0
      exact hx.2 (by rw [← norm_eq_zero, ← norm_singleRightFiber s x, h0, norm_zero])

end ContinuousLinearMap

end
