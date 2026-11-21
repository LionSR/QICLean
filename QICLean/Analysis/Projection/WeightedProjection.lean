/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Abel

/-!
# Weighted projections and their range restrictions

Commuting idempotents and weights give an exact projected Sylvester equation. Restricting its
domain and codomain produces actual maps between the two projection ranges. Ambient matrix
order and operator norms give the corresponding bounds on these restrictions.

These are supporting results for ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, lines873–886, and the proof of `t:ais`, lines1010–1024.
-/

section

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator BigOperators

/-- An inverse weight cancels through a right cutoff supporting the residual.
Auxiliary algebra for the weighted truncation argument of AKL14,
arXiv:1406.3898, Theorem lowspec, low70.tex, lines 1102–1168.
No norm estimate or spectral interpretation is part of this statement. -/
theorem mul_inverse_weight_mul_eq_of_right_support
    {R : Type*} [Ring R] (D Winv W Q : R)
    (hW : Winv * W = 1) (hD : D * (1 - Q) = 0) :
    (D * Winv) * (W * Q) = D := by
  have hDQ : D * Q = D := by
    have hsub : D - D * Q = 0 := by
      simpa only [mul_sub, mul_one] using hD
    exact (sub_eq_zero.mp hsub).symm
  calc
    (D * Winv) * (W * Q) = D * ((Winv * W) * Q) := by simp only [mul_assoc]
    _ = D * Q := by rw [hW, one_mul]
    _ = D := hDQ

namespace WeightedProjection

/-- The forcing term is a conjugated boundary operator followed by the low
part of the weight. Its norm is not bounded merely by the norm of `Y`.
This is auxiliary algebra for ALVV, arXiv:1602.08828v2, Theorem `t:ais`,
source lines 1010–1024; the identity is not quoted from that passage. -/
theorem forcing_identity
    {𝔄 : Type*} [Ring 𝔄] (Y W Winv Q R : 𝔄)
    (hWQ : Commute W Q) (hInv : Winv * W = 1) :
    W * Q * Y * (1 - Q) * R =
      (Q * W * Y * Winv) * (W * (1 - Q) * R) := by
  calc
    W * Q * Y * (1 - Q) * R = (Q * W) * Y * (1 - Q) * R := by
      rw [hWQ.eq]
    _ = (Q * W * Y) * ((Winv * W) * (1 - Q) * R) := by
      simp only [hInv, one_mul, mul_assoc]
    _ = (Q * W * Y * Winv) * (W * (1 - Q) * R) := by
      simp only [mul_assoc]
end WeightedProjection

section

namespace WeightedProjection

/-- The weighted projected equation, before restriction to the two ranges.
Only a left inverse of the weight is needed. This is auxiliary algebra for
ALVV, arXiv:1602.08828v2, Theorem `t:ais`, source lines 1010–1024; the
identity itself is not asserted to be printed there. -/
private theorem sylvester_identity
    {𝔄 : Type*} [Ring 𝔄] (X Y W Winv Q R : 𝔄)
    (hQQ : Q * Q = Q) (hWQ : Commute W Q)
    (hXW : Commute X W) (hXQ : Commute X Q)
    (hRH : Commute R (X + Y)) (hInv : Winv * W = 1) :
    X * (W * Q * R) - (W * Q * R) * (X + Y) =
      -((Q * W * Y * Winv * Q) * (W * Q * R)) -
        W * Q * Y * (1 - Q) * R := by
  let K := W * Q
  let J := Q * W * Y * Winv * Q
  have hQWQ : Q * (W * Q) = W * Q := by
    calc
      Q * (W * Q) = (Q * W) * Q := (mul_assoc _ _ _).symm
      _ = (W * Q) * Q := congrArg (fun a ↦ a * Q) hWQ.eq.symm
      _ = W * Q := by rw [mul_assoc, hQQ]
  have hInvQ : Winv * Q * (W * Q) = Q := by
    calc
      Winv * Q * (W * Q) = Winv * (Q * (W * Q)) := mul_assoc _ _ _
      _ = Winv * (W * Q) := congrArg (fun a ↦ Winv * a) hQWQ
      _ = (Winv * W) * Q := (mul_assoc _ _ _).symm
      _ = Q := by rw [hInv, one_mul]
  have hJK : J * K = K * Y * Q := by
    dsimp [J, K]
    calc
      (Q * W * Y * Winv * Q) * (W * Q) =
          (Q * W * Y) * (Winv * Q * (W * Q)) := by simp only [mul_assoc]
      _ = (Q * W * Y) * Q := by rw [hInvQ]
      _ = W * Q * Y * Q := congrArg (fun a ↦ a * Y * Q) hWQ.eq.symm
  have hXK : Commute X K := hXW.mul_right hXQ
  have hbasic : X * (K * R) - (K * R) * (X + Y) = -(K * Y * R) := by
    calc
      X * (K * R) - (K * R) * (X + Y) =
          (K * X) * R - K * ((X + Y) * R) := by
        exact congrArg₂ (fun a b : 𝔄 ↦ a - b)
          ((mul_assoc X K R).symm.trans (congrArg (fun a ↦ a * R) hXK.eq))
          ((mul_assoc K R (X + Y)).trans (congrArg (fun a ↦ K * a) hRH.eq))
      _ = -(K * Y * R) := by noncomm_ring
  change X * (K * R) - (K * R) * (X + Y) =
    -(J * (K * R)) - K * Y * (1 - Q) * R
  rw [hbasic, ← mul_assoc J K R, hJK]
  noncomm_ring
end WeightedProjection

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Range preservation from the existing idempotent commutation criterion.
Auxiliary linear algebra for ALVV, arXiv:1602.08828v2, `t:ais`, lines 1010–1024. -/
private theorem mapsTo_range_of_commute (Q W : E →L[𝕜] E)
    (hQ : IsIdempotentElem Q) (hQW : Commute Q W) :
    ∀ x ∈ Q.range, W x ∈ Q.range := by
  have hQl : IsIdempotentElem (Q : E →ₗ[𝕜] E) := by
    exact congrArg (fun f : E →L[𝕜] E ↦ (f : E →ₗ[𝕜] E)) hQ.eq
  have hQWl : Commute (Q : E →ₗ[𝕜] E) (W : E →ₗ[𝕜] E) := by
    exact congrArg (fun f : E →L[𝕜] E ↦ (f : E →ₗ[𝕜] E)) hQW.eq
  exact (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem
    (W : E →ₗ[𝕜] E)).mp
      ((LinearMap.IsIdempotentElem.commute_iff hQl).mp hQWl).1
end ContinuousLinearMap

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The actual weighted projected equation on the two projection ranges.
All range conditions are consequences of idempotence and commutation.
This is auxiliary linear algebra for ALVV, arXiv:1602.08828v2,
Theorem `t:ais`, source lines 1010–1024, not a quoted identity or the
physical subspace perturbation estimate. -/
theorem exists_restricted_weighted_sylvester
    (X Y W Winv Q R : E →L[𝕜] E)
    (hQ : IsIdempotentElem Q) (hR : IsIdempotentElem R)
    (hWQ : Commute W Q) (hXW : Commute X W) (hXQ : Commute X Q)
    (hRH : Commute R (X + Y)) (hInv : Winv * W = 1) :
    let U : Submodule 𝕜 E := Q.range
    let G : Submodule 𝕜 E := R.range
    let J := Q * W * Y * Winv * Q
    let L := W * Q * Y * (1 - Q)
    ∃ (B : G →L[𝕜] G) (XU : U →L[𝕜] U) (Z : G →L[𝕜] U)
        (V : U →L[𝕜] U) (F : G →L[𝕜] U),
      G.subtypeL ∘L B = (X + Y).domRestrict G ∧
      U.subtypeL ∘L XU = X.domRestrict U ∧
      U.subtypeL ∘L Z = (W * Q).domRestrict G ∧
      U.subtypeL ∘L V = J.domRestrict U ∧
      U.subtypeL ∘L F = L.domRestrict G ∧
      XU ∘L Z - Z ∘L B = -(V ∘L Z) - F := by
  dsimp only
  let U : Submodule 𝕜 E := Q.range
  let G : Submodule 𝕜 E := R.range
  let K := W * Q
  let J := Q * W * Y * Winv * Q
  let L := W * Q * Y * (1 - Q)
  have hHG : ∀ x ∈ G, (X + Y) x ∈ G :=
    mapsTo_range_of_commute R (X + Y) hR hRH
  have hXU : ∀ x ∈ U, X x ∈ U :=
    mapsTo_range_of_commute Q X hQ hXQ.symm
  have hKU (x : E) : K x ∈ U :=
    mapsTo_range_of_commute Q W hQ hWQ.symm (Q x) ⟨x, rfl⟩
  have hZG : ∀ x ∈ G, K x ∈ U := fun x _ ↦ hKU x
  have hJU : ∀ x ∈ U, J x ∈ U := by
    intro x _
    change Q (W (Y (Winv (Q x)))) ∈ Q.range
    exact ⟨W (Y (Winv (Q x))), rfl⟩
  have hLG : ∀ x ∈ G, L x ∈ U := by
    intro x _
    exact hKU (Y ((1 - Q) x))
  let B : G →L[𝕜] G := (X + Y).restrict hHG
  let XU : U →L[𝕜] U := X.restrict hXU
  let Z : G →L[𝕜] U := K.restrict hZG
  let V : U →L[𝕜] U := J.restrict hJU
  let F : G →L[𝕜] U := L.restrict hLG
  have hRl : IsIdempotentElem (R : E →ₗ[𝕜] E) :=
    congrArg (fun f : E →L[𝕜] E ↦ (f : E →ₗ[𝕜] E)) hR.eq
  have hRfix (x : G) : R (x : E) = (x : E) :=
    (LinearMap.IsIdempotentElem.mem_range_iff hRl).mp x.property
  have hEq := WeightedProjection.sylvester_identity X Y W Winv Q R
    hQ.eq hWQ hXW hXQ hRH hInv
  refine ⟨B, XU, Z, V, F, rfl, rfl, rfl, rfl, rfl, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change X (K (x : E)) - K ((X + Y) (x : E)) =
    -(J (K (x : E))) - L (x : E)
  have hx := congrArg (fun f : E →L[𝕜] E ↦ f (x : E)) hEq
  change X (K (R (x : E))) - K (R ((X + Y) (x : E))) =
    -(J (K (R (x : E)))) - L (R (x : E)) at hx
  have hRHx : R ((X + Y) (x : E)) = (X + Y) (x : E) := hRfix (B x)
  rw [hRfix x, hRHx] at hx
  exact hx
end ContinuousLinearMap
end

section

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- An ambient order bound gives a lower quadratic bound on the actual
restriction to the projection range. Idempotence suffices for this step.
This is auxiliary spectral algebra for ALVV, arXiv:1602.08828v2,
`def:hard-trunc`, source lines 873–886, and `t:ais`, lines 1010–1024. -/
theorem exists_restrict_range_quadratic_lower
    (Q X : E →L[ℂ] E) (hQ : IsIdempotentElem Q) (hXQ : Commute X Q)
    (u : ℝ) (horder : (u : ℂ) • Q ≤ X) :
    ∃ XU : Q.range →L[ℂ] Q.range,
      Q.range.subtypeL ∘L XU = X.domRestrict Q.range ∧
      ∀ y : Q.range, u * ‖y‖ ^ 2 ≤ (inner ℂ y (XU y)).re := by
  have hmap : ∀ x ∈ Q.range, X x ∈ Q.range :=
    mapsTo_range_of_commute Q X hQ hXQ.symm
  let XU : Q.range →L[ℂ] Q.range := X.restrict hmap
  have hQl : IsIdempotentElem (Q : E →ₗ[ℂ] E) :=
    congrArg (fun f : E →L[ℂ] E ↦ (f : E →ₗ[ℂ] E)) hQ.eq
  have hfix (y : Q.range) : Q (y : E) = (y : E) :=
    (LinearMap.IsIdempotentElem.mem_range_iff hQl).mp y.property
  refine ⟨XU, rfl, ?_⟩
  intro y
  have hp := (ContinuousLinearMap.le_def.mp horder).re_inner_nonneg_right (y : E)
  change 0 ≤ (inner ℂ (y : E) (X (y : E) - (u : ℂ) • Q (y : E))).re at hp
  rw [hfix y] at hp
  simp only [inner_sub_right, Complex.sub_re, inner_smul_right,
    Complex.re_ofReal_mul] at hp
  have hself : (inner ℂ (y : E) (y : E)).re = ‖(y : E)‖ ^ 2 := by
    change RCLike.re (inner ℂ (y : E) (y : E)) = ‖(y : E)‖ ^ 2
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (y : E)
  rw [hself] at hp
  change u * ‖(y : E)‖ ^ 2 ≤ (inner ℂ (y : E) (X (y : E))).re
  exact sub_nonneg.mp hp
end ContinuousLinearMap
end

section

namespace ContinuousLinearMap

/-- The ambient realization bounds the norm of an actual restricted map.
Supporting ALVV, arXiv:1602.08828v2, `t:ais`, source lines 1010–1024.
No nontriviality of either subspace is required. -/
theorem norm_le_of_subtypeL_comp_eq_domRestrict
    {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {G U : Submodule 𝕜 E} (f : G →L[𝕜] U) (A : E →L[𝕜] E)
    (h : U.subtypeL ∘L f = A.domRestrict G) : ‖f‖ ≤ ‖A‖ := by
  calc
    ‖f‖ = ‖U.subtypeL ∘L f‖ := by
      simpa only [Submodule.subtypeₗᵢ_toContinuousLinearMap] using
        (LinearIsometry.norm_toContinuousLinearMap_comp U.subtypeₗᵢ (g := f)).symm
    _ = ‖A.domRestrict G‖ := congrArg norm h
    _ ≤ ‖A‖ * ‖G.subtypeL‖ := A.opNorm_comp_le G.subtypeL
    _ ≤ ‖A‖ * 1 := mul_le_mul_of_nonneg_left (Submodule.norm_subtypeL_le G) (norm_nonneg A)
    _ = ‖A‖ := mul_one _
end ContinuousLinearMap
end

namespace Matrix

open scoped MatrixOrder

/-- The matrix order is transported to the actual Euclidean operator order.
Auxiliary to the weighted spectral argument of ALVV, t:ais, lines 1010--1024. -/
theorem toEuclideanCLM_le_of_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hAB : A ≤ B) :
    toEuclideanCLM (n := n) (𝕜 := ℂ) A ≤ toEuclideanCLM (n := n) (𝕜 := ℂ) B := by
  apply ContinuousLinearMap.le_def.mpr
  have hpos : (B - A).toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr (Matrix.le_iff.mp hAB)
  have hposC : (toEuclideanCLM (n := n) (𝕜 := ℂ) (B - A)).IsPositive := by
    apply (ContinuousLinearMap.isPositive_toLinearMap_iff _).mp
    simpa only [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using hpos
  simpa only [map_sub] using hposC
end Matrix
end
