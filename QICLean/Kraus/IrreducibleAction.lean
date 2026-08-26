/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixFamilyAction
import QICLean.Kraus.InvariantProjection
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Irreducible actions of finite matrix families

A finite family of complex square matrices has no nontrivial invariant submodule if and only if
it has no nontrivial invariant orthogonal projection.
-/

open scoped Matrix BigOperators

namespace Kraus

variable {d D : ℕ}

noncomputable section

/-- `Kraus.IsIrreducibleFamily` implies `Matrix.IsIrreducibleAction`.

If a nontrivial `K`-invariant submodule `W` existed, its orthogonal projection would give a
nontrivial invariant orthogonal projection matrix, contradicting `Kraus.IsIrreducibleFamily`. -/
lemma isIrreducibleAction_of_isIrreducibleFamily
    {d D : ℕ} (K : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (hIrr : Kraus.IsIrreducibleFamily (d := d) (D := D) K) :
    Matrix.IsIrreducibleAction (d := d) (D := D) K := by
  classical
  intro W hW
  -- Assume `W` is a nontrivial proper invariant submodule; derive a contradiction.
  by_contra hWT
  push Not at hWT
  obtain ⟨hW_ne_bot, hW_ne_top⟩ := hWT
  -- Work in the finite-dimensional Hilbert space `EuclideanSpace ℂ (Fin D)`.
  let E := EuclideanSpace ℂ (Fin D)
  let e : (Fin D → ℂ) ≃ₗ[ℂ] E :=
    (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℂ) (V := (Fin D → ℂ))).symm
  let W' : Submodule ℂ E := W.map e.toLinearMap
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro h
    have : W = ⊥ :=
      (Submodule.map_eq_bot_iff (p := W) (e := e)).1 (by simpa [W'] using h)
    exact hW_ne_bot this
  have hW'_ne_top : W' ≠ ⊤ := by
    intro h
    have : W = ⊤ :=
      (Submodule.map_eq_top_iff (p := W) (e := e)).1 (by simpa [W'] using h)
    exact hW_ne_top this
  have : W'.HasOrthogonalProjection := by infer_instance
  let p' : E →L[ℂ] E := W'.starProjection
  -- Convert the orthogonal projection to a matrix via `Matrix.toEuclideanLin.symm`.
  let P : Matrix (Fin D) (Fin D) ℂ :=
    (Matrix.toEuclideanLin : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] E →ₗ[ℂ] E).symm p'.toLinearMap
  -- `W'` is invariant under `K i` (transported to `EuclideanSpace`).
  have hW' : ∀ i : Fin d, ∀ v ∈ W', (Matrix.toEuclideanLin (K i)) v ∈ W' := by
    intro i v hv
    rcases (Submodule.mem_map).1 hv with ⟨u, huW, rfl⟩
    have huW' : (K i).mulVec u ∈ W := hW i u huW
    have : e.toLinearMap ((K i).mulVec u) ∈ W' :=
      Submodule.mem_map_of_mem (f := e.toLinearMap) huW'
    convert this using 1
    rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    rfl
  -- The matrix `P` is Hermitian.
  have hHerm : P.IsHermitian := by
    have hSymm : (Matrix.toEuclideanLin P).IsSymmetric := by
      simpa [P, p'] using (Submodule.starProjection_isSymmetric (K := W'))
    exact (Matrix.isSymmetric_toEuclideanLin_iff (A := P) (𝕜 := ℂ) (n := Fin D)).mp hSymm
  -- The matrix `P` is idempotent.
  have hPP : P * P = P := by
    apply (Matrix.toEuclideanLin : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] E →ₗ[ℂ] E).injective
    apply LinearMap.ext
    intro x
    simp [Matrix.toEuclideanLin, P, p']
    have hx : W'.starProjection x ∈ W' := by
      simp
    have : W'.starProjection (W'.starProjection x) = W'.starProjection x :=
      (Submodule.starProjection_eq_self_iff (K := W') (v := W'.starProjection x)).2 hx
    simpa using this
  have horth : IsOrthogonalProjection (D := D) P := ⟨hHerm, hPP⟩
  -- `P` is nontrivial.
  have hP_ne0 : P ≠ 0 := by
    intro hP0
    have hp0 : p'.toLinearMap = 0 := by
      have : Matrix.toEuclideanLin P = 0 := by
        simp [hP0]
      simpa [P] using this
    have : W' = (⊥ : Submodule ℂ E) := by
      have : (p' : E →L[ℂ] E).range = (⊥ : Submodule ℂ E) := by
        simp [p', hp0]
      simpa [p'] using this
    exact hW'_ne_bot this
  have hP_ne1 : P ≠ 1 := by
    intro hP1
    have hp1 : p'.toLinearMap = (LinearMap.id : E →ₗ[ℂ] E) := by
      have : Matrix.toEuclideanLin P = Matrix.toEuclideanLin (1 : Matrix (Fin D) (Fin D) ℂ) := by
        simp [hP1]
      simpa [Matrix.toEuclideanLin, P] using this
    have : W' = (⊤ : Submodule ℂ E) := by
      have : (p' : E →L[ℂ] E).range = (⊤ : Submodule ℂ E) := by
        -- `p'` is the identity map.
        have hp1' : (p' : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E := by
          -- Avoid `ext` (which would unfold `EuclideanSpace` to pointwise goals).
          apply ContinuousLinearMap.ext
          intro x
          simpa using congrArg (fun f : E →ₗ[ℂ] E => f x) hp1
        simp [hp1']
      simpa [p'] using this
    exact hW'_ne_top this
  -- Invariance: `(1 - P) * K i * P = 0` for all `i`.
  have hPinv : ∀ i : Fin d, (1 - P) * K i * P = 0 := by
    intro i
    apply (Matrix.toEuclideanLin : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] E →ₗ[ℂ] E).injective
    apply LinearMap.ext
    intro x
    -- Expand the triple product using the `Matrix.toLpLin` linear equivalence.
    simp [Matrix.toEuclideanLin]
    -- Show the intermediate vector lies in `W'`.
    have hP_lin : Matrix.toEuclideanLin P = p'.toLinearMap := by
      simp [P]
    have hy : (Matrix.toEuclideanLin P) x ∈ W' := by
      -- The orthogonal projection always lands in the submodule.
      rw [hP_lin]
      change p' x ∈ W'
      simp [p']
    have hz : (Matrix.toEuclideanLin (K i)) ((Matrix.toEuclideanLin P) x) ∈ W' :=
      hW' i ((Matrix.toEuclideanLin P) x) hy
    -- `P` fixes vectors in `W'`.
    have hfix : (Matrix.toEuclideanLin P)
        ((Matrix.toEuclideanLin (K i)) ((Matrix.toEuclideanLin P) x)) =
        (Matrix.toEuclideanLin (K i)) ((Matrix.toEuclideanLin P) x) := by
      have : W'.starProjection
          ((Matrix.toEuclideanLin (K i)) ((Matrix.toEuclideanLin P) x)) =
          (Matrix.toEuclideanLin (K i)) ((Matrix.toEuclideanLin P) x) :=
        (Submodule.starProjection_eq_self_iff (K := W')
          (v := (Matrix.toEuclideanLin (K i)) ((Matrix.toEuclideanLin P) x))).2 hz
      simpa [P, p'] using this
    -- Now `toEuclideanLin (1 - P)` kills vectors in `W'`.
    simp [Matrix.toEuclideanLin, hfix]
  -- Build `Kraus.HasInvariantProj K`, contradicting `Kraus.IsIrreducibleFamily K`.
  have : Kraus.HasInvariantProj (d := d) (D := D) K :=
    ⟨P, horth, hP_ne0, hP_ne1, hPinv⟩
  exact hIrr this

/-- `IsIrreducibleAction` implies `Kraus.IsIrreducibleFamily`.

If there are no nontrivial invariant submodules, then there are no
nontrivial invariant orthogonal projections. -/
lemma isIrreducibleFamily_of_isIrreducibleAction
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) (hIrr : Matrix.IsIrreducibleAction K) :
    Kraus.IsIrreducibleFamily (d := d) (D := D) K := by
  intro ⟨P, horth, hne0, hne1, hinv⟩
  let V : Type := Fin D → ℂ
  let f : V →ₗ[ℂ] V := Matrix.toLin' P
  -- The range of `f` is an invariant submodule.
  set W : Submodule ℂ V := LinearMap.range f
  have hW_inv : Matrix.IsInvariantSubmodule K W := by
    intro i v ⟨u, hu⟩
    have hAP : K i * P = P * (K i * P) := by
      rw [← sub_eq_zero]
      calc
        K i * P - P * (K i * P) = (1 - P) * K i * P := by noncomm_ring
        _ = 0 := hinv i
    refine ⟨(K i * P).mulVec u, ?_⟩
    simp only [V, f, Matrix.toLin'_apply] at hu ⊢
    rw [Matrix.mulVec_mulVec, ← hAP, ← Matrix.mulVec_mulVec, hu]
  rcases hIrr W hW_inv with hW | hW
  · -- `W = ⊥`: the range is trivial, hence `P = 0`.
    apply hne0
    have hf0 : f = 0 := by
      have : f.range = ⊥ := by
        simpa [W] using hW
      exact (LinearMap.range_eq_bot).1 this
    have hP0 := congrArg LinearMap.toMatrix' hf0
    simpa [f, LinearMap.toMatrix'_toLin'] using hP0
  · -- `W = ⊤`: the range is all of `V`, hence `P = 1`.
    apply hne1
    have hsurj : Function.Surjective f := by
      have : f.range = ⊤ := by
        simpa [W] using hW
      exact (LinearMap.range_eq_top).1 this
    have hfid : f = LinearMap.id := by
      apply LinearMap.ext
      intro v
      rcases hsurj v with ⟨u, rfl⟩
      -- Simplify the goal and unfold `f`.
      simp only [f, LinearMap.id_apply]
      have hmul :
          (Matrix.toLin' P) ((Matrix.toLin' P) u) = (Matrix.toLin' (P * P)) u :=
        (Matrix.toLin'_mul_apply P P u).symm
      rw [horth.2] at hmul
      exact hmul
    have hP1 := congrArg LinearMap.toMatrix' hfid
    simpa [V, f, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using hP1

/-- A finite matrix family acts irreducibly if and only if it has no nontrivial invariant
orthogonal projection. -/
theorem isIrreducibleAction_iff_isIrreducibleFamily
    (K : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Matrix.IsIrreducibleAction K ↔ IsIrreducibleFamily K :=
  ⟨isIrreducibleFamily_of_isIrreducibleAction K,
    isIrreducibleAction_of_isIrreducibleFamily K⟩

end

end Kraus
