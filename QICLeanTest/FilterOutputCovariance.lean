/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.FilterOutputCovariance

/-! Ordered-action, complex singular, empty, and site/basis permutation regressions. -/

open Complex Matrix Entropy
open scoped ComplexOrder

-- Empty lists act as the identity, without a nonempty coordinate type.
example {ι : Type*} [Fintype ι] [DecidableEq ι] (Ω : EuclideanSpace ℂ ι) :
    (([] : List (Matrix ι ι ℂ)).map (fun A ↦ toEuclideanCLM A)).foldl
      (fun ψ T ↦ T ψ) Ω = Ω := rfl

example (l : List (Matrix (Fin 0) (Fin 0) ℂ)) (Ω : EuclideanSpace ℂ (Fin 0)) :
    (l.map (fun A ↦ toEuclideanCLM A)).foldl (fun ψ T ↦ T ψ) Ω = toEuclideanLin l.reverse.prod Ω :=
  foldl_toEuclideanCLM_eq_reverse_prod l Ω

-- Empty chains preserve the input.
example {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (D : ℕ → Finset V)
    (K : (j : Fin 0) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ)
    (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω = Ω := by
  simpa using (foldl_localLift_eq_liftProd_chainList D K Ω).symm

-- Repeated regions retain the order of their independent matrix occurrences.
example {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}
    (D : Finset V) (K L : Matrix (RegionConfig n D) (RegionConfig n D) ℂ)
    (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    ([localLift D K, localLift D L].map (fun A ↦ toEuclideanCLM A)).foldl (fun ψ T ↦ T ψ) Ω =
      toEuclideanLin (localLift D L * localLift D K) Ω := by
  simpa using foldl_toEuclideanCLM_eq_reverse_prod [localLift D K, localLift D L] Ω

-- Empty regions remain valid when every physical alphabet is empty.
example (K : Matrix (RegionConfig (fun _ : Fin 2 ↦ 0) ∅)
    (RegionConfig (fun _ : Fin 2 ↦ 0) ∅) ℂ) :
    reindex (siteConfigurationEquiv (Equiv.swap (0 : Fin 2) 1)
        (fun _ ↦ Equiv.refl (Fin 0)))
      (siteConfigurationEquiv (Equiv.swap (0 : Fin 2) 1)
        (fun _ ↦ Equiv.refl (Fin 0))) (localLift ∅ K) =
      localLift ∅ (reindex
        (regionConfigurationEquiv ∅ ∅ (Equiv.swap (0 : Fin 2) 1)
          (by simp) (fun _ ↦ Equiv.refl (Fin 0)))
        (regionConfigurationEquiv ∅ ∅ (Equiv.swap (0 : Fin 2) 1)
          (by simp) (fun _ ↦ Equiv.refl (Fin 0))) K) :=
  localLift_relabel ∅ ∅ _ (by simp) _ K

-- A non-involutive site cycle and a local basis exchange fix the transport direction.
example (K : Matrix (RegionConfig (fun _ : Fin 3 ↦ 2) {0})
    (RegionConfig (fun _ : Fin 3 ↦ 2) {0}) ℂ) :
    let e := (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)
    let hD : ∀ v : Fin 3, v ∈ ({0} : Finset (Fin 3)) ↔ e v ∈ ({2} : Finset (Fin 3)) := by
      intro v
      fin_cases v <;> simp [e]
    let f := fun _ : Fin 3 ↦ Equiv.swap (0 : Fin 2) 1
    reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) (localLift {0} K) =
      localLift {2} (reindex (regionConfigurationEquiv {0} {2} e hD f)
        (regionConfigurationEquiv {0} {2} e hD f) K) := by
  dsimp only
  exact localLift_relabel _ _ _ _ _ K

private noncomputable def firstProjection : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal ![1, 0]

private noncomputable def complexProjection : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℝ) • vecMulVec ![1, I] (star ![1, I])

-- P = diag(1,0), Q = (1/2)[[1,-i],[i,1]] are singular PSD matrices.
example : firstProjection.PosSemidef ∧ complexProjection.PosSemidef ∧
    firstProjection.det = 0 ∧ complexProjection.det = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  · exact (posSemidef_vecMulVec_self_star (![1, I] : Fin 2 → ℂ)).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
  · norm_num [firstProjection, det_fin_two]
  · norm_num [complexProjection, det_fin_two, vecMulVec_apply, Complex.ext_iff]

-- The ascending fold is Q P e₀ = (e₀ + i e₁)/2.
example : ([firstProjection, complexProjection].map (fun A ↦ toEuclideanCLM A)).foldl
      (fun ψ T ↦ T ψ) (WithLp.toLp 2 ![(1 : ℂ), 0]) =
    WithLp.toLp 2 ![(1 / 2 : ℂ), I / 2] := by
  rw [foldl_toEuclideanCLM_eq_reverse_prod]
  ext i
  fin_cases i <;>
    norm_num [firstProjection, complexProjection, toLpLin_apply, mulVec, dotProduct,
      Fin.sum_univ_two, mul_apply, vecMulVec_apply, Complex.ext_iff]

-- The ascending matrix product gives a different vector.
example : toEuclideanLin (firstProjection * complexProjection)
      (WithLp.toLp 2 ![(1 : ℂ), 0]) ≠ WithLp.toLp 2 ![(1 / 2 : ℂ), I / 2] := by
  intro h
  have hIm := congrArg (fun ψ : EuclideanSpace ℂ (Fin 2) ↦ (ψ 1).im) h
  norm_num [firstProjection, complexProjection, toLpLin_apply, mulVec, dotProduct,
    Fin.sum_univ_two, mul_apply, vecMulVec_apply] at hIm

-- Transposing the correct product also gives a different vector.
example : toEuclideanLin (complexProjection * firstProjection)ᵀ
      (WithLp.toLp 2 ![(1 : ℂ), 0]) ≠ WithLp.toLp 2 ![(1 / 2 : ℂ), I / 2] := by
  intro h
  have hIm := congrArg (fun ψ : EuclideanSpace ℂ (Fin 2) ↦ (ψ 1).im) h
  norm_num [firstProjection, complexProjection, toLpLin_apply, mulVec, dotProduct,
    Fin.sum_univ_two, mul_apply, vecMulVec_apply, transpose_apply] at hIm

-- A zero input needs no nonvanishing premise for normalized covariance.
example {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {n : V → ℕ} {n' : V' → ℕ} {m : ℕ}
    (D : ℕ → Finset V) (D' : ℕ → Finset V') (e : V ≃ V')
    (hD : ∀ j v, v ∈ D j ↔ e v ∈ D' j)
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ) :
    let ψ := toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) 0
    relabelVector e f (((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ) = 0 := by
  have h := relabelVector_normalized_liftProd_chainList D D' e hD f K (fun _ ↦ True) 0
  simpa [relabelVector] using h

-- Every target competitor is covered, at arbitrary floors/weights and without hK.
example {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
    {n : V → ℕ} {n' : V' → ℕ} {m : ℕ}
    (D : ℕ → Finset V) (D' : ℕ → Finset V') (e : V ≃ V')
    (hD : ∀ j v, v ∈ D j ↔ e v ∈ D' j)
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v))) (b a : Fin m → ℝ)
    (K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ)
    (Ω : EuclideanSpace ℂ (SiteConfig n))
    (hmax : ∀ L : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      (∀ j, IsFeasibleFilter (b j) (a j) (L j)) →
      ‖toEuclideanLin (liftProd (chainList D L fun _ ↦ True)) Ω‖ ≤
        ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) :
    ∀ L : (j : Fin m) → Matrix (RegionConfig n' (D' j)) (RegionConfig n' (D' j)) ℂ,
      (∀ j, IsFeasibleFilter (b j) (a j) (L j)) →
      ‖toEuclideanLin (liftProd (chainList D' L fun _ ↦ True)) (relabelVector e f Ω)‖ ≤
        ‖toEuclideanLin (liftProd (chainList D'
          (fun j ↦ reindex (regionConfigurationEquiv (D j) (D' j) e (hD j) f)
            (regionConfigurationEquiv (D j) (D' j) e (hD j) f) (K j)) fun _ ↦ True))
          (relabelVector e f Ω)‖ :=
  (forall_norm_liftProd_chainList_le_relabel_iff D D' e hD f b a K Ω).mpr hmax
