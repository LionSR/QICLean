/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.OrderedMatrixAction
import QICLean.Entropy.FilterFeasibility
import QICLean.Entropy.FilterMaximizer
import QICLean.Entropy.RegionCovariance

/-!
# Ordered filter outputs under site relabelling

The ascending fold of local continuous linear maps equals the action of the
reverse matrix product. Site and basis-label bijections preserve local lifts,
that ordered product, its output, its normalized output, and its global norm
comparison against all feasible competitors. Repeated regions retain their
independent matrix occurrences. No nesting, positivity, invertibility, positive local dimension, or
nonzero output is needed for the operator and vector identities.

## Source and scope

The ascending fold and inverse-norm normalization are the matrix expressions in
`output` and `normalizedOutput` in `openai/math`, commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`lean/OAI/MathematicalPhysics/PEPSFilters/Basic.lean`, lines 166–179.
The entrywise local lift is described in `LocalOperators.lean`, lines 54–62,
at the same commit. These are source-shaped matrix identities, not equalities
with an imported source filter type. The proofs below are independently written;
no upstream Lean proof text is reused. They reuse the existing configuration
equivalences, matrix action under reindexing, and feasibility invariance.

The family in a maximality statement is transported unchanged. No second
optimizer is selected. Physical Hamiltonians, geometric region construction,
and the remaining literal source-interface comparison are outside this module.
-/

open Matrix
open scoped Kronecker

namespace Entropy

variable {V V' : Type*} [Fintype V] [DecidableEq V]
  [Fintype V'] [DecidableEq V'] {n : V → ℕ} {n' : V' → ℕ} {m : ℕ}

/-- The ascending list of local actions gives exactly the reverse product
used by the filter chain. No commutation or nesting is assumed. -/
theorem foldl_localLift_eq_liftProd_chainList (D : ℕ → Finset V)
    (K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ)
    (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    (List.ofFn fun j ↦
      toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ) (localLift (D j) (K j))).foldl
        (fun ψ T ↦ T ψ) Ω =
      toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω := by
  simpa [liftProd_chainList_eq, List.ofFn_eq_map, List.map_reverse,
    List.map_map, Function.comp_def] using
    foldl_toEuclideanCLM_eq_reverse_prod
      (List.ofFn fun j ↦ localLift (D j) (K j)) Ω

/-- Relabelling sites and local basis labels commutes with a local lift,
including empty regions and empty configuration types. -/
theorem localLift_relabel (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (K : Matrix (RegionConfig n D) (RegionConfig n D) ℂ) :
    reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f) (localLift D K) =
      localLift D' (reindex (regionConfigurationEquiv D D' e hD f)
        (regionConfigurationEquiv D D' e hD f) K) := by
  let R := regionConfigurationEquiv D D' e hD f
  let C := complementConfigurationEquiv D D' e hD f
  ext σ τ
  simp only [localLift, reindex_apply, submatrix_apply, Equiv.symm_symm,
    kroneckerMap_apply, one_apply]
  change K (R.symm ((cutEquiv n' D') σ).1) (R.symm ((cutEquiv n' D') τ).1) *
      (if C.symm ((cutEquiv n' D') σ).2 = C.symm ((cutEquiv n' D') τ).2 then 1 else 0) =
    K (R.symm ((cutEquiv n' D') σ).1) (R.symm ((cutEquiv n' D') τ).1) *
      (if ((cutEquiv n' D') σ).2 = ((cutEquiv n' D') τ).2 then 1 else 0)
  simp only [C.symm.injective.eq_iff]

variable (D : ℕ → Finset V) (D' : ℕ → Finset V') (e : V ≃ V')
  (hD : ∀ j v, v ∈ D j ↔ e v ∈ D' j)
  (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))

/-- Relabelling every occurrence of a regional matrix preserves the ordered
chain product. An arbitrary selection of occurrences is allowed. -/
theorem liftProd_chainList_relabel
    (K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ)
    (P : Fin m → Prop) [DecidablePred P] :
    reindex (siteConfigurationEquiv e f) (siteConfigurationEquiv e f)
        (liftProd (chainList D K P)) =
      liftProd (chainList D'
        (fun j ↦ reindex (regionConfigurationEquiv (D j) (D' j) e (hD j) f)
          (regionConfigurationEquiv (D j) (D' j) e (hD j) f) (K j)) P) := by
  have hL (j : Fin m) := localLift_relabel (D j) (D' j) e (hD j) f (K j)
  simpa only [liftProd_chainList_eq, List.map_map, Function.comp_def,
    coe_reindexAlgEquiv, hL] using
    map_list_prod (reindexAlgEquiv ℂ ℂ (siteConfigurationEquiv e f))
      ((((List.finRange m).filter fun j ↦ decide (P j)).reverse).map
        fun j : Fin m ↦ localLift (D j) (K j))

/-- The same input and regional matrices have the same ordered output in the
transported configuration basis. -/
theorem relabelVector_liftProd_chainList
    (K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ)
    (P : Fin m → Prop) [DecidablePred P] (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    relabelVector e f (toEuclideanLin (liftProd (chainList D K P)) Ω) =
      toEuclideanLin (liftProd (chainList D'
        (fun j ↦ reindex (regionConfigurationEquiv (D j) (D' j) e (hD j) f)
          (regionConfigurationEquiv (D j) (D' j) e (hD j) f) (K j)) P))
        (relabelVector e f Ω) := by
  rw [← liftProd_chainList_relabel D D' e hD f]
  ext σ
  exact (congrFun (reindex_mulVec (siteConfigurationEquiv e f)
    (liftProd (chainList D K P)) (WithLp.ofLp Ω)) σ).symm

/-- Inverse-norm normalization commutes with the same ordered-output
identification. This also holds at zero output, with inverse zero equal to zero. -/
theorem relabelVector_normalized_liftProd_chainList
    (K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ)
    (P : Fin m → Prop) [DecidablePred P] (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    let ψ := toEuclideanLin (liftProd (chainList D K P)) Ω
    let ψ' := toEuclideanLin (liftProd (chainList D'
      (fun j ↦ reindex (regionConfigurationEquiv (D j) (D' j) e (hD j) f)
        (regionConfigurationEquiv (D j) (D' j) e (hD j) f) (K j)) P))
      (relabelVector e f Ω)
    relabelVector e f (((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ) = ((‖ψ'‖⁻¹ : ℝ) : ℂ) • ψ' := by
  dsimp only
  rw [← relabelVector_liftProd_chainList D D' e hD f, norm_relabelVector]
  rfl

/-- Global output-norm comparison against every feasible competitor is
preserved in both directions. The distinguished family need not itself be
feasible, and floors and weights are arbitrary real numbers. -/
theorem forall_norm_liftProd_chainList_le_relabel_iff
    (b a : Fin m → ℝ)
    (K : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ)
    (Ω : EuclideanSpace ℂ (SiteConfig n)) :
    (∀ K' : (j : Fin m) → Matrix (RegionConfig n' (D' j)) (RegionConfig n' (D' j)) ℂ,
      (∀ j, IsFeasibleFilter (b j) (a j) (K' j)) →
      ‖toEuclideanLin (liftProd (chainList D' K' fun _ ↦ True)) (relabelVector e f Ω)‖ ≤
        ‖toEuclideanLin (liftProd (chainList D'
          (fun j ↦ reindex (regionConfigurationEquiv (D j) (D' j) e (hD j) f)
            (regionConfigurationEquiv (D j) (D' j) e (hD j) f) (K j)) fun _ ↦ True))
          (relabelVector e f Ω)‖) ↔
    (∀ K' : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ,
      (∀ j, IsFeasibleFilter (b j) (a j) (K' j)) →
      ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
        ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) := by
  let R (j : Fin m) := regionConfigurationEquiv (D j) (D' j) e (hD j) f
  have hnorm (L : (j : Fin m) → Matrix (RegionConfig n (D j)) (RegionConfig n (D j)) ℂ) :
      ‖toEuclideanLin (liftProd (chainList D'
        (fun j ↦ reindex (R j) (R j) (L j)) fun _ ↦ True)) (relabelVector e f Ω)‖ =
        ‖toEuclideanLin (liftProd (chainList D L fun _ ↦ True)) Ω‖ := by
    rw [← relabelVector_liftProd_chainList D D' e hD f, norm_relabelVector]
  constructor
  · intro h K' hK'
    rw [← hnorm K', ← hnorm K]
    exact h (fun j ↦ reindex (R j) (R j) (K' j)) (fun j ↦ (hK' j).reindex (R j))
  · intro h K' hK'
    let L (j : Fin m) := reindex (R j).symm (R j).symm (K' j)
    have hL (j : Fin m) : reindex (R j) (R j) (L j) = K' j := by
      simp [L, reindex_apply]
    have hle := h L (fun j ↦ (hK' j).reindex (R j).symm)
    rw [← hnorm L, ← hnorm K] at hle
    simpa only [hL] using hle

end Entropy
