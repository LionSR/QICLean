/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Matrix.OrderedMatrixAction
import QICLean.ManyBody.Entropy.Filter.FilterFeasibility
import QICLean.ManyBody.Entropy.Filter.Maximizer
import QICLean.ManyBody.Sites.Relabel

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
open ManyBody (siteConfigurationEquiv regionConfigurationEquiv complementConfigurationEquiv
  relabelVector norm_relabelVector)

namespace Entropy

variable {V V' : Type*} [Fintype V] [DecidableEq V]
  [Fintype V'] [DecidableEq V'] {n : V → ℕ} {n' : V' → ℕ} {m : ℕ}

/-- The ascending list of local actions gives exactly the reverse product
used by the filter chain. No commutation or nesting is assumed. -/
theorem foldl_localLift_eq_liftProd_chainList (D : ℕ → Finset V)
    (K : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ)
    (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    (List.ofFn fun j ↦
      toEuclideanCLM (n := (∀ v, Fin (n v))) (𝕜 := ℂ) (ManyBody.place (D j) (K j))).foldl
        (fun ψ T ↦ T ψ) Ω =
      toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω := by
  simpa [liftProd_chainList_eq, List.ofFn_eq_map, List.map_reverse,
    List.map_map, Function.comp_def] using
    foldl_toEuclideanCLM_eq_reverse_prod
      (List.ofFn fun j ↦ ManyBody.place (D j) (K j)) Ω

/-- Relabelling sites and local basis labels commutes with a local lift,
including empty regions and empty configuration types. -/
theorem localLift_relabel (D : Finset V) (D' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D')
    (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))
    (K : Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D)
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) D) ℂ) :
    reindex (siteConfigurationEquiv (X' := fun v ↦ Fin (n' v)) e f)
        (siteConfigurationEquiv (X' := fun v ↦ Fin (n' v)) e f) (ManyBody.place D K) =
      ManyBody.place D' (reindex (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) D D' e hD f)
        (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) D D' e hD f) K) := by
  let R := regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) D D' e hD f
  let C := complementConfigurationEquiv (X := fun v ↦ Fin (n v)) (X' := fun v ↦ Fin (n' v))
    D D' e hD f
  ext σ τ
  simp only [ManyBody.place, reindex_apply, submatrix_apply]
  change K (R.symm ((ManyBody.cutEquiv (fun v ↦ Fin (n' v)) D') σ).1)
      (R.symm ((ManyBody.cutEquiv (fun v ↦ Fin (n' v)) D') τ).1) *
      (if C.symm ((ManyBody.cutEquiv (fun v ↦ Fin (n' v)) D') σ).2 = C.symm
          ((ManyBody.cutEquiv (fun v ↦ Fin (n' v)) D') τ).2 then 1 else 0) =
    K (R.symm ((ManyBody.cutEquiv (fun v ↦ Fin (n' v)) D') σ).1)
        (R.symm ((ManyBody.cutEquiv (fun v ↦ Fin (n' v)) D') τ).1) *
      (if ((ManyBody.cutEquiv (fun v ↦ Fin (n' v)) D') σ).2 =
          ((ManyBody.cutEquiv (fun v ↦ Fin (n' v)) D') τ).2 then 1 else 0)
  simp only [C.symm.injective.eq_iff]

variable (D : ℕ → Finset V) (D' : ℕ → Finset V') (e : V ≃ V')
  (hD : ∀ j v, v ∈ D j ↔ e v ∈ D' j)
  (f : ∀ v, Fin (n v) ≃ Fin (n' (e v)))

/-- Relabelling every occurrence of a regional matrix preserves the ordered
chain product. An arbitrary selection of occurrences is allowed. -/
theorem liftProd_chainList_relabel
    (K : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ)
    (P : Fin m → Prop) [DecidablePred P] :
    reindex (siteConfigurationEquiv (X' := fun v ↦ Fin (n' v)) e f)
        (siteConfigurationEquiv (X' := fun v ↦ Fin (n' v)) e f) (liftProd (chainList D K P)) =
      liftProd (chainList D'
        (fun j ↦ reindex
          (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f)
          (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f)
          (K j)) P) := by
  have hL (j : Fin m) := localLift_relabel (D j) (D' j) e (hD j) f (K j)
  simpa only [liftProd_chainList_eq, List.map_map, Function.comp_def,
    coe_reindexAlgEquiv, hL] using
    map_list_prod
      (reindexAlgEquiv ℂ ℂ (siteConfigurationEquiv (X' := fun v ↦ Fin (n' v)) e f))
      ((((List.finRange m).filter fun j ↦ decide (P j)).reverse).map
        fun j : Fin m ↦ ManyBody.place (D j) (K j))

/-- The same input and regional matrices have the same ordered output in the
transported configuration basis. -/
theorem relabelVector_liftProd_chainList
    (K : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ)
    (P : Fin m → Prop) [DecidablePred P] (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    relabelVector (X' := fun v ↦ Fin (n' v)) e f
        (toEuclideanLin (liftProd (chainList D K P)) Ω) =
      toEuclideanLin (liftProd (chainList D'
        (fun j ↦ reindex
          (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f)
          (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f)
          (K j)) P))
        (relabelVector (X' := fun v ↦ Fin (n' v)) e f Ω) := by
  rw [← liftProd_chainList_relabel D D' e hD f]
  ext σ
  exact (congrFun (reindex_mulVec (siteConfigurationEquiv (X' := fun v ↦ Fin (n' v)) e f)
    (liftProd (chainList D K P)) (WithLp.ofLp Ω)) σ).symm

/-- Inverse-norm normalization commutes with the same ordered-output
identification. This also holds at zero output, with inverse zero equal to zero. -/
theorem relabelVector_normalized_liftProd_chainList
    (K : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ)
    (P : Fin m → Prop) [DecidablePred P] (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    let ψ := toEuclideanLin (liftProd (chainList D K P)) Ω
    let ψ' := toEuclideanLin (liftProd (chainList D'
      (fun j ↦ reindex
          (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f)
        (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f)
        (K j)) P))
      (relabelVector (X' := fun v ↦ Fin (n' v)) e f Ω)
    relabelVector (X' := fun v ↦ Fin (n' v)) e f (((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ) =
      ((‖ψ'‖⁻¹ : ℝ) : ℂ) • ψ' := by
  dsimp only
  rw [← relabelVector_liftProd_chainList D D' e hD f, norm_relabelVector]
  rfl

/-- Global output-norm comparison against every feasible competitor is
preserved in both directions. The distinguished family need not itself be
feasible, and floors and weights are arbitrary real numbers. -/
theorem forall_norm_liftProd_chainList_le_relabel_iff
    (b a : Fin m → ℝ)
    (K : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ)
    (Ω : EuclideanSpace ℂ (∀ v, Fin (n v))) :
    (∀ K' : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n' v)) (D' j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n' v)) (D' j)) ℂ,
      (∀ j, IsFeasibleFilter (b j) (a j) (K' j)) →
      ‖toEuclideanLin (liftProd (chainList D' K' fun _ ↦ True))
          (relabelVector (X' := fun v ↦ Fin (n' v)) e f Ω)‖ ≤
        ‖toEuclideanLin (liftProd (chainList D'
          (fun j ↦ reindex
          (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f)
            (regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f)
            (K j)) fun _ ↦ True))
          (relabelVector (X' := fun v ↦ Fin (n' v)) e f Ω)‖) ↔
    (∀ K' : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
        (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ,
      (∀ j, IsFeasibleFilter (b j) (a j) (K' j)) →
      ‖toEuclideanLin (liftProd (chainList D K' fun _ ↦ True)) Ω‖ ≤
        ‖toEuclideanLin (liftProd (chainList D K fun _ ↦ True)) Ω‖) := by
  let R (j : Fin m) :=
    regionConfigurationEquiv (X' := fun v ↦ Fin (n' v)) (D j) (D' j) e (hD j) f
  have hnorm
      (L : (j : Fin m) → Matrix (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j))
      (ManyBody.RegionConfig (fun v ↦ Fin (n v)) (D j)) ℂ) :
      ‖toEuclideanLin (liftProd (chainList D'
        (fun j ↦ reindex (R j) (R j) (L j)) fun _ ↦ True))
          (relabelVector (X' := fun v ↦ Fin (n' v)) e f Ω)‖ =
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
