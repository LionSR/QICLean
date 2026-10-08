/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaIntegral
import QICLean.Representation.CoherentResolution
import QICLean.Entropy.LocalLift

/-!
# The integral representation in lifted form

On `V = ⨂_v ℂ^{n_v}` a one-copy operator `M` on a region `Q` acts on `V` as its local lift
`M ⊗ 1`, and on `V^{⊗k}` as `(M ⊗ 1)^{⊗k}`. This file rewrites the integral representation of
the replica metrics (`05-replicas.tex`, equation `replicas:W-integral`) in this form,
`W_{Q,k} = ∫ ((τ^t ⊗ 1)^{⊗k}) dζ_Q(τ)`, as used in the proof of Lemma 6.3 (lines 553–559), and
records the norm of a tensor-power vector, `‖v^{⊗k}‖ = ‖v‖^k`.

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.reindex_tensorPow_localLift` — `(M ⊗ 1)^{⊗k} = M^{⊗k} ⊗ 1` after `splitEquiv`.
* `TensorPower.exists_replicaMetric_integral_localLift`.
* `TensorPower.norm_tensorVec` — `‖v^{⊗k}‖ = ‖v‖^k`.
-/

open MeasureTheory Matrix Finset PermutationRepresentation Entropy
open scoped MatrixOrder ComplexOrder Kronecker

namespace TensorPower

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

theorem localLift_splitEquiv_apply (Q : Finset V)
    (M : Matrix (RegionConfig n Q) (RegionConfig n Q) ℂ)
    (a b : RegionConfig n Q) (c c' : (v : {v // v ∉ Q}) → Fin (n v)) :
    localLift Q M ((cutEquiv n Q).symm (a, c)) ((cutEquiv n Q).symm (b, c')) =
      M a b * if c = c' then 1 else 0 := by
  simp only [localLift, reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    kroneckerMap_apply, one_apply]

omit [Fintype V] in
theorem splitEquiv_symm_apply_eq (k : ℕ) (Q : Finset V)
    (p : (Fin k → RegionConfig n Q) × (Fin k → (v : {v // v ∉ Q}) → Fin (n v))) (j : Fin k) :
    (splitEquiv (fun v => Fin (n v)) k Q).symm p j = (cutEquiv n Q).symm (p.1 j, p.2 j) := by
  funext v
  by_cases h : v ∈ Q <;> simp [splitEquiv, Equiv.piEquivPiSubtypeProd, h]

/-- The tensor power of a local lift, in split coordinates. -/
theorem reindex_tensorPow_localLift (k : ℕ) (Q : Finset V)
    (M : Matrix (RegionConfig n Q) (RegionConfig n Q) ℂ) :
    reindex (splitEquiv (fun v => Fin (n v)) k Q) (splitEquiv (fun v => Fin (n v)) k Q)
        (tensorPow (k := k) (localLift Q M)) =
      tensorPow (k := k) M ⊗ₖ (1 : Matrix (Fin k → (v : {v // v ∉ Q}) → Fin (n v))
        (Fin k → (v : {v // v ∉ Q}) → Fin (n v)) ℂ) := by
  ext p p'
  simp only [reindex_apply, submatrix_apply, kroneckerMap_apply, tensorPow_apply,
    splitEquiv_symm_apply_eq, localLift_splitEquiv_apply, prod_mul_distrib, one_apply]
  congr 1
  by_cases h : p.2 = p'.2
  · simp [h]
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [ite_eq_right h, prod_eq_zero (mem_univ j) (ite_eq_right hj)]

theorem reindex_injective {α β : Type*} (e : α ≃ β) {A B : Matrix α α ℂ}
    (h : reindex e e A = reindex e e B) : A = B :=
  (reindex e e).injective h

/-- **The integral representation in lifted form** (`05-replicas.tex`, equation
`replicas:W-integral`): `W_{Q,k} = ∫ ((τ^t ⊗ 1)^{⊗k}) dζ_Q(τ)` on `V^{⊗k}`, for
`0 < t ≤ 1` and every region `Q`. -/
theorem exists_replicaMetric_integral_localLift [∀ v, NeZero (n v)] {t : ℝ} (ht0 : 0 < t)
    (ht1 : t ≤ 1) (Q : Finset V) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P ∧
      ∃ τ : Ω → Matrix (RegionConfig n Q) (RegionConfig n Q) ℂ,
        (∀ᵐ ω ∂P, (τ ω).PosDef ∧ (τ ω).trace.re ≤ 1) ∧
        (∀ (k : ℕ) (x y : Config k fun v => Fin (n v)),
          Integrable (fun ω => tensorPow (k := k) (localLift Q (τ ω ^ t)) x y) P) ∧
        ∀ (k : ℕ) (x y : Config k fun v => Fin (n v)),
          replicaMetric (fun v => Fin (n v)) t k Q x y =
            ∫ ω, tensorPow (k := k) (localLift Q (τ ω ^ t)) x y ∂P := by
  have : ∀ v, Nonempty (Fin (n v)) := fun v => ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨Ω, _, P, hP, τ, hτ, hint, heq⟩ :=
    exists_replicaMetric_integral (fun v => Fin (n v)) ht0 ht1 Q
  have hentry : ∀ (k : ℕ) (x y : Config k fun v => Fin (n v)) (ω : Ω),
      tensorPow (k := k) (localLift Q (τ ω ^ t)) x y =
        tensorPow (k := k) (τ ω ^ t) (splitEquiv _ k Q x).1 (splitEquiv _ k Q y).1 *
          (1 : Matrix (Fin k → (v : {v // v ∉ Q}) → Fin (n v))
            (Fin k → (v : {v // v ∉ Q}) → Fin (n v)) ℂ) (splitEquiv _ k Q x).2
              (splitEquiv _ k Q y).2 := by
    intro k x y ω
    have h := congrFun (congrFun (reindex_tensorPow_localLift k Q (τ ω ^ t))
      (splitEquiv _ k Q x)) (splitEquiv _ k Q y)
    simpa [reindex_apply, kroneckerMap_apply] using h
  refine ⟨Ω, inferInstance, P, hP, τ, hτ, fun k x y => ?_, fun k x y => ?_⟩
  · simp only [hentry]
    exact (hint k _ _).mul_const _
  · have h := congrFun (congrFun (heq k) (splitEquiv _ k Q x)) (splitEquiv _ k Q y)
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply,
      of_apply] at h
    rw [h]
    simp only [hentry]
    rw [integral_mul_const]

/-! ### Tensor-power vectors -/

section Vectors

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem norm_tensorVec (k : ℕ) (v : Ω → ℂ) :
    ‖(EuclideanSpace.equiv (Fin k → Ω) ℂ).symm (tensorVec k v)‖ =
      ‖(EuclideanSpace.equiv Ω ℂ).symm v‖ ^ k := by
  have h2 : ‖(EuclideanSpace.equiv (Fin k → Ω) ℂ).symm (tensorVec k v)‖ ^ 2 =
      (‖(EuclideanSpace.equiv Ω ℂ).symm v‖ ^ k) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _), ← pow_mul,
      mul_comm, pow_mul, EuclideanSpace.norm_eq,
      Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
    change ∑ x, ‖tensorVec k v x‖ ^ 2 = (∑ i, ‖v i‖ ^ 2) ^ k
    simp only [tensorVec, norm_prod]
    rw [show (∑ i : Ω, ‖v i‖ ^ 2) ^ k = ∏ _j : Fin k, ∑ i : Ω, ‖v i‖ ^ 2 by simp,
      Fintype.prod_sum]
    simp only [← prod_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (pow_nonneg (norm_nonneg _) _) two_ne_zero).mp h2

end Vectors

end TensorPower
