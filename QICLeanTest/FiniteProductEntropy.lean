/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.TwoFamilies
import QICLean.Entropy.FiniteProductConditional
import Mathlib.Tactic.NormNum

/-! Regression checks for actual finite-product density matrices and entropies. -/

open scoped Matrix BigOperators ComplexOrder

/-- A genuinely complex coefficient matrix makes the conjugation in the second
Gram marginal visible. This is deliberately not a real-vector regression. -/
def complexCoefficients : Bool × Bool → ℂ
  | (false, false) => 1
  | (false, true) => Complex.I
  | _ => 0

example : Matrix.partialTraceLeft
    (Matrix.vecMulVec complexCoefficients (star complexCoefficients)) false true =
      -Complex.I := by
  norm_num [Matrix.partialTraceLeft_apply, Matrix.vecMulVec_apply,
    complexCoefficients, Fintype.sum_bool]

example : ((Matrix.schmidtCoeffMatrix complexCoefficients)ᴴ *
    Matrix.schmidtCoeffMatrix complexCoefficients) false true = Complex.I := by
  norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.schmidtCoeffMatrix_apply, complexCoefficients, Fintype.sum_bool]

example :
    vonNeumannEntropy (Matrix.partialTraceRight
        (Matrix.vecMulVec complexCoefficients (star complexCoefficients)))
      (Matrix.posSemidef_vecMulVec_self_star _).partialTraceRight.isHermitian =
    vonNeumannEntropy (Matrix.partialTraceLeft
        (Matrix.vecMulVec complexCoefficients (star complexCoefficients)))
      (Matrix.posSemidef_vecMulVec_self_star _).partialTraceLeft.isHermitian :=
  Entropy.pure_marginal_entropy_eq _

/-- Varying local dimensions, including a one-dimensional factor. -/
def heterogeneousDimension : Fin 3 → ℕ := ![1, 2, 3]

example (ψ : EuclideanSpace ℂ ((v : Fin 3) → Fin (heterogeneousDimension v)))
    (R : Finset (Fin 3)) :
    FiniteProduct.entropy (fun v ↦ Fin (heterogeneousDimension v)) ψ Rᶜ =
      FiniteProduct.entropy (fun v ↦ Fin (heterogeneousDimension v)) ψ R :=
  FiniteProduct.entropy_compl _ ψ R

/-- Both ordered families may be empty, with no restrictions on the remainder. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) (D : Finset V) :
    FiniteProduct.entropy β ψ D ≤ FiniteProduct.entropy β ψ D +
      (1 / 2) * ((∑ _i ∈ (∅ : Finset ℤ), (0 : ℝ)) +
        ∑ _j ∈ (∅ : Finset ℚ), (0 : ℝ)) := by
  apply FiniteProduct.entropy_le_remainder_add_half_sum β ψ hψ D D
    (fun _ : ℤ ↦ ∅) ∅ (fun _ : ℚ ↦ ∅) ∅
  all_goals simp

/-- The empty region has a single product-basis configuration even with no
nonemptiness assumption on the individual local bases. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] :
    Fintype.card (FiniteProduct.Configuration β ∅) = 1 := by simp

/-- A normalized entangled vector in dimensions two and three; its second
marginal is singular, so no invertibility assumption can enter the API. -/
noncomputable def entangledVector : EuclideanSpace ℂ (Fin 2 × Fin 3) :=
  WithLp.toLp 2 fun p ↦ if p = (0, 0) then (3 / 5 : ℂ) else
    if p = (1, 1) then (4 / 5 : ℂ) else 0

example : ‖entangledVector‖ = 1 := by
  have hinner : inner (𝕜 := ℂ) entangledVector entangledVector = 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    norm_num [dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_succ, entangledVector, map_ofNat]
  have hn := inner_self_eq_norm_sq (𝕜 := ℂ) entangledVector
  rw [hinner] at hn
  have hs : ‖entangledVector‖ ^ 2 = (1 : ℝ) := by simpa using hn.symm
  nlinarith [norm_nonneg entangledVector]

example : (Matrix.partialTraceLeft
    (Matrix.vecMulVec (WithLp.ofLp entangledVector) (star (WithLp.ofLp entangledVector))))
      2 2 = 0 := by
  norm_num [Matrix.partialTraceLeft_apply, Matrix.vecMulVec_apply,
    entangledVector, Fin.sum_univ_succ]

example : (Matrix.partialTraceLeft
    (Matrix.vecMulVec (WithLp.ofLp entangledVector)
      (star (WithLp.ofLp entangledVector)))).det = 0 := by
  norm_num [Matrix.det_fin_three, Matrix.partialTraceLeft_apply, Matrix.vecMulVec_apply,
    entangledVector, Fin.sum_univ_succ]

/-- One family is empty and the remainder is empty. The nonempty family
contains the whole region, with the exterior information bound supplied as input. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1)
    (R : Finset V) (ε : ℝ) (hε : FiniteProduct.mutualInformation β ψ R Rᶜ ≤ ε) :
    FiniteProduct.entropy β ψ R ≤ (1 / 2) * ε := by
  have h := FiniteProduct.entropy_le_remainder_add_half_sum β ψ hψ R ∅
    (fun _ : ℤ ↦ ∅) ∅ (fun _ : ℤ ↦ R) {0}
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _ ↦ 0) (fun _ ↦ ε) (by simp)
    (by
      intro i hi
      simp only [Finset.mem_singleton] at hi
      subst i
      simpa [Entropy.OrderedSetFunction.past, Finset.filter_singleton] using hε)
  simpa [FiniteProduct.entropy_empty β ψ hψ] using h

/-- A nonempty index family of empty tiles is permitted by the physical result. -/
example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) (D : Finset V) :
    FiniteProduct.entropy β ψ D ≤ FiniteProduct.entropy β ψ D := by
  have h := FiniteProduct.entropy_le_remainder_add_half_sum β ψ hψ D D
    (fun _ : ℤ ↦ ∅) {0} (fun _ : ℚ ↦ ∅) ∅
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (fun _ ↦ 0) (fun _ ↦ 0)
    (by intro i hi; simp [FiniteProduct.mutualInformation,
          FiniteProduct.entropy_empty β ψ hψ, Entropy.OrderedSetFunction.past])
    (by simp)
  simpa only [Finset.sum_empty, Finset.sum_singleton, add_zero, mul_zero] using h

example {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ψ : EuclideanSpace ℂ ((v : V) → β v)) (hψ : ‖ψ‖ = 1) :
    FiniteProduct.entropy β ψ ∅ = 0 ∧ FiniteProduct.entropy β ψ Finset.univ = 0 :=
  ⟨FiniteProduct.entropy_empty β ψ hψ, FiniteProduct.entropy_univ β ψ hψ⟩

/--
info: 'FiniteProduct.trace_reducedPure' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.trace_reducedPure

/--
info: 'FiniteProduct.partialTraceRight_reducedMatrix_union' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.partialTraceRight_reducedMatrix_union

/--
info: 'FiniteProduct.partialTraceLeft_reducedMatrix_union' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.partialTraceLeft_reducedMatrix_union

/--
info: 'Entropy.subadditivity' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.subadditivity

/--
info: 'Entropy.pure_marginal_entropy_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms Entropy.pure_marginal_entropy_eq

/--
info: 'FiniteProduct.entropy_compl' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.entropy_compl

/--
info: 'FiniteProduct.entropy_union_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.entropy_union_le

/--
info: 'FiniteProduct.mutualInformation_eq_matrix' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.mutualInformation_eq_matrix

/--
info: 'FiniteProduct.entropy_le_remainder_add_half_mutualInformation' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.entropy_le_remainder_add_half_mutualInformation

/--
info: 'FiniteProduct.entropy_le_remainder_add_half_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.entropy_le_remainder_add_half_sum

/--
info: 'FiniteProduct.conditionalMutualInformation_eq_sub' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.conditionalMutualInformation_eq_sub

/--
info: 'FiniteProduct.conditionalMutualInformation_le_mutualInformation_union' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.conditionalMutualInformation_le_mutualInformation_union

/--
info: 'FiniteProduct.conditionalMutualInformation_pure_duality' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.conditionalMutualInformation_pure_duality

/--
info: 'FiniteProduct.sum_conditionalMutualInformation_past' depends on axioms:
[propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms FiniteProduct.sum_conditionalMutualInformation_past
