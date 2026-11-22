/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Elementary facts on monoids and groups

* Conjugating a group element leaves its conjugacy class unchanged.
* A power of an element `W` commuting with the image of a monoid homomorphism `U` can be moved
  past a factor: `U a * W ^ n * U b = W ^ n * U (a * b)`; in particular two adjacent factors `W`
  combine to `W ^ 2`. This is the algebra used to combine weights in Schuch, Cirac, and
  Pérez-García, arXiv:1001.3807, Section 7, lines 2977–3019.
* A multiplicatively closed predicate containing the identity and every single-coordinate
  function holds on every element of a finite product of monoids, without commutativity
  assumptions.

Moved from TNLean, `TNLean/Algebra/ConjClassesConjugation.lean`,
`TNLean/Algebra/MonoidHomCommutingWeight.lean` and `TNLean/Algebra/PiMulSingleInduction.lean`
at commit `49b78ed821` (Apache-2.0). Changes: the three modules are merged.

## Main results

* `ConjClasses.mk_conjugate`
* `MonoidHom.mul_commuting_pow_mul`, `MonoidHom.mul_weight_mul_weight_mul`
* `Pi.mulSingle_induction_noncomm`
-/

namespace ConjClasses

/-- Conjugating a group element leaves its class unchanged.
Source: SCP10, Theorem 6.15, lines 2217–2267, and lines 2370–2395. -/
theorem mk_conjugate {G : Type*} [Group G] (g x : G) :
    ConjClasses.mk (x * g * x⁻¹) = ConjClasses.mk g := by
  apply mk_eq_mk_iff_isConj.mpr
  exact (isConj_iff.mpr ⟨x, rfl⟩).symm

end ConjClasses

namespace MonoidHom
variable {M N : Type*} [Monoid M] [Monoid N]

/-- A commuting weight leaves only the product of the two represented elements.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem mul_commuting_pow_mul (U : M →* N) (W : N) (hc : ∀ a, Commute W (U a))
    (n : ℕ) (a b : M) : U a * W ^ n * U b = W ^ n * U (a * b) := by
  rw [((hc a).pow_left n).eq.symm, mul_assoc, ← map_mul]

/-- Two adjacent commuting weights combine to the square of the weight.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem mul_weight_mul_weight_mul (U : M →* N) (W : N)
    (hc : ∀ a, Commute W (U a)) (a b : M) :
    (U a * W) * (W * U b) = W ^ 2 * U (a * b) := by
  simpa only [pow_two, mul_assoc] using U.mul_commuting_pow_mul W hc 2 a b
end MonoidHom

namespace Pi

/-- Induction over single-coordinate functions in a finite product of possibly noncommutative
monoids. -/
@[elab_as_elim]
theorem mulSingle_induction_noncomm {ι : Type*} [Finite ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, Monoid (M i)] (p : (Π i, M i) → Prop) (f : Π i, M i)
    (one : p 1) (mul : ∀ f g, p f → p g → p (f * g))
    (mulSingle : ∀ i m, p (Pi.mulSingle i m)) : p f := by
  cases nonempty_fintype ι
  have h (s : Finset ι) : p (fun i ↦ if i ∈ s then f i else 1) := by
    induction s using Finset.induction_on with
    | empty => simpa [Pi.one_def] using one
    | @insert a s ha ih =>
        have heq : (fun i ↦ if i ∈ insert a s then f i else 1) =
            Pi.mulSingle a (f a) * (fun i ↦ if i ∈ s then f i else 1) := by
          funext i
          by_cases hi : i = a
          · subst i
            simp [ha]
          · simp [hi]
        rw [heq]
        exact mul _ _ (mulSingle a (f a)) ih
  simpa using h Finset.univ

end Pi
