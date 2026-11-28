/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Basic.Complex.Basic

/-!
# Computational equivalences of star-subalgebras

These are the star-preserving forms of the existing subalgebra
identifications by an injective homomorphism and by equality. Their
underlying maps are exactly the Mathlib algebra equivalences. They keep
the ambient value of every element explicit when coordinates are
prescribed on a subalgebra, as in Schumacher–Werner bruleU/bruleV and the
translation of factors in defBBq, quant-ph/0405174, lines 980–1001 and
1199–1226.

Moved from TNLean, `TNLean/Algebra/StarSubalgebraEquiv.lean`
at commit `49b78ed821` (Apache-2.0).

Moved from TNLean, `TNLean/Algebra/CyclicMomentRigidity.lean` at commit `021ba0bd19` (Apache-2.0).
-/

namespace StarSubalgebra

variable {R A B : Type*} [CommSemiring R] [StarRing R]
  [Ring A] [Algebra R A] [StarRing A] [StarModule R A]
  [Ring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- The restriction of an injective star-algebra homomorphism identifies
an actual star-subalgebra with its image. This retains the underlying
Mathlib subalgebra equivalence, adding only preservation of star. -/
noncomputable def equivMapOfInjective (S : StarSubalgebra R A)
    (f : A →⋆ₐ[R] B) (hf : Function.Injective f) :
    S ≃⋆ₐ[R] S.map f :=
  StarAlgEquiv.ofAlgEquiv (S.toSubalgebra.equivMapOfInjective f.toAlgHom hf)
    (fun x => Subtype.ext (map_star f (x : A)))

/-- The image equivalence evaluates as the original ambient map. -/
@[simp] theorem equivMapOfInjective_coe (S : StarSubalgebra R A)
    (f : A →⋆ₐ[R] B) (hf : Function.Injective f) (x : S) :
    (S.equivMapOfInjective f hf x : B) = f (x : A) := rfl

/-- Equal star-subalgebras are identified without changing ambient
values, using Mathlib's equality equivalence for their subalgebras. -/
def equivOfEq (S T : StarSubalgebra R A) (h : S = T) : S ≃⋆ₐ[R] T :=
  StarAlgEquiv.ofAlgEquiv
    (S.toSubalgebra.equivOfEq T.toSubalgebra (congrArg StarSubalgebra.toSubalgebra h))
    (fun _ => Subtype.ext rfl)

/-- The equality equivalence leaves every ambient value unchanged. -/
@[simp] theorem equivOfEq_coe (S T : StarSubalgebra R A) (h : S = T) (x : S) :
    (S.equivOfEq T h x : A) = (x : A) := rfl

end StarSubalgebra

namespace LinearMap

variable {A B : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B]

/-- Two-point, three-point, and reflected four-point contractions determine
multiplicativity when the target functional is faithful on adjoint squares. -/
theorem map_mul_of_reflected_moments (V : B →ₗ[ℂ] A)
    (τA : A →ₗ[ℂ] ℂ) (τB : B →ₗ[ℂ] ℂ)
    (hstar : ∀ x, V (star x) = star (V x))
    (hfaithful : ∀ a, τA (star a * a) = 0 → a = 0)
    (h₂ : ∀ x y, τA (V x * V y) = τB (x * y))
    (h₃ : ∀ x y z, τA (V x * V y * V z) = τB (x * y * z))
    (h₄ : ∀ x y, τA ((star (V y) * star (V x)) * (V x * V y)) =
      τB ((star y * star x) * (x * y))) (x y : B) :
    V (x * y) = V x * V y := by
  symm
  apply sub_eq_zero.mp
  apply hfaithful
  rw [star_sub, sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub]
  rw [star_mul, h₄]
  rw [← hstar y, ← hstar x, ← hstar (x * y), h₃]
  rw [← mul_assoc (V (star (x * y))) (V x) (V y), h₃, h₂]
  simp only [mul_assoc, sub_self]

end LinearMap
