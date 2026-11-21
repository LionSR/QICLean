/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.Algebra.Star.LinearMap

/-!
# Pre-bialgebras

A `PreBialgebra R A` structure on an `R`-algebra `A` is a coalgebra structure on `A`, in the
sense of Mathlib's `Coalgebra` (a coassociative comultiplication `Δ` with a counit `ε`
satisfying `(ε ⊗ id) ∘ Δ = (id ⊗ ε) ∘ Δ = id`), whose comultiplication is multiplicative,
`Δ(xy) = Δ(x) Δ(y)`.  This is the pre-bialgebra of Molnár et al., arXiv:2204.05940, `mpo.tex`,
Definition 4.1 (lines 1409--1414), with the coalgebra of Definition 3.1 (lines 866--875).

No compatibility of the counit with the unit or the product is imposed (line 1407), and
`Δ(1)` need not be `1 ⊗ 1` (lines 1421 and 1708, equation `eq:delta_epsilon`); multiplicativity
only makes `Δ(1)` an idempotent.  Mathlib's `Bialgebra` requires both a multiplicative unital
counit and `Δ(1) = 1 ⊗ 1`; the second condition fails for the coproducts of the source (lines
1421 and 1708).  Every bialgebra is a pre-bialgebra (`Bialgebra.toPreBialgebra`).

The source works over `ℂ` with finite-dimensional spaces; the structure here is stated over any
commutative semiring.

For a coalgebra whose comultiplication preserves the involution, the intrinsic involution of
its scalar-valued dual preserves the order of convolution: `κ(f * g) = κ(f) * κ(g)`, where
`κ(f)(x) = star (f (star x))`. This is a multiplicative equivalence, not an anti-multiplicative
star-ring structure. Its preservation of the convolution unit follows from bijectivity, so no
separate compatibility condition on the counit is needed.

Moved from TNLean, `TNLean/Algebra/PreBialgebra.lean` and `TNLean/Algebra/CoalgebraDualStar.lean`
at commit `49b78ed821` (Apache-2.0). Changes: the two files are merged.

## Main definitions

* `PreBialgebra R A`: a coalgebra structure on the algebra `A` with multiplicative
  comultiplication.
* `Coalgebra.dualStarMulEquiv`: the involution of the convolution dual as a multiplicative
  equivalence.

## Main results

* `Coalgebra.dualStar_mul`, `Coalgebra.dualStar_one`: the involution of the convolution dual
  preserves products and the unit.

## References

* Molnár, Ruiz-de-Alarcón, Garre-Rubio, Schuch, Cirac, Pérez-García, arXiv:2204.05940,
  `mpo.tex`, Definition 3.1 (coalgebra, lines 866--875), Definition 4.1 (pre-bialgebra,
  lines 1409--1414), and lines 1415--1421 and 1708; Definition 5.8 and Proposition 5.4.
* Garre-Rubio, Lootens, Molnár, arXiv:2203.12563v3, lines 1236--1320.
* arXiv:2509.03600.
-/

open TensorProduct

universe u v

/-- A **pre-bialgebra** structure on an `R`-algebra `A`: a coalgebra structure on `A`
(a coassociative comultiplication `Δ` with a counit `ε` satisfying the two counit laws) whose
comultiplication is multiplicative, `Δ(xy) = Δ(x) Δ(y)`.

Neither `Δ 1 = 1 ⊗ 1` nor any compatibility of `ε` with the unit or the product is required.

Source: arXiv:2204.05940, `mpo.tex`, Definition 4.1 (lines 1409--1414), with the coalgebra of
Definition 3.1 (lines 866--875). -/
class PreBialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A]
    extends Coalgebra R A where
  /-- The comultiplication is multiplicative.

  Source: arXiv:2204.05940, `mpo.tex`, Definition 4.1 (lines 1409--1414). -/
  comul_mul : ∀ a b : A, comul (a * b) = comul a * comul b

/-- Every bialgebra is a pre-bialgebra, by forgetting that the counit is an algebra
homomorphism and that the comultiplication is unital. -/
instance Bialgebra.toPreBialgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A]
    [Bialgebra R A] : PreBialgebra R A where
  toCoalgebra := inferInstance
  comul_mul := Bialgebra.comul_mul

noncomputable section

open WithConv
open scoped TensorProduct

namespace Coalgebra

variable {R H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid H] [Module R H] [StarAddMonoid H] [StarModule R H]
  [Coalgebra R H]

/-- A star-preserving comultiplication induces a same-order multiplicative
involution of the scalar-valued convolution dual. The tensor factors are not
exchanged. -/
theorem dualStar_mul
    (hcomul : ∀ x : H, comul (R := R) (star x) = star (comul (R := R) x))
    (f g : WithConv (H →ₗ[R] R)) : star (f * g) = star f * star g := by
  ext x
  simp only [LinearMap.intrinsicStar_apply, LinearMap.convMul_apply, hcomul]
  have ht (t : H ⊗[R] H) :
      star (LinearMap.mul' R R (_root_.TensorProduct.map f.ofConv g.ofConv (star t))) =
        LinearMap.mul' R R
          (_root_.TensorProduct.map (star f).ofConv (star g).ofConv t) := by
    induction t using TensorProduct.inductionOn with
    | tmul a b => simp
    | add t u ht hu => simp only [star_add, map_add, ht, hu]
  exact ht (comul x)

/-- The involution of the convolution dual, regarded as a multiplicative
equivalence. Its unit law follows from the same-order product law and
involutivity. -/
def dualStarMulEquiv
    (hcomul : ∀ x : H, comul (R := R) (star x) = star (comul (R := R) x)) :
    WithConv (H →ₗ[R] R) ≃* WithConv (H →ₗ[R] R) where
  toFun := star
  invFun := star
  left_inv := star_star
  right_inv := star_star
  map_mul' := dualStar_mul hcomul

/-- Counit compatibility follows from the comultiplication compatibility:
the intrinsic involution fixes the convolution unit. -/
theorem dualStar_one
    (hcomul : ∀ x : H, comul (R := R) (star x) = star (comul (R := R) x)) :
    star (1 : WithConv (H →ₗ[R] R)) = 1 :=
  (dualStarMulEquiv hcomul).map_one

end Coalgebra
