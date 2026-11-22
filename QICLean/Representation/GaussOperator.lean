/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Basic.Complex.Basic
import QICLean.Algebra.Matrix.MonomialMatrix
import QICLean.Algebra.Unitary.UnitaryFactorizationComparison
import QICLean.Representation.Twirl.FiniteGroupUnitaryAverage

/-!
# Local Gauss operators of a finite group

For a finite group `G`, the gauge labels transform by

`T_g(a,b) = (a * g⁻¹, g * b)`.

Given unitary matter operators `R a b`, the corresponding local Gauss operator
has the block from `(a,b)` to `T_g(a,b)` equal to

`(R (T_g(a,b)))⁻¹ * R a b`.

The local Gauss operators form a unitary representation of `G`, which is the
representation part of FBC25, Proposition `prop:gausslaws` and Equation `eq:mcG`
(arXiv:2502.20257, lines 3380--3387). Its normalized average is the local
projector of FBC25, Equation `eq:gauge_projs` (arXiv:2502.20257,
lines 3494--3499), and it is a star projection.

When every matter unitary $U_{a,b}$ is a monomial matrix
$U_{a,b}\ket{i}=\varphi_{a,b}(i)\ket{\sigma_{a,b}(i)}$, the local Gauss
operator

$\widetilde{\mathcal G}_g=\sum_{a,b}U_{T_g(a,b)}^\dagger U_{a,b}
  \otimes\ket{T_g(a,b)}\bra{a,b}$

is again a monomial matrix. Its permutation part sends $(i,(a,b))$ to
$(\sigma_{T_g(a,b)}^{-1}\sigma_{a,b}(i),T_g(a,b))$, and its phase is
$\overline{\varphi_{T_g(a,b)}(\sigma_{T_g(a,b)}^{-1}\sigma_{a,b}(i))}\,
\varphi_{a,b}(i)$.

Placement of these operators on the sites of a chain, and invariance of a gauged
state under them, are not treated here.

## Main results

* `GaussLaw.gaussRepresentation`: the local Gauss operators form a unitary
  representation of `G`.
* `GaussLaw.isStarProjection_gaussProjector`: their normalized average is a
  star projection.
* `GaussLaw.gaussOperator_eq_monomial`: the local Gauss operator of monomial
  matter unitaries is monomial.

Moved from TNLean, `TNLean/Algebra/GaussRepresentation.lean`,
`TNLean/Algebra/GaussProjector.lean` and `TNLean/Algebra/MonomialGaussOperator.lean` at
commit `49b78ed821` (Apache-2.0). Changes: the three modules are merged into one, and
the namespace `TNLean.Algebra` becomes `GaussLaw`.
-/
noncomputable section

namespace GaussLaw

section Representation

variable {G n : Type*} [Group G]

/-- The two-leg gauge-label permutation
`T_g(a,b) = (a * g⁻¹, g * b)` from FBC25, Equation `eq:mcG`
(arXiv:2502.20257, lines 3380--3387). -/
def gaussLegAction (g : G) : G × G ≃ G × G where
  toFun p := (p.1 * g⁻¹, g * p.2)
  invFun p := (p.1 * g, g⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp]
theorem gaussLegAction_apply (g : G) (a b : G) :
    gaussLegAction g (a, b) = (a * g⁻¹, g * b) :=
  rfl

@[simp]
theorem gaussLegAction_one : gaussLegAction (1 : G) = 1 := by
  ext p <;> simp [gaussLegAction]

/-- The paper's label permutations compose in representation order:
`T_g ∘ T_h = T_{g * h}`. -/
theorem gaussLegAction_mul (g h : G) :
    gaussLegAction g * gaussLegAction h = gaussLegAction (g * h) := by
  ext p <;> simp [gaussLegAction, mul_assoc]

variable [Fintype n] [DecidableEq n]

/-- The local Gauss operator whose unique nonzero gauge block in column
`(a,b)` lies in row `T_g(a,b)` and equals
`(R (T_g(a,b)))⁻¹ R(a,b)`.

This is exactly
`G_g = ∑_{a,b} λ_{a,b}^{a g⁻¹,g b} ⊗ |a g⁻¹,g b⟩⟨a,b|`
from FBC25, Equation `eq:mcG` (arXiv:2502.20257, lines 3380--3387), with
`λ` supplied by `Matrix.unitaryFactorizationComparison`. -/
def gaussOperator (R : G → G → Matrix.unitaryGroup n ℂ) (g : G) :
    Matrix (n × (G × G)) (n × (G × G)) ℂ := by
  classical
  exact fun x y ↦
    if x.2 = gaussLegAction g y.2 then
      (Matrix.unitaryFactorizationComparison R y.2.1 y.2.2 x.2.1 x.2.2 :
        Matrix n n ℂ) x.1 y.1
    else 0

/-- The nonzero block of the Gauss operator is the factorization comparison
specified in FBC25, Equation `eq:mcG`. -/
@[simp]
theorem gaussOperator_apply_target
    (R : G → G → Matrix.unitaryGroup n ℂ) (g a b : G) (i j : n) :
    gaussOperator R g (i, gaussLegAction g (a, b)) (j, (a, b)) =
      (Matrix.unitaryFactorizationComparison R a b (a * g⁻¹) (g * b) :
        Matrix n n ℂ) i j := by
  classical
  simp [gaussOperator]

/-- Every other gauge block in a fixed column of the Gauss operator vanishes. -/
@[simp]
theorem gaussOperator_apply_of_ne
    (R : G → G → Matrix.unitaryGroup n ℂ) (g : G)
    (x y : n × (G × G)) (hxy : x.2 ≠ gaussLegAction g y.2) :
    gaussOperator R g x y = 0 := by
  classical
  simp [gaussOperator, hxy]

variable [Fintype G]

/-- Local Gauss operators multiply according to the group law. This is the
first conclusion of FBC25, Proposition `prop:gausslaws`
(arXiv:2502.20257, lines 3380--3387). -/
theorem gaussOperator_mul
    (R : G → G → Matrix.unitaryGroup n ℂ) (g h : G) :
    gaussOperator R g * gaussOperator R h = gaussOperator R (g * h) := by
  classical
  ext x y
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Fintype.sum_eq_single (gaussLegAction h y.2)]
  · have hcomp : gaussLegAction g (gaussLegAction h y.2) =
        gaussLegAction (g * h) y.2 := by
      simpa using congrArg (fun T : G × G ≃ G × G ↦ T y.2) (gaussLegAction_mul g h)
    by_cases hxy : x.2 = gaussLegAction (g * h) y.2
    · have hx : x.2 = gaussLegAction g (gaussLegAction h y.2) :=
        hxy.trans hcomp.symm
      simp only [gaussOperator, hx, hcomp, ite_true]
      rw [← Matrix.mul_apply]
      exact (congrFun₂ (congrArg Subtype.val
        (Matrix.unitaryFactorizationComparison_trans R y.2.1 y.2.2
          (gaussLegAction h y.2).1 (gaussLegAction h y.2).2
          (gaussLegAction (g * h) y.2).1 (gaussLegAction (g * h) y.2).2)) x.1 y.1).symm
    · have hx : x.2 ≠ gaussLegAction g (gaussLegAction h y.2) := fun heq ↦
        hxy (heq.trans hcomp)
      simp [gaussOperator, hx, hxy]
  · intro q hq
    simp [gaussOperator, hq]

variable [DecidableEq G]

omit [Fintype G] in
/-- The Gauss operator of the identity group element is the identity matrix. -/
@[simp]
theorem gaussOperator_one (R : G → G → Matrix.unitaryGroup n ℂ) :
    gaussOperator R 1 = 1 := by
  classical
  ext x y
  by_cases hxy : x.2 = y.2
  · by_cases hij : x.1 = y.1
    · have hfull : x = y := Prod.ext hij hxy
      subst y
      simp [gaussOperator]
    · have hfull : x ≠ y := fun h ↦ hij (congrArg Prod.fst h)
      simp [gaussOperator, hxy, hij, hfull]
  · have hfull : x ≠ y := fun h ↦ hxy (congrArg Prod.snd h)
    simp [gaussOperator, hxy, hfull]

omit [Fintype G] [DecidableEq G] in
/-- The adjoint of a local Gauss operator is the operator for the inverse group
element. -/
theorem star_gaussOperator
    (R : G → G → Matrix.unitaryGroup n ℂ) (g : G) :
    star (gaussOperator R g) = gaussOperator R g⁻¹ := by
  classical
  ext x y
  rw [Matrix.star_apply]
  by_cases hxy : y.2 = gaussLegAction g x.2
  · have hyx : x.2 = gaussLegAction g⁻¹ y.2 := by
      rw [hxy]
      simp [gaussLegAction]
    rw [gaussOperator, ite_eq_left hxy, gaussOperator, ite_eq_left hyx]
    change star ((Matrix.unitaryFactorizationComparison R x.2.1 x.2.2
      y.2.1 y.2.2 : Matrix n n ℂ) y.1 x.1) = _
    rw [← Matrix.star_apply]
    change ((Matrix.unitaryFactorizationComparison R x.2.1 x.2.2
      y.2.1 y.2.2)⁻¹ : Matrix.unitaryGroup n ℂ) x.1 y.1 = _
    rw [Matrix.unitaryFactorizationComparison_inv]
  · have hyx : x.2 ≠ gaussLegAction g⁻¹ y.2 := by
      intro heq
      apply hxy
      rw [heq]
      simp [gaussLegAction]
    rw [gaussOperator, ite_eq_right hxy, gaussOperator, ite_eq_right hyx]
    exact star_zero ℂ

/-- Every local Gauss operator is unitary. -/
theorem gaussOperator_mem_unitaryGroup
    (R : G → G → Matrix.unitaryGroup n ℂ) (g : G) :
    gaussOperator R g ∈ Matrix.unitaryGroup (n × (G × G)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_gaussOperator, gaussOperator_mul]
  simp

/-- The local Gauss operators form a unitary representation of `G`. This is
the representation part of FBC25, Proposition `prop:gausslaws`
(arXiv:2502.20257, lines 3380--3387), isolated from the proposition's separate
gauged-tensor invariance statement. -/
def gaussRepresentation (R : G → G → Matrix.unitaryGroup n ℂ) :
    G →* Matrix.unitaryGroup (n × (G × G)) ℂ where
  toFun g := ⟨gaussOperator R g, gaussOperator_mem_unitaryGroup R g⟩
  map_one' := Subtype.ext (gaussOperator_one R)
  map_mul' g h := Subtype.ext (gaussOperator_mul R g h).symm

@[simp]
theorem gaussRepresentation_coe
    (R : G → G → Matrix.unitaryGroup n ℂ) (g : G) :
    (gaussRepresentation R g : Matrix (n × (G × G)) (n × (G × G)) ℂ) =
      gaussOperator R g :=
  rfl

end Representation

/-! ### The local Gauss projector -/

section Projector


variable {G n : Type*} [Group G] [Fintype G] [DecidableEq G]
  [Fintype n] [DecidableEq n]

/-- The unplaced local Gauss projector kernel obtained by averaging the Gauss
representation over the finite group, as in FBC25, Equation `eq:gauge_projs`
(arXiv:2502.20257, lines 3494--3499). -/
def gaussProjector (R : G → G → Matrix.unitaryGroup n ℂ) :
    Matrix (n × (G × G)) (n × (G × G)) ℂ :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (gaussRepresentation R g : Matrix _ _ ℂ)

/-- The local Gauss projector is the normalized sum of the local Gauss
operators from FBC25, Equation `eq:gauge_projs`. -/
theorem gaussProjector_eq_average (R : G → G → Matrix.unitaryGroup n ℂ) :
    gaussProjector R =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, gaussOperator R g :=
  rfl

/-- The unplaced local Gauss projector kernel is a star projection. -/
theorem isStarProjection_gaussProjector
    (R : G → G → Matrix.unitaryGroup n ℂ) :
    IsStarProjection (gaussProjector R) :=
  Matrix.isStarProjection_inv_card_smul_sum (gaussRepresentation R)

end Projector

/-! ### Monomial matter unitaries -/

section Monomial

open Matrix

variable {G n : Type*} [Group G]

/-- The permutation part of the local Gauss operator of a tuple of monomial matter
unitaries: $(i,(a,b))\mapsto(\sigma_{T_g(a,b)}^{-1}\sigma_{a,b}(i),T_g(a,b))$. -/
def gaussMonomialPerm (σ : G → G → Equiv.Perm n) (g : G) : Equiv.Perm (n × (G × G)) :=
  (Equiv.prodComm n (G × G)).trans
    ((Equiv.prodShear (gaussLegAction g)
      (fun l ↦ (σ l.1 l.2).trans
        (σ (gaussLegAction g l).1 (gaussLegAction g l).2).symm)).trans
      (Equiv.prodComm (G × G) n))

@[simp]
theorem gaussMonomialPerm_apply (σ : G → G → Equiv.Perm n) (g : G) (x : n × (G × G)) :
    gaussMonomialPerm σ g x =
      ((σ (gaussLegAction g x.2).1 (gaussLegAction g x.2).2).symm (σ x.2.1 x.2.2 x.1),
        gaussLegAction g x.2) :=
  rfl

/-- The phase of the local Gauss operator of a tuple of monomial matter unitaries:
$\overline{\varphi_{T_g(a,b)}(\sigma_{T_g(a,b)}^{-1}\sigma_{a,b}(i))}\,
\varphi_{a,b}(i)$. -/
def gaussMonomialPhase (σ : G → G → Equiv.Perm n) (φ : G → G → n → ℂ) (g : G)
    (x : n × (G × G)) : ℂ :=
  star (φ (gaussLegAction g x.2).1 (gaussLegAction g x.2).2
    ((σ (gaussLegAction g x.2).1 (gaussLegAction g x.2).2).symm (σ x.2.1 x.2.2 x.1))) *
    φ x.2.1 x.2.2 x.1

variable [DecidableEq G] [Fintype n] [DecidableEq n]

/-- The local Gauss operator of a tuple of monomial matter unitaries is monomial.
This is FBC25, Equation `eq:mcG` (arXiv:2502.20257, lines 3380--3387) evaluated on
monomial blocks. -/
theorem gaussOperator_eq_monomial (R : G → G → Matrix.unitaryGroup n ℂ)
    (σ : G → G → Equiv.Perm n) (φ : G → G → n → ℂ)
    (hR : ∀ a b, (R a b : Matrix n n ℂ) = monomial (σ a b) (φ a b)) (g : G) :
    gaussOperator R g = monomial (gaussMonomialPerm σ g) (gaussMonomialPhase σ φ g) := by
  classical
  ext x y
  by_cases h2 : x.2 = gaussLegAction g y.2
  · obtain ⟨i, l⟩ := x
    obtain ⟨j, m⟩ := y
    simp only at h2
    subst h2
    have hblock : (Matrix.unitaryFactorizationComparison R m.1 m.2
        (gaussLegAction g m).1 (gaussLegAction g m).2 : Matrix n n ℂ) =
        monomial ((σ m.1 m.2).trans
            (σ (gaussLegAction g m).1 (gaussLegAction g m).2).symm)
          fun s ↦ star (φ (gaussLegAction g m).1 (gaussLegAction g m).2
            ((σ (gaussLegAction g m).1 (gaussLegAction g m).2).symm (σ m.1 m.2 s))) *
            φ m.1 m.2 s := by
      rw [Matrix.unitaryFactorizationComparison_coe, hR, hR, star_eq_conjTranspose,
        conjTranspose_monomial, monomial_mul_monomial]
      rfl
    have hx : gaussOperator R g (i, gaussLegAction g m) (j, m) =
        (Matrix.unitaryFactorizationComparison R m.1 m.2
          (gaussLegAction g m).1 (gaussLegAction g m).2 : Matrix n n ℂ) i j := by
      simp [gaussOperator]
    rw [hx, hblock, monomial_apply, monomial_apply]
    by_cases hij : i = (σ (gaussLegAction g m).1 (gaussLegAction g m).2).symm (σ m.1 m.2 j)
    · subst hij
      simp [gaussMonomialPhase]
    · rw [ite_eq_right, ite_eq_right]
      · intro h
        exact hij (by simpa using congrArg Prod.fst h)
      · simpa using hij
  · rw [gaussOperator_apply_of_ne R g x y h2, monomial_apply_of_ne]
    intro h
    exact h2 (by simpa using congrArg Prod.snd h)

end Monomial

end GaussLaw
