/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Unital matrix-algebra homomorphisms with scalar relative commutant

Let `Φ : M_p(ℂ) → M_q(ℂ)` be a unital homomorphism of complex algebras. Its *relative
commutant* is the set of `q × q` matrices commuting with every matrix in the image of `Φ`;
it always contains the scalar matrices. This module proves that if the relative commutant
consists of scalars only, then `Φ` is onto, and records the contrapositive: a unital
homomorphism of full matrix algebras that is not onto has a non-scalar matrix in its
relative commutant.

The argument is the irreducible-projection specialization of the representation-theoretic
argument used by Schumacher and Werner for Proposition `Cshom`
(`LionSR/TNLean/Papers/quant-ph_0405174/qca.tex`, lines 2101--2116): pulling the standard
action back along `Φ` makes `ℂ^q` a module over `M_p(ℂ)`; each of its submodules is the range
of a module projection, and such a projection lies in the relative commutant, hence is a
scalar, hence has range `0` or everything. So `ℂ^q` is a simple module. Since all simple
modules over a simple Artinian ring are isomorphic -- the "basic property of `M_d`" that all
its irreducible representations are unitarily equivalent to the defining representation on
`ℂ^d`, quoted at lines 2112--2114 of the same source -- the module `ℂ^q` is isomorphic to the
defining module `ℂ^p`, so `p = q`; and a unital homomorphism out of a simple ring is
injective, so equal dimensions make it onto.

This is reusable finite-dimensional matrix-algebra infrastructure, not a theorem stated
separately in any of the sources below, and it does not by itself close one of their
theorems; no paper-gap note is attached to it. It is the finite-dimensional step behind two
passages of Gross, Nesme, Vogts and Werner
(`LionSR/TNLean/References/0910.3675/QCI12.tex`): the support-product inclusion at
lines 1276--1286 (equation `AARReven`) is non-strict because a strict inclusion would produce
an element of the relative commutant, and the inclusion at lines 1306--1314 (equation
`AARRodd`) is non-strict because otherwise the automorphism would fail to be onto.

## Main results

* `Matrix.isSimpleModule_pi` -- the defining module of a full matrix algebra over a field is
  simple.
* `IsSimpleRing.nonempty_linearEquiv_of_isSimpleModule` -- any two simple modules over a
  simple Artinian ring are isomorphic.
* `Matrix.AlgHom.size_eq_of_centralizer_range_eq_bot` -- a unital homomorphism of full complex
  matrix algebras with scalar relative commutant has equal source and target sizes.
* `Matrix.AlgHom.surjective_of_centralizer_range_eq_bot` -- such a homomorphism is onto.
* `Matrix.StarAlgHom.surjective_of_centralizer_range_eq_bot` -- the same for a unital
  homomorphism of complex matrix `*`-algebras.
* `Matrix.AlgHom.exists_commute_notMem_bot_of_not_surjective` -- a unital homomorphism of full
  complex matrix algebras that is not onto has a non-scalar matrix in its relative commutant.
-/

open scoped Matrix

/-- The defining module `n → K` of the full matrix algebra `M_n(K)` over a field `K` is
simple: a nonzero vector is carried onto every vector by a single matrix.

Mathlib already records this for the endomorphism ring of a nonzero vector space over a
division ring, so the proof only transports that instance along the algebra isomorphism
`Matrix.toLinAlgEquiv'` between `M_n(K)` and the endomorphism ring of `n → K`; the identity
of `n → K` is semilinear along that isomorphism because it carries the matrix action to the
endomorphism action. Commutativity of `K` enters only through the isomorphism, the matrix
action on `n → K` being `K`-linear only over a commutative `K`.

Schumacher--Werner call this the defining representation of `M_d`
(`LionSR/TNLean/Papers/quant-ph_0405174/qca.tex`, lines 2112--2114). -/
theorem Matrix.isSimpleModule_pi {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {K : Type*} [Field K] : IsSimpleModule (Matrix n n K) (n → K) := by
  have : RingHomSurjective (Matrix.toLinAlgEquiv' (R := K) (n := n)).toRingHom :=
    ⟨Matrix.toLinAlgEquiv'.surjective⟩
  let l : (n → K) →ₛₗ[(Matrix.toLinAlgEquiv' (R := K) (n := n)).toRingHom] (n → K) :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun A v => by simp [Matrix.toLinAlgEquiv'_apply] }
  exact (l.isSimpleModule_iff_of_bijective Function.bijective_id).2 inferInstance

/-- Any two simple modules over a simple Artinian ring are isomorphic.

Both are isomorphic to simple left ideals, and over a simple Artinian ring the regular module
is isotypic, so its simple left ideals are mutually isomorphic. This is the general form of
the property of `M_d` that Schumacher and Werner invoke as the uniqueness of the irreducible
representation (`LionSR/TNLean/Papers/quant-ph_0405174/qca.tex`, lines 2112--2114). -/
theorem IsSimpleRing.nonempty_linearEquiv_of_isSimpleModule
    (R : Type*) [Ring R] [IsSimpleRing R] [IsArtinianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [IsSimpleModule R M]
    (N : Type*) [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (M ≃ₗ[R] N) := by
  obtain ⟨I, ⟨eM⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R M
  obtain ⟨J, ⟨eN⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R N
  have : IsSimpleModule R I := IsSimpleModule.congr eM.symm
  have : IsSimpleModule R J := IsSimpleModule.congr eN.symm
  exact ⟨eM.trans ((IsSimpleRing.isIsotypic R R J I).some.trans eN.symm)⟩

namespace Matrix.AlgHom

variable {p q : ℕ} [NeZero p] [NeZero q]

/-- A unital homomorphism `Φ : M_p(ℂ) → M_q(ℂ)` of complex algebras whose relative commutant
consists of scalar matrices only has `p = q`.

Pulled back along `Φ`, the space `ℂ^q` is a module over `M_p(ℂ)`. Each of its submodules is
the range of a module projection along a complement; read as a matrix, such a projection
commutes with the whole image of `Φ`, hence is scalar, hence has range `0` or everything.
So `ℂ^q` is simple, and therefore isomorphic to the defining module `ℂ^p`; comparing complex
dimensions gives `p = q`. This is the single-summand case of the representation argument of
Schumacher--Werner, Proposition `Cshom`
(`LionSR/TNLean/Papers/quant-ph_0405174/qca.tex`, lines 2101--2116), specialized to a
relative commutant of scalars, where the multiplicity is one. -/
theorem size_eq_of_centralizer_range_eq_bot
    (Φ : Matrix (Fin p) (Fin p) ℂ →ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ)
    (hΦ : Subalgebra.centralizer ℂ (Set.range Φ) = ⊥) :
    p = q := by
  let _ : Module (Matrix (Fin p) (Fin p) ℂ) (Fin q → ℂ) :=
    Module.compHom _ (Φ : Matrix (Fin p) (Fin p) ℂ →+* Matrix (Fin q) (Fin q) ℂ)
  have hsmul : ∀ (A : Matrix (Fin p) (Fin p) ℂ) (v : Fin q → ℂ), A • v = Φ A *ᵥ v :=
    fun _ _ => rfl
  have : IsScalarTower ℂ (Matrix (Fin p) (Fin p) ℂ) (Fin q → ℂ) := by
    refine ⟨fun c A v => ?_⟩
    rw [hsmul, hsmul, map_smul, Matrix.smul_mulVec]
  have : Nontrivial (Submodule (Matrix (Fin p) (Fin p) ℂ) (Fin q → ℂ)) :=
    (Submodule.nontrivial_iff _).2 inferInstance
  have : IsSimpleModule (Matrix (Fin p) (Fin p) ℂ) (Fin q → ℂ) := by
    refine { __ := (⟨fun W => ?_⟩ :
      IsSimpleOrder (Submodule (Matrix (Fin p) (Fin p) ℂ) (Fin q → ℂ))) }
    obtain ⟨W', hW'⟩ := exists_isCompl W
    have hrange : LinearMap.range (W.projection W' hW') = W := Submodule.range_projection hW'
    have hTv : ∀ v, (LinearMap.toMatrix' (((W.projection W' hW').restrictScalars ℂ))) *ᵥ v
        = W.projection W' hW' v := by
      intro v
      rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
      rfl
    have hmem : LinearMap.toMatrix' ((W.projection W' hW').restrictScalars ℂ) ∈
        Subalgebra.centralizer ℂ (Set.range Φ) := by
      rintro _ ⟨A, rfl⟩
      refine Matrix.ext_iff_mulVec.2 fun v => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hTv, hTv]
      simp only [← hsmul]
      exact (map_smul (W.projection W' hW') A v).symm
    rw [hΦ] at hmem
    obtain ⟨c, hc⟩ := Algebra.mem_bot.1 hmem
    have hproj : ∀ v, W.projection W' hW' v = c • v := by
      intro v
      rw [← hTv, ← hc, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rcases eq_or_ne c 0 with rfl | hc0
    · refine Or.inl (hrange.symm.trans (LinearMap.range_eq_bot.2 ?_))
      exact LinearMap.ext fun v => by simp [hproj]
    · refine Or.inr (hrange.symm.trans (LinearMap.range_eq_top.2 fun v => ⟨c⁻¹ • v, ?_⟩))
      rw [hproj, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  have : IsSimpleModule (Matrix (Fin p) (Fin p) ℂ) (Fin p → ℂ) := Matrix.isSimpleModule_pi
  obtain ⟨e⟩ := IsSimpleRing.nonempty_linearEquiv_of_isSimpleModule
    (Matrix (Fin p) (Fin p) ℂ) (Fin q → ℂ) (Fin p → ℂ)
  have hfin := (e.restrictScalars ℂ).finrank_eq
  simpa [Module.finrank_pi] using hfin.symm

/-- **Scalar relative commutant forces surjectivity.** A unital homomorphism
`Φ : M_p(ℂ) → M_q(ℂ)` of complex algebras whose relative commutant is the scalar algebra is
onto.

Injectivity is not assumed: it follows from simplicity of `M_p(ℂ)` and nontriviality of
`M_q(ℂ)`. Together with the equality of matrix sizes, an injective complex-linear map between
spaces of equal finite dimension is onto.

This is reusable matrix-algebra infrastructure; see the module docstring for the passages of
Schumacher--Werner and of Gross--Nesme--Vogts--Werner that use it. -/
theorem surjective_of_centralizer_range_eq_bot
    (Φ : Matrix (Fin p) (Fin p) ℂ →ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ)
    (hΦ : Subalgebra.centralizer ℂ (Set.range Φ) = ⊥) :
    Function.Surjective Φ := by
  have hinj : Function.Injective Φ :=
    (Φ : Matrix (Fin p) (Fin p) ℂ →+* Matrix (Fin q) (Fin q) ℂ).injective
  have hpq : p = q := size_eq_of_centralizer_range_eq_bot Φ hΦ
  have hrank : Module.finrank ℂ (Matrix (Fin p) (Fin p) ℂ)
      = Module.finrank ℂ (Matrix (Fin q) (Fin q) ℂ) := by
    subst hpq; rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank
    (f := Φ.toLinearMap)).1 hinj

/-- A unital homomorphism `Φ : M_p(ℂ) → M_q(ℂ)` of complex algebras that is not onto has a
non-scalar matrix in its relative commutant.

This is the contrapositive of `Matrix.AlgHom.surjective_of_centralizer_range_eq_bot`, phrased
as the witness that Gross--Nesme--Vogts--Werner extract from a strict inclusion of
support-product algebras (`LionSR/TNLean/References/0910.3675/QCI12.tex`, lines 1276--1286
and 1306--1314). -/
theorem exists_commute_notMem_bot_of_not_surjective
    (Φ : Matrix (Fin p) (Fin p) ℂ →ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ)
    (hΦ : ¬ Function.Surjective Φ) :
    ∃ T : Matrix (Fin q) (Fin q) ℂ, (∀ A, Commute T (Φ A)) ∧
      T ∉ (⊥ : Subalgebra ℂ (Matrix (Fin q) (Fin q) ℂ)) := by
  by_contra hcon
  push Not at hcon
  refine hΦ (surjective_of_centralizer_range_eq_bot Φ (le_antisymm (fun T hT => ?_) bot_le))
  exact hcon T fun A => ((Subalgebra.mem_centralizer_iff ℂ).1 hT (Φ A) ⟨A, rfl⟩).symm

end Matrix.AlgHom

namespace Matrix.StarAlgHom

variable {p q : ℕ} [NeZero p] [NeZero q]

/-- **Scalar relative commutant forces surjectivity**, for `*`-homomorphisms. A unital
homomorphism `Φ : M_p(ℂ) → M_q(ℂ)` of complex matrix `*`-algebras whose relative commutant is
the scalar algebra is onto.

Star preservation plays no part in the argument; this is the form matching the unital
`*`-homomorphisms of Schumacher--Werner, Proposition `Cshom`
(`LionSR/TNLean/Papers/quant-ph_0405174/qca.tex`, lines 2101--2116). -/
theorem surjective_of_centralizer_range_eq_bot
    (Φ : Matrix (Fin p) (Fin p) ℂ →⋆ₐ[ℂ] Matrix (Fin q) (Fin q) ℂ)
    (hΦ : Subalgebra.centralizer ℂ (Set.range Φ) = ⊥) :
    Function.Surjective Φ :=
  Matrix.AlgHom.surjective_of_centralizer_range_eq_bot (Φ : Matrix (Fin p) (Fin p) ℂ →ₐ[ℂ]
    Matrix (Fin q) (Fin q) ℂ) hΦ

end Matrix.StarAlgHom
