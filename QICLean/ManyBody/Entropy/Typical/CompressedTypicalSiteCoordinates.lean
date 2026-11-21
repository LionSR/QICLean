/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Sites.CompressedSiteCoordinates
import Mathlib.Logic.Equiv.Basic
import QICLean.ManyBody.Entropy.Typical.RegionTypicalState
import QICLean.Entropy.Typical.PureCompression

/-!
# Physical sites and the compressed auxiliary coordinate

The exterior sites are the physical complement of the selected region,
together with one auxiliary site. A configuration on these sites is exactly
a compressed auxiliary index and a physical complementary configuration.
For a physical region disjoint from the selected region, the canonical split
agrees with the regional coordinates of the actual compressed vector.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–247 and 332–354,
  source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

section CompressedTypicalRegionalMarginal

/-!
# Regional marginals of the compressed selected vector

Let a spectral selection be made on one physical region. Replacing the
selected spectral subspace by its coordinate space preserves the density
matrix on every disjoint physical region. The coordinates discarded below
are the selected spectral index and the physical complement of both regions.

The statement concerns the literal compressed vector, with the selected
indices identified with `Fin E.card`. No normalization or positive selected
mass is needed for the equality.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–247 and 332–354,
  `comparator:post-marginal` and `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped BigOperators Matrix

noncomputable section

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The actual compressed selected vector has the same marginal on every
disjoint physical region as the selected vector in the original physical
space. The discarded coordinates are placed first, so the statement can be
used directly in a left-partial-trace formula for tensor powers.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–354. -/
theorem partialTraceLeft_compressedTypicalPureState_region
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X B : Finset V)
    (hXB : Disjoint X B) (E : Finset (RegionConfig β X)) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
    let χ : Fin E.card × ComplConfig β X → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    let τ : (Fin E.card × ComplConfig β (X ∪ B)) × RegionConfig β B → ℂ :=
      fun x ↦ χ (x.1.1, (complementUnionEquiv β X B hXB).symm (x.2, x.1.2))
    Matrix.partialTraceLeft (Matrix.vecMulVec τ (star τ)) =
      regionState (typicalPureState β Ω X E) B := by
  intro ΩX χ τ
  let Ψ := typicalPureState β Ω X E
  have hselected (a : RegionConfig β X) (u : ComplConfig β X) :
      Matrix.typicalPureState ΩX E (a, u) = Ψ ((cutEquiv β X).symm (a, u)) := by
    exact (congrArg (fun v ↦ v (a, u)) (split_typicalPureState β Ω X E)).symm
  have hcomplement (u v : ComplConfig β X) :
      (∑ r : Fin E.card, χ (r, u) * star (χ (r, v))) =
        ∑ a : RegionConfig β X,
          Ψ ((cutEquiv β X).symm (a, u)) *
            star (Ψ ((cutEquiv β X).symm (a, v))) := by
    calc
      _ = ∑ i : E, Matrix.compressedTypicalPureState ΩX E (i, u) *
          star (Matrix.compressedTypicalPureState ΩX E (i, v)) :=
        (Finset.equivFin E).symm.sum_comp (fun i : E ↦
          Matrix.compressedTypicalPureState ΩX E (i, u) *
            star (Matrix.compressedTypicalPureState ΩX E (i, v)))
      _ = _ := by
        have hm := congrArg (fun M ↦ M u v)
          (Matrix.partialTraceLeft_compressedTypicalPureState ΩX E)
        simpa only [Matrix.partialTraceLeft_apply, Matrix.vecMulVec_apply,
          Pi.star_apply, hselected] using hm
  change Matrix.partialTraceLeft (Matrix.vecMulVec τ (star τ)) = regionState Ψ B
  rw [regionState, ← partialTraceLeft_regionMatrix_union β
    (Matrix.vecMulVec (WithLp.ofLp Ψ) (star (WithLp.ofLp Ψ))) X B hXB]
  ext b b'
  change (∑ rc : Fin E.card × ComplConfig β (X ∪ B),
      χ (rc.1, (complementUnionEquiv β X B hXB).symm (b, rc.2)) *
        star (χ (rc.1, (complementUnionEquiv β X B hXB).symm (b', rc.2)))) =
    ∑ a : RegionConfig β X, ∑ c : ComplConfig β (X ∪ B),
      Ψ ((cutEquiv β (X ∪ B)).symm ((regionUnionEquiv (β := β) hXB).symm (a, b), c)) *
        star (Ψ ((cutEquiv β (X ∪ B)).symm
          ((regionUnionEquiv (β := β) hXB).symm (a, b'), c)))
  simp_rw [split_union_symm]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hcomplement]
  exact Finset.sum_comm

end ManyBody
end

end CompressedTypicalRegionalMarginal

open scoped BigOperators Matrix

universe u

noncomputable section

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]

section GeneralCoordinates

variable (β : V → Type u) (X B : Finset V) (R : Type u)

/-- The regional coordinates are precisely the original physical coordinates.
The disjointness assumption removes no physical degree of freedom in `B`. -/
def exteriorRegionEquiv (hXB : Disjoint X B) :
    RegionConfig (compressedSiteSpace β X R) (exteriorRegion X B) ≃
      RegionConfig β B where
  toFun x v := x ⟨some ⟨v, fun hx ↦ Finset.disjoint_left.mp hXB hx v.property⟩,
    by simp [exteriorRegion, v.property]⟩
  invFun x f := match f with
    | ⟨none, hf⟩ => False.elim (by simp [exteriorRegion] at hf)
    | ⟨some v, hf⟩ => x ⟨v, by simpa [exteriorRegion] using hf⟩
  left_inv x := by
    funext f
    rcases f with ⟨f, hf⟩
    cases f with
    | none => simp [exteriorRegion] at hf
    | some v => rfl
  right_inv x := by
    funext v
    rfl

/-- The discarded coordinates consist of the auxiliary index and the physical
complement of the two regions. -/
def exteriorComplementEquiv :
    ComplConfig (compressedSiteSpace β X R) (exteriorRegion X B) ≃
      R × ComplConfig β (X ∪ B) where
  toFun x := (x ⟨none, by simp [exteriorRegion]⟩,
    fun v ↦ x ⟨some ⟨v, fun hx ↦ v.property (Finset.mem_union_left B hx)⟩,
      by
        have hv : (v : V) ∉ B := fun hb ↦ v.property (Finset.mem_union_right X hb)
        simp [exteriorRegion, hv]⟩)
  invFun x f := match f with
    | ⟨none, _⟩ => x.1
    | ⟨some v, hf⟩ => x.2 ⟨v, by
        have hv : (v : V) ∉ B := by simpa [exteriorRegion] using hf
        exact fun h ↦ (Finset.mem_union.mp h).elim v.property hv⟩
  left_inv x := by
    funext f
    rcases f with ⟨f, hf⟩
    cases f <;> rfl
  right_inv x := by
    rcases x with ⟨r, c⟩
    apply Prod.ext
    · rfl
    · funext v
      rfl

/-- Splitting the actual exterior site family agrees with splitting the
physical complement, while retaining the same auxiliary coordinate. -/
theorem piOptionEquivProd_split_exteriorRegion (hXB : Disjoint X B)
    (b : RegionConfig (compressedSiteSpace β X R) (exteriorRegion X B))
    (c : ComplConfig (compressedSiteSpace β X R)
        (exteriorRegion X B)) :
    Equiv.piOptionEquivProd
        ((cutEquiv (compressedSiteSpace β X R)
            (exteriorRegion X B)).symm (b, c)) =
      ((exteriorComplementEquiv β X B R c).1,
        (complementUnionEquiv β X B hXB).symm
          (exteriorRegionEquiv β X B R hXB b,
            (exteriorComplementEquiv β X B R c).2)) := by
  apply Prod.ext
  · exact cutEquiv_symm_apply_not_mem b c (by simp [exteriorRegion])
  · funext v
    change
        ((cutEquiv (compressedSiteSpace β X R)
        (exteriorRegion X B)).symm
      (b, c)) (some v) =
        (complementUnionEquiv β X B hXB).symm
          (exteriorRegionEquiv β X B R hXB b,
            (exteriorComplementEquiv β X B R c).2) v
    by_cases hv : (v : V) ∈ B
    · rw [cutEquiv_symm_apply_mem b c (v := some v)
        (by simp [exteriorRegion, hv])]
      simp [complementUnionEquiv, exteriorRegionEquiv, Equiv.coe_fn_mk, hv]
      rfl
    · rw [cutEquiv_symm_apply_not_mem b c (v := some v)
        (by simp [exteriorRegion, hv])]
      simp [complementUnionEquiv, exteriorComplementEquiv, Equiv.coe_fn_mk, hv]

variable [∀ v, Fintype (β v)] [Fintype R]

/-- Regional reduction in the actual site coordinates is the partial trace
over the auxiliary coordinate and the remaining physical sites. -/
private theorem reducedPure_exteriorSiteState (hXB : Disjoint X B)
    (χ : R × ComplConfig β X → ℂ) :
    (regionState
        (WithLp.toLp 2 (fun x ↦ χ (Equiv.piOptionEquivProd x)))
        (exteriorRegion X B)).submatrix
          (exteriorRegionEquiv β X B R hXB).symm
          (exteriorRegionEquiv β X B R hXB).symm =
      Matrix.partialTraceLeft (Matrix.vecMulVec
        (fun x : (R × ComplConfig β (X ∪ B)) × RegionConfig β B ↦
          χ (x.1.1, (complementUnionEquiv β X B hXB).symm (x.2, x.1.2)))
        (star (fun x : (R × ComplConfig β (X ∪ B)) × RegionConfig β B ↦
          χ (x.1.1, (complementUnionEquiv β X B hXB).symm (x.2, x.1.2))))) := by
  have hχ (a : RegionConfig β B)
      (c : ComplConfig (compressedSiteSpace β X R)
          (exteriorRegion X B)) :
      χ (Equiv.piOptionEquivProd
        ((cutEquiv (compressedSiteSpace β X R)
            (exteriorRegion X B)).symm
          ((exteriorRegionEquiv β X B R hXB).symm a, c))) =
      χ ((exteriorComplementEquiv β X B R c).1,
        (complementUnionEquiv β X B hXB).symm
          (a, (exteriorComplementEquiv β X B R c).2)) := by
    have h := congrArg χ
      (piOptionEquivProd_split_exteriorRegion β X B R hXB
        ((exteriorRegionEquiv β X B R hXB).symm a) c)
    simpa only [Equiv.apply_symm_apply] using h
  ext b b'
  change
      (∑ c : ComplConfig (compressedSiteSpace β X R)
      (exteriorRegion X B),
      χ (Equiv.piOptionEquivProd
        ((cutEquiv (compressedSiteSpace β X R)
            (exteriorRegion X B)).symm
          ((exteriorRegionEquiv β X B R hXB).symm b, c))) *
      star (χ (Equiv.piOptionEquivProd
        ((cutEquiv (compressedSiteSpace β X R)
            (exteriorRegion X B)).symm
          ((exteriorRegionEquiv β X B R hXB).symm b', c))))) = _
  simp_rw [hχ]
  exact (exteriorComplementEquiv β X B R).sum_comp (fun rc ↦
    χ (rc.1, (complementUnionEquiv β X B hXB).symm (b, rc.2)) *
      star (χ (rc.1, (complementUnionEquiv β X B hXB).symm (b', rc.2))))

end GeneralCoordinates

variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (X B : Finset V)

/-- The actual compressed selected vector on the augmented site family has
the actual selected physical marginal, after the canonical identification of
regional configurations. Neither state normalization nor positive selected
mass is needed for this coordinate identity.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 332–354. -/
theorem regionState_compressedTypicalSiteState
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (hXB : Disjoint X B)
    (E : Finset (RegionConfig β X)) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
    let χ : Fin E.card × ComplConfig β X → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    (regionState
        (WithLp.toLp 2 (fun x ↦ χ (Equiv.piOptionEquivProd x)))
        (exteriorRegion X B)).submatrix
          (exteriorRegionEquiv β X B (Fin E.card) hXB).symm
          (exteriorRegionEquiv β X B (Fin E.card) hXB).symm =
      regionState (typicalPureState β Ω X E) B := by
  intro ΩX χ
  rw [reducedPure_exteriorSiteState]
  exact partialTraceLeft_compressedTypicalPureState_region β Ω X B hXB E

end ManyBody

section CompressedTypicalSiteEntropy

/-!
# Regional entropy of the actual compressed selected vector

The actual regional marginal in the augmented site family is the selected
physical marginal after a canonical coordinate change. Entropy is invariant
under this change. The existing entropy comparison for the selected physical
state therefore applies to this same compressed vector on every disjoint
physical region.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 320–343,
  `comparator:post-marginal` and `comparator:rough-overlap`, source commit
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped ComplexOrder

noncomputable section

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- The actual compressed state's entropy on a disjoint physical region is
at most the original regional entropy divided by the actual selected mass.
The regional marginal equality is derived from the literal selected state,
not supplied as a hypothesis.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 320–343. -/
theorem regionEntropy_compressedTypicalSiteState_le
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X B : Finset V)
    (hXB : Disjoint X B) (E : Finset (RegionConfig β X)) (hΩ : ‖Ω‖ = 1)
    (hz : 0 < (regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
    let χsite := WithLp.toLp 2
      (fun x : (f : Option {v // v ∉ X}) → compressedSiteSpace β X (Fin E.card) f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))
    regionEntropy χsite (exteriorRegion X B) ≤
      regionEntropy Ω B /
        (regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E := by
  intro ΩX χsite
  let ρ := regionState χsite (exteriorRegion X B)
  have hρ : ρ.IsHermitian :=
    (regionState_posSemidef
      (exteriorRegion X B) χsite).isHermitian
  let e := exteriorRegionEquiv β X B (Fin E.card) hXB
  have hm : ρ.submatrix e.symm e.symm =
      regionState (typicalPureState β Ω X E) B :=
    regionState_compressedTypicalSiteState β X B Ω hXB E
  have hentropy :
      regionEntropy χsite (exteriorRegion X B) =
        regionEntropy (typicalPureState β Ω X E) B := by
    exact (vonNeumannEntropy_submatrix_equiv e.symm ρ hρ).symm.trans
      (vonNeumannEntropy_congr hm _
        (regionState_posSemidef B (typicalPureState β Ω X E)).isHermitian)
  rw [hentropy]
  exact regionEntropy_typicalPureState_le β Ω X E B hXB hΩ hz

end ManyBody
end

end CompressedTypicalSiteEntropy

section CompressedTypicalSiteNorm

/-!
# Norm of the actual compressed selected vector on exterior sites

The exterior site family carries the same compressed selected vector as the
selected spectral coordinate space. The identification is the actual option
product equivalence followed by the inverse enumeration of the selected
indices. It is a coordinate isometry, so positive actual selected mass gives
a unit vector. No normalization assumption on the original vector is needed.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 240–247 and 332–354,
  source commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped ComplexOrder

noncomputable section

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]

/-- Positive actual selected mass normalizes the literal compressed vector
on the auxiliary site and the original complementary physical sites.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 240–247. -/
theorem norm_compressedTypicalSiteState
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
    (E : Finset (RegionConfig β X))
    (hz : 0 < (regionState_posSemidef X Ω).isHermitian.spectralRestrictionMass E) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (cutEquiv β X) Ω
    ‖WithLp.toLp 2
      (fun x : (f : Option {v // v ∉ X}) → compressedSiteSpace β X (Fin E.card) f ↦
        Matrix.compressedTypicalPureState ΩX E
          ((Finset.equivFin E).symm (x none), fun v ↦ x (some v)))‖ = 1 := by
  intro ΩX
  let e : ((f : Option {v // v ∉ X}) → compressedSiteSpace β X (Fin E.card) f) ≃
      E × ComplConfig β X :=
    (Equiv.piOptionEquivProd (β := compressedSiteSpace β X (Fin E.card))).trans
      ((Finset.equivFin E).symm.prodCongr (Equiv.refl (ComplConfig β X)))
  have hzX : 0 < Matrix.IsHermitian.spectralRestrictionMass
      (Matrix.PosSemidef.isHermitian
        (Matrix.posSemidef_vecMulVec_self_star ΩX).partialTraceRight) E := by
    exact hz
  calc
    _ = ‖Matrix.compressedTypicalPureState ΩX E‖ :=
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).norm_map
        (Matrix.compressedTypicalPureState ΩX E)
    _ = 1 := Matrix.norm_compressedTypicalPureState ΩX E hzX

end ManyBody
end

end CompressedTypicalSiteNorm
