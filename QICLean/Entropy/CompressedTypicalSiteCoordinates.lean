/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CompressedSiteCoordinates
import QICLean.Entropy.CompressedTypicalRegionalMarginal
import Mathlib.Logic.Equiv.Basic

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

open scoped BigOperators Matrix

universe u

noncomputable section

namespace FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

section GeneralCoordinates

variable (β : V → Type u) (X B : Finset V) (R : Type u)

/-- The regional coordinates are precisely the original physical coordinates.
The disjointness assumption removes no physical degree of freedom in `B`. -/
def exteriorRegionEquiv (hXB : Disjoint X B) :
    Configuration (compressedSiteSpace β X R) (exteriorRegion X B) ≃
      Configuration β B where
  toFun x v := x ⟨some ⟨v, Finset.mem_compl.mpr
      (fun hx ↦ Finset.disjoint_left.mp hXB hx v.property)⟩,
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
    Configuration (compressedSiteSpace β X R) (exteriorRegion X B)ᶜ ≃
      R × Configuration β (X ∪ B)ᶜ where
  toFun x := (x ⟨none, by simp [exteriorRegion]⟩,
    fun v ↦ x ⟨some ⟨v, Finset.mem_compl.mpr (fun hx ↦
      Finset.mem_compl.mp v.property (Finset.mem_union_left B hx))⟩,
      by
        have hv : (v : V) ∉ B := fun hb ↦
          Finset.mem_compl.mp v.property (Finset.mem_union_right X hb)
        simp [exteriorRegion, hv]⟩)
  invFun x f := match f with
    | ⟨none, _⟩ => x.1
    | ⟨some v, hf⟩ => x.2 ⟨v, by
        have hv : (v : V) ∉ B := by simpa [exteriorRegion] using hf
        exact Finset.mem_compl.mpr (fun h ↦
          (Finset.mem_union.mp h).elim (Finset.mem_compl.mp v.property) hv)⟩
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
    (b : Configuration (compressedSiteSpace β X R) (exteriorRegion X B))
    (c : Configuration (compressedSiteSpace β X R) (exteriorRegion X B)ᶜ) :
    Equiv.piOptionEquivProd
        ((splitEquiv (compressedSiteSpace β X R) (exteriorRegion X B)).symm (b, c)) =
      ((exteriorComplementEquiv β X B R c).1,
        (complementUnionEquiv β X B hXB).symm
          (exteriorRegionEquiv β X B R hXB b,
            (exteriorComplementEquiv β X B R c).2)) := by
  apply Prod.ext
  · change ((splitEquiv (compressedSiteSpace β X R) (exteriorRegion X B)).symm
      (b, c)) none = c ⟨none, by simp [exteriorRegion]⟩
    exact splitEquiv_symm_apply_of_notMem _ _ b c none (by simp [exteriorRegion])
  · funext v
    change ((splitEquiv (compressedSiteSpace β X R) (exteriorRegion X B)).symm
      (b, c)) (some v) =
        (complementUnionEquiv β X B hXB).symm
          (exteriorRegionEquiv β X B R hXB b,
            (exteriorComplementEquiv β X B R c).2) v
    by_cases hv : (v : V) ∈ B
    · rw [splitEquiv_symm_apply_of_mem _ _ b c (some v)
        (by simp [exteriorRegion, hv])]
      simp [complementUnionEquiv, exteriorRegionEquiv, Equiv.coe_fn_mk, hv]
      rfl
    · rw [splitEquiv_symm_apply_of_notMem _ _ b c (some v)
        (by simp [exteriorRegion, hv])]
      simp [complementUnionEquiv, exteriorComplementEquiv, Equiv.coe_fn_mk, hv]

variable [∀ v, Fintype (β v)] [Fintype R]

/-- Regional reduction in the actual site coordinates is the partial trace
over the auxiliary coordinate and the remaining physical sites. -/
private theorem reducedPure_exteriorSiteState (hXB : Disjoint X B)
    (χ : R × Configuration β Xᶜ → ℂ) :
    (reducedPure (compressedSiteSpace β X R)
        (WithLp.toLp 2 (fun x ↦ χ (Equiv.piOptionEquivProd x)))
        (exteriorRegion X B)).submatrix
          (exteriorRegionEquiv β X B R hXB).symm
          (exteriorRegionEquiv β X B R hXB).symm =
      Matrix.partialTraceLeft (Matrix.vecMulVec
        (fun x : (R × Configuration β (X ∪ B)ᶜ) × Configuration β B ↦
          χ (x.1.1, (complementUnionEquiv β X B hXB).symm (x.2, x.1.2)))
        (star (fun x : (R × Configuration β (X ∪ B)ᶜ) × Configuration β B ↦
          χ (x.1.1, (complementUnionEquiv β X B hXB).symm (x.2, x.1.2))))) := by
  have hχ (a : Configuration β B)
      (c : Configuration (compressedSiteSpace β X R) (exteriorRegion X B)ᶜ) :
      χ (Equiv.piOptionEquivProd
        ((splitEquiv (compressedSiteSpace β X R) (exteriorRegion X B)).symm
          ((exteriorRegionEquiv β X B R hXB).symm a, c))) =
      χ ((exteriorComplementEquiv β X B R c).1,
        (complementUnionEquiv β X B hXB).symm
          (a, (exteriorComplementEquiv β X B R c).2)) := by
    have h := congrArg χ
      (piOptionEquivProd_split_exteriorRegion β X B R hXB
        ((exteriorRegionEquiv β X B R hXB).symm a) c)
    simpa only [Equiv.apply_symm_apply] using h
  ext b b'
  change (∑ c : Configuration (compressedSiteSpace β X R) (exteriorRegion X B)ᶜ,
      χ (Equiv.piOptionEquivProd
        ((splitEquiv (compressedSiteSpace β X R) (exteriorRegion X B)).symm
          ((exteriorRegionEquiv β X B R hXB).symm b, c))) *
      star (χ (Equiv.piOptionEquivProd
        ((splitEquiv (compressedSiteSpace β X R) (exteriorRegion X B)).symm
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
theorem reducedPure_compressedTypicalSiteState
    (Ω : EuclideanSpace ℂ ((v : V) → β v)) (hXB : Disjoint X B)
    (E : Finset (Configuration β X)) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let χ : Fin E.card × Configuration β Xᶜ → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.1, x.2)
    (reducedPure (compressedSiteSpace β X (Fin E.card))
        (WithLp.toLp 2 (fun x ↦ χ (Equiv.piOptionEquivProd x)))
        (exteriorRegion X B)).submatrix
          (exteriorRegionEquiv β X B (Fin E.card) hXB).symm
          (exteriorRegionEquiv β X B (Fin E.card) hXB).symm =
      reducedPure β (typicalPureState β Ω X E) B := by
  intro ΩX χ
  rw [reducedPure_exteriorSiteState]
  exact partialTraceLeft_compressedTypicalPureState_region β Ω X B hXB E

end FiniteProduct
