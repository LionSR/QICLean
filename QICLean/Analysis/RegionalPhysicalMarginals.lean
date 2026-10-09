/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.RegionalFiveFactorCoordinates
import QICLean.Analysis.PhysicalSingletonDensity
import QICLean.Analysis.SurprisalMoment
import QICLean.Representation.RegionalPhysicalVector
import QICLean.Entropy.FiniteProduct
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The original physical marginals in regional coordinates

Grouping the physical sites into two disjoint regions and the complement
of their union changes only the coordinates of the original vector. Each
of the three singleton density matrices is exactly its original regional
reduction. Consequently its entropy and every real surprisal moment are
unchanged, including when the density matrix has a nontrivial kernel.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 20--37, 421--456 and 550--590, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u

noncomputable section
open TensorPower
open scoped Matrix

namespace FiniteProduct

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The three original physical regions, in the order used by the
five-factor estimates. Source: `07-comparators.tex`, lines 20--37. -/
def regionalPhysicalRegion (Q Y : Finset V) : Fin 3 → Finset V :=
  ![Q, Y, (Q ∪ Y)ᶜ]


end FiniteProduct

namespace Matrix

private def physicalRemainingPairEquiv (ι : Fin 5 → Type*) (j : Fin 3) :
    (ι ((j.succAbove 0).castAdd 2) × ι ((j.succAbove 1).castAdd 2)) ≃
      ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)) :=
  (piFinTwoEquiv (fun i : Fin 2 => ι ((j.succAbove i).castAdd 2))).symm.trans
    (Equiv.piCongrLeft (fun l : {l : Fin 3 // l ≠ j} => ι (l.1.castAdd 2))
      (finSuccAboveEquiv j))

private theorem singletonDensity_eq_reducedPure_of_coordinates
    {V : Type*} [Fintype V] [DecidableEq V]
    (β : V → Type*) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ((v : V) → β v) → ℂ) (T : Finset V) (j : Fin 3)
    (e : ((v : V) → β v) ≃ ι 0 × (ι 1 × ι 2))
    (a : FiniteProduct.Configuration β T ≃ ι (j.castAdd 2))
    (b : FiniteProduct.Configuration β Tᶜ ≃
      ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)))
    (hcoords : ∀ x, physicalSingletonEquiv ι j (e x) =
      (a.prodCongr b) (FiniteProduct.splitEquiv β T x)) :
    physicalSingletonDensity ι (Ω ∘ e.symm) j =
      (FiniteProduct.reducedPure β (WithLp.toLp 2 Ω) T).submatrix a.symm a.symm := by
  have he : e.trans (physicalSingletonEquiv ι j) =
      (FiniteProduct.splitEquiv β T).trans (a.prodCongr b) := by
    ext x
    exact hcoords x
  let M := (vecMulVec Ω (star Ω)).submatrix
    (FiniteProduct.splitEquiv β T).symm (FiniteProduct.splitEquiv β T).symm
  calc
    _ = partialTraceRight (M.submatrix (a.prodCongr b).symm
        (a.prodCongr b).symm) := by
      unfold physicalSingletonDensity
      congr 1
      ext x y
      change Ω ((e.trans (physicalSingletonEquiv ι j)).symm x) *
          star (Ω ((e.trans (physicalSingletonEquiv ι j)).symm y)) =
        Ω (((FiniteProduct.splitEquiv β T).trans (a.prodCongr b)).symm x) *
          star (Ω (((FiniteProduct.splitEquiv β T).trans (a.prodCongr b)).symm y))
      rw [he]
    _ = _ := partialTraceRight_submatrix_prod_equiv a b M

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (C R : Type u) [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

/-- The three actual five-factor singleton densities are the original
regional reductions, with no normalization or nonsingularity assumption.
Source: `07-comparators.tex`, lines 421--456 and 550--590. -/
theorem regional_physicalSingletonDensity_eq_reducedPure
    (Ω : ((v : V) → β v) → ℂ) (Q Y : Finset V) (hQY : Disjoint Q Y) :
    let ι := regionalFiveFactorSpace β C R Q Y
    let ψ := Ω ∘ (FiniteProduct.regionalPhysicalEquiv β Q Y hQY).symm
    physicalSingletonDensity ι ψ 0 = FiniteProduct.reducedPure β (WithLp.toLp 2 Ω) Q ∧
      physicalSingletonDensity ι ψ 1 = FiniteProduct.reducedPure β (WithLp.toLp 2 Ω) Y ∧
      physicalSingletonDensity ι ψ 2 =
        FiniteProduct.reducedPure β (WithLp.toLp 2 Ω) (Q ∪ Y)ᶜ := by
  intro ι ψ
  let e := FiniteProduct.regionalPhysicalEquiv β Q Y hQY
  let b₀ := (FiniteProduct.complementUnionEquiv β Q Y hQY).trans
    (physicalRemainingPairEquiv ι 0)
  let b₁ := (FiniteProduct.complementUnionEquiv β Y Q hQY.symm).trans
    (((Equiv.refl _).prodCongr
      (FiniteProduct.configurationCongr β
        (congrArg (fun T : Finset V => Tᶜ) (Finset.union_comm Y Q)))).trans
      (physicalRemainingPairEquiv ι 1))
  let b₂ := (FiniteProduct.configurationCongr β (compl_compl (Q ∪ Y))).trans
    ((FiniteProduct.unionEquiv β Q Y hQY).trans (physicalRemainingPairEquiv ι 2))
  have h₀ (x : (v : V) → β v) : physicalSingletonEquiv ι 0 (e x) =
      ((Equiv.refl _).prodCongr b₀) (FiniteProduct.splitEquiv β Q x) := by
    apply Prod.ext
    · rfl
    · apply (physicalRemainingPairEquiv ι 0).symm.injective
      simpa only [b₀, Equiv.prodCongr_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
  have h₁ (x : (v : V) → β v) : physicalSingletonEquiv ι 1 (e x) =
      ((Equiv.refl _).prodCongr b₁) (FiniteProduct.splitEquiv β Y x) := by
    apply Prod.ext
    · rfl
    · apply (physicalRemainingPairEquiv ι 1).symm.injective
      simp only [b₁, Equiv.prodCongr_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
      apply Prod.ext <;> funext v <;>
        simp only [FiniteProduct.configurationCongr_apply]
  have h₂ (x : (v : V) → β v) : physicalSingletonEquiv ι 2 (e x) =
      ((Equiv.refl _).prodCongr b₂) (FiniteProduct.splitEquiv β (Q ∪ Y)ᶜ x) := by
    apply Prod.ext
    · rfl
    · apply (physicalRemainingPairEquiv ι 2).symm.injective
      simp only [b₂, Equiv.prodCongr_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
      apply Prod.ext <;> funext v <;>
        simp only [FiniteProduct.configurationCongr_apply]
  exact ⟨singletonDensity_eq_reducedPure_of_coordinates β ι Ω Q 0 e
      (Equiv.refl _) b₀ h₀,
    singletonDensity_eq_reducedPure_of_coordinates β ι Ω Y 1 e
      (Equiv.refl _) b₁ h₁,
    singletonDensity_eq_reducedPure_of_coordinates β ι Ω (Q ∪ Y)ᶜ 2 e
      (Equiv.refl _) b₂ h₂⟩

private theorem spectral_statistics_eq_of_eq
    {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    vonNeumannEntropy A hA = vonNeumannEntropy B hB ∧
      ∀ v : ℝ, Entropy.surprisalMoment hA.eigenvalues v =
        Entropy.surprisalMoment hB.eigenvalues v := by
  subst B
  exact ⟨rfl, fun _ => rfl⟩

/-- Entropy and every real surprisal moment in the grouped marginal are
those of the original region. Zero spectral weights remain zero summands;
no inverse density or positive-definiteness assumption is used.
Source: `07-comparators.tex`, lines 550--590. -/
theorem regional_physicalSingleton_spectral_statistics
    (Ω : ((v : V) → β v) → ℂ) (Q Y : Finset V) (hQY : Disjoint Q Y) (j : Fin 3) :
    let ι := regionalFiveFactorSpace β C R Q Y
    let ψ := Ω ∘ (FiniteProduct.regionalPhysicalEquiv β Q Y hQY).symm
    let T := FiniteProduct.regionalPhysicalRegion Q Y j
    vonNeumannEntropy (physicalSingletonDensity ι ψ j)
        (posSemidef_physicalSingletonDensity ι ψ j).isHermitian =
      FiniteProduct.entropy β (WithLp.toLp 2 Ω) T ∧
      ∀ v : ℝ, Entropy.surprisalMoment
          (posSemidef_physicalSingletonDensity ι ψ j).isHermitian.eigenvalues v =
        Entropy.surprisalMoment
          (FiniteProduct.reducedPure_posSemidef β (WithLp.toLp 2 Ω) T).isHermitian.eigenvalues v := by
  intro ι ψ T
  obtain ⟨h₀, h₁, h₂⟩ := regional_physicalSingletonDensity_eq_reducedPure β C R Ω Q Y hQY
  fin_cases j
  · exact spectral_statistics_eq_of_eq h₀ _ _
  · exact spectral_statistics_eq_of_eq h₁ _ _
  · exact spectral_statistics_eq_of_eq h₂ _ _

end Matrix
