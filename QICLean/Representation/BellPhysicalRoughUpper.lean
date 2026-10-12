/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellPhysicalWitness
import QICLean.Representation.BellCompressedInverseNorm
import QICLean.Analysis.BellOverlapLogBound

/-!
# The rough upper comparison for the supplied Schmidt--Bell prevector

Fix the original physical state, a positive-mass spectral selection, the
supplied auxiliary-label sequence, and a finite nested family of regions.
The actual auxiliary-mass estimate gives an upper bound on the negative
logarithm of the norm of the original prevector under the inverse metric.
The metric and the vector use the same supplied symmetric coordinates.

The polynomial constant and eventual threshold are chosen before the band
families, cutoff bounds, mean tree and inverse-power exponent. The displayed
remainder is uniform in these choices when the number of bands is fixed.
The auxiliary register on the selected spectral space is indexed by that
space itself. Its identification with an enumerated register is separate.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 153--163, 283--308,
332--381 and 659--667, `comparator:rough-upper`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Topology Matrix PermutationRepresentation TensorPower
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder symmDiff
open scoped MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace FiniteProduct

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (Configuration β X))

local notation "A" => Configuration β X
local notation "B" => Configuration β Xᶜ
local notation "ι₀" => addedSiteSpace (addedSiteSpace β E) (Fin E.card)
local notation "ιe" => compressedSiteSpace β X (Fin E.card)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (reducedPure_posSemidef β Ω X)) E

local instance bellPhysicalRoughUpperConfigDecidableEq (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

open Classical in
/-- The rough upper estimate for the original supplied-label prevector and
actual compressed band metric. The auxiliary-mass premise belongs to the
same state, spectral selection and label sequence. The polynomial constant
and eventual threshold are independent of the subsequent matrix mean tree,
band families and cutoff bounds. Source: area-law manuscript,
`07-comparators.tex`, `comparator:rough-upper`, lines 153--163,
283--308, 332--381 and 659--667. -/
theorem eventually_suppliedSchmidtBell_rough_upper {S : Type*} [Finite S]
    (hΩ : ‖Ω‖ = 1) (hz : 0 < z)
    (regions : List (Finset V))
    (hnested : regions.Pairwise fun D D' ↦ D ⊆ D' ∨ D' ⊆ D)
    (hdisjoint : ∀ D ∈ regions, Disjoint X D)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    {t : ℝ} (ht : 0 < t) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let ψ : B × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (Config k ιe) := fun k ↦
      WithLp.toLp 2 (fun x ↦ ∏ j, ψ ((fun v ↦ x j (some v)), x j none))
    let q : ℕ → ℝ := fun k ↦
      ‖toEuclideanLin (labelProj (subsystemPerm k ιe {none}) (ell k)) (Ψ k)‖ ^ 2
    (∀ᶠ k : ℕ in atTop,
      1 / (2 * (((k + 1 : ℕ) : ℝ) ^ (E.card ^ 2))) ≤ q k) →
    ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ k : ℕ in atTop,
      ∀ (n : ℕ) (Z : Matrix (Config k ι₀) (Fin n) ℂ),
      Zᴴ * Z = 1 →
      Z * Zᴴ = symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) →
      ∀ (K : ℕ) (U Y : S → Fin K → Finset V),
      (∀ j g, Disjoint (U j g) (Y j g)) →
      (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
      (∀ j g, Disjoint X (U j g ∪ Y j g)) →
      ∀ (T : Matrix.MeanTree S) (Bsh Bexc : ℝ),
      (∀ D ∈ regions, entropy β Ω D ≤ Bsh) →
      (∀ j g (Q : Finset V), Q = U j g ∨ Q = U j g ∪ Y j g →
        ∃ D ∈ regions, (D ⊆ Q ∨ Q ⊆ D) ∧
          1 + Real.log (Fintype.card (Configuration β (D ∆ Q))) ≤ Bexc) →
      ∀ s : ℝ, 2 * s ∈ Set.Icc (0 : ℝ) 1 →
      let τ := schmidtBellWitnessEquiv β X E k
      let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
        (schmidtBellSitePrevector β X E k ΩX (ell k) ∘ τ)
      let extRegion := fun Q : Finset V ↦ (Q \ X).image fun x ↦ some (some x)
      let W := replicaMetric ι₀ t k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun x ↦ some (some x))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun x ↦ some (some x))
      let H := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (extRegion (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ T.eval (fun j ↦ Zᴴ * H j g * Z)).prod
      let Nsq := ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ v)‖ ^ 2
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (E.card : ℝ) - Real.log z +
          8 * s * t * (K : ℝ) * (Bsh / z + Bexc) +
          Real.bellOverlapRemainder E.card c K k := by
  classical
  intro ΩX ψ Ψ q hmass
  obtain ⟨hsite, hb, hw⟩ :=
    eventually_exists_suppliedSchmidtBell_physicalWitness
      (S := S) β Ω X E hΩ hz regions hnested hdisjoint ell hmass
  obtain ⟨c, hc, hC⟩ :=
    letI : ∀ o, Nonempty (ι₀ o) := hsite
    exists_replicaMetric_compressed_bell_inverse_norm_bound
      (S := S) β X E (Fin E.card) ht
  refine ⟨c, hc, (hw.and (eventually_ge_atTop 1)).mono (fun k ⟨hw, hk⟩ ↦ ?_)⟩
  obtain ⟨Φ, hΦ, _, _, _, hover, hcuts⟩ := hw
  intro n Z hZ hZZ K U Y hUY hnest hXY T Bsh Bexc hsh hmatch s hs
    τ v extRegion W Q F H M Nsq
  have hu := hC k n Z hZ hZZ K U Y hUY hnest (selectedBellVector ΩX E) hb
    T ((k : ℝ) * (Bsh / z + Bexc)) Φ v hΦ
    (hcuts K U Y Bsh Bexc hsh hXY hmatch) s hs
  done

end FiniteProduct
