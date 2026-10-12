/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellPhysicalRoughUpper
import QICLean.Representation.SchmidtBellEnumeratedCompression
import QICLean.Representation.SymmetricProjectionCoordinates

/-!
# The rough upper bound in enumerated physical coordinates

Enumerating the selected auxiliary register carries the upper comparison to
the original physical prevector with two auxiliary registers of equal dimension.
The symmetric coordinates, their column space and the label sequence are fixed.
The weights use the full one-copy dimension on both sides.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 80--110, 130--163,
  240--254, 283--308 and 332--381, manuscript revision
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
local notation "ι₀" => addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card)
local notation "ιe" => compressedSiteSpace β X (Fin E.card)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (reducedPure_posSemidef β Ω X)) E

local instance replicaPrevectorRoughUpperConfigDecidableEq (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

local instance replicaPrevectorRoughUpperSelectedConfigDecidableEq (k : ℕ) :
    DecidableEq (Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card))) :=
  Fintype.decidablePiFintype

open Classical in
/-- The rough upper estimate in the original physical and enumerated auxiliary
coordinates. The supplied symmetric isometry keeps the same column space,
and the common-label prevector is not selected again. The constant and
threshold precede the band families, mean tree and entropy bounds.
Source: area-law manuscript, `07-comparators.tex`, `comparator:rough-upper`,
lines 80--110, 130--163, 240--254, 283--308 and 332--381. -/
theorem eventually_suppliedReplicaPrevector_rough_upper {S : Type*} [Finite S]
    (hΩ : ‖Ω‖ = 1) (hz : 0 < z)
    (regions : List (Finset V))
    (hnested : regions.Pairwise fun D D' ↦ D ⊆ D' ∨ D' ⊆ D)
    (hdisjoint : ∀ D ∈ regions, Disjoint X D)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)))
    {t : ℝ} (ht : 0 < t) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (splitEquiv β X) Ω
    let ψ : B × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    let Ψ : (k : ℕ) → EuclideanSpace ℂ (Config k ιe) := fun _ ↦
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
      let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
        (replicaPrevector Ω E.card k (ell k) ∘
          globalReplicaCopiesEquiv β (Fin E.card) (Fin E.card) k)
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
  obtain ⟨c, hc, hu⟩ := eventually_suppliedSchmidtBell_rough_upper
    (S := S) β Ω X E hΩ hz regions hnested hdisjoint ell ht hmass
  refine ⟨c, hc, hu.mono fun k hk n Z hZ hZZ K U Y hUY hnest hXY
    T Bsh Bexc hsh hmatch s hs ↦ ?_⟩
  let e : Config k ι₀ ≃
      Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card)) :=
    Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight fun o ↦
      match o with
      | none => Equiv.refl (Fin E.card)
      | some none => (Finset.equivFin E).symm
      | some (some v) => Equiv.refl (β v)
  let ZE := Z.submatrix e.symm (id : Fin n → Fin n)
  have hZE : ZEᴴ * ZE = 1 := by
    simpa only [ZE, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id] using hZ
  done

end FiniteProduct
