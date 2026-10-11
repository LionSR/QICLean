/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellMetricFactorPositivity
import QICLean.Representation.BellSymmetricPinProjection
import QICLean.Analysis.OperatorMean.MeanTreeIntertwine
import QICLean.Algebra.MatrixSandwichIntertwine

/-!
# The actual Bell pin and the weighted mean tree

The insertion is the literal map from the exterior coordinates to the original
physical coordinates. Exterior central label observables commute with
`J * Π * Jᴴ`: this is derived from their actual rectangular intertwining,
self-adjointness, and commutation with the exterior symmetry projection.
Consequently the original and exterior metric factors have the same action
through this operator. The existing weighted-mean and real-power identities
then transport this equality without changing the replica label weights.

The statements allow an arbitrary inserted vector. For a unit vector the
operator `J * Π * Jᴴ` is the orthogonal projection already constructed in
`BellSymmetricPinProjection`. Each family below concerns one band, with
arbitrary status labels. No assertion of positivity for an unrestricted
product of different original bands is made.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 291–308 and 370–381,
  `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* The weighted mean is as in `06-transport.tex`, lines 28–34 and
  Lemma 7.1, `transport:means`.

-/

open Matrix PermutationRepresentation FiniteProduct
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => compressedSiteSpace β X R
local notation "B" => Configuration β X × C

local instance bellPinnedTreeConfigDecidableEq (k : ℕ) : DecidableEq (Config k ι₀) :=
  Fintype.decidablePiFintype

/-- Every actual exterior label observable commutes with the Bell-inserted
symmetric operator. The label function remains arbitrary and unchanged.

Source: area-law manuscript, `07-comparators.tex`, lines 291–308,
`comparator:pinned-metric`. -/
theorem commute_labelObservable_bellPin (k : ℕ) (Q : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : B → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe B k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
    Commute (labelObservable (subsystemPerm k ι₀
      ((Q \ X).image fun v ↦ some (some v))) f) (J * Pe * Jᴴ) := by
  intro e J Pe
  let L₀ := labelObservable (subsystemPerm k ι₀
    ((Q \ X).image fun v ↦ some (some v))) f
  let L := labelObservable (subsystemPerm k ιe (exteriorRegion X Q)) f
  have hL₀ : L₀.IsHermitian := isHermitian_labelObservable _ _
  have hL : L.IsHermitian := isHermitian_labelObservable _ _
  have hJ : L₀ * J = J * L :=
    labelObservable_mul_bellInsertion_exterior β X C R k Q f b
  have hJadj : Jᴴ * L₀ = L * Jᴴ :=
    (hL₀.conjTranspose_intertwine hL J hJ).symm
  have hSym : Commute L Pe :=
    commute_labelObservable_symProj ιe k (exteriorRegion X Q) f
  change L₀ * (J * Pe * Jᴴ) = (J * Pe * Jᴴ) * L₀
  calc
    L₀ * (J * Pe * Jᴴ) = (L₀ * J) * Pe * Jᴴ := by simp only [Matrix.mul_assoc]
    _ = (J * L) * Pe * Jᴴ := by rw [hJ]
    _ = (J * Pe) * (L * Jᴴ) := by
      rw [Matrix.mul_assoc J L Pe, hSym.eq]
      simp only [Matrix.mul_assoc]
    _ = (J * Pe) * (Jᴴ * L₀) := by rw [← hJadj]
    _ = (J * Pe * Jᴴ) * L₀ := by simp only [Matrix.mul_assoc]

/-- The two actual metric factors preserve the Bell-inserted symmetric
operator and have the same action through it. The replica weights are those
of the original full family in every factor.

Source: area-law manuscript, `07-comparators.tex`, lines 299–308,
`comparator:pinned-metric`. -/
theorem replicaMetric_factors_bellPin [∀ v, Nonempty (ι₀ v)]
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (U Y : Finset V)
    (hUY : Disjoint U Y) (b : B → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe B k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
    let P := J * Pe * Jᴴ
    let W := replicaMetric ι₀ t k
    let Q := insert (some none) ((X ∪ U).image fun v ↦ some (some v))
    let F := insert none (((X ∪ (U ∪ Y))ᶜ).image fun v ↦ some (some v))
    let E := fun Z : Finset V ↦ (Z \ X).image fun v ↦ some (some v)
    let A := ((W Q)⁻¹ * (W F)⁻¹ * W (E Y)) ^ 2
    let D := ((W (E U))⁻¹ * (W (E (U ∪ Y)))⁻¹ * W (E Y)) ^ 2
    Commute A P ∧ Commute D P ∧ A * P = P * D := by
  intro e J Pe P W Q F E A D
  have hSym : Pe.IsHermitian :=
    (exists_labelProj_eq_symProj (G := Equiv.Perm (Fin k))
      (X := Config k ιe)).elim (fun l hl ↦
        (hl (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)) ▸ isHermitian_labelProj _ l)
  have hP : P.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose J hSym
  have hpos := posDef_bellMetric_factors β X C R ht k U Y hUY
  have hA : A.IsHermitian := hpos.1.isHermitian
  have hD : D.IsHermitian := hpos.2.isHermitian
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι₀ t
  have hinv (Z : Finset (Option (Option V))) : (W Z)⁻¹ =
      labelObservable (subsystemPerm k ι₀ Z) (fun l ↦ (w l)⁻¹) :=
    labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι₀ ht l).ne')
  have hext (Z : Finset V) (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
      Commute (labelObservable (subsystemPerm k ι₀ (E Z)) f) P :=
    commute_labelObservable_bellPin β X C R k Z f b
  have hDP : Commute D P := by
    dsimp only [D]
    rw [hinv, hinv]
    exact (((hext U _).mul_left (hext (U ∪ Y) _)).mul_left (hext Y w)).pow_left 2
  have hAP : A * P = P * D := by
    have hK : A * (J * Pe) = D * (J * Pe) :=
      replicaMetric_factor_mul_bellInsertion_symProj β X C R ht k U Y b
    calc
      A * P = D * P := by
        simpa only [P, Matrix.mul_assoc] using
          congrArg (fun (L : Matrix (Config k ι₀) (Config k ιe) ℂ) ↦ L * Jᴴ) hK
      _ = P * D := hDP.eq
  have hPA : P * A = D * P := by
    simpa only [Matrix.conjTranspose_mul, hP.eq, hA.eq, hD.eq] using
      congrArg Matrix.conjTranspose hAP
  refine ⟨?_, hDP, hAP⟩
  change A * P = P * A
  exact hAP.trans (hDP.eq.symm.trans hPA.symm)

/-- An actual weighted mean tree of the original factors and the corresponding
exterior factors have the same action through the Bell-inserted symmetric
operator. The identity persists under every real power, including negative
powers. Positivity and both commutations are derived from the actual region
relations; no intertwining or positivity conclusion is supplied as a premise.

Source: area-law manuscript, `07-comparators.tex`, lines 299–308 and 370–381;
`06-transport.tex`, lines 28–34 and Lemma 7.1, `transport:means`. -/
theorem replicaMetric_meanTree_bellPin {S : Type*}
    [∀ v, Nonempty (ι₀ v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (U Y : S → Finset V) (hUY : ∀ j, Disjoint (U j) (Y j))
    (b : B → ℂ) (T : Matrix.MeanTree S) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe B k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
    let P := J * Pe * Jᴴ
    let W := replicaMetric ι₀ t k
    let Q := fun j ↦ insert (some none) ((X ∪ U j).image fun v ↦ some (some v))
    let F := fun j ↦ insert none
      (((X ∪ (U j ∪ Y j))ᶜ).image fun v ↦ some (some v))
    let E := fun Z : Finset V ↦ (Z \ X).image fun v ↦ some (some v)
    let A := fun j ↦ ((W (Q j))⁻¹ * (W (F j))⁻¹ * W (E (Y j))) ^ 2
    let D := fun j ↦ ((W (E (U j)))⁻¹ *
      (W (E (U j ∪ Y j)))⁻¹ * W (E (Y j))) ^ 2
    Commute (T.eval A) P ∧ Commute (T.eval D) P ∧
      T.eval A * P = P * T.eval D ∧
      ∀ s : ℝ, (T.eval A) ^ s * P = P * (T.eval D) ^ s := by
  intro e J Pe P W Q F E A D
  have hpos (j : S) := posDef_bellMetric_factors β X C R ht k (U j) (Y j) (hUY j)
  have hA : ∀ j, (A j).PosDef := fun j ↦ (hpos j).1
  have hD : ∀ j, (D j).PosDef := fun j ↦ (hpos j).2
  have hpin (j : S) := replicaMetric_factors_bellPin β X C R ht k
    (U j) (Y j) (hUY j) b
  have hAP : T.eval A * P = P * T.eval D :=
    Matrix.MeanTree.eval_intertwine hA hD P (fun j ↦ (hpin j).2.2) T
  refine ⟨(Matrix.MeanTree.commute_eval_right hA (fun j ↦ (hpin j).1.symm) T).symm,
    (Matrix.MeanTree.commute_eval_right hD (fun j ↦ (hpin j).2.1.symm) T).symm,
    hAP, ?_⟩
  exact fun s ↦ (Matrix.MeanTree.posDef_eval hA T).posSemidef.rpow_intertwine
    (Matrix.MeanTree.posDef_eval hD T).posSemidef P hAP s

end TensorPower
