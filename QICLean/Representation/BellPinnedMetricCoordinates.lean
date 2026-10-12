/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.BellInsertionSymmetry
import QICLean.Representation.ReplicaSimilarity

/-!
# The actual metric factor on the pinned symmetric range

The original site family has physical coordinates β and separate auxiliary
coordinates C and R. The Bell insertion groups X and C and retains R in the
exterior. On the inserted symmetric range, complementary labels identify
the far region R together with the physical complement of X ∪ U with the
exterior part of U. The actual far-region action is derived from this
complementarity and the literal insertion identities.

Consequently the original squared three-factor metric acts on this range
exactly as the product involving the exterior U, U ∪ Y, and Y regions.
Every replica metric in that equality is defined on the original full
family. Intermediate exterior observables use the same original label
weight and its reciprocal, not a weight recomputed at the compressed
dimension. No metric compression, vector equality, or operator estimate is
assumed. The inserted vector need not be normalized.

The auxiliary-label identity from the preceding coordinate result retains
any chosen R label through the same insertion. The present equality holds
on the whole inserted symmetric range and hence also on each such label
sector. Restriction of a matrix mean to that range is a separate result.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308,
  `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open Matrix PermutationRepresentation FiniteProduct

universe u

noncomputable section

namespace TensorPower

section Symmetry

variable {F : Type*} [Fintype F] [DecidableEq F]
variable (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

/-- A subsystem's central label function commutes with the full symmetry
average, by the existing nested group-algebra commutation theorem.

Source: area-law manuscript, `05-replicas.tex`, lines 101–102, and
`07-comparators.tex`, lines 299–308. -/
theorem commute_labelObservable_symProj (k : ℕ) (Q : Finset F)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k ι Q) f)
      (symProj (copyPerm ((v : F) → ι v) k)) := by
  simpa only [subsystemPerm_univ k ι] using
    commute_labelObservable_symProj_of_subset ι k Q Finset.univ
      (Finset.subset_univ Q) f

end Symmetry

/-- Append an invariant symmetry projection to a rectangular intertwining. -/
private theorem intertwine_mul_projection
    {m n : Type*} [Fintype m] [Fintype n]
    {A : Matrix m m ℂ} {B P : Matrix n n ℂ} {J : Matrix m n ℂ}
    (h : A * J = J * B) (hP : Commute B P) :
    A * (J * P) = (J * P) * B := by
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, hP.eq, ← Matrix.mul_assoc]

/-- Rectangular intertwinings multiply without any commutation assumption. -/
private theorem intertwine_mul
    {m n : Type*} [Fintype m] [Fintype n]
    {A B : Matrix m m ℂ} {A' B' : Matrix n n ℂ} {K : Matrix m n ℂ}
    (hA : A * K = K * A') (hB : B * K = K * B') :
    (A * B) * K = K * (A' * B') := by
  rw [Matrix.mul_assoc, hB, ← Matrix.mul_assoc, hA, Matrix.mul_assoc]

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => compressedSiteSpace β X R
local notation "B" => Configuration β X × C

/-- The actual far region consists of R and the physical complement of X ∪ U. -/
private theorem bellFarRegion_eq_compl (U : Finset V) :
    insert none (((X ∪ U)ᶜ).image fun v ↦ some (some v)) =
      (insert (some none) ((X ∪ U).image fun v ↦ some (some v)))ᶜ := by
  ext o
  cases o with
  | none => simp
  | some o => cases o <;> simp [Finset.mem_image]

/-- On the actual Bell-inserted symmetric range, the far-region label is the
exterior-U label. This is the original full-system complementarity statement,
transported through the literal Bell insertion for the same arbitrary f.

Source: area-law manuscript, `07-comparators.tex`, lines 299–308,
`comparator:pinned-metric`. -/
theorem labelObservable_mul_bellInsertion_symProj_far (k : ℕ) (U : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (b : B → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe B k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
    labelObservable (subsystemPerm k ι₀
        (insert none (((X ∪ U)ᶜ).image fun v ↦ some (some v)))) f * (J * Pe) =
      (J * Pe) * labelObservable (subsystemPerm k ιe (exteriorRegion X U)) f := by
  intro e J Pe
  let P := insert (some none) ((X ∪ U).image fun v ↦ some (some v))
  let P₀ := symProj (copyPerm ((v : Option (Option V)) → ι₀ v) k)
  have hsym : P₀ * J = J * Pe := symProj_mul_bellInsertion β X C R k b
  have hcompl : labelObservable (subsystemPerm k ι₀ Pᶜ) f * P₀ =
      labelObservable (subsystemPerm k ι₀ P) f * P₀ := by
    simp only [labelObservable, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    rw [smul_mul_assoc, smul_mul_assoc, labelProj_mul_symProj_compl]
    simp only [compl_compl, P₀]
  rw [bellFarRegion_eq_compl X U]
  calc
    labelObservable (subsystemPerm k ι₀ Pᶜ) f * (J * Pe) =
        labelObservable (subsystemPerm k ι₀ P) f * (J * Pe) := by
      rw [← hsym, ← Matrix.mul_assoc, hcompl, Matrix.mul_assoc, hsym]
    _ = _ := intertwine_mul_projection
      (labelObservable_mul_bellInsertion_withPin β X C R k U f b)
      (commute_labelObservable_symProj ιe k (exteriorRegion X U) f)

/-- The actual original metric factor agrees on the Bell-inserted symmetric
range with the exterior U, U ∪ Y, Y product. All six replica metrics in this
identity use the same original full-system family and hence the same weights.
The far region is literally R together with the physical complement of X ∪ U ∪ Y.

Source: area-law manuscript, `07-comparators.tex`, lines 299–308,
`comparator:pinned-metric`. -/
theorem replicaMetric_factor_mul_bellInsertion_symProj
    [∀ v, Nonempty (ι₀ v)] {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (U Y : Finset V) (b : B → ℂ) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe B k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option ↥(Xᶜ)) → ιe v) k)
    let W := replicaMetric ι₀ t k
    let P := insert (some none) ((X ∪ U).image fun v ↦ some (some v))
    let F := insert none (((X ∪ (U ∪ Y))ᶜ).image fun v ↦ some (some v))
    let E := fun Q : Finset V ↦ (Q \ X).image fun v ↦ some (some v)
    ((W P)⁻¹ * (W F)⁻¹ * W (E Y)) ^ 2 * (J * Pe) =
      ((W (E U))⁻¹ * (W (E (U ∪ Y)))⁻¹ * W (E Y)) ^ 2 * (J * Pe) := by
  intro e J Pe W P F E
  let K := J * Pe
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι₀ t
  let w' := fun l ↦ (w l)⁻¹
  let L := fun Q f ↦ labelObservable (subsystemPerm k ιe (exteriorRegion X Q)) f
  have hinv (Q : Finset (Option (Option V))) : (W Q)⁻¹ =
      labelObservable (subsystemPerm k ι₀ Q) w' :=
    labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι₀ ht l).ne')
  have hext (Q : Finset V) (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
      labelObservable (subsystemPerm k ι₀ (E Q)) f * K = K * L Q f :=
    intertwine_mul_projection
      (labelObservable_mul_bellInsertion_exterior β X C R k Q f b)
      (commute_labelObservable_symProj ιe k (exteriorRegion X Q) f)
  have hP : (W P)⁻¹ * K = K * L U w' := by
    rw [hinv]
    exact intertwine_mul_projection
      (labelObservable_mul_bellInsertion_withPin β X C R k U w' b)
      (commute_labelObservable_symProj ιe k (exteriorRegion X U) w')
  have hF : (W F)⁻¹ * K = K * L (U ∪ Y) w' := by
    rw [hinv]
    exact labelObservable_mul_bellInsertion_symProj_far β X C R k (U ∪ Y) w' b
  have hY : W (E Y) * K = K * L Y w := hext Y w
  have hU : (W (E U))⁻¹ * K = K * L U w' := by
    rw [hinv]
    exact hext U w'
  have hUY : (W (E (U ∪ Y)))⁻¹ * K = K * L (U ∪ Y) w' := by
    rw [hinv]
    exact hext (U ∪ Y) w'
  have horiginal := intertwine_mul (intertwine_mul hP hF) hY
  have hexterior := intertwine_mul (intertwine_mul hU hUY) hY
  have hsquareOriginal := intertwine_mul horiginal horiginal
  have hsquareExterior := intertwine_mul hexterior hexterior
  simpa only [pow_two] using hsquareOriginal.trans hsquareExterior.symm

end TensorPower
