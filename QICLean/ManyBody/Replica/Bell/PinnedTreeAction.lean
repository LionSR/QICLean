/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Bell.InsertionSymmetry
import QICLean.Analysis.OperatorMean.FiniteTree
import QICLean.Algebra.Hermitian.MatrixSandwichIntertwine
import QICLean.ManyBody.Replica.Bell.PinnedMetricCoordinates
import QICLean.ManyBody.Replica.Metric.LaminarBandMetrics
import Mathlib.Data.List.Forall2
import QICLean.ManyBody.Replica.Metric.CutoffNorm
import QICLean.Analysis.FunctionalCalculus.MatrixPowers
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import QICLean.Analysis.OperatorMean.MeanTreeUniformExpectation

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

It also contains the following results.

* `TensorPower.posDef_bellMetric_factors`: positivity of the actual Bell metric factors.
* `TensorPower.replicaMetric_bandProduct_bellPin`: the ordered product of actual band roots on the
  Bell pin.
* `TensorPower.exists_replicaPinnedLeaf_expectation_le`: the expectation of a literal pinned product
  leaf.
* `TensorPower.replicaPinnedTree_eval_eq_prod`,
  `TensorPower.exists_replicaPinnedTree_inverse_norm_bound`: the actual pinned band product and its
  inverse-power estimate.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 291–308 and 370–381,
  `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
* The weighted mean is as in `06-transport.tex`, lines 28–34 and
  Lemma 7.1, `transport:means`.

-/

open Matrix PermutationRepresentation

section MetricFactorPositivity

/-!
## Positivity of the actual Bell metric factors

For disjoint physical regions U and Y, the original pin region, the far
region, and the exterior part of Y are pairwise disjoint. Their positive
replica metrics commute, as do their inverses. The resulting squared factor
is positive definite. The corresponding exterior factor is the single-band
case of the existing positive pinned leaf.

Every metric uses the original full-system weights. The conclusion supplies
both positive matrices in the actual Bell coordinate identity. It requires
neither disjointness from X nor a supplied positivity certificate.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 283–308,
  `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped ComplexOrder

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R

/-- Both literal squared metric factors in the Bell insertion identity are
positive definite when the two physical regions are disjoint. All metrics
retain the original full-system weights.

Source: area-law manuscript, `07-comparators.tex`, lines 299–308,
`comparator:pinned-metric`. -/
theorem posDef_bellMetric_factors [∀ v, Nonempty (ι₀ v)]
    {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (U Y : Finset V) (hUY : Disjoint U Y) :
    let W := replicaMetric ι₀ t k
    let P := insert (some none) ((X ∪ U).image fun v ↦ some (some v))
    let F := insert none (((X ∪ (U ∪ Y))ᶜ).image fun v ↦ some (some v))
    let E := fun Q : Finset V ↦ (Q \ X).image fun v ↦ some (some v)
    (((W P)⁻¹ * (W F)⁻¹ * W (E Y)) ^ 2).PosDef ∧
      (((W (E U))⁻¹ * (W (E (U ∪ Y)))⁻¹ * W (E Y)) ^ 2).PosDef := by
  classical
  intro W P F E
  have hPF : Disjoint P F := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    cases o with
    | none => simp [P] at ho
    | some o =>
        cases o with
        | none => simp [F, Finset.mem_image] at h'o
        | some v =>
            have hp : v ∈ X ∨ v ∈ U := by simpa [P, Finset.mem_image] using ho
            have hf : v ∉ X ∧ v ∉ U ∧ v ∉ Y := by
              simpa [F, Finset.mem_image, not_or] using h'o
            exact hp.elim hf.1 hf.2.1
  have hPY : Disjoint P (E Y) := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    cases o with
    | none => simp [P] at ho
    | some o =>
        cases o with
        | none => simp [E, Finset.mem_image] at h'o
        | some v =>
            have hp : v ∈ X ∨ v ∈ U := by simpa [P, Finset.mem_image] using ho
            have hy : v ∈ Y ∧ v ∉ X := by simpa [E, Finset.mem_image] using h'o
            exact hp.elim hy.2 (fun hu ↦ Finset.disjoint_left.mp hUY hu hy.1)
  have hFY : Disjoint F (E Y) := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    cases o with
    | none => simp [E, Finset.mem_image] at h'o
    | some o =>
        cases o with
        | none => simp [E, Finset.mem_image] at h'o
        | some v =>
            have hf : v ∉ X ∧ v ∉ U ∧ v ∉ Y := by
              simpa [F, Finset.mem_image, not_or] using ho
            have hy : v ∈ Y ∧ v ∉ X := by simpa [E, Finset.mem_image] using h'o
            exact hf.2.2 hy.1
  have hEUY : Disjoint (E U) (E Y) := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp h'o
    have hyu' : y = u := Option.some.inj (Option.some.inj hyu)
    subst y
    exact Finset.disjoint_left.mp hUY (Finset.mem_sdiff.mp hu).1
      (Finset.mem_sdiff.mp hy).1
  have hEunion : E (U ∪ Y) = E U ∪ E Y := by
    simp only [E, Finset.union_sdiff_distrib, Finset.image_union]
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι₀ t
  have hinv (Q : Finset (Option (Option V))) : (W Q)⁻¹ =
      labelObservable (subsystemPerm k ι₀ Q) (fun l ↦ (w l)⁻¹) :=
    labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι₀ ht l).ne')
  have hcPF : Commute (W P)⁻¹ (W F)⁻¹ := by
    rw [hinv, hinv]
    exact commute_labelObservables_subsystemPerm_of_laminar ι₀ k
      (Or.inr (Or.inr hPF)) _ _
  have hcPY : Commute (W P)⁻¹ (W (E Y)) := by
    rw [hinv]
    exact commute_labelObservables_subsystemPerm_of_laminar ι₀ k
      (Or.inr (Or.inr hPY)) _ w
  have hcFY : Commute (W F)⁻¹ (W (E Y)) := by
    rw [hinv]
    exact commute_labelObservables_subsystemPerm_of_laminar ι₀ k
      (Or.inr (Or.inr hFY)) _ w
  constructor
  · have hroot := ((posDef_replicaMetric ι₀ ht k P).inv.mul_of_commute
      (posDef_replicaMetric ι₀ ht k F).inv hcPF).mul_of_commute
        (posDef_replicaMetric ι₀ ht k (E Y)) (hcPY.mul_left hcFY)
    exact (hroot.posSemidef.pow 2).posDef_iff_isUnit.mpr (hroot.isUnit.pow 2)
  · simpa only [W, hEunion] using
      posDef_replicaPinnedFactor ι₀ ht k (E U) (E Y) hEUY

end TensorPower

end

end MetricFactorPositivity

section PinnedTreeAction

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => ManyBody.compressedSiteSpace β X R
local notation "B" => ManyBody.RegionConfig β X × C

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
    let Pe := symProj (copyPerm ((v : Option {v // v ∉ X}) → ιe v) k)
    Commute (labelObservable (subsystemPerm k ι₀
      ((Q \ X).image fun v ↦ some (some v))) f) (J * Pe * Jᴴ) := by
  intro e J Pe
  let L₀ := labelObservable (subsystemPerm k ι₀
    ((Q \ X).image fun v ↦ some (some v))) f
  let L := labelObservable (subsystemPerm k ιe (ManyBody.exteriorRegion X Q)) f
  have hL₀ : L₀.IsHermitian := isHermitian_labelObservable _ _
  have hL : L.IsHermitian := isHermitian_labelObservable _ _
  have hJ : L₀ * J = J * L :=
    labelObservable_mul_bellInsertion_exterior β X C R k Q f b
  have hJadj : Jᴴ * L₀ = L * Jᴴ :=
    (hL₀.conjTranspose_intertwine hL J hJ).symm
  have hSym : Commute L Pe :=
    commute_labelObservable_symProj ιe k (ManyBody.exteriorRegion X Q) f
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
    let Pe := symProj (copyPerm ((v : Option {v // v ∉ X}) → ιe v) k)
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
        Eq.mp (congrArg Matrix.IsHermitian
          (hl (copyPerm ((v : Option {v // v ∉ X}) → ιe v) k))) (isHermitian_labelProj _ l))
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
    let Pe := symProj (copyPerm ((v : Option {v // v ∉ X}) → ιe v) k)
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

end

end PinnedTreeAction

section PinnedLeafExpectation

/-!
## The expectation of a literal pinned product leaf

The regions in one product leaf consist of successive disjoint bands: the
union of each inner region and its band lies in every later inner region.
The replica metrics therefore preserve the common label cutoffs. Applying
the actual metric and cutoff-inverse estimates to these factors gives a
homogeneous bound on their ordered product. The same region relations and
the positivity of the actual replica weights show that this product is
positive definite; no positivity hypothesis on the leaf is imposed.

The replica weights are those of the original full system. The vector is
arbitrary within the stated cutoffs; no normalization or symmetry is needed.
The empty product, zero copies, and negative cutoff thresholds are included.
This is the product of physical-region operators appearing after the Bell
restriction. Its identification with that restriction is a separate result.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, `comparator:nesting`,
  `comparator:pinned-metric`, and lines 356–373, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Compose two bounds on the same invariant set of vectors. -/
private theorem norm_mul_on_invariant {P : EuclideanSpace ℂ n → Prop}
    {A B : Matrix n n ℂ} {a b : ℝ} (ha : 0 ≤ a)
    (hA : ∀ v, P v → P (toEuclideanLin A v) ∧ ‖toEuclideanLin A v‖ ≤ a * ‖v‖)
    (hB : ∀ v, P v → P (toEuclideanLin B v) ∧ ‖toEuclideanLin B v‖ ≤ b * ‖v‖) :
    ∀ v, P v → P (toEuclideanLin (A * B) v) ∧
      ‖toEuclideanLin (A * B) v‖ ≤ (a * b) * ‖v‖ := by
  intro v hv
  obtain ⟨hBv, hBn⟩ := hB v hv
  obtain ⟨hABv, hABn⟩ := hA (toEuclideanLin B v) hBv
  simp only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply]
  refine ⟨hABv, hABn.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hBn ha

/-- A uniform invariant-set bound multiplies along an ordered list. -/
private theorem norm_listProd_on_invariant {P : EuclideanSpace ℂ n → Prop}
    (l : List (Matrix n n ℂ)) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ A ∈ l, ∀ v, P v →
      P (toEuclideanLin A v) ∧ ‖toEuclideanLin A v‖ ≤ b * ‖v‖) :
    ∀ v, P v → P (toEuclideanLin l.prod v) ∧
      ‖toEuclideanLin l.prod v‖ ≤ b ^ l.length * ‖v‖ := by
  induction l with
  | nil =>
    intro v hv
    simpa only [List.prod_nil, List.length_nil, pow_zero, one_mul,
      toEuclideanLin, toLpLin_one, LinearMap.id_apply] using And.intro hv (le_refl ‖v‖)
  | cons A l ih =>
    have htail := ih (fun B hB ↦ h B (List.mem_cons_of_mem A hB))
    simpa only [List.prod_cons, List.length_cons, pow_succ'] using
      norm_mul_on_invariant hb (h A List.mem_cons_self) htail

/-- A commuting matrix preserves the fixed space of another matrix. -/
private theorem fixed_toEuclideanLin_of_commute {C A : Matrix n n ℂ}
    (h : Commute C A) {v : EuclideanSpace ℂ n} (hv : toEuclideanLin C v = v) :
    toEuclideanLin C (toEuclideanLin A v) = toEuclideanLin A v := by
  have heq := congrArg (fun M ↦ toEuclideanLin M v) h.eq
  simp only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply] at heq
  simpa only [hv] using heq

end Matrix

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)]

/-- The expectation of the literal physical-region product in a pinned leaf
is bounded using only its actual nesting and its cutoffs. The vector need not
be normalized. One exponent works for every copy number, leaf length, choice
of regions, and real cutoff threshold.

Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:pinned-metric`, `comparator:nesting`, and lines 356–373. -/
theorem exists_replicaPinnedLeaf_expectation_le {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k K : ℕ) (U Y : Fin K → Finset F),
      (∀ g, Disjoint (U g) (Y g)) →
      (∀ g h, g < h → U g ∪ Y g ⊆ U h) →
      ∀ (T : ℝ) (φ : EuclideanSpace ℂ (Config k ι)),
        (∀ g, toEuclideanLin (labelCutoff (subsystemPerm k ι (U g)) T) φ = φ ∧
          toEuclideanLin (labelCutoff (subsystemPerm k ι (U g ∪ Y g)) T) φ = φ) →
        (inner ℂ φ (toEuclideanLin
          (List.ofFn fun g : Fin K ↦
            ((replicaMetric ι t k (U g))⁻¹ *
              (replicaMetric ι t k (U g ∪ Y g))⁻¹ *
                replicaMetric ι t k (Y g)) ^ 2).prod φ)).re ≤
          ((k : ℝ) + 2) ^ (C * (K : ℝ)) *
            Real.exp (4 * t * (K : ℝ) * T) * ‖φ‖ ^ 2 := by
  classical
  obtain ⟨C₀, hC₀, hC⟩ := exists_replicaMetric_cutoff_norm_bound ι ht
  refine ⟨6 * C₀, by positivity, ?_⟩
  intro k K U Y hdisj hnest T φ hφ
  let W : Finset F → Matrix (Config k ι) (Config k ι) ℂ := replicaMetric ι t k
  let P : EuclideanSpace ℂ (Config k ι) → Prop := fun v ↦ ∀ g,
    toEuclideanLin (labelCutoff (subsystemPerm k ι (U g)) T) v = v ∧
    toEuclideanLin (labelCutoff (subsystemPerm k ι (U g ∪ Y g)) T) v = v
  let p : ℝ := ((k : ℝ) + 2) ^ C₀
  let e : ℝ := Real.exp (t * T)
  have hp : 0 ≤ p := Real.rpow_nonneg (by positivity) _
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hpres (g : Fin K) (R : Finset F)
      (hR : R = U g ∨ R = Y g ∨ R = U g ∪ Y g)
      (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) (v) (hv : P v) :
      P (toEuclideanLin (labelObservable (subsystemPerm k ι R) f) v) := by
    intro h
    have hkeep (S : Finset F) (hS : S = U h ∨ S = Y h ∨ S = U h ∪ Y h)
        (hfix : toEuclideanLin (labelCutoff (subsystemPerm k ι S) T) v = v) :=
      Matrix.fixed_toEuclideanLin_of_commute
        (commute_labelObservables_subsystemPerm_of_laminar ι k
          (replicaBandRegions_subset_or_disjoint U Y hdisj hnest hR hS) f
            (fun l ↦ if Real.log l.dim ≤ T then 1 else 0)).symm hfix
    exact ⟨hkeep (U h) (Or.inl rfl) (hv h).1,
      hkeep (U h ∪ Y h) (Or.inr (Or.inr rfl)) (hv h).2⟩
  have hmetric (g : Fin K) : ∀ v, P v →
      P (toEuclideanLin (W (Y g)) v) ∧ ‖toEuclideanLin (W (Y g)) v‖ ≤ p * ‖v‖ := by
    intro v hv
    refine ⟨hpres g (Y g) (Or.inr (Or.inl rfl)) (replicaLabelWeight ι t) v hv, ?_⟩
    exact ((W (Y g)).l2_opNorm_mulVec v).trans
      (mul_le_mul_of_nonneg_right (hC k (Y g)).1 (norm_nonneg v))
  have hinverse (g : Fin K) (R : Finset F) (hR : R = U g ∨ R = U g ∪ Y g) :
      ∀ v, P v → P (toEuclideanLin ((W R)⁻¹) v) ∧
        ‖toEuclideanLin ((W R)⁻¹) v‖ ≤ (p * e) * ‖v‖ := by
    have hinv : (W R)⁻¹ = labelObservable (subsystemPerm k ι R)
        (fun l ↦ (replicaLabelWeight ι t l)⁻¹) :=
      labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι ht.le l).ne')
    have hR' : R = U g ∨ R = Y g ∨ R = U g ∪ Y g :=
      hR.imp_right Or.inr
    intro v hv
    refine ⟨by rw [hinv]; exact hpres g R hR' _ v hv, ?_⟩
    have hfix : toEuclideanLin (labelCutoff (subsystemPerm k ι R) T) v = v := by
      rcases hR with rfl | rfl
      · exact (hv g).1
      · exact (hv g).2
    have hrestrict : toEuclideanLin ((W R)⁻¹ *
        labelCutoff (subsystemPerm k ι R) T) v = toEuclideanLin ((W R)⁻¹) v := by
      simp only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply]
      exact congrArg (fun x ↦ toEuclideanLin ((W R)⁻¹) x) hfix
    rw [← hrestrict]
    exact (((W R)⁻¹ * labelCutoff (subsystemPerm k ι R) T).l2_opNorm_mulVec v).trans
      (mul_le_mul_of_nonneg_right ((hC k R).2 T) (norm_nonneg v))
  let a : ℝ := (p * e) * (p * e) * p
  let b : ℝ := a * a
  have ha : 0 ≤ a := mul_nonneg (mul_nonneg (mul_nonneg hp he) (mul_nonneg hp he)) hp
  have hb : 0 ≤ b := mul_nonneg ha ha
  have hroot (g : Fin K) : ∀ v, P v →
      P (toEuclideanLin ((W (U g))⁻¹ * (W (U g ∪ Y g))⁻¹ * W (Y g)) v) ∧
      ‖toEuclideanLin ((W (U g))⁻¹ * (W (U g ∪ Y g))⁻¹ * W (Y g)) v‖ ≤ a * ‖v‖ :=
    Matrix.norm_mul_on_invariant (mul_nonneg (mul_nonneg hp he) (mul_nonneg hp he))
      (Matrix.norm_mul_on_invariant (mul_nonneg hp he)
        (hinverse g (U g) (Or.inl rfl)) (hinverse g (U g ∪ Y g) (Or.inr rfl)))
      (hmetric g)
  have hfactor (g : Fin K) : ∀ v, P v →
      P (toEuclideanLin (((W (U g))⁻¹ * (W (U g ∪ Y g))⁻¹ * W (Y g)) ^ 2) v) ∧
      ‖toEuclideanLin (((W (U g))⁻¹ * (W (U g ∪ Y g))⁻¹ * W (Y g)) ^ 2) v‖ ≤
        b * ‖v‖ := by
    simpa only [pow_two] using Matrix.norm_mul_on_invariant ha (hroot g) (hroot g)
  let l := List.ofFn fun g : Fin K ↦
    ((W (U g))⁻¹ * (W (U g ∪ Y g))⁻¹ * W (Y g)) ^ 2
  have hprod := Matrix.norm_listProd_on_invariant l hb
    (List.forall_mem_ofFn_iff.mpr hfactor) φ hφ
  have hnorm : ‖toEuclideanLin l.prod φ‖ ≤ b ^ K * ‖φ‖ := by
    simpa only [l, List.length_ofFn] using hprod.2
  have hscalar : b ^ K = ((k : ℝ) + 2) ^ ((6 * C₀) * (K : ℝ)) *
      Real.exp (4 * t * (K : ℝ) * T) := by
    have hb' : b = p ^ 6 * e ^ 4 := by dsimp [b, a]; ring
    rw [hb', mul_pow, ← pow_mul, ← pow_mul]
    dsimp only [p, e]
    rw [← Real.rpow_mul_natCast (by positivity), ← Real.exp_nat_mul]
    congr 1 <;> congr 1 <;> push_cast <;> ring
  calc
    (inner ℂ φ (toEuclideanLin l.prod φ)).re ≤
        ‖inner ℂ φ (toEuclideanLin l.prod φ)‖ := Complex.re_le_norm _
    _ ≤ ‖φ‖ * ‖toEuclideanLin l.prod φ‖ := norm_inner_le_norm _ _
    _ ≤ ‖φ‖ * (b ^ K * ‖φ‖) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg φ)
    _ = b ^ K * ‖φ‖ ^ 2 := by ring
    _ = _ := by rw [hscalar]

end TensorPower

end PinnedLeafExpectation

section PinnedTreeExpectation

/-!
## The actual pinned band product and its inverse-power estimate

The same weighted mean tree is evaluated separately in each band, and the
resulting roots are multiplied in band order. The manuscript's nesting
across all statuses makes different bands commute. The existing finite-tree
factorization therefore identifies this actual product with the tree whose
inputs are the corresponding ordered products.

Positivity, cross-band commutation, and leaf expectation bounds are derived
from the actual replica metrics and region relations. The final overlap
estimate takes only the actual cutoff conditions and a unit test vector;
no leaf-positivity, commutation, or operator-bound certificate is assumed.
The original full-system label weights are retained throughout.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, `comparator:nesting`,
  `comparator:pinned-metric`, and lines 367–381; `06-transport.tex`,
  Lemma 7.1, `transport:means` and `transport:vector-jensen`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix.Norms.L2Operator InnerProductSpace MatrixOrder ComplexOrder

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)]
variable {J : Type*}

/-- Actual cross-status nesting identifies the ordered product of band roots
with the same weighted tree evaluated on the actual ordered leaf products.
Both positivity and the cross-band commutations are derived internally.

Source: area-law manuscript, `06-transport.tex`, Lemma 7.1,
`transport:means`; `07-comparators.tex`, lines 367–375. -/
theorem replicaPinnedTree_eval_eq_prod {t : ℝ} (ht : 0 ≤ t) (k K : ℕ)
    (U Y : J → Fin K → Finset F)
    (hdisj : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h)
    (T : Matrix.MeanTree J) :
    let D := fun j g ↦ ((replicaMetric ι t k (U j g))⁻¹ *
      (replicaMetric ι t k (U j g ∪ Y j g))⁻¹ * replicaMetric ι t k (Y j g)) ^ 2
    T.eval (fun j ↦ (List.ofFn (D j)).prod) =
      (List.ofFn fun g ↦ T.eval (D · g)).prod := by
  intro D
  obtain ⟨hD, hcomm⟩ := replicaPinnedBands_posDef_commute ι ht k K U Y hdisj hnest
  exact T.eval_listProd_ofFn hD hcomm

variable [Finite J]

/-- The actual ordered product of band roots satisfies the inverse-power
Cauchy–Schwarz bound obtained from the derived cutoff estimates and the two
Jensen inequalities. No positivity, commutation, or leaf estimate is supplied.
The vector u is arbitrary; only the test vector φ is normalized.

Source: area-law manuscript, `07-comparators.tex`, lines 367–381. -/
theorem exists_replicaPinnedTree_inverse_norm_bound {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k K : ℕ) (U Y : J → Fin K → Finset F),
      (∀ j g, Disjoint (U j g) (Y j g)) →
      (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
      ∀ (T : Matrix.MeanTree J) (a : ℝ)
        (φ u : EuclideanSpace ℂ (Config k ι)), ‖φ‖ = 1 →
        (∀ j g, toEuclideanLin (labelCutoff (subsystemPerm k ι (U j g)) a) φ = φ ∧
          toEuclideanLin (labelCutoff (subsystemPerm k ι (U j g ∪ Y j g)) a) φ = φ) →
        ∀ s : ℝ, 2 * s ∈ Set.Icc (0 : ℝ) 1 →
        let D := fun j g ↦ ((replicaMetric ι t k (U j g))⁻¹ *
          (replicaMetric ι t k (U j g ∪ Y j g))⁻¹ * replicaMetric ι t k (Y j g)) ^ 2
        ‖inner ℂ φ u‖ ^ 2 ≤
          (((k : ℝ) + 2) ^ (C * (K : ℝ)) * Real.exp (4 * t * (K : ℝ) * a)) ^
            (2 * s) *
          ‖toEuclideanLin (((List.ofFn fun g ↦ T.eval (D · g)).prod) ^ (-s)) u‖ ^ 2 := by
  classical
  obtain ⟨C, hC0, hC⟩ := exists_replicaPinnedLeaf_expectation_le ι ht
  refine ⟨C, hC0, ?_⟩
  intro k K U Y hdisj hnest T a φ u hφ hcuts s hs D
  let L : ℝ := ((k : ℝ) + 2) ^ (C * (K : ℝ)) * Real.exp (4 * t * (K : ℝ) * a)
  have hL : 0 < L := mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)
  have hpos (j : J) : (List.ofFn (D j)).prod.PosDef :=
    posDef_replicaPinnedLeaf ι ht.le k K (U j) (Y j) (hdisj j) (hnest j j)
  have hleaf (j : J) :
      (inner ℂ φ (toEuclideanLin (List.ofFn (D j)).prod φ)).re ≤ L := by
    simpa only [hφ, one_pow, mul_one] using
      hC k K (U j) (Y j) (hdisj j) (hnest j j) a φ (hcuts j)
  have h := T.norm_inner_sq_le_rpow_mul_inverse_norm_sq hpos φ u hφ hL hs hleaf
  rw [replicaPinnedTree_eval_eq_prod ι ht.le k K U Y hdisj hnest T] at h
  exact h

end TensorPower

end PinnedTreeExpectation

section PinnedProductAction

/-!
## The ordered product of actual band roots on the Bell pin

The same weighted mean tree is evaluated in every band. Its original and
exterior roots intertwine through the actual Bell-inserted symmetric operator;
this property is preserved by their ordered product. Cross-status nesting
of the physical bands makes the exterior product positive definite by the
existing pinned-tree factorization.

The conclusion does not assert positivity of the unrestricted original
product. Real powers of that product require its actual symmetric restriction,
which is a separate step. All weights here remain those of the original full
site family, and the inserted vector is arbitrary.

### References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, lines 20–37, 299–308 and 370–381,
  `comparator:nesting` and `comparator:pinned-metric`, at revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

-/

open scoped ComplexOrder MatrixOrder

universe u

noncomputable section

namespace TensorPower

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (β : V → Type u) (X : Finset V) (C R : Type u)
variable [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]

local notation "ι₀" => addedSiteSpace (addedSiteSpace β C) R
local notation "ιe" => ManyBody.compressedSiteSpace β X R

/-- The actual ordered original and exterior band products have the same
pinned action. The exterior product is positive definite by the actual
cross-band nesting, rather than by a supplied positivity premise.

Source: area-law manuscript, `07-comparators.tex`, lines 20–37, 299–308
and 370–381, `comparator:nesting` and `comparator:pinned-metric`. -/
theorem replicaMetric_bandProduct_bellPin {S : Type*}
    [∀ v, Nonempty (ι₀ v)] {t : ℝ} (ht : 0 ≤ t) (k K : ℕ)
    (U Y : S → Fin K → Finset V)
    (hdisj : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h)
    (b : (ManyBody.RegionConfig β X × C) → ℂ) (T : Matrix.MeanTree S) :
    let e := bellInsertionCopyEquiv β X C R k
    let J := (addedSiteInsertion ιe (ManyBody.RegionConfig β X × C) k b).submatrix e id
    let Pe := symProj (copyPerm ((v : Option {v // v ∉ X}) → ιe v) k)
    let P := J * Pe * Jᴴ
    let W := replicaMetric ι₀ t k
    let Q := fun j g ↦ insert (some none)
      ((X ∪ U j g).image fun v ↦ some (some v))
    let F := fun j g ↦ insert none
      (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
    let E := fun Z : Finset V ↦ (Z \ X).image fun v ↦ some (some v)
    let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (E (Y j g))) ^ 2
    let D := fun j g ↦ ((W (E (U j g)))⁻¹ *
      (W (E (U j g ∪ Y j g)))⁻¹ * W (E (Y j g))) ^ 2
    let M := (List.ofFn fun g ↦ T.eval (A · g)).prod
    let N := (List.ofFn fun g ↦ T.eval (D · g)).prod
    N.PosDef ∧ Commute M P ∧ Commute N P ∧ M * P = P * N := by
  classical
  intro e J Pe P W Q F E A D M N
  have hband (g : Fin K) :
      Commute (T.eval (A · g)) P ∧ Commute (T.eval (D · g)) P ∧
        T.eval (A · g) * P = P * T.eval (D · g) := by
    have h := replicaMetric_meanTree_bellPin β X C R ht k
      (U · g) (Y · g) (hdisj · g) b T
    exact ⟨h.1, h.2.1, h.2.2.1⟩
  have hMP : Commute M P := Commute.list_prod_left _ _
    (List.forall_mem_ofFn_iff.mpr fun g ↦ (hband g).1)
  have hNP : Commute N P := Commute.list_prod_left _ _
    (List.forall_mem_ofFn_iff.mpr fun g ↦ (hband g).2.1)
  have hMN : M * P = P * N := by
    apply List.rel_prod (R := fun A D ↦ A * P = P * D) (by simp) ?_ ?_
    · intro a d had a' d' had'
      rw [mul_assoc, had', ← mul_assoc, had, mul_assoc]
    · apply List.forall₂_iff_get.mpr
      refine ⟨by simp, ?_⟩
      intro i hi hi'
      simpa using (hband ⟨i, by simpa using hi⟩).2.2
  have hEunion (Z Z' : Finset V) : E (Z ∪ Z') = E Z ∪ E Z' := by
    simp only [E, Finset.union_sdiff_distrib, Finset.image_union]
  have hEmono {Z Z' : Finset V} (h : Z ⊆ Z') : E Z ⊆ E Z' :=
    Finset.image_subset_image (Finset.sdiff_subset_sdiff_left X h)
  have hdisjE (j : S) (g : Fin K) : Disjoint (E (U j g)) (E (Y j g)) := by
    apply Finset.disjoint_left.mpr
    intro o ho h'o
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ho
    obtain ⟨y, hy, hyu⟩ := Finset.mem_image.mp h'o
    have hyu' : y = u := Option.some.inj (Option.some.inj hyu)
    subst y
    exact Finset.disjoint_left.mp (hdisj j g) (Finset.mem_sdiff.mp hu).1
      (Finset.mem_sdiff.mp hy).1
  have hnestE (j j' : S) (g h : Fin K) (hgh : g < h) :
      E (U j g) ∪ E (Y j g) ⊆ E (U j' h) := by
    rw [← hEunion]
    exact hEmono (hnest j j' g h hgh)
  have hleaf (j : S) : (List.ofFn (D j)).prod.PosDef := by
    simpa only [D, W, hEunion] using posDef_replicaPinnedLeaf ι₀ ht k K
      (fun g ↦ E (U j g)) (fun g ↦ E (Y j g)) (hdisjE j)
      (fun g h hgh ↦ hnestE j j g h hgh)
  have hfactor : T.eval (fun j ↦ (List.ofFn (D j)).prod) = N := by
    simpa only [D, N, W, hEunion] using replicaPinnedTree_eval_eq_prod ι₀ ht k K
      (fun j g ↦ E (U j g)) (fun j g ↦ E (Y j g)) hdisjE hnestE T
  refine ⟨?_, hMP, hNP, hMN⟩
  rw [← hfactor]
  exact Matrix.MeanTree.posDef_eval hleaf T

end TensorPower

end

end PinnedProductAction
