/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SubsystemLabelCommutation
import QICLean.Representation.GroupedLabelSymmetricSupport
import QICLean.Analysis.OperatorMean.MatrixPowers
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# Replica metrics for nested regional bands

The inner regions, disjoint bands, and their unions form a laminar family.
Their central replica metrics therefore give positive ordered products.
The same cross-status nesting makes factors from distinct bands commute.
On the simultaneous symmetric space, complementary subsystem labels
identify the original far-region factor with the laminar factor.

Every weight is evaluated with the original full local family. Neither a
cutoff nor a selected label is required for these operator identities.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `05-replicas.tex`, Lemma 6.2; `06-transport.tex`,
lines 268–276; `07-comparators.tex`, `comparator:nesting` and
`comparator:pinned-metric`, lines 20–37, 299–308 and 367–378, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TensorPower

variable {F : Type*} [Fintype F] [DecidableEq F]
  (ι : F → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
  [∀ f, Nonempty (ι f)]

local instance replicaLaminarBandMetrics_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

omit [Fintype F] in
/-- Successive disjoint bands form a laminar family, including their inner
regions and inner-region unions. -/
private theorem leaf_regions_laminar {K : ℕ} (U Y : Fin K → Finset F)
    (hdisj : ∀ g, Disjoint (U g) (Y g))
    (hnest : ∀ g h, g < h → U g ∪ Y g ⊆ U h)
    {g h : Fin K} {R S : Finset F}
    (hR : R = U g ∨ R = Y g ∨ R = U g ∪ Y g)
    (hS : S = U h ∨ S = Y h ∨ S = U h ∪ Y h) :
    R ⊆ S ∨ S ⊆ R ∨ Disjoint R S := by
  have hforward {i j : Fin K} {A B : Finset F} (hij : i < j)
      (hA : A = U i ∨ A = Y i ∨ A = U i ∪ Y i)
      (hB : B = U j ∨ B = Y j ∨ B = U j ∪ Y j) :
      A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
    have hAi : A ⊆ U i ∪ Y i := by
      rcases hA with rfl | rfl | rfl
      · exact Finset.subset_union_left
      · exact Finset.subset_union_right
      · exact Finset.Subset.refl _
    have hAj := hAi.trans (hnest i j hij)
    rcases hB with rfl | rfl | rfl
    · exact Or.inl hAj
    · exact Or.inr (Or.inr ((hdisj j).mono_left hAj))
    · exact Or.inl (hAj.trans Finset.subset_union_left)
  rcases lt_trichotomy g h with hgh | rfl | hhg
  · exact hforward hgh hR hS
  · rcases hR with rfl | rfl | rfl <;> rcases hS with rfl | rfl | rfl
    all_goals first
      | exact Or.inl (Finset.Subset.refl _)
      | exact Or.inl Finset.subset_union_left
      | exact Or.inl Finset.subset_union_right
      | exact Or.inr (Or.inl Finset.subset_union_left)
      | exact Or.inr (Or.inl Finset.subset_union_right)
      | exact Or.inr (Or.inr (hdisj g))
      | exact Or.inr (Or.inr (hdisj g).symm)
  · rcases hforward hhg hS hR with hSR | hRS | hd
    · exact Or.inr (Or.inl hSR)
    · exact Or.inl hRS
    · exact Or.inr (Or.inr hd.symm)

omit [∀ f, Nonempty (ι f)] in
/-- Central label functions commute for nested or disjoint subsystems.
Source: OpenAI area-law manuscript, `05-replicas.tex`, lines 101–102,
and `07-comparators.tex`, `comparator:nesting`, lines 367–373. -/
theorem commute_labelObservables_subsystemPerm_of_laminar (k : ℕ) {R S : Finset F}
    (hRS : R ⊆ S ∨ S ⊆ R ∨ Disjoint R S)
    (f g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
    Commute (labelObservable (subsystemPerm k ι R) f)
      (labelObservable (subsystemPerm k ι S) g) := by
  rcases hRS with hRS | hSR | hd
  · simpa only [MonoidHom.comp_id] using
      commute_subgroup_labelObservables_of_subset_or_disjoint ι
        (MonoidHom.id (Equiv.Perm (Fin k))) R S (Or.inl hRS) f g
  · simpa only [MonoidHom.comp_id] using
      (commute_subgroup_labelObservables_of_subset_or_disjoint ι
        (MonoidHom.id (Equiv.Perm (Fin k))) S R (Or.inl hSR) g f).symm
  · simpa only [MonoidHom.comp_id] using
      commute_subgroup_labelObservables_of_subset_or_disjoint ι
        (MonoidHom.id (Equiv.Perm (Fin k))) R S (Or.inr hd) f g

/-- The actual ordered pinned leaf is positive definite. Positivity of each
metric, inverse, and product is derived from the replica weights and the
within-leaf region relations; no positivity certificate is supplied.

Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:pinned-metric`, and lines 367–378, where the positive leaf metrics
are combined by the matrix mean and spectral Jensen. -/
theorem posDef_replicaPinnedLeaf {t : ℝ} (ht : 0 ≤ t) (k K : ℕ)
    (U Y : Fin K → Finset F) (hdisj : ∀ g, Disjoint (U g) (Y g))
    (hnest : ∀ g h, g < h → U g ∪ Y g ⊆ U h) :
    (List.ofFn fun g : Fin K ↦
      ((replicaMetric ι t k (U g))⁻¹ *
        (replicaMetric ι t k (U g ∪ Y g))⁻¹ *
          replicaMetric ι t k (Y g)) ^ 2).prod.PosDef := by
  classical
  let W : Finset F → Matrix (Config k ι) (Config k ι) ℂ := replicaMetric ι t k
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι t
  let root : Fin K → Matrix (Config k ι) (Config k ι) ℂ := fun g ↦
    (W (U g))⁻¹ * (W (U g ∪ Y g))⁻¹ * W (Y g)
  have hinv (Q : Finset F) : (W Q)⁻¹ =
      labelObservable (subsystemPerm k ι Q) (fun l ↦ (w l)⁻¹) :=
    labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι ht l).ne')
  have hcentral (g h : Fin K) (A B : Finset F)
      (hA : A = U g ∨ A = Y g ∨ A = U g ∪ Y g)
      (hB : B = U h ∨ B = Y h ∨ B = U h ∪ Y h)
      (f f' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
      Commute (labelObservable (subsystemPerm k ι A) f)
        (labelObservable (subsystemPerm k ι B) f') :=
    commute_labelObservables_subsystemPerm_of_laminar ι k
      (leaf_regions_laminar U Y hdisj hnest hA hB) f f'
  have hroot (g : Fin K) : (root g).PosDef := by
    have hU := posDef_replicaMetric ι ht k (U g)
    have hUY := posDef_replicaMetric ι ht k (U g ∪ Y g)
    have hY := posDef_replicaMetric ι ht k (Y g)
    have hAB : Commute (W (U g))⁻¹ (W (U g ∪ Y g))⁻¹ := by
      rw [hinv, hinv]
      exact hcentral g g _ _ (Or.inl rfl) (Or.inr (Or.inr rfl)) _ _
    have hAD : Commute (W (U g))⁻¹ (W (Y g)) := by
      rw [hinv]
      exact hcentral g g _ _ (Or.inl rfl) (Or.inr (Or.inl rfl)) _ w
    have hBD : Commute (W (U g ∪ Y g))⁻¹ (W (Y g)) := by
      rw [hinv]
      exact hcentral g g _ _ (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) _ w
    exact (hU.inv.mul_of_commute hUY.inv hAB).mul_of_commute hY (hAD.mul_left hBD)
  have hrootComm (g h : Fin K) : Commute (root g) (root h) := by
    have hleft (B : Finset F) (hB : B = U h ∨ B = Y h ∨ B = U h ∪ Y h)
        (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
        Commute (root g) (labelObservable (subsystemPerm k ι B) f) := by
      dsimp only [root]
      rw [hinv, hinv]
      exact ((hcentral g h _ B (Or.inl rfl) hB _ f).mul_left
        (hcentral g h _ B (Or.inr (Or.inr rfl)) hB _ f)).mul_left
          (hcentral g h _ B (Or.inr (Or.inl rfl)) hB w f)
    change Commute (root g) ((W (U h))⁻¹ * (W (U h ∪ Y h))⁻¹ * W (Y h))
    rw [hinv, hinv]
    exact ((hleft (U h) (Or.inl rfl) _).mul_right
      (hleft (U h ∪ Y h) (Or.inr (Or.inr rfl)) _)).mul_right
        (hleft (Y h) (Or.inr (Or.inl rfl)) w)
  let l := List.ofFn fun g : Fin K ↦ root g ^ 2
  have hpos : ∀ A ∈ l, A.PosSemidef :=
    List.forall_mem_ofFn_iff.mpr fun g ↦ (hroot g).posSemidef.pow 2
  have hcomm : l.Pairwise fun A B ↦ A * B = B * A := by
    apply List.pairwise_ofFn.mpr
    intro g h _
    exact ((hrootComm g h).pow_left 2 |>.pow_right 2).eq
  have hunit : IsUnit l.prod := List.prod_isUnit
    (List.forall_mem_ofFn_iff.mpr fun g ↦ (hroot g).isUnit.pow 2)
  exact (Matrix.posSemidef_list_prod hpos hcomm).posDef_iff_isUnit.mpr hunit

/-- The actual squared factor for one disjoint band is positive definite.
This is the one-band case of the positive pinned product leaf; all replica
weights are evaluated on the original full-system family.

Source: OpenAI area-law manuscript, `07-comparators.tex`,
`comparator:pinned-metric`, and lines 367–378. -/
theorem posDef_replicaPinnedFactor {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (U Y : Finset F) (hUY : Disjoint U Y) :
    (((replicaMetric ι t k U)⁻¹ * (replicaMetric ι t k (U ∪ Y))⁻¹ *
      replicaMetric ι t k Y) ^ 2).PosDef := by
  have h := posDef_replicaPinnedLeaf ι ht k 1
    (fun _ ↦ U) (fun _ ↦ Y) (fun _ ↦ hUY)
    (fun a b hab ↦ False.elim (by
      simp only [Subsingleton.elim a b, lt_self_iff_false] at hab))
  simpa using h

variable {J : Type*}

/-- The actual band inputs are positive definite, and inputs from different
bands commute even when their status labels differ.

Source: area-law manuscript, `06-transport.tex`, lines 268–276;
`07-comparators.tex`, `comparator:nesting` and `comparator:pinned-metric`,
lines 20–37 and 367–378. -/
theorem replicaPinnedBands_posDef_commute {t : ℝ} (ht : 0 ≤ t) (k K : ℕ)
    (U Y : J → Fin K → Finset F)
    (hdisj : ∀ j g, Disjoint (U j g) (Y j g))
    (hnest : ∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) :
    let D := fun j g ↦ ((replicaMetric ι t k (U j g))⁻¹ *
      (replicaMetric ι t k (U j g ∪ Y j g))⁻¹ * replicaMetric ι t k (Y j g)) ^ 2
    (∀ j g, (D j g).PosDef) ∧
      ∀ j j' g h, g ≠ h → Commute (D j g) (D j' h) := by
  classical
  intro D
  let W : Finset F → Matrix (Config k ι) (Config k ι) ℂ := replicaMetric ι t k
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι t
  have hinv (A : Finset F) : (W A)⁻¹ =
      labelObservable (subsystemPerm k ι A) (fun l ↦ (w l)⁻¹) :=
    labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι ht l).ne')
  constructor
  · intro j g
    exact posDef_replicaPinnedFactor ι ht k (U j g) (Y j g) (hdisj j g)
  · have hgeom {j j' : J} {g h : Fin K} {A B : Finset F} (hgh : g < h)
        (hA : A = U j g ∨ A = Y j g ∨ A = U j g ∪ Y j g)
        (hB : B = U j' h ∨ B = Y j' h ∨ B = U j' h ∪ Y j' h) :
        A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
      have hA' : A ⊆ U j g ∪ Y j g := by
        rcases hA with rfl | rfl | rfl
        · exact Finset.subset_union_left
        · exact Finset.subset_union_right
        · exact Finset.Subset.refl _
      have hAh := hA'.trans (hnest j j' g h hgh)
      rcases hB with rfl | rfl | rfl
      · exact Or.inl hAh
      · exact Or.inr (Or.inr ((hdisj j' h).mono_left hAh))
      · exact Or.inl (hAh.trans Finset.subset_union_left)
    have hforward (j j' : J) (g h : Fin K) (hgh : g < h) :
        Commute (D j g) (D j' h) := by
      have hcentral (A B : Finset F)
          (hA : A = U j g ∨ A = Y j g ∨ A = U j g ∪ Y j g)
          (hB : B = U j' h ∨ B = Y j' h ∨ B = U j' h ∪ Y j' h)
          (f f' : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
          Commute (labelObservable (subsystemPerm k ι A) f)
            (labelObservable (subsystemPerm k ι B) f') :=
        commute_labelObservables_subsystemPerm_of_laminar ι k (hgeom hgh hA hB) f f'
      have hleft (B : Finset F)
          (hB : B = U j' h ∨ B = Y j' h ∨ B = U j' h ∪ Y j' h)
          (f : IrrepLabel (Equiv.Perm (Fin k)) → ℝ) :
          Commute ((W (U j g))⁻¹ * (W (U j g ∪ Y j g))⁻¹ * W (Y j g))
            (labelObservable (subsystemPerm k ι B) f) := by
        rw [hinv, hinv]
        exact ((hcentral _ B (Or.inl rfl) hB _ f).mul_left
          (hcentral _ B (Or.inr (Or.inr rfl)) hB _ f)).mul_left
            (hcentral _ B (Or.inr (Or.inl rfl)) hB w f)
      have hc : Commute
          ((W (U j g))⁻¹ * (W (U j g ∪ Y j g))⁻¹ * W (Y j g))
          ((W (U j' h))⁻¹ * (W (U j' h ∪ Y j' h))⁻¹ * W (Y j' h)) := by
        conv_rhs => rw [hinv, hinv]
        exact ((hleft (U j' h) (Or.inl rfl) _).mul_right
          (hleft (U j' h ∪ Y j' h) (Or.inr (Or.inr rfl)) _)).mul_right
            (hleft (Y j' h) (Or.inr (Or.inl rfl)) w)
      exact (hc.pow_left 2).pow_right 2
    intro j j' g h hgh
    rcases lt_or_gt_of_ne hgh with hlt | hgt
    · exact hforward j j' g h hlt
    · exact (hforward j' j h g hgt).symm

/-- The original far-region factor and its complementary laminar factor
have the same action on the actual symmetric space. No relation between Q
and Y is required for this algebraic identity; all weights belong to the
same original full-system family.

Source: area-law manuscript, `05-replicas.tex`, Lemma 6.2,
`replicas:metric`; `07-comparators.tex`, lines 299–308. -/
theorem replicaMetric_factors_symProj {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    (Q Y : Finset F) :
    let Pe := symProj (copyPerm ((f : F) → ι f) k)
    let W := replicaMetric ι t k
    let A := ((W Q)⁻¹ * (W (Q ∪ Y)ᶜ)⁻¹ * W Y) ^ 2
    let D := ((W Q)⁻¹ * (W (Q ∪ Y))⁻¹ * W Y) ^ 2
    Commute A Pe ∧ Commute D Pe ∧ A * Pe = Pe * D := by
  intro Pe W A D
  let w : IrrepLabel (Equiv.Perm (Fin k)) → ℝ := replicaLabelWeight ι t
  have hinv (Z : Finset F) : (W Z)⁻¹ =
      labelObservable (subsystemPerm k ι Z) (fun l ↦ (w l)⁻¹) :=
    labelObservable_inv _ (fun l ↦ (replicaLabelWeight_pos ι ht l).ne')
  have hc (Z : Finset F) : Commute (W Z) Pe := by
    simpa only [MonoidHom.comp_id, subsystemPerm_univ, W, Pe, w, replicaMetric] using
      commute_subgroup_labelObservable_symProj_of_subset ι
        (MonoidHom.id (Equiv.Perm (Fin k))) Z Finset.univ (Finset.subset_univ Z) w
  have hci (Z : Finset F) : Commute (W Z)⁻¹ Pe := by
    rw [hinv]
    simpa only [MonoidHom.comp_id, subsystemPerm_univ] using
      commute_subgroup_labelObservable_symProj_of_subset ι
        (MonoidHom.id (Equiv.Perm (Fin k))) Z Finset.univ (Finset.subset_univ Z)
        (fun l ↦ (w l)⁻¹)
  have hcompl (Z : Finset F) : (W Zᶜ)⁻¹ * Pe = (W Z)⁻¹ * Pe := by
    rw [hinv, hinv]
    simp only [labelObservable, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro l hl
    rw [smul_mul_assoc, smul_mul_assoc, labelProj_mul_symProj_compl]
    simp only [compl_compl, Pe]
  have hQ : SemiconjBy Pe (W Q)⁻¹ (W Q)⁻¹ := (hci Q).symm
  have hY : SemiconjBy Pe (W Y) (W Y) := (hc Y).symm
  have hF : SemiconjBy Pe (W (Q ∪ Y))⁻¹ (W (Q ∪ Y)ᶜ)⁻¹ :=
    (hci (Q ∪ Y)).symm.eq.trans (hcompl (Q ∪ Y)).symm
  exact ⟨(((hci Q).mul_left (hci (Q ∪ Y)ᶜ)).mul_left (hc Y)).pow_left 2,
    (((hci Q).mul_left (hci (Q ∪ Y))).mul_left (hc Y)).pow_left 2,
    (((hQ.mul_right hF).mul_right hY).pow_right 2).eq.symm⟩


end TensorPower
