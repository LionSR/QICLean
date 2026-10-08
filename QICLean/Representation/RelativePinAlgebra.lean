/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaSimilarity

/-!
# The relative metric of a move

Let `P, x, Y₀, F` be pairwise disjoint subsystems, `A_k = A_k(P, x Y₀, F)` and
`B_k = A_k(P x, Y₀, F)` the partition metrics before and after moving `x` from the middle part
to `P`, and `C_{x,k} = A_k^{-1/2} B_k A_k^{-1/2}` (*A two-dimensional area law from a global
spectral gap*, `05-replicas.tex`, Lemma 6.3, lines 489–495). This file proves the algebraic
first step of the proof of Lemma 6.3 (lines 512–533):

* the inverse Cauchy–Schwarz inequality `C ≥ ⟨z, C^{-1} z⟩^{-1} |z⟩⟨z|` for `C > 0`, in the
  form `|⟨z, w⟩|² ≤ ⟨z, C^{-1} z⟩ ⟨w, C w⟩`;
* `⟨z, C_{x,k}^{-1} z⟩ = ‖W_{Px,k} W_{xY₀,k} W_{P,k}^{-1} W_{Y₀,k}^{-1} z‖²`, obtained by
  cancelling the disjoint `F` factors and commuting the remaining nested or disjoint central
  factors (no commutation of `A_k` with `B_k` is used).

The proofs are written from the paper; no Lean source was adapted.

## Main declarations

* `TensorPower.norm_star_dotProduct_sq_le_inv` — inverse Cauchy–Schwarz.
* `TensorPower.relativeMetric` — `C_{x,k}`.
* `TensorPower.moveWord` — `W_{Px} W_{xY₀} W_P^{-1} W_{Y₀}^{-1}`.
* `TensorPower.re_dotProduct_relativeMetric_inv` — `⟨z, C^{-1} z⟩ = ‖moveWord z‖²`.
-/

open Matrix PermutationRepresentation Entropy
open scoped Kronecker Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TensorPower

/-! ### Inverse Cauchy–Schwarz -/

section CauchySchwarz

variable {X : Type*} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
theorem norm_euclidean_sq (u : X → ℂ) :
    ‖(EuclideanSpace.equiv X ℂ).symm u‖ ^ 2 = (star u ⬝ᵥ u).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

/-- **Inverse Cauchy–Schwarz** (`05-replicas.tex`, lines 515–520): for `C > 0`,
`|⟨z, w⟩|² ≤ ⟨z, C^{-1} z⟩ ⟨w, C w⟩`. -/
theorem norm_star_dotProduct_sq_le_inv {C : Matrix X X ℂ} (hC : C.PosDef) (z w : X → ℂ) :
    ‖star z ⬝ᵥ w‖ ^ 2 ≤ (star z ⬝ᵥ (C⁻¹ *ᵥ z)).re * (star w ⬝ᵥ (C *ᵥ w)).re := by
  set S := CFC.sqrt C
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg C
  have hSS : S * S = C := CFC.sqrt_mul_sqrt_self C hC.posSemidef.nonneg
  have hSh : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian
  have hdet : IsUnit S.det := by
    have := hC.isUnit
    rw [← hSS, isUnit_iff_isUnit_det, det_mul, IsUnit.mul_iff] at this
    exact this.1
  have hSinv : S⁻¹ * S = 1 := nonsing_inv_mul S hdet
  have hSinv' : S * S⁻¹ = 1 := mul_nonsing_inv S hdet
  have hSinvh : (S⁻¹)ᴴ = S⁻¹ := by rw [conjTranspose_nonsing_inv, hSh]
  have hCinv : C⁻¹ = S⁻¹ * S⁻¹ := by
    rw [← hSS, Matrix.mul_inv_rev]
  set u := S⁻¹ *ᵥ z
  set v := S *ᵥ w
  have h1 : star u ⬝ᵥ v = star z ⬝ᵥ w := by
    simp only [u, v, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hSinvh, hSinv,
      one_mulVec]
  have h2 : (star u ⬝ᵥ u).re = (star z ⬝ᵥ (C⁻¹ *ᵥ z)).re := by
    simp only [u, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hSinvh, hCinv]
  have h3 : (star v ⬝ᵥ v).re = (star w ⬝ᵥ (C *ᵥ w)).re := by
    simp only [v, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hSh, hSS]
  have hcs := norm_star_dotProduct_le u v
  rw [h1] at hcs
  calc ‖star z ⬝ᵥ w‖ ^ 2
      ≤ (‖(EuclideanSpace.equiv X ℂ).symm u‖ * ‖(EuclideanSpace.equiv X ℂ).symm v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hcs 2
    _ = _ := by rw [mul_pow, norm_euclidean_sq, norm_euclidean_sq, h2, h3]

end CauchySchwarz

/-! ### Central label functions of subsystems -/

section Central

variable {F : Type*} [DecidableEq F] [Fintype F] (ι : F → Type*) [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {k : ℕ}

/-- An operator is a label function of the copy permutations of `Q`. -/
def IsLabelFunctionOn (Q : Finset F) (M : Matrix (Config k ι) (Config k ι) ℂ) : Prop :=
  ∃ g : IrrepLabel (Equiv.Perm (Fin k)) → ℝ, M = labelObservable (subsystemPerm k ι Q) g

variable {ι}

theorem IsLabelFunctionOn.commute_of_disjoint {Q Q' : Finset F}
    {M M' : Matrix (Config k ι) (Config k ι) ℂ} (hM : IsLabelFunctionOn ι Q M)
    (hM' : IsLabelFunctionOn ι Q' M') (h : Disjoint Q Q') : Commute M M' := by
  obtain ⟨g, rfl⟩ := hM
  obtain ⟨g', rfl⟩ := hM'
  rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep]
  exact commute_groupAlgebraRep_subsystemPerm_of_disjoint ι k h _ _

theorem IsLabelFunctionOn.commute_of_subset {Q Q' : Finset F}
    {M M' : Matrix (Config k ι) (Config k ι) ℂ} (hM : IsLabelFunctionOn ι Q M)
    (hM' : IsLabelFunctionOn ι Q' M') (h : Q ⊆ Q') : Commute M M' := by
  obtain ⟨g, rfl⟩ := hM
  obtain ⟨g', rfl⟩ := hM'
  rw [labelObservable_eq_groupAlgebraRep, labelObservable_eq_groupAlgebraRep]
  exact commute_groupAlgebraRep_subsystemPerm_of_subset ι k h
    (sum_smul_centralIdem_mem_center _) _

theorem isLabelFunctionOn_replicaMetric (t : ℝ) (Q : Finset F) :
    IsLabelFunctionOn ι Q (replicaMetric ι t k Q) :=
  ⟨_, rfl⟩

theorem isLabelFunctionOn_replicaMetric_inv [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t)
    (Q : Finset F) : IsLabelFunctionOn ι Q (replicaMetric ι t k Q)⁻¹ :=
  ⟨_, labelObservable_inv _ fun l => (replicaLabelWeight_pos ι ht l).ne'⟩

theorem isUnit_det_replicaMetric [∀ f, Nonempty (ι f)] {t : ℝ} (ht : 0 ≤ t) (Q : Finset F) :
    IsUnit (replicaMetric ι t k Q).det :=
  (posDef_replicaMetric ι ht k Q).det_pos.ne'.isUnit

end Central

/-! ### The relative metric of a move -/

section Move

variable {V : Type*} [Fintype V] [DecidableEq V] (n : V → ℕ)

/-- The relative metric `C_{x,k} = A_k^{-1/2} B_k A_k^{-1/2}` of moving `x` from the middle
part to `P` (`05-replicas.tex`, Lemma 6.3, lines 489–495). -/
noncomputable def relativeMetric (t : ℝ) (k : ℕ) (P x Y₀ F : Finset V) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  (CFC.sqrt (leafMetric n t k P (x ∪ Y₀) F))⁻¹ * leafMetric n t k (P ∪ x) Y₀ F *
    (CFC.sqrt (leafMetric n t k P (x ∪ Y₀) F))⁻¹

/-- The word `W_{Px,k} W_{xY₀,k} W_{P,k}^{-1} W_{Y₀,k}^{-1}` (`05-replicas.tex`, equation
`replicas:move-inverse`). -/
noncomputable def moveWord (t : ℝ) (k : ℕ) (P x Y₀ : Finset V) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  replicaMetric (fun v => Fin (n v)) t k (P ∪ x) * replicaMetric (fun v => Fin (n v)) t k (x ∪ Y₀) *
    (replicaMetric (fun v => Fin (n v)) t k P)⁻¹ * (replicaMetric (fun v => Fin (n v)) t k Y₀)⁻¹

variable {n} [∀ v, NeZero (n v)]

/-- Disjointness of the four parts of a move. -/
structure MoveParts (P x Y₀ F : Finset V) : Prop where
  Px : Disjoint P x
  PY : Disjoint P Y₀
  PF : Disjoint P F
  xY : Disjoint x Y₀
  xF : Disjoint x F
  YF : Disjoint Y₀ F

theorem leafRoot_inv_mul_leafRoot {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P x Y₀ F : Finset V}
    (h : MoveParts P x Y₀ F) :
    (leafRoot n t k (P ∪ x) Y₀ F)⁻¹ * leafRoot n t k P (x ∪ Y₀) F = moveWord n t k P x Y₀ := by
  set ι : V → Type := fun v => Fin (n v)
  set a := replicaMetric ι t k (P ∪ x)
  set b := replicaMetric ι t k (x ∪ Y₀)
  set p := replicaMetric ι t k P
  set y := replicaMetric ι t k Y₀
  set f := replicaMetric ι t k F
  have ha := isUnit_det_replicaMetric (k := k) ht (P ∪ x) (ι := ι)
  have hf := isUnit_det_replicaMetric (k := k) ht F (ι := ι)
  have hRB : (leafRoot n t k (P ∪ x) Y₀ F)⁻¹ = y⁻¹ * f * a := by
    simp only [leafRoot, Matrix.mul_inv_rev]
    rw [nonsing_inv_nonsing_inv _ hf, nonsing_inv_nonsing_inv _ ha, ← Matrix.mul_assoc]
  have Lf := isLabelFunctionOn_replicaMetric (ι := ι) (k := k) t F
  have La := isLabelFunctionOn_replicaMetric (ι := ι) (k := k) t (P ∪ x)
  have Lb := isLabelFunctionOn_replicaMetric (ι := ι) (k := k) t (x ∪ Y₀)
  have Lpi := isLabelFunctionOn_replicaMetric_inv (ι := ι) (k := k) ht P
  have Lyi := isLabelFunctionOn_replicaMetric_inv (ι := ι) (k := k) ht Y₀
  have hFPx : Disjoint F (P ∪ x) := Finset.disjoint_union_right.mpr ⟨h.PF.symm, h.xF.symm⟩
  have hYPx : Disjoint Y₀ (P ∪ x) := Finset.disjoint_union_right.mpr ⟨h.PY.symm, h.xY.symm⟩
  have hPxY : Disjoint P (x ∪ Y₀) := Finset.disjoint_union_right.mpr ⟨h.Px, h.PY⟩
  have c1 : Commute f a := Lf.commute_of_disjoint La hFPx
  have c2 : Commute f p⁻¹ := Lf.commute_of_disjoint Lpi h.PF.symm
  have c3 : Commute y⁻¹ a := Lyi.commute_of_disjoint La hYPx
  have c4 : Commute y⁻¹ p⁻¹ := Lyi.commute_of_disjoint Lpi h.PY.symm
  have c5 : Commute y⁻¹ b := Lyi.commute_of_subset Lb Finset.subset_union_right
  have c6 : Commute p⁻¹ b := Lpi.commute_of_disjoint Lb hPxY
  have hff : f * f⁻¹ = 1 := mul_nonsing_inv f hf
  rw [hRB]
  simp only [leafRoot, moveWord]
  change y⁻¹ * f * a * (p⁻¹ * f⁻¹ * b) = a * b * p⁻¹ * y⁻¹
  calc y⁻¹ * f * a * (p⁻¹ * f⁻¹ * b) = y⁻¹ * a * p⁻¹ * (f * f⁻¹) * b := by
        rw [mul_assoc y⁻¹ f a, c1.eq, ← mul_assoc]
        simp only [mul_assoc]
        rw [← mul_assoc f p⁻¹, c2.eq]
        simp only [mul_assoc]
    _ = a * b * p⁻¹ * y⁻¹ := by
        rw [hff, Matrix.mul_one, c3.eq, mul_assoc a y⁻¹, c4.eq, mul_assoc, mul_assoc, c5.eq,
          ← mul_assoc p⁻¹, c6.eq]
        simp only [mul_assoc]

theorem relativeMetric_eq {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P x Y₀ F : Finset V}
    (h : MoveParts P x Y₀ F) :
    relativeMetric n t k P x Y₀ F = (leafRoot n t k P (x ∪ Y₀) F)⁻¹ *
      (leafRoot n t k (P ∪ x) Y₀ F * leafRoot n t k (P ∪ x) Y₀ F) *
        (leafRoot n t k P (x ∪ Y₀) F)⁻¹ := by
  have hPxY : Disjoint P (x ∪ Y₀) := Finset.disjoint_union_right.mpr ⟨h.Px, h.PY⟩
  have hxYF : Disjoint (x ∪ Y₀) F := Finset.disjoint_union_left.mpr ⟨h.xF, h.YF⟩
  have hPxY0 : Disjoint (P ∪ x) Y₀ := Finset.disjoint_union_left.mpr ⟨h.PY, h.xY⟩
  have hPxF : Disjoint (P ∪ x) F := Finset.disjoint_union_left.mpr ⟨h.PF, h.xF⟩
  rw [relativeMetric, sqrt_leafMetric ht k hPxY h.PF hxYF, leafMetric, pow_two]

/-- **The inverse quadratic form of a move** (`05-replicas.tex`, equation
`replicas:move-inverse`): `⟨z, C_{x,k}^{-1} z⟩ = ‖W_{Px} W_{xY₀} W_P^{-1} W_{Y₀}^{-1} z‖²`, and
`C_{x,k} > 0`. -/
theorem posDef_relativeMetric_and_inv {t : ℝ} (ht : 0 ≤ t) (k : ℕ) {P x Y₀ F : Finset V}
    (h : MoveParts P x Y₀ F) :
    (relativeMetric n t k P x Y₀ F).PosDef ∧
      ∀ z : Config k (fun v => Fin (n v)) → ℂ,
        (star z ⬝ᵥ ((relativeMetric n t k P x Y₀ F)⁻¹ *ᵥ z)).re =
          ‖(EuclideanSpace.equiv _ ℂ).symm (moveWord n t k P x Y₀ *ᵥ z)‖ ^ 2 := by
  have hPxY : Disjoint P (x ∪ Y₀) := Finset.disjoint_union_right.mpr ⟨h.Px, h.PY⟩
  have hxYF : Disjoint (x ∪ Y₀) F := Finset.disjoint_union_left.mpr ⟨h.xF, h.YF⟩
  have hPxY0 : Disjoint (P ∪ x) Y₀ := Finset.disjoint_union_left.mpr ⟨h.PY, h.xY⟩
  have hPxF : Disjoint (P ∪ x) F := Finset.disjoint_union_left.mpr ⟨h.PF, h.xF⟩
  set RA := leafRoot n t k P (x ∪ Y₀) F
  set RB := leafRoot n t k (P ∪ x) Y₀ F
  have hA := posDef_leafRoot ht k hPxY h.PF hxYF (n := n)
  have hB := posDef_leafRoot ht k hPxY0 hPxF h.YF (n := n)
  have hAu : IsUnit RA.det := hA.det_pos.ne'.isUnit
  have hBu : IsUnit RB.det := hB.det_pos.ne'.isUnit
  have hAh : RAᴴ = RA := hA.isHermitian
  have hAih : (RA⁻¹)ᴴ = RA⁻¹ := by rw [conjTranspose_nonsing_inv, hAh]
  have hBih : (RB⁻¹)ᴴ = RB⁻¹ := by rw [conjTranspose_nonsing_inv, hB.isHermitian]
  rw [relativeMetric_eq ht k h]
  refine ⟨?_, fun z => ?_⟩
  · have hBB : (RB * RB).PosDef := by
      have := (Matrix.PosDef.one (n := Config k fun v => Fin (n v))
        (R := ℂ)).conjTranspose_mul_mul_same (B := RB) (Matrix.mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det _).mpr hBu))
      rwa [Matrix.mul_one, hB.isHermitian] at this
    have hinj : Function.Injective RA⁻¹.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr
      ((isUnit_iff_isUnit_det _).mpr (isUnit_nonsing_inv_det RA hAu))
    have := hBB.conjTranspose_mul_mul_same hinj
    rwa [hAih] at this
  · have hinv : (RA⁻¹ * (RB * RB) * RA⁻¹)⁻¹ = RA * RB⁻¹ * (RB⁻¹ * RA) := by
      simp only [Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ hAu]
      simp only [Matrix.mul_assoc]
    rw [hinv, ← leafRoot_inv_mul_leafRoot ht k h, norm_euclidean_sq, ← mulVec_mulVec,
      star_mulVec (RB⁻¹ * RA)]
    congr 1
    rw [← dotProduct_mulVec, conjTranspose_mul, hAh, hBih]

/-- The inverse Cauchy–Schwarz inequality for the relative metric:
`|⟨z, w⟩|² ≤ ‖W_{Px} W_{xY₀} W_P^{-1} W_{Y₀}^{-1} z‖² ⟨w, C_{x,k} w⟩`. -/
theorem norm_star_dotProduct_sq_le_moveWord {t : ℝ} (ht : 0 ≤ t) (k : ℕ)
    {P x Y₀ F : Finset V} (h : MoveParts P x Y₀ F) (z w : Config k (fun v => Fin (n v)) → ℂ) :
    ‖star z ⬝ᵥ w‖ ^ 2 ≤ ‖(EuclideanSpace.equiv _ ℂ).symm (moveWord n t k P x Y₀ *ᵥ z)‖ ^ 2 *
      (star w ⬝ᵥ (relativeMetric n t k P x Y₀ F *ᵥ w)).re := by
  obtain ⟨hC, hinv⟩ := posDef_relativeMetric_and_inv ht k h (n := n)
  rw [← hinv]
  exact norm_star_dotProduct_sq_le_inv hC z w

end Move

end TensorPower
