/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaMetricCutoffNorm
import QICLean.Representation.ReplicaLaminarBandMetrics
import QICLean.Analysis.OperatorMean.MatrixPowers
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# The expectation of a literal pinned product leaf

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

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `07-comparators.tex`, `comparator:nesting`,
  `comparator:pinned-metric`, and lines 356–373, at manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation
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
