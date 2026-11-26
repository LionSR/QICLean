/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.YoungSubgroup.GroupedCopies
import QICLean.Representation.Permutation.SchurSurprisal
import QICLean.Analysis.FunctionalCalculus.ProjectionCfcUpperBound

/-!
# Label observables under a split of the copies

For any permutation representation of the copy permutations, the central observables
of the two groups of copies and of all copies satisfy
\(F_g + F_b \le F_w \le F_g + F_b + \log\binom{k}{r}\,I\).
The good, bad, and whole label projections give an actual joint orthogonal resolution.
On each nonzero joint projection, the subgroup dimension bounds give the corresponding
scalar logarithmic inequalities.

This is the operator consequence of *A two-dimensional area law from a global spectral
gap*, Lemma 6.1(4), `05-replicas.tex`, lines 116–123, used in
`07-comparators.tex`, lines 455–467, equation `comparator:restriction-dimensions`.
The later estimates for the good auxiliary systems require further bounds on the
occurring bad-copy labels and are not asserted here.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.

It also contains the following results.

* `TensorPower.copyPerm_groupedGood_labelEntropy_compression`: the good auxiliary observable on a
  whole-copy label subspace.
* `TensorPower.copyPerm_groupedCopies_labelEntropy_bounds`: a whole-space bound for the good
  auxiliary label observable.
* `TensorPower.copyPerm_groupedGood_auxiliaryPair_labelEntropy_compression`,
  `TensorPower.copyPerm_groupedGood_auxiliaryPair_exp_compression`: the joint good auxiliary
  exponential on the original label subspaces.
-/

section GroupedLabelEntropy

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, Lemma 6.1(4), lem:schur,
replicas:group-dimensions; comparator:restriction-dimensions.
-/

private theorem resolution_hom_fst {X I J : Type*} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {P : I → Matrix X X ℂ} {Q : J → Matrix X X ℂ}
    (hP : IsOrthogonalResolution P) (hQ : IsOrthogonalResolution Q)
    (hc : ∀ i j, Commute (P i) (Q j)) (f : I → ℂ) :
    (hP.prod hQ hc).hom (fun p => f p.1) = hP.hom f := by
  rw [IsOrthogonalResolution.hom_apply, IsOrthogonalResolution.hom_apply,
    Fintype.sum_prod_type]
  simp only [← Finset.smul_sum, ← Finset.mul_sum, hQ.sum_eq, mul_one]

private theorem resolution_hom_snd {X I J : Type*} [Fintype X] [DecidableEq X]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    {P : I → Matrix X X ℂ} {Q : J → Matrix X X ℂ}
    (hP : IsOrthogonalResolution P) (hQ : IsOrthogonalResolution Q)
    (hc : ∀ i j, Commute (P i) (Q j)) (f : J → ℂ) :
    (hP.prod hQ hc).hom (fun p => f p.2) = hQ.hom f := by
  rw [IsOrthogonalResolution.hom_apply, IsOrthogonalResolution.hom_apply,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [← Finset.smul_sum, ← Finset.sum_mul, hP.sum_eq, one_mul]

/-- *A two-dimensional area law from a global spectral gap*, Lemma 6.1(4),
`05-replicas.tex`, lines 116–123; its operator use is equation
`comparator:restriction-dimensions`, `07-comparators.tex`, lines 455–467.
For any permutation representation of the `k` copies and any specified split into
`m` good copies and `r` bad copies, the subgroup label observables bound the whole
label observable, with additive error \(\log\binom{k}{r}\).

The inequalities hold on the full representation space; compatibility of labels is
proved on each nonzero joint projection, not assumed in the statement. -/
theorem groupedCopies_labelEntropy_bounds {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    {X : Type*} [Fintype X] [DecidableEq X] (φ : Equiv.Perm (Fin k) →* Equiv.Perm X) :
    labelEntropy (φ.comp (groupHom₁ e)) + labelEntropy (φ.comp (groupHom₂ e)) ≤
      labelEntropy φ ∧
    labelEntropy φ ≤ labelEntropy (φ.comp (groupHom₁ e)) +
      labelEntropy (φ.comp (groupHom₂ e)) + (Real.log (k.choose r) : ℂ) • 1 := by
  classical
  have hc : ∀ α β, Commute (labelProj (φ.comp (groupHom₁ e)) α)
      (labelProj (φ.comp (groupHom₂ e)) β) := fun α β =>
    commute_groupAlgebraRep_of_commute _ _ (comp_commute φ (groupHom_commute e)) _ _
  let hG := isOrthogonalResolution_labelProj (φ.comp (groupHom₁ e))
  let hB := isOrthogonalResolution_labelProj (φ.comp (groupHom₂ e))
  let hW := isOrthogonalResolution_labelProj φ
  let hGB := hG.prod hB hc
  have hcW : ∀ (p : IrrepLabel (Equiv.Perm (Fin m)) × IrrepLabel (Equiv.Perm (Fin r)))
      (l : IrrepLabel (Equiv.Perm (Fin k))), Commute
      (labelProj (φ.comp (groupHom₁ e)) p.1 * labelProj (φ.comp (groupHom₂ e)) p.2)
      (labelProj φ l) := fun p l =>
    ((groupedCopies_commute e φ p.1 p.2 l).1).mul_left
      (groupedCopies_commute e φ p.1 p.2 l).2
  let R := hGB.prod hW hcW
  have hHerm : ∀ (p : (IrrepLabel (Equiv.Perm (Fin m)) ×
      IrrepLabel (Equiv.Perm (Fin r))) × IrrepLabel (Equiv.Perm (Fin k))),
      ((labelProj (φ.comp (groupHom₁ e)) p.1.1 *
      labelProj (φ.comp (groupHom₂ e)) p.1.2) * labelProj φ p.2).IsHermitian :=
    fun p => (((isHermitian_labelProj _ p.1.1).commute_iff
      (isHermitian_labelProj _ p.1.2)).mp (hc p.1.1 p.1.2)).commute_iff
        (isHermitian_labelProj _ p.2) |>.mp (hcW p.1 p.2)
  have hGood : R.hom (fun p => (Real.log p.1.1.dim : ℂ)) =
      labelEntropy (φ.comp (groupHom₁ e)) :=
    (resolution_hom_fst hGB hW hcW (fun p => (Real.log p.1.dim : ℂ))).trans
      ((resolution_hom_fst hG hB hc (fun α => (Real.log α.dim : ℂ))).trans
        (labelObservable_eq_hom _ (fun α => Real.log α.dim)).symm)
  have hBad : R.hom (fun p => (Real.log p.1.2.dim : ℂ)) =
      labelEntropy (φ.comp (groupHom₂ e)) :=
    (resolution_hom_fst hGB hW hcW (fun p => (Real.log p.2.dim : ℂ))).trans
      ((resolution_hom_snd hG hB hc (fun β => (Real.log β.dim : ℂ))).trans
        (labelObservable_eq_hom _ (fun β => Real.log β.dim)).symm)
  have hWhole : R.hom (fun p => (Real.log p.2.dim : ℂ)) = labelEntropy φ :=
    (resolution_hom_snd hGB hW hcW (fun l => (Real.log l.dim : ℂ))).trans
      (labelObservable_eq_hom _ (fun l => Real.log l.dim)).symm
  have hk : m + r = k := by simpa using Fintype.card_congr e
  have hchoose : (0 : ℝ) < k.choose r := by
    exact_mod_cast Nat.choose_pos (show r ≤ k by omega)
  have hLog : ∀ (p : (IrrepLabel (Equiv.Perm (Fin m)) ×
      IrrepLabel (Equiv.Perm (Fin r))) × IrrepLabel (Equiv.Perm (Fin k))),
      labelProj (φ.comp (groupHom₁ e)) p.1.1 *
        labelProj (φ.comp (groupHom₂ e)) p.1.2 * labelProj φ p.2 ≠ 0 →
      Real.log p.1.1.dim + Real.log p.1.2.dim ≤ Real.log p.2.dim ∧
      Real.log p.2.dim ≤ Real.log p.1.1.dim + Real.log p.1.2.dim +
        Real.log (k.choose r) := by
    intro p hp
    have hd := groupedCopies_dim e φ hp
    have ha : (0 : ℝ) < p.1.1.dim := Nat.cast_pos.mpr p.1.1.dim_pos
    have hb : (0 : ℝ) < p.1.2.dim := Nat.cast_pos.mpr p.1.2.dim_pos
    have hw : (0 : ℝ) < p.2.dim := Nat.cast_pos.mpr p.2.dim_pos
    have hlo := Real.log_le_log (mul_pos ha hb)
      (show (p.1.1.dim : ℝ) * p.1.2.dim ≤ p.2.dim by exact_mod_cast hd.1)
    have hup := Real.log_le_log hw
      (show (p.2.dim : ℝ) ≤ (k.choose r : ℝ) * ((p.1.1.dim : ℝ) * p.1.2.dim)
        by exact_mod_cast hd.2)
    constructor
    · simpa only [Real.log_mul ha.ne' hb.ne'] using hlo
    · simpa only [Real.log_mul hchoose.ne' (mul_pos ha hb).ne',
        Real.log_mul ha.ne' hb.ne', add_comm (Real.log (k.choose r))] using hup
  have hConst : R.hom (fun _ => (Real.log (k.choose r) : ℂ)) =
      (Real.log (k.choose r) : ℂ) • 1 := by
    rw [IsOrthogonalResolution.hom_apply, ← Finset.smul_sum, R.sum_eq]
  constructor
  · rw [Matrix.le_iff, ← hWhole, ← hGood, ← hBad, ← map_add, ← map_sub]
    simpa only [Pi.sub_def, Pi.add_def, Complex.ofReal_sub, Complex.ofReal_add] using
      R.posSemidef_hom_of_ne_zero hHerm
        (f := fun p => Real.log p.2.dim - (Real.log p.1.1.dim + Real.log p.1.2.dim))
        (fun p hp => sub_nonneg.mpr (hLog p hp).1)
  · rw [Matrix.le_iff, ← hWhole, ← hGood, ← hBad, ← hConst,
      ← map_add, ← map_add, ← map_sub]
    simpa only [Pi.sub_def, Pi.add_def, Complex.ofReal_sub, Complex.ofReal_add] using
      R.posSemidef_hom_of_ne_zero hHerm
        (f := fun p => Real.log p.1.1.dim + Real.log p.1.2.dim +
          Real.log (k.choose r) - Real.log p.2.dim)
        (fun p hp => sub_nonneg.mpr (hLog p hp).2)

end TensorPower

end GroupedLabelEntropy

section GoodAuxiliaryLabelEntropy

/-!
## A whole-space bound for the good auxiliary label observable

For the actual copy-permutation action on a finite coordinate tensor power,
the bad label observable is bounded by the number of bad copies times the
logarithm of the one-copy dimension. Together with the subgroup label
inequality, this bounds the whole observable above by the good observable
plus an explicit scalar multiple of the identity.

This is the operator input to *A two-dimensional area law from a global
spectral gap*, `07-comparators.tex`, lines 481–493, equation
`comparator:good-auxiliary`. The actual physical excitation projection,
preservation of whole-copy auxiliary labels, and the whole-label threshold
are separate assertions. No commutation with the band metric is asserted.
The formulas use the total real logarithm, with \(\log 0=0\); empty
coordinate sets and zero copy groups remain included.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder

namespace TensorPower

variable {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    {C : Type*} [Fintype C] [DecidableEq C]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:good-auxiliary, lines 481–493.
-/

/-- The actual bad-copy label observable is bounded by the bad-copy ambient
logarithmic dimension. Hence the whole-copy observable is at most the
good-copy observable plus the bad-copy dimension and binomial correction.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 481–493, equation `comparator:good-auxiliary`. This is a whole-space
operator inequality, before selecting a physical excitation component. -/
theorem copyPerm_groupedCopies_labelEntropy_bounds :
    labelEntropy ((copyPerm C k).comp (groupHom₂ e)) ≤
        ((r : ℝ) * Real.log (Fintype.card C) : ℂ) • 1 ∧
      labelEntropy (copyPerm C k) ≤
        labelEntropy ((copyPerm C k).comp (groupHom₁ e)) +
          ((r : ℝ) * Real.log (Fintype.card C) + Real.log (k.choose r) : ℂ) • 1 := by
  classical
  have hLog : ∀ (β : IrrepLabel (Equiv.Perm (Fin r))),
      labelProj ((copyPerm C k).comp (groupHom₂ e)) β ≠ 0 →
      Real.log β.dim ≤ (r : ℝ) * Real.log (Fintype.card C) := by
    intro β hβ
    have hd : (β.dim : ℝ) ≤ (Fintype.card C : ℝ) ^ r := by
      exact_mod_cast groupHom₂_labelProj_dim_le e β hβ
    simpa only [Real.log_pow] using Real.log_le_log (Nat.cast_pos.mpr β.dim_pos) hd
  let R := isOrthogonalResolution_labelProj ((copyPerm C k).comp (groupHom₂ e))
  have hConst : R.hom (fun _ => ((r : ℝ) * Real.log (Fintype.card C) : ℂ)) =
      ((r : ℝ) * Real.log (Fintype.card C) : ℂ) • 1 := by
    rw [IsOrthogonalResolution.hom_apply, ← Finset.smul_sum, R.sum_eq]
  have hBad : labelEntropy ((copyPerm C k).comp (groupHom₂ e)) ≤
      ((r : ℝ) * Real.log (Fintype.card C) : ℂ) • 1 := by
    rw [Matrix.le_iff, ← hConst, labelEntropy, labelObservable_eq_hom, ← map_sub]
    simpa only [Pi.sub_def, Complex.ofReal_sub, Complex.ofReal_mul] using
      R.posSemidef_hom_of_ne_zero (fun β => isHermitian_labelProj _ β)
        (f := fun β => (r : ℝ) * Real.log (Fintype.card C) - Real.log β.dim)
        (fun β hβ => sub_nonneg.mpr (hLog β hβ))
  refine ⟨hBad, ?_⟩
  have hWhole := (groupedCopies_labelEntropy_bounds e (copyPerm C k)).2
  rw [add_smul, ← add_assoc]
  refine hWhole.trans ?_
  simpa only [Matrix.le_iff, add_sub_add_right_eq_sub, add_sub_add_left_eq_sub] using hBad

end TensorPower

end GoodAuxiliaryLabelEntropy

section GoodAuxiliaryLabelCompression

/-!
## The good auxiliary observable on a whole-copy label subspace

Compressing the actual whole-space label inequality by a whole-copy central
projection yields a lower bound for the good-copy label observable on that
subspace. The good-copy observable commutes with the whole-copy projection,
and the whole-copy observable acts there by the logarithm of the actual
irreducible dimension. No occurring-label assumption is needed.

This is the support compression used in *A two-dimensional area law from a
global spectral gap*, `07-comparators.tex`, lines 481–493, equation
`comparator:good-auxiliary`. Preservation of that auxiliary label by a
physical excitation projection is a separate step. No commutation with the
band metric is asserted. The total real logarithm includes empty coordinate
sets and zero copy groups, with \(\log 0=0\).

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation
open scoped MatrixOrder ComplexOrder

namespace TensorPower

variable {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)
    {C : Type*} [Fintype C] [DecidableEq C]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:good-auxiliary, lines 481–493.
-/

/-- On an actual whole-copy label subspace, the good-copy logarithmic label
observable is bounded below by the whole-label logarithmic dimension minus
its bad-copy and binomial corrections. It commutes with the whole-label
projection. *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 481–493, equation `comparator:good-auxiliary`,
using Lemma 6.1(4), `05-replicas.tex`, lines 116–123. No occurrence assumption
is needed: a label that does not occur has zero central projection. -/
theorem copyPerm_groupedGood_labelEntropy_compression
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    let P := labelProj (copyPerm C k) l
    let Fg := labelEntropy ((copyPerm C k).comp (groupHom₁ e))
    Commute Fg P ∧
      ((Real.log l.dim - (r : ℝ) * Real.log (Fintype.card C) -
          Real.log (k.choose r) : ℝ) : ℂ) • P ≤ P * Fg * P := by
  classical
  dsimp only
  have hc : Commute (labelEntropy ((copyPerm C k).comp (groupHom₁ e)))
      (labelProj (copyPerm C k) l) :=
    commute_labelObservable_of_forall_commute ((copyPerm C k).comp (groupHom₁ e))
      (fun σ => (commute_labelProj_permOp (copyPerm C k) l (groupHom₁ e σ)).symm) _
  refine ⟨hc, ?_⟩
  have hWhole := (copyPerm_groupedCopies_labelEntropy_bounds (C := C) e).2
  have h := (Matrix.le_iff.mp hWhole).conjTranspose_mul_mul_same
    (labelProj (copyPerm C k) l)
  simp only [(isHermitian_labelProj (copyPerm C k) l).eq, mul_sub, mul_add, sub_mul,
    add_mul, mul_smul_comm, smul_mul_assoc, mul_one, labelProj_mul_self, mul_assoc,
    labelEntropy, labelObservable_mul_labelProj] at h
  rw [Matrix.le_iff]
  convert h using 1
  simp only [labelEntropy, mul_assoc, Complex.ofReal_sub, Complex.ofReal_mul,
    sub_smul, add_smul]
  abel

end TensorPower

end GoodAuxiliaryLabelCompression

section GoodAuxiliaryPairCompression

/-!
## The joint good auxiliary exponential on the original label subspaces

The two good auxiliary label entropies have a summed lower bound on the
intersection of their original whole-copy label subspaces. Exponentiating
this single compressed lower bound gives a joint operator bound. Thus no
product of separate expectation estimates is used.

Both original labels and both auxiliary dimensions are retained. An arbitrary
spectator register is included. Empty coordinate sets and zero copy groups
are permitted, with the total real logarithm.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 481--493,
`comparator:good-auxiliary`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped Matrix ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator

namespace TensorPower

variable {A C R : Type*} [Fintype A] [DecidableEq A]
variable [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
variable {m r k : ℕ} (e : Fin m ⊕ Fin r ≃ Fin k)

/-- The actual good auxiliary entropy sum has the sum of the two accepted
floors on the intersection of the original whole-label subspaces.
Source: `07-comparators.tex`, lines 481--493. -/
theorem copyPerm_groupedGood_auxiliaryPair_labelEntropy_compression
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) :
    let PC := labelProj (copyPerm C k) ellC
    let PR := labelProj (copyPerm R k) ellR
    let FC := labelEntropy ((copyPerm C k).comp (groupHom₁ e))
    let FR := labelEntropy ((copyPerm R k).comp (groupHom₁ e))
    let P := (1 : Matrix A A ℂ) ⊗ₖ (PC ⊗ₖ PR)
    let L := (1 : Matrix A A ℂ) ⊗ₖ
      (FC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ) +
        (1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ FR)
    let b := Real.log ellC.dim + Real.log ellR.dim -
      (r : ℝ) * (Real.log (Fintype.card C) + Real.log (Fintype.card R)) -
        2 * Real.log (k.choose r)
    IsStarProjection P ∧ Commute L P ∧ b • P ≤ P * L * P := by
  intro PC PR FC FR P L b
  let bC := Real.log ellC.dim - (r : ℝ) * Real.log (Fintype.card C) -
    Real.log (k.choose r)
  let bR := Real.log ellR.dim - (r : ℝ) * Real.log (Fintype.card R) -
    Real.log (k.choose r)
  have hb : b = bC + bR := by dsimp only [b, bC, bR]; ring
  obtain ⟨hCC, hC⟩ := copyPerm_groupedGood_labelEntropy_compression (C := C) e ellC
  obtain ⟨hRR, hR⟩ := copyPerm_groupedGood_labelEntropy_compression (C := R) e ellR
  have hPC : PC.IsHermitian := isHermitian_labelProj _ _
  have hPR : PR.IsHermitian := isHermitian_labelProj _ _
  have hPCP : PC * PC = PC := labelProj_mul_self _ _
  have hPRP : PR * PR = PR := labelProj_mul_self _ _
  have hPCpos : PC.PosSemidef := hPC.posSemidef_of_mul_self hPCP
  have hPRpos : PR.PosSemidef := hPR.posSemidef_of_mul_self hPRP
  have hP : IsStarProjection P := by
    rw [isStarProjection_iff']
    constructor
    · simp only [P, ← mul_kronecker_mul, one_mul, hPCP, hPRP]
    · change Pᴴ = P
      simp only [P, conjTranspose_kronecker, conjTranspose_one, hPC.eq, hPR.eq]
  have hLP : Commute L P := by
    change L * P = P * L
    simp only [L, P, ← mul_kronecker_mul, one_mul, mul_add, add_mul,
      mul_one, show FC * PC = PC * FC from hCC.eq,
      show FR * PR = PR * FR from hRR.eq]
  refine ⟨hP, hLP, ?_⟩
  have hC' : (PC * FC * PC - bC • PC).PosSemidef := by
    simpa only [Complex.coe_smul] using Matrix.le_iff.mp hC
  have hR' : (PR * FR * PR - bR • PR).PosSemidef := by
    simpa only [Complex.coe_smul] using Matrix.le_iff.mp hR
  have hsum := (PosSemidef.one (n := A)).kronecker
    ((hC'.kronecker hPRpos).add (hPCpos.kronecker hR'))
  apply Matrix.le_iff.mpr
  convert hsum using 1
  simp only [P, L, hb, add_smul, mul_add, add_mul, ← mul_kronecker_mul,
    mul_one, hPCP, hPRP, sub_eq_add_neg, add_kronecker, kronecker_add]
  ext x y
  simp only [kroneckerMap_apply, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply]
  simp only [RCLike.real_smul_eq_coe_mul]
  ring

/-- The two good auxiliary exponentials obey one joint compressed bound on
the intersection of the original label subspaces. This is a single operator
inequality, not a multiplication of separate quadratic estimates.
Source: `07-comparators.tex`, lines 481--493. -/
theorem copyPerm_groupedGood_auxiliaryPair_exp_compression
    (ellC ellR : IrrepLabel (Equiv.Perm (Fin k))) {a : ℝ} (ha : 0 ≤ a) :
    let PC := labelProj (copyPerm C k) ellC
    let PR := labelProj (copyPerm R k) ellR
    let FC := labelEntropy ((copyPerm C k).comp (groupHom₁ e))
    let FR := labelEntropy ((copyPerm R k).comp (groupHom₁ e))
    let P := (1 : Matrix A A ℂ) ⊗ₖ (PC ⊗ₖ PR)
    let L := (1 : Matrix A A ℂ) ⊗ₖ
      (FC ⊗ₖ (1 : Matrix (Fin k → R) (Fin k → R) ℂ) +
        (1 : Matrix (Fin k → C) (Fin k → C) ℂ) ⊗ₖ FR)
    let b := Real.log ellC.dim + Real.log ellR.dim -
      (r : ℝ) * (Real.log (Fintype.card C) + Real.log (Fintype.card R)) -
        2 * Real.log (k.choose r)
    P * NormedSpace.exp ((-a) • L) * P ≤ Real.exp (-a * b) • P := by
  intro PC PR FC FR P L b
  obtain ⟨hP, hLP, hfloor⟩ :=
    copyPerm_groupedGood_auxiliaryPair_labelEntropy_compression
      (A := A) (C := C) (R := R) e ellC ellR
  have hL : L.IsHermitian := by
    have hFC : FC.IsHermitian := isHermitian_labelObservable _ _
    have hFR : FR.IsHermitian := isHermitian_labelObservable _ _
    simp only [L, IsHermitian, conjTranspose_kronecker, conjTranspose_add,
      conjTranspose_one, hFC.eq, hFR.eq]
  exact hL.compression_exp_neg_smul_le_of_lower_bound hP hLP hfloor ha

end TensorPower

end

end GoodAuxiliaryPairCompression
