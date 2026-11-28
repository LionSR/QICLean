/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Replica.Configuration.GoodConfigurationMergeTransport
import QICLean.ManyBody.Replica.Configuration.GoodPairMarginal
import QICLean.Representation.TensorPower.PairMergeDeficit
import QICLean.Analysis.TraceInequality.WeightedTraceHolder
import QICLean.Representation.TensorPower.PairMergeMoment
import QICLean.Representation.Permutation.MergeExponential
import QICLean.ManyBody.Replica.Configuration.JointDensity
import QICLean.Algebra.Matrix.MatrixReindex
import QICLean.Representation.Replica.PermutationCovariance

/-!
# Merge moments in the actual five-factor good density

The two merge deficits on the good five-factor configuration space have
exactly the same exponential expectation as their paired-copy operators
in the actual common good-pair marginal. Applying the paired moment
estimate gives its arithmetic-mean polynomial bound, with the squared
norm of the same excitation component. No normalization of that component
or of either marginal is required.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 520–555, `comparator:merge-moments` and
`comparator:component-inverse`. The estimate below is the arithmetic-mean
consequence for the two merges, not the complete inverse-filter estimate.

It also contains the following results.

* `Matrix.replicaGoodPairMarginal_exp_mergeDeficits_le`,
  `Matrix.replicaGoodPairMarginal_exp_sum_mergeDeficit_le`: two merge moments of an actual
  excitation component.

## Main results

* `Matrix.replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le`: exponential merge moments of
  excitation components.
-/

section ComponentMergeMoment

/-!
## Exponential merge moments of excitation components

The good regional and auxiliary marginal of an actual excitation component
satisfies the exponential Schur-label merge-moment estimate. Its positivity,
separate copy-permutation invariances and trace mass are derived from the
component itself. The moment is bounded by a polynomial in the number of good
copies times the squared norm of the component.

OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 520–549, equation
`comparator:merge-moments`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Zero components, zero copies and an empty set of good copies are included.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open Matrix PermutationRepresentation

open scoped Kronecker
namespace TensorPower
variable {Q C : Type*} [Fintype Q] [Fintype C] [DecidableEq Q] [DecidableEq C]
    {m : ℕ}

private theorem permOp_pairCopyLeft (σ : Equiv.Perm (Fin m)) :
    permOp (pairCopyLeft Q C m) σ =
      permOp (copyPerm Q m) σ ⊗ₖ (1 : Matrix (Fin m → C) (Fin m → C) ℂ) := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [permOp_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  change (if (((copyPerm Q m) σ) y, b) = (x, a) then (1 : ℂ) else 0) =
    (if ((copyPerm Q m) σ) y = x then 1 else 0) * (if a = b then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

private theorem permOp_pairCopyRight (σ : Equiv.Perm (Fin m)) :
    permOp (pairCopyRight Q C m) σ =
      (1 : Matrix (Fin m → Q) (Fin m → Q) ℂ) ⊗ₖ permOp (copyPerm C m) σ := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [permOp_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]
  change (if (y, ((copyPerm C m) σ) b) = (x, a) then (1 : ℂ) else 0) =
    (if x = y then 1 else 0) * (if ((copyPerm C m) σ) b = a then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

private theorem commute_pair_product_left {A : Matrix (Fin m → Q) (Fin m → Q) ℂ}
    (B : Matrix (Fin m → C) (Fin m → C) ℂ) (σ : Equiv.Perm (Fin m))
    (hA : Commute (permOp (copyPerm Q m) σ) A) :
    Commute (permOp (pairCopyLeft Q C m) σ) (A ⊗ₖ B) := by
  rw [permOp_pairCopyLeft]
  change (permOp (copyPerm Q m) σ ⊗ₖ 1) * (A ⊗ₖ B) =
    (A ⊗ₖ B) * (permOp (copyPerm Q m) σ ⊗ₖ 1)
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hA.eq]

private theorem commute_pair_product_right (A : Matrix (Fin m → Q) (Fin m → Q) ℂ)
    {B : Matrix (Fin m → C) (Fin m → C) ℂ} (σ : Equiv.Perm (Fin m))
    (hB : Commute (permOp (copyPerm C m) σ) B) :
    Commute (permOp (pairCopyRight Q C m) σ) (A ⊗ₖ B) := by
  rw [permOp_pairCopyRight]
  change (1 ⊗ₖ permOp (copyPerm C m) σ) * (A ⊗ₖ B) =
    (A ⊗ₖ B) * (1 ⊗ₖ permOp (copyPerm C m) σ)
  simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, hB.eq]
end TensorPower

open scoped BigOperators Matrix Kronecker ComplexOrder Matrix.Norms.Operator
namespace Matrix

private theorem trace_actualGoodAuxiliary {A C D : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → A) × ((Fin k → C) × (Fin k → D)) → ℂ) :
    (replicaGoodAuxiliaryMarginal Ω k B u).trace =
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ u
      (vecMulVec w (star w)).trace := by
  dsimp only [replicaGoodAuxiliaryMarginal]
  rw [trace_partialTraceRight, trace_reindex, trace_partialTraceLeft]

private theorem trace_piKronecker_const {Q : Type*} [Fintype Q] (H : Matrix Q Q ℂ) (m : ℕ) :
    (piKronecker (fun _ : Fin m ↦ H)).trace = H.trace ^ m := by
  simp only [Matrix.trace, Matrix.diag, piKronecker_apply]
  calc
    _ = ∏ _ : Fin m, ∑ i : Q, H i i :=
      (Fintype.prod_sum (fun (_ : Fin m) (i : Q) ↦ H i i)).symm
    _ = _ := by simp

private theorem trace_groundRegional {Q T : Type*} [Fintype Q] [Fintype T]
    (Ω : Q × T → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) :
    (partialTraceRight (vecMulVec Ω (star Ω))).trace = 1 := by
  rw [trace_partialTraceRight, trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 Ω) (WithLp.toLp 2 Ω),
    inner_self_eq_norm_sq_to_K, hΩ]
  norm_num

private theorem trace_vecMulVec_re_norm_sq {X : Type*} [Fintype X] (w : X → ℂ) :
    (vecMulVec w (star w)).trace.re = ‖WithLp.toLp 2 w‖ ^ 2 := by
  rw [trace_vecMulVec,
    ← EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 w) (WithLp.toLp 2 w),
    inner_self_eq_norm_sq_to_K]
  change ((‖WithLp.toLp 2 w‖ : ℂ) ^ 2).re = ‖WithLp.toLp 2 w‖ ^ 2
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments, lines 520–549.
-/

/-- The exponential merge moment of the actual good regional and auxiliary
marginal is bounded by a polynomial times the squared norm of the same
excitation component. OpenAI, *A two-dimensional area law from a global
spectral gap*, `07-comparators.tex`, lines 520–549, equation
`comparator:merge-moments`. The only vector assumptions are normalization of
the one-copy ground vector and simultaneous permutation symmetry of the
original vector. The component need not be nonzero or normalized. -/
theorem replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le
    {Q T C D : Type*} [Fintype Q] [DecidableEq Q] [Fintype T] [DecidableEq T]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (Ω : Q × T → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → Q × T) × ((Fin k → C) × (Fin k → D)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (Q × T) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
          permOp (TensorPower.copyPerm D k) σ)) *ᵥ u = u)
    {b : ℝ} (hb : b ≤ 1) :
    let m := Bᶜ.card
    let ρ := replicaGoodRegionalAuxiliaryMarginal Ω k B u
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ u
    (ρ * NormedSpace.exp ((b : ℂ) •
      (labelEntropy (TensorPower.pairCopyLeft Q C m) +
        labelEntropy (TensorPower.pairCopyRight Q C m) -
          labelEntropy (TensorPower.pairCopyBoth Q C m)))).trace.re ≤
      ((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) * ‖WithLp.toLp 2 w‖ ^ 2 := by
  classical
  dsimp only
  let ρ := replicaGoodRegionalAuxiliaryMarginal Ω k B u
  have hρ : ρ.PosSemidef := by
    dsimp only [ρ, replicaGoodRegionalAuxiliaryMarginal]
    exact (posSemidef_vecMulVec_self_star (R := ℂ) _).partialTraceRight
  have hρQ (σ : Equiv.Perm (Fin Bᶜ.card)) :
      Commute (permOp (TensorPower.pairCopyLeft Q C Bᶜ.card) σ) ρ := by
    dsimp only [ρ]
    rw [replicaGoodRegionalAuxiliaryMarginal_eq Ω hΩ]
    exact TensorPower.commute_pair_product_left _ σ
      (commute_piKronecker_const_permOp _ _ σ).symm
  have hρC (σ : Equiv.Perm (Fin Bᶜ.card)) :
      Commute (permOp (TensorPower.pairCopyRight Q C Bᶜ.card) σ) ρ := by
    dsimp only [ρ]
    rw [replicaGoodRegionalAuxiliaryMarginal_eq Ω hΩ]
    exact TensorPower.commute_pair_product_right _ σ
      (commute_replicaGoodAuxiliaryMarginal_copyPerm Ω k B u hu σ)
  rw [re_trace_mul_exp_mergeDeficit_eq_sum (TensorPower.commute_pairCopy Q C Bᶜ.card)
    (TensorPower.pairCopyBoth_eq_mul Q C Bᶜ.card)]
  have h := TensorPower.pair_merge_moment_le_mul_trace Q C Bᶜ.card hρ hρQ hρC hb
  have hmass : ρ.trace =
      let w := (replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix ((Fin k → C) × (Fin k → D)) ((Fin k → C) × (Fin k → D)) ℂ)) *ᵥ u
      (vecMulVec w (star w)).trace := by
    dsimp only [ρ]
    rw [replicaGoodRegionalAuxiliaryMarginal_eq Ω hΩ, trace_kronecker,
      trace_piKronecker_const, trace_groundRegional Ω hΩ, one_pow, one_mul,
      trace_actualGoodAuxiliary]
  rw [hmass, trace_vecMulVec_re_norm_sq] at h
  exact h
end Matrix

end ComponentMergeMoment

section GoodConfigurationMergeMoment

section TwoMergeMoment

/-!
## Two merge moments of an actual excitation component

For a one-copy ground vector on three physical regions, retain the two exterior
physical regions and their auxiliary registers on the good copies. Trace every
middle physical coordinate and all bad-copy coordinates. The resulting positive
matrix has the two actual regional auxiliary marginals. Their doubled merge
moments bound the exponential of the sum of the two lifted merge deficits.

The second moment is derived by exchanging the exterior physical regions and
auxiliary registers, while preserving the middle physical region. Normalization,
simultaneous copy symmetry and the component norm are preserved by this literal
coordinate permutation; none is supplied independently for the exchanged state.

This is an auxiliary arithmetic-mean consequence for the rough estimate in
OpenAI, *A two-dimensional area law from a global spectral gap* (September 24,
2026), `07-comparators.tex`, lines 23, 103–110 and 524–555, equations
`comparator:merge-moments` and `comparator:component-inverse`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. It does not assert the printed
Cauchy–Schwarz geometric-mean bound or the full inverse-filter estimate.
The exponent may be any real number whose double is at most one. Zero
components, zero copies and an empty good set are included.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open scoped Kronecker BigOperators ComplexOrder Matrix.Norms.Operator
open Matrix PermutationRepresentation
namespace Matrix
variable {A C R : Type*} [Fintype A] [DecidableEq A]
  [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
omit [Fintype A] [Fintype C] in
/-- The matrix of a product coordinate permutation is the Kronecker product.
This elementary identity is used for the simultaneous copy symmetries in
OpenAI area-law manuscript, `07-comparators.tex`, lines 524–549. -/
private theorem perm_kronecker (e : Equiv.Perm A) (f : Equiv.Perm C) :
    e.permMatrix ℂ ⊗ₖ f.permMatrix ℂ =
      (show Equiv.Perm (A × C) from e.prodCongr f).permMatrix ℂ := by
  ext x y
  simp [Matrix.kroneckerMap_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp only [Prod.ext_iff, Prod.map_fst, Prod.map_snd]
  split_ifs <;> simp_all
omit [DecidableEq A] in
/-- A finite coordinate equivalence preserves the Euclidean vector norm.
This is used for the exterior-region exchange in the OpenAI area-law manuscript,
`07-comparators.tex`, lines 524–549. -/
private theorem norm_reindex {A' : Type*} [Fintype A']
    (e : A ≃ A') (v : A → ℂ) :
    ‖WithLp.toLp 2 (v ∘ e.symm)‖ = ‖WithLp.toLp 2 v‖ := by
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).norm_map (WithLp.toLp 2 v)

/-- The simultaneous copy action precomposes each literal copy string.
OpenAI area-law manuscript, `07-comparators.tex`, lines 524–549. -/
private theorem tripleCopy_mulVec (k : ℕ) (σ : Equiv.Perm (Fin k))
    (u : (Fin k → A) × ((Fin k → C) × (Fin k → R)) → ℂ) :
    (permOp (TensorPower.copyPerm A k) σ ⊗ₖ
      (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
        permOp (TensorPower.copyPerm R k) σ)) *ᵥ u =
      fun x => u (fun i => x.1 (σ i),
        (fun i => x.2.1 (σ i), fun i => x.2.2 (σ i))) := by
  rw [permOp_apply, permOp_apply, permOp_apply, perm_kronecker, perm_kronecker,
    Matrix.permMatrix_mulVec]
  rfl
omit [Fintype A] in
/-- A coordinate equivalence transports every actual ground and defect factor.
OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456 and 524–549. -/
private theorem excitation_reindex {A' : Type*} [DecidableEq A']
    (e : A ≃ A') (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k)) :
    replicaExcitationProjection (fun x => Ω (e.symm x)) k B =
      (replicaExcitationProjection Ω k B).submatrix
        (fun x i => e.symm (x i)) (fun x i => e.symm (x i)) := by
  ext x y
  simp only [replicaExcitationProjection, piKronecker_apply, submatrix_apply]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ B <;>
    simp [hi, Matrix.sub_apply, Matrix.one_apply, vecMulVec_apply, e.symm.injective.eq_iff]

/-- Transporting the actual excitation component preserves its norm.
OpenAI area-law manuscript, `07-comparators.tex`, lines 441–456 and 524–549. -/
private theorem norm_excitation_reindex {A' K K' : Type*}
    [Fintype A'] [DecidableEq A'] [Fintype K] [DecidableEq K]
    [Fintype K'] [DecidableEq K'] (e : A ≃ A') (g : K ≃ K')
    (Ω : A → ℂ) (k : ℕ) (B : Finset (Fin k)) (u : (Fin k → A) × K → ℂ) :
    let E := (Equiv.arrowCongr (Equiv.refl (Fin k)) e).prodCongr g
    ‖WithLp.toLp 2 ((replicaExcitationProjection (fun x => Ω (e.symm x)) k B ⊗ₖ
      (1 : Matrix K' K' ℂ)) *ᵥ (u ∘ E.symm))‖ =
      ‖WithLp.toLp 2 ((replicaExcitationProjection Ω k B ⊗ₖ
        (1 : Matrix K K ℂ)) *ᵥ u)‖ := by
  classical
  dsimp only
  have hmatrix : (replicaExcitationProjection (fun x => Ω (e.symm x)) k B ⊗ₖ
      (1 : Matrix K' K' ℂ)) =
      (replicaExcitationProjection Ω k B ⊗ₖ (1 : Matrix K K ℂ)).submatrix
        ((Equiv.arrowCongr (Equiv.refl (Fin k)) e).prodCongr g).symm
        ((Equiv.arrowCongr (Equiv.refl (Fin k)) e).prodCongr g).symm := by
    ext x y
    simp [excitation_reindex, kroneckerMap_apply, Matrix.one_apply,
      g.symm.injective.eq_iff, Equiv.arrowCongr, Function.comp_def]
  rw [hmatrix, submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  exact norm_reindex _ _

/-- Exchange the exterior physical coordinates while preserving the middle one.
OpenAI area-law manuscript, `07-comparators.tex`, lines 23, 103–110 and 524–549. -/
private def physicalExchange (Q Y V : Type*) : Q × (Y × V) ≃ V × (Y × Q) where
  toFun x := (x.2.2, (x.2.1, x.1))
  invFun x := (x.2.2, (x.2.1, x.1))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The literal exterior-region exchange preserves the one-copy ground norm.
OpenAI area-law manuscript, `07-comparators.tex`, lines 524–549. -/
private theorem norm_physicalExchange {Q Y V : Type*}
    [Fintype Q] [Fintype Y] [Fintype V] (Ω : Q × (Y × V) → ℂ) :
    ‖WithLp.toLp 2 (fun x : V × (Y × Q) => Ω (x.2.2, (x.2.1, x.1)))‖ =
      ‖WithLp.toLp 2 Ω‖ := by
  exact norm_reindex (physicalExchange Q Y V) Ω

/-- Original simultaneous copy fixedness implies fixedness after exchanging both
exterior physical and auxiliary coordinates. The middle physical coordinates
are retained. OpenAI area-law manuscript, `07-comparators.tex`, lines 524–549. -/
private theorem swapped_fixed {Q Y V : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype Y] [DecidableEq Y]
    [Fintype V] [DecidableEq V] (k : ℕ)
    (u : (Fin k → Q × (Y × V)) × ((Fin k → C) × (Fin k → R)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (Q × (Y × V)) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
          permOp (TensorPower.copyPerm R k) σ)) *ᵥ u = u) :
    ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (V × (Y × Q)) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm R k) σ ⊗ₖ
          permOp (TensorPower.copyPerm C k) σ)) *ᵥ
        (fun x => u ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))),
          (x.2.2, x.2.1))) =
        fun x => u ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))),
          (x.2.2, x.2.1)) := by
  intro σ
  simp only [tripleCopy_mulVec] at hu ⊢
  exact funext fun x => congrFun (hu σ)
    ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))), (x.2.2, x.2.1))
end Matrix

namespace Matrix

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, comparator:merge-moments and comparator:component-inverse,
lines 23, 103–110 and 524–555.
-/

/-- Each separate merge exponential on the actual common good-pair
marginal obeys its own polynomial moment bound. The parameter is any real
number at most one; no normalization or nonvanishing of the excitation
component is required. Both inequalities retain its original mass.
Source: September 24, 2026 area-law manuscript, `07-comparators.tex`,
lines 524–549, `comparator:merge-moments`. -/
theorem replicaGoodPairMarginal_exp_mergeDeficits_le {Q Y V C R : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype Y] [DecidableEq Y]
    [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (Ω : Q × (Y × V) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → Q × (Y × V)) × ((Fin k → C) × (Fin k → R)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (Q × (Y × V)) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
          permOp (TensorPower.copyPerm R k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : a ≤ 1) :
    let m := Bᶜ.card
    let ρ := replicaGoodPairMarginal Ω k B u
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) *ᵥ u
    let DC := TensorPower.pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ)
    let DR := (1 : Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ
      TensorPower.pairMergeDeficit V R m
    (ρ * NormedSpace.exp ((a : ℂ) • DC)).trace.re ≤
      (((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 ∧
    (ρ * NormedSpace.exp ((a : ℂ) • DR)).trace.re ≤
      (((m + 1) ^ ((Fintype.card V * Fintype.card R) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 := by
  classical
  intro m ρ w DC DR
  have hQC : (ρ * NormedSpace.exp ((a : ℂ) • DC)).trace.re ≤
      (((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 := by
    rw [TensorPower.trace_exp_pairMergeDeficit_left,
      partialTraceRight_replicaGoodPairMarginal]
    exact replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le Ω hΩ k B u hu ha
  have hVR : (ρ * NormedSpace.exp ((a : ℂ) • DR)).trace.re ≤
      (((m + 1) ^ ((Fintype.card V * Fintype.card R) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 := by
    rw [TensorPower.trace_exp_pairMergeDeficit_right,
      partialTraceLeft_replicaGoodPairMarginal]
    have hlocal := replicaGoodRegionalAuxiliaryMarginal_exp_mergeDeficit_le
      (fun x : V × (Y × Q) => Ω (x.2.2, (x.2.1, x.1)))
      ((norm_physicalExchange Ω).trans hΩ) k B
      (fun x => u ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))),
        (x.2.2, x.2.1))) (swapped_fixed k u hu) ha
    have hnorm :
        ‖WithLp.toLp 2 ((replicaExcitationProjection
          (fun x : V × (Y × Q) => Ω (x.2.2, (x.2.1, x.1))) k B ⊗ₖ
          (1 : Matrix ((Fin k → R) × (Fin k → C)) ((Fin k → R) × (Fin k → C)) ℂ)) *ᵥ
          (fun x => u ((fun i => ((x.1 i).2.2, ((x.1 i).2.1, (x.1 i).1))),
            (x.2.2, x.2.1))))‖ = ‖WithLp.toLp 2 w‖ := by
      simpa [physicalExchange, Equiv.arrowCongr, Function.comp_def, Prod.map, Prod.swap] using
        norm_excitation_reindex (physicalExchange Q Y V)
          (Equiv.prodComm (Fin k → C) (Fin k → R)) Ω k B u
    simpa only [hnorm, TensorPower.pairMergeDeficit, m] using hlocal
  exact ⟨hQC, hVR⟩

/-- The exponential of the two actual merge deficits on the common good-copy
marginal is bounded by the average of their polynomial bounds, multiplied by
the squared norm of the same excitation component. The physical middle region
is independent of the two exterior regions and all its copies are traced out.
The exchanged one-copy norm, simultaneous symmetry and component norm are
derived from the original vector by the literal exterior-region and auxiliary
exchange. No separate moment or marginal-invariance premise is imposed.
OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 23, 103–110 and 524–555, equations
`comparator:merge-moments` and `comparator:component-inverse`. This is an auxiliary
arithmetic-mean bound; the full inverse-filter estimate is a subsequent result. -/
theorem replicaGoodPairMarginal_exp_sum_mergeDeficit_le {Q Y V C R : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype Y] [DecidableEq Y]
    [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype R] [DecidableEq R]
    (Ω : Q × (Y × V) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → Q × (Y × V)) × ((Fin k → C) × (Fin k → R)) → ℂ)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (TensorPower.copyPerm (Q × (Y × V)) k) σ ⊗ₖ
        (permOp (TensorPower.copyPerm C k) σ ⊗ₖ
          permOp (TensorPower.copyPerm R k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : 2 * a ≤ 1) :
    let m := Bᶜ.card
    let ρ := replicaGoodPairMarginal Ω k B u
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → C) × (Fin k → R)) ((Fin k → C) × (Fin k → R)) ℂ)) *ᵥ u
    let DC := TensorPower.pairMergeDeficit Q C m ⊗ₖ
      (1 : Matrix ((Fin m → V) × (Fin m → R)) ((Fin m → V) × (Fin m → R)) ℂ)
    let DR := (1 : Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ) ⊗ₖ
      TensorPower.pairMergeDeficit V R m
    (ρ * NormedSpace.exp ((a : ℂ) • (DC + DR))).trace.re ≤
      ((((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card V * Fintype.card R) ^ 2) : ℕ) : ℝ)) / 2 *
          ‖WithLp.toLp 2 w‖ ^ 2 := by
  classical
  intro m ρ w DC DR
  have hρ : ρ.PosSemidef :=
    (posSemidef_vecMulVec_self_star (R := ℂ) _).partialTraceRight
  have hDC : DC.IsHermitian := by
    simp only [IsHermitian, DC, conjTranspose_kronecker,
      (TensorPower.isHermitian_pairMergeDeficit Q C m).eq, conjTranspose_one]
  have hDR : DR.IsHermitian := by
    simp only [IsHermitian, DR, conjTranspose_kronecker,
      (TensorPower.isHermitian_pairMergeDeficit V R m).eq, conjTranspose_one]
  have hAM := hρ.re_trace_mul_exp_add_le_half_sum hDC hDR
    (TensorPower.commute_pairMergeDeficit_lifts Q C m V R) a
  obtain ⟨hQC, hVR⟩ :=
    replicaGoodPairMarginal_exp_mergeDeficits_le Ω hΩ k B u hu (2 * a) ha
  linarith only [hAM, hQC, hVR]
end Matrix

end TwoMergeMoment

section GoodConfigurationMergeMoment

noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped BigOperators Kronecker Matrix.Norms.Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

local instance goodConfigurationMergeMoment_decidableEqConfig :
    DecidableEq (Config Bᶜ.card ι) := Fintype.decidablePiFintype

/-- The paired merge exponential has the same trace pairing in the full
good-copy density and its actual common good-pair marginal. No symmetry
or normalization is needed for this identity, and the parameter is any
real number. Source: `07-comparators.tex`, lines 520–549. -/
theorem trace_replicaGoodConfigurationMarginal_exp_sum_mergeDeficit (a : ℝ) :
    let m := Bᶜ.card
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    let DC := pairMergeDeficit (ι 0) (ι 3) m ⊗ₖ
      (1 : Matrix ((Fin m → ι 2) × (Fin m → ι 4))
        ((Fin m → ι 2) × (Fin m → ι 4)) ℂ)
    let DR := (1 : Matrix ((Fin m → ι 0) × (Fin m → ι 3))
      ((Fin m → ι 0) × (Fin m → ι 3)) ℂ) ⊗ₖ pairMergeDeficit (ι 2) (ι 4) m
    (replicaGoodConfigurationMarginal ι Ω k B u * NormedSpace.exp ((a : ℂ) •
      ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4})))).trace =
      (replicaGoodPairMarginal Ω k B u *
        NormedSpace.exp ((a : ℂ) • (DC + DR))).trace := by
  intro m F DC DR
  have h := trace_replicaGoodConfigurationMarginal_pairMiddle_mul ι Ω k B u
    (NormedSpace.exp ((a : ℂ) • (DC + DR)))
  rw [← fiveFactorPairMiddle_exp_sum_mergeDeficit ι m a,
    submatrix_mul_equiv, trace_submatrix_equiv] at h
  exact h

/-- The two actual five-factor merge deficits satisfy the paired
arithmetic-mean moment bound. The original vector is fixed by the
simultaneous copy action, the one-copy physical vector has norm one,
and the only restriction on the exponential parameter is `2 * a ≤ 1`.
The mass is the norm squared of the original excitation component.
Source: `07-comparators.tex`, lines 520–555. -/
theorem replicaGoodConfigurationMarginal_exp_sum_mergeDeficit_le
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ
          permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : 2 * a ≤ 1) :
    let m := Bᶜ.card
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u * NormedSpace.exp ((a : ℂ) •
      ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4})))).trace.re ≤
      ((((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) +
        (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ)) / 2 *
          ‖WithLp.toLp 2 w‖ ^ 2 := by
  intro m F w
  rw [trace_replicaGoodConfigurationMarginal_exp_sum_mergeDeficit]
  exact replicaGoodPairMarginal_exp_sum_mergeDeficit_le Ω hΩ k B u hu a ha

end Matrix

section ReplicaGoodConfigurationIndividualMergeMoment

/-!
# The two individual merge moments of the actual good density

Each original five-factor merge deficit has the same exponential trace
as its actual paired-copy deficit. Thus each retains its own polynomial
moment bound at every real parameter at most one. The component mass is
unchanged in both estimates.

Source: September 24, 2026 area-law manuscript, `07-comparators.tex`,
lines 524–560, `comparator:merge-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped BigOperators Kronecker Matrix.Norms.Operator

namespace Matrix

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

local instance goodIndividualMerge_decidableEqConfig :
    DecidableEq (Config Bᶜ.card ι) := Fintype.decidablePiFintype

local instance goodIndividualMerge_decidableEqCopies (j : Fin 5) :
    DecidableEq (Fin Bᶜ.card → ι j) := Fintype.decidablePiFintype

local instance goodIndividualMerge_decidableEqPair (i j : Fin 5) :
    DecidableEq ((Fin Bᶜ.card → ι i) × (Fin Bᶜ.card → ι j)) := inferInstance

local instance goodIndividualMerge_decidableEqPairMiddle :
    DecidableEq ((((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
      ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4))) ×
        (Fin Bᶜ.card → ι 1)) := inferInstance

private theorem trace_pairMiddle_exp_of_reindex
    (A : Matrix (Config Bᶜ.card ι) (Config Bᶜ.card ι) ℂ)
    (H : Matrix (((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
        ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4)))
      (((Fin Bᶜ.card → ι 0) × (Fin Bᶜ.card → ι 3)) ×
        ((Fin Bᶜ.card → ι 2) × (Fin Bᶜ.card → ι 4))) ℂ)
    (hA : A.submatrix (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm
        (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm =
      H ⊗ₖ (1 : Matrix (Fin Bᶜ.card → ι 1) (Fin Bᶜ.card → ι 1) ℂ)) (a : ℝ) :
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • A)).trace =
      (replicaGoodPairMarginal Ω k B u * NormedSpace.exp ((a : ℂ) • H)).trace := by
  have he : (NormedSpace.exp ((a : ℂ) • A)).submatrix
      (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm
      (fiveFactorPairMiddleEquiv ι Bᶜ.card).symm =
        NormedSpace.exp ((a : ℂ) • H) ⊗ₖ
          (1 : Matrix (Fin Bᶜ.card → ι 1) (Fin Bᶜ.card → ι 1) ℂ) := by
    rw [← reindex_apply, reindex_exp, reindex_apply, submatrix_smul,
      Pi.smul_apply, Pi.smul_apply, hA,
      ← smul_kronecker,
      exp_kronecker_one (n := Fin Bᶜ.card → ι 1) ((a : ℂ) • H)]
  have h := trace_replicaGoodConfigurationMarginal_pairMiddle_mul ι Ω k B u
    (NormedSpace.exp ((a : ℂ) • H))
  rw [← he, submatrix_mul_equiv, trace_submatrix_equiv] at h
  exact h

/-- Each of the two actual merge exponentials satisfies its own moment
bound on the full good-copy density. The original simultaneous symmetry
and one-copy normalization suffice; the component may vanish.
Source: `07-comparators.tex`, lines 524–560. -/
theorem replicaGoodConfigurationMarginal_exp_mergeDeficits_le
    (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (hu : ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (ι 0 × (ι 1 × ι 2)) k) σ ⊗ₖ
        (permOp (copyPerm (ι 3) k) σ ⊗ₖ permOp (copyPerm (ι 4) k) σ)) *ᵥ u = u)
    (a : ℝ) (ha : a ≤ 1) :
    let m := Bᶜ.card
    let F := fun S ↦ labelEntropy (subsystemPerm m ι S)
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • (F {0} + F {3} - F {0, 3}))).trace.re ≤
      (((m + 1) ^ ((Fintype.card (ι 0) * Fintype.card (ι 3)) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 ∧
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) • (F {2} + F {4} - F {2, 4}))).trace.re ≤
      (((m + 1) ^ ((Fintype.card (ι 2) * Fintype.card (ι 4)) ^ 2) : ℕ) : ℝ) *
        ‖WithLp.toLp 2 w‖ ^ 2 := by
  intro m F w
  obtain ⟨hC, hR⟩ := fiveFactorPairMiddle_mergeDeficits ι m
  have hm := replicaGoodPairMarginal_exp_mergeDeficits_le Ω hΩ k B u hu a ha
  constructor
  · rw [trace_pairMiddle_exp_of_reindex ι Ω k B u _ _ hC a]
    exact hm.1
  · rw [trace_pairMiddle_exp_of_reindex ι Ω k B u _ _ hR a]
    exact hm.2

end Matrix
end

end ReplicaGoodConfigurationIndividualMergeMoment

end

end GoodConfigurationMergeMoment

end GoodConfigurationMergeMoment
