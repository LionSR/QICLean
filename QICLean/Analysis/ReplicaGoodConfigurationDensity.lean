/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodPhysicalSupport
import QICLean.Analysis.ReplicaGoodAuxiliaryMarginal

/-!
# Physical symmetric support after tracing all bad copies

The five finite factors are ordered as physical `Q`, `Y`, `V`, followed by
auxiliary `C`, `R`. The actual excitation component is formed from an
arbitrary original vector. Its reduced density retains all five factors on
every good copy and traces only the bad physical and auxiliary coordinates.
In particular, every good middle physical coordinate `Y` is retained.

The one-copy ground vector being unit implies physical symmetric support.
The proof derives the coordinate transport from the actual permutation
entries, and traces the bad auxiliary coordinates in the previously proved
physical-support identity. No symmetry or support assumption on the original
vector, and no supplied coordinate identity, is needed.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 23 and 103–110 for the independent physical
factors, lines 513–517 for physical symmetric support, and lines 520–549 for
the actual good-copy density. This result does not identify the marginal
obtained by subsequently tracing the good middle physical coordinates.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

open scoped BigOperators Matrix Kronecker
open TensorPower PermutationRepresentation

private def fiveFactorEquiv (ι : Fin 5 → Type*) :
    ((f : Fin 5) → ι f) ≃ (ι 0 × (ι 1 × ι 2)) × (ι 3 × ι 4) where
  toFun x := ((x 0, (x 1, x 2)), (x 3, x 4))
  invFun x := Fin.cons x.1.1 (Fin.cons x.1.2.1 (Fin.cons x.1.2.2
    (Fin.cons x.2.1 (Fin.cons x.2.2 (fun i => Fin.elim0 i)))))
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := rfl

namespace TensorPower

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, 07-comparators.tex,
lines 23, 103–110, 513–517 and 520–549.
Labels: comparator:merge-decomposition, comparator:merge-moments.
-/

/-- Regroup five-factor copy configurations as the whole physical copies and
the two auxiliary copy registers. The order is `Q`, `Y`, `V`, `C`, `R`.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 23, 103–110 and 513–517. The equivalence includes zero copies. -/
def fiveFactorCopiesEquiv (ι : Fin 5 → Type*) (m : ℕ) :
    Config m ι ≃ (Fin m → ι 0 × (ι 1 × ι 2)) ×
      ((Fin m → ι 3) × (Fin m → ι 4)) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) (fiveFactorEquiv ι)).trans
    ((Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => ι 0 × (ι 1 × ι 2)) (fun _ => ι 3 × ι 4)).trans
      ((Equiv.refl (Fin m → ι 0 × (ι 1 × ι 2))).prodCongr
        (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => ι 3) (fun _ => ι 4))))

end TensorPower

private theorem fiveFactorCopiesEquiv_subsystemPerm (ι : Fin 5 → Type*) (m : ℕ)
    (σ : Equiv.Perm (Fin m)) (x : Config m ι) :
    fiveFactorCopiesEquiv ι m (subsystemPerm m ι ({0, 1, 2} : Finset (Fin 5)) σ x) =
      (copyPerm (ι 0 × (ι 1 × ι 2)) m σ ((fiveFactorCopiesEquiv ι m x).1),
        (fiveFactorCopiesEquiv ι m x).2) := by
  rfl

private theorem fiveFactorCopiesEquiv_perm_condition (ι : Fin 5 → Type*) (m : ℕ)
    (σ : Equiv.Perm (Fin m))
    (x y : (Fin m → ι 0 × (ι 1 × ι 2)) × ((Fin m → ι 3) × (Fin m → ι 4))) :
    subsystemPerm m ι ({0, 1, 2} : Finset (Fin 5)) σ
        ((fiveFactorCopiesEquiv ι m).symm y) = (fiveFactorCopiesEquiv ι m).symm x ↔
      copyPerm (ι 0 × (ι 1 × ι 2)) m σ y.1 = x.1 ∧ y.2 = x.2 := by
  rw [← (fiveFactorCopiesEquiv ι m).injective.eq_iff,
    fiveFactorCopiesEquiv_subsystemPerm]
  simp only [Equiv.apply_symm_apply]
  exact Prod.ext_iff

private theorem fiveFactorCopiesEquiv_permOp (ι : Fin 5 → Type*) (m : ℕ)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (σ : Equiv.Perm (Fin m)) :
    (permOp (subsystemPerm m ι ({0, 1, 2} : Finset (Fin 5))) σ).submatrix
      (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      permOp (copyPerm (ι 0 × (ι 1 × ι 2)) m) σ ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
  ext x y
  simp only [Matrix.submatrix_apply, permOp_apply_apply,
    fiveFactorCopiesEquiv_perm_condition, Matrix.kroneckerMap_apply, Matrix.one_apply]
  split_ifs <;> simp_all

private theorem fiveFactorCopiesEquiv_symProj (ι : Fin 5 → Type*) (m : ℕ)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] :
    (symProj (subsystemPerm m ι ({0, 1, 2} : Finset (Fin 5)))).submatrix
      (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      symProj (copyPerm (ι 0 × (ι 1 × ι 2)) m) ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
  ext x y
  have he (σ : Equiv.Perm (Fin m)) :
      permOp (subsystemPerm m ι ({0, 1, 2} : Finset (Fin 5))) σ
        ((fiveFactorCopiesEquiv ι m).symm x) ((fiveFactorCopiesEquiv ι m).symm y) =
      permOp (copyPerm (ι 0 × (ι 1 × ι 2)) m) σ x.1 y.1 *
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) x.2 y.2 :=
    congrArg (fun M => M x y) (fiveFactorCopiesEquiv_permOp ι m σ)
  simp only [symProj, Matrix.submatrix_apply, Matrix.smul_apply,
    Matrix.sum_apply, Matrix.kroneckerMap_apply, smul_eq_mul]
  simp_rw [he]
  rw [← Finset.sum_mul, mul_assoc]

namespace Matrix

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, 07-comparators.tex,
lines 23, 103–110, 513–517 and 520–549.
Labels: comparator:merge-decomposition, comparator:merge-moments.
-/

/-- The actual excitation density retaining every good physical and auxiliary
coordinate and tracing only the bad copies. All good middle physical
coordinates are retained, using the same chosen good-copy enumeration in
every factor. *A two-dimensional area law from a global spectral gap*,
`07-comparators.tex`, lines 23, 103–110 and 520–549. No normalization or
symmetry is assumed in this definition. -/
noncomputable def replicaGoodConfigurationMarginal (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ) :
    Matrix (Config Bᶜ.card ι) (Config Bᶜ.card ι) ℂ :=
  let w := (Matrix.replicaExcitationProjection Ω k B ⊗ₖ
    (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
      ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
  let f := fun x : Config Bᶜ.card ι ×
      ((↥B → ι 0 × (ι 1 × ι 2)) × ((Fin B.card → ι 3) × (Fin B.card → ι 4))) =>
    let g := fiveFactorCopiesEquiv ι Bᶜ.card x.1
    w ((FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).symm
      (x.2.1, fun i => g.1 ((Finset.equivFin Bᶜ) i)),
      ((goodBadCopiesEquiv (ι 3) B).symm (g.2.1, x.2.2.1),
        (goodBadCopiesEquiv (ι 4) B).symm (g.2.2, x.2.2.2)))
  Matrix.partialTraceRight (Matrix.vecMulVec f (star f))

private noncomputable def goodAuxiliarySplit (ι : Fin 5 → Type*) {k : ℕ}
    (B : Finset (Fin k)) :
    ((Fin k → ι 3) × (Fin k → ι 4)) ≃
      ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4)) ×
        ((Fin B.card → ι 3) × (Fin B.card → ι 4)) :=
  ((goodBadCopiesEquiv (ι 3) B).prodCongr (goodBadCopiesEquiv (ι 4) B)).trans
    (Equiv.prodProdProdComm (Fin Bᶜ.card → ι 3) (Fin B.card → ι 3)
      (Fin Bᶜ.card → ι 4) (Fin B.card → ι 4))

private theorem replicaGoodConfigurationMarginal_eq (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ) :
    let w := (Matrix.replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let f := fun x : ((Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) ×
        ((Fin k → ι 3) × (Fin k → ι 4))) × (↥B → ι 0 × (ι 1 × ι 2)) =>
      w ((FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).symm
        (x.2, fun i => x.1.1 ((Finset.equivFin Bᶜ) i)), x.1.2)
    replicaGoodConfigurationMarginal ι Ω k B u =
      (Matrix.partialTraceRightAlong (goodAuxiliarySplit ι B)
        (Matrix.partialTraceRight (Matrix.vecMulVec f (star f)))).submatrix
          (fiveFactorCopiesEquiv ι Bᶜ.card) (fiveFactorCopiesEquiv ι Bᶜ.card) := by
  intro w f
  ext x y
  let H (b : ↥B → ι 0 × (ι 1 × ι 2))
      (c : Fin B.card → ι 3) (r : Fin B.card → ι 4) :=
    f (((fiveFactorCopiesEquiv ι Bᶜ.card x).1,
      (goodAuxiliarySplit ι B).symm ((fiveFactorCopiesEquiv ι Bᶜ.card x).2, (c, r))), b) *
    star (f (((fiveFactorCopiesEquiv ι Bᶜ.card y).1,
      (goodAuxiliarySplit ι B).symm ((fiveFactorCopiesEquiv ι Bᶜ.card y).2, (c, r))), b))
  change (∑ b : (↥B → ι 0 × (ι 1 × ι 2)) ×
      ((Fin B.card → ι 3) × (Fin B.card → ι 4)), H b.1 b.2.1 b.2.2) =
    ∑ d : (Fin B.card → ι 3) × (Fin B.card → ι 4), ∑ b, H b d.1 d.2
  rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

private theorem partialTraceRightAlong_kronecker_mul_left
    {A K G H : Type*} [Fintype A] [Fintype K] [DecidableEq K]
    [Fintype G] [DecidableEq G] [Fintype H]
    (e : K ≃ G × H) (P : Matrix A A ℂ) (M : Matrix (A × K) (A × K) ℂ) :
    Matrix.partialTraceRightAlong e ((P ⊗ₖ (1 : Matrix K K ℂ)) * M) =
      (P ⊗ₖ (1 : Matrix G G ℂ)) * Matrix.partialTraceRightAlong e M := by
  classical
  ext ⟨a, g⟩ ⟨a', g'⟩
  simp only [Matrix.partialTraceRightAlong_apply, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type,
    mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_one]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-
Original formalization, no upstream Lean proof text reused.
Manuscript: September 24, 2026, 07-comparators.tex,
lines 23, 103–110, 513–517 and 520–549.
Labels: comparator:merge-decomposition, comparator:merge-moments.
-/

/-- The physical-only symmetrizer fixes the actual full good-copy density.
Only the one-copy ground vector is unit; the original vector is arbitrary.
*A two-dimensional area law from a global spectral gap*, `07-comparators.tex`,
lines 513–517 and 520–549, with the independent middle physical factor of
lines 23 and 103–110 retained. Zero components, zero copies and empty good
sets are included. -/
theorem symProj_mul_replicaGoodConfigurationMarginal (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ) :
    symProj (subsystemPerm Bᶜ.card ι ({0, 1, 2} : Finset (Fin 5))) *
        replicaGoodConfigurationMarginal ι Ω k B u =
      replicaGoodConfigurationMarginal ι Ω k B u := by
  have hs := Matrix.symProj_mul_replicaExcitationComponent_goodAuxiliary_density Ω hΩ B u
  have hr := congrArg (Matrix.partialTraceRightAlong (goodAuxiliarySplit ι B)) hs
  rw [partialTraceRightAlong_kronecker_mul_left] at hr
  apply (Matrix.reindex (fiveFactorCopiesEquiv ι Bᶜ.card)
    (fiveFactorCopiesEquiv ι Bᶜ.card)).injective
  simp only [Matrix.reindex_apply]
  rw [← Matrix.submatrix_mul_equiv _ _ (fiveFactorCopiesEquiv ι Bᶜ.card).symm
    (fiveFactorCopiesEquiv ι Bᶜ.card).symm (fiveFactorCopiesEquiv ι Bᶜ.card).symm,
    fiveFactorCopiesEquiv_symProj, replicaGoodConfigurationMarginal_eq]
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm,
    Matrix.submatrix_id_id] using hr

end Matrix
