/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.KroneckerExponential
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Analysis.TraceDistance
import QICLean.Entropy.PureTensorPower
import QICLean.Representation.SchurLabelIIDMoments

/-!
# Signed physical label moments of the full good-copy density

The three physical tensor factors are distinct, and all three remain in the
actual good-copy density together with the two good auxiliary registers.
The ground vector may be entangled among these physical factors. For any
physical singleton, the centered exponential trace equals the actual component
mass times the independent-copy moment of its ground-state marginal.

The one-copy surprisal-growth hypothesis therefore gives both signed physical
label moments with their explicit logarithmic loss. The original vector is
arbitrary. The argument retains the squared norm of its excitation component
without normalization, and includes zero components and zero good copies.
No reduced-density identity or label-moment estimate is supplied as a premise.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
  2026, `07-comparators.tex`, lines 75–85 (`comparator:mgf-data`), 227–238
  (`comparator:signed-label-moments`), 501–518 and 556–560
  (`comparator:component-inverse`), manuscript revision
  `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

universe u
noncomputable section
open Matrix TensorPower PermutationRepresentation
open scoped BigOperators ComplexOrder MatrixOrder Matrix Kronecker Matrix.Norms.Operator

namespace Matrix

private def goodAuxiliarySplit (ι : Fin 5 → Type*) {k : ℕ} (B : Finset (Fin k)) :
    ((Fin k → ι 3) × (Fin k → ι 4)) ≃
      ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4)) ×
        ((Fin B.card → ι 3) × (Fin B.card → ι 4)) :=
  ((goodBadCopiesEquiv (ι 3) B).prodCongr (goodBadCopiesEquiv (ι 4) B)).trans
    (Equiv.prodProdProdComm (Fin Bᶜ.card → ι 3) (Fin B.card → ι 3)
      (Fin Bᶜ.card → ι 4) (Fin B.card → ι 4))

private theorem full_good_density_product (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let φ := fun g : Fin Bᶜ.card → ι 0 × (ι 1 × ι 2) => ∏ i, Ω (g i)
    let τ := partialTraceRight ((partialTraceLeft (vecMulVec w (star w))).submatrix
      (goodAuxiliarySplit ι B).symm (goodAuxiliarySplit ι B).symm)
    (replicaGoodConfigurationMarginal ι Ω k B u).submatrix
      (fiveFactorCopiesEquiv ι Bᶜ.card).symm (fiveFactorCopiesEquiv ι Bᶜ.card).symm =
      vecMulVec φ (star φ) ⊗ₖ τ := by
  intro w φ τ
  let e : (↥(Bᶜ) → ι 0 × (ι 1 × ι 2)) ≃
      (Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) :=
    Equiv.arrowCongr (Finset.equivFin Bᶜ) (Equiv.refl _)
  have hd := congrArg (fun M : Matrix
      ((↥(Bᶜ) → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)))
      ((↥(Bᶜ) → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4))) ℂ =>
    M.submatrix (e.prodCongr (Equiv.refl _)).symm
      (e.prodCongr (Equiv.refl _)).symm)
    (partialTraceRight_replicaExcitationComponent_goodAuxiliary_density Ω hΩ B u)
  rw [← partialTraceRight_submatrix_prod_equiv (e.prodCongr (Equiv.refl _))
    (Equiv.refl (↥B → ι 0 × (ι 1 × ι 2)))] at hd
  have hprod (g : Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) :
      (∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i))) = φ g :=
    (Finset.equivFin Bᶜ).prod_comp (fun i => Ω (g i))
  change partialTraceRight (vecMulVec
      (fun x : ((Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) ×
          ((Fin k → ι 3) × (Fin k → ι 4))) × (↥B → ι 0 × (ι 1 × ι 2)) =>
        w ((FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).symm
          (x.2, fun i => x.1.1 ((Finset.equivFin Bᶜ) i)), x.1.2))
      (star (fun x =>
        w ((FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).symm
          (x.2, fun i => x.1.1 ((Finset.equivFin Bᶜ) i)), x.1.2)))) =
    vecMulVec (fun g => ∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i)))
      (star (fun g => ∏ i : ↥(Bᶜ), Ω (g ((Finset.equivFin Bᶜ) i)))) ⊗ₖ
      partialTraceLeft (vecMulVec w (star w)) at hd
  simp_rw [hprod] at hd
  ext x y
  have he (a : ((Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) ×
      ((Fin k → ι 3) × (Fin k → ι 4))))
      (a' : ((Fin Bᶜ.card → ι 0 × (ι 1 × ι 2)) ×
      ((Fin k → ι 3) × (Fin k → ι 4)))) := congrArg (fun M => M a a') hd
  let H (b : ↥B → ι 0 × (ι 1 × ι 2))
      (d : (Fin B.card → ι 3) × (Fin B.card → ι 4)) :=
    w ((FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).symm
      (b, fun i => x.1 ((Finset.equivFin Bᶜ) i)),
      (goodAuxiliarySplit ι B).symm (x.2, d)) *
    star (w ((FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).symm
      (b, fun i => y.1 ((Finset.equivFin Bᶜ) i)),
      (goodAuxiliarySplit ι B).symm (y.2, d)))
  simp only [replicaGoodConfigurationMarginal, Matrix.submatrix_apply]
  change (∑ p : (↥B → ι 0 × (ι 1 × ι 2)) ×
      ((Fin B.card → ι 3) × (Fin B.card → ι 4)), H p.1 p.2) =
    φ x.1 * star (φ y.1) *
      ∑ d : (Fin B.card → ι 3) × (Fin B.card → ι 4),
        partialTraceLeft (vecMulVec w (star w))
          ((goodAuxiliarySplit ι B).symm (x.2, d))
          ((goodAuxiliarySplit ι B).symm (y.2, d))
  rw [Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  exact he (x.1, (goodAuxiliarySplit ι B).symm (x.2, d))
    (y.1, (goodAuxiliarySplit ι B).symm (y.2, d))

private theorem auxiliary_trace_mass (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)]
    (k : ℕ) (B : Finset (Fin k))
    (w : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ) :
    (partialTraceRight ((partialTraceLeft (vecMulVec w (star w))).submatrix
      (goodAuxiliarySplit ι B).symm (goodAuxiliarySplit ι B).symm)).trace =
      (‖WithLp.toLp 2 w‖ ^ 2 : ℂ) := by
  rw [trace_partialTraceRight, trace_submatrix_equiv, trace_partialTraceLeft,
    trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct
      (WithLp.toLp 2 w) (WithLp.toLp 2 w), inner_self_eq_norm_sq_to_K]
  norm_cast

end Matrix

private abbrev physicalFamily (ι : Fin 5 → Type u) (r : Fin 3) : Type u :=
  ι r.castSucc.castSucc

private def physicalProductEquiv (ι : Fin 5 → Type*) :
    ((r : Fin 3) → physicalFamily ι r) ≃ ι 0 × (ι 1 × ι 2) where
  toFun x := (x 0, (x 1, x 2))
  invFun x := Fin.cons x.1 (Fin.cons x.2.1 (Fin.cons x.2.2 (fun i => Fin.elim0 i)))
  left_inv x := by
    funext r
    fin_cases r <;> rfl
  right_inv x := rfl

private def physicalRegionEquiv (ι : Fin 5 → Type*) (r : Fin 3) :
    (ι 0 × (ι 1 × ι 2)) ≃
      ((s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) × physicalFamily ι r :=
  ((physicalProductEquiv ι).symm.trans (Equiv.piSplitAt r (physicalFamily ι))).trans
    (Equiv.prodComm _ _)

private def physicalRegionCopiesEquiv (ι : Fin 5 → Type*) (m : ℕ) (r : Fin 3) :
    (Fin m → ι 0 × (ι 1 × ι 2)) ≃
      (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ×
        (Fin m → physicalFamily ι r) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) (physicalRegionEquiv ι r)).trans
    (Equiv.arrowProdEquivProdArrow _ _ _)

private def singletonCopiesEquiv (ι : Fin 5 → Type*) (m : ℕ) (r : Fin 3) :
    Config m ι ≃
      ((Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ×
        (Fin m → physicalFamily ι r)) × ((Fin m → ι 3) × (Fin m → ι 4)) :=
  (fiveFactorCopiesEquiv ι m).trans
    ((physicalRegionCopiesEquiv ι m r).prodCongr (Equiv.refl _))

private theorem singletonCopiesEquiv_subsystemPerm (ι : Fin 5 → Type*)
    (m : ℕ) (r : Fin 3) (σ : Equiv.Perm (Fin m)) (x : Config m ι) :
    singletonCopiesEquiv ι m r
        (subsystemPerm m ι {r.castSucc.castSucc} σ x) =
      (((singletonCopiesEquiv ι m r x).1.1,
        copyPerm (physicalFamily ι r) m σ (singletonCopiesEquiv ι m r x).1.2),
        (singletonCopiesEquiv ι m r x).2) := by
  have hcoordinate (z : Config m ι) (i : Fin m) (s : Fin 3) :
      (physicalProductEquiv ι).symm ((fiveFactorCopiesEquiv ι m z).1 i) s =
        z i s.castSucc.castSucc := by
    fin_cases s <;> rfl
  apply Prod.ext
  · apply Prod.ext
    · funext i s
      have hne : s.1.castSucc.castSucc ≠ r.castSucc.castSucc := by
        intro he
        apply s.2
        apply Fin.ext
        simpa only [Fin.val_castSucc] using congrArg Fin.val he
      change (physicalProductEquiv ι).symm
        ((fiveFactorCopiesEquiv ι m (subsystemPerm m ι {r.castSucc.castSucc} σ x)).1 i) s.1 =
        (physicalProductEquiv ι).symm ((fiveFactorCopiesEquiv ι m x).1 i) s.1
      rw [hcoordinate, hcoordinate]
      change (if s.1.castSucc.castSucc ∈ ({r.castSucc.castSucc} : Finset (Fin 5))
        then x (σ.symm i) s.1.castSucc.castSucc
        else x i s.1.castSucc.castSucc) = x i s.1.castSucc.castSucc
      simp only [Finset.mem_singleton, hne, ↓reduceIte]
    · funext i
      change (physicalProductEquiv ι).symm
        ((fiveFactorCopiesEquiv ι m (subsystemPerm m ι {r.castSucc.castSucc} σ x)).1 i) r =
        (physicalProductEquiv ι).symm ((fiveFactorCopiesEquiv ι m x).1 (σ.symm i)) r
      rw [hcoordinate, hcoordinate]
      change (if r.castSucc.castSucc ∈ ({r.castSucc.castSucc} : Finset (Fin 5))
        then x (σ.symm i) r.castSucc.castSucc
        else x i r.castSucc.castSucc) = x (σ.symm i) r.castSucc.castSucc
      simp only [Finset.mem_singleton, ↓reduceIte]
  · apply Prod.ext
    · funext i
      have hne : (3 : Fin 5) ≠ r.castSucc.castSucc := by
        intro he
        have hr := r.isLt
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc] at hv
        omega
      change (if (3 : Fin 5) ∈ ({r.castSucc.castSucc} : Finset (Fin 5))
        then x (σ.symm i) 3 else x i 3) = x i 3
      simp only [Finset.mem_singleton, hne, ↓reduceIte]
    · funext i
      have hne : (4 : Fin 5) ≠ r.castSucc.castSucc := by
        intro he
        have hr := r.isLt
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc] at hv
        omega
      change (if (4 : Fin 5) ∈ ({r.castSucc.castSucc} : Finset (Fin 5))
        then x (σ.symm i) 4 else x i 4) = x i 4
      simp only [Finset.mem_singleton, hne, ↓reduceIte]

private theorem singleton_labelEntropy_transport (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (m : ℕ) (r : Fin 3) :
    (labelEntropy (subsystemPerm m ι {r.castSucc.castSucc})).submatrix
      (singletonCopiesEquiv ι m r).symm (singletonCopiesEquiv ι m r).symm =
      ((1 : Matrix (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s)
        (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ℂ) ⊗ₖ
        labelEntropy (copyPerm (physicalFamily ι r) m)) ⊗ₖ
      (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
        ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
  have hp (σ : Equiv.Perm (Fin m)) :
      (permOp (subsystemPerm m ι {r.castSucc.castSucc}) σ).submatrix
        (singletonCopiesEquiv ι m r).symm (singletonCopiesEquiv ι m r).symm =
      ((1 : Matrix (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s)
        (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ℂ) ⊗ₖ
        permOp (copyPerm (physicalFamily ι r) m) σ) ⊗ₖ
      (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
        ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
    ext x y
    have hc : subsystemPerm m ι {r.castSucc.castSucc} σ
        ((singletonCopiesEquiv ι m r).symm y) =
        (singletonCopiesEquiv ι m r).symm x ↔
        y.1.1 = x.1.1 ∧ copyPerm (physicalFamily ι r) m σ y.1.2 = x.1.2 ∧
          y.2 = x.2 := by
      rw [← (singletonCopiesEquiv ι m r).injective.eq_iff,
        singletonCopiesEquiv_subsystemPerm]
      simp only [Equiv.apply_symm_apply, Prod.ext_iff, and_assoc]
    simp only [Matrix.submatrix_apply, permOp_apply_apply, hc,
      Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases hT : x.1.1 = y.1.1 <;>
      by_cases hQ : copyPerm (physicalFamily ι r) m σ y.1.2 = x.1.2 <;>
      by_cases hK : x.2 = y.2 <;> simp only [hT, hQ, hK, eq_comm, ↓reduceIte,
        and_true, and_false, mul_zero, mul_one]
  have hl (l : IrrepLabel (Equiv.Perm (Fin m))) :
      (labelProj (subsystemPerm m ι {r.castSucc.castSucc}) l).submatrix
        (singletonCopiesEquiv ι m r).symm (singletonCopiesEquiv ι m r).symm =
      ((1 : Matrix (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s)
        (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ℂ) ⊗ₖ
        labelProj (copyPerm (physicalFamily ι r) m) l) ⊗ₖ
      (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
        ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
    ext x y
    simp only [labelProj, groupAlgebraRep_eq_sum, Matrix.submatrix_apply,
      Matrix.sum_apply, Matrix.smul_apply]
    simp_rw [← Matrix.submatrix_apply (permOp (subsystemPerm m ι {r.castSucc.castSucc}) _), hp]
    simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    ring
  ext x y
  simp only [labelEntropy, labelObservable, Matrix.submatrix_apply,
    Matrix.sum_apply, Matrix.smul_apply]
  simp_rw [← Matrix.submatrix_apply (labelProj (subsystemPerm m ι {r.castSucc.castSucc}) _), hl]
  simp only [Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

namespace Matrix
private theorem exp_submatrix_equiv {A D : Type*}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (e : A ≃ D) (X : Matrix A A ℂ) :
    (NormedSpace.exp X).submatrix e.symm e.symm =
      NormedSpace.exp (X.submatrix e.symm e.symm) := by
  let f : Matrix A A ℂ →+* Matrix D D ℂ :=
    (Matrix.reindexAlgEquiv ℂ ℂ e).toRingEquiv.toRingHom
  have hf : Continuous f := by
    change Continuous (fun Y : Matrix A A ℂ => Y.submatrix e.symm e.symm)
    fun_prop
  exact NormedSpace.map_exp f hf X
end Matrix

namespace Matrix

private theorem ground_density_region_reindex (ι : Fin 5 → Type*)
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (m : ℕ) (r : Fin 3) :
    let Ωr := fun x : ((s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ×
        physicalFamily ι r => Ω ((physicalRegionEquiv ι r).symm x)
    let φ := fun g : Fin m → ι 0 × (ι 1 × ι 2) => ∏ i, Ω (g i)
    let ψ := fun x : (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ×
        (Fin m → physicalFamily ι r) => ∏ i, Ωr (x.1 i, x.2 i)
    (vecMulVec φ (star φ)).submatrix (physicalRegionCopiesEquiv ι m r).symm
      (physicalRegionCopiesEquiv ι m r).symm = vecMulVec ψ (star ψ) := by
  rfl

private theorem full_good_density_region_product (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (r : Fin 3) :
    let Ωr := fun x : ((s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ×
        physicalFamily ι r => Ω ((physicalRegionEquiv ι r).symm x)
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let τ := partialTraceRight ((partialTraceLeft (vecMulVec w (star w))).submatrix
      (goodAuxiliarySplit ι B).symm (goodAuxiliarySplit ι B).symm)
    let ψ := fun x : (Fin Bᶜ.card → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ×
        (Fin Bᶜ.card → physicalFamily ι r) => ∏ i, Ωr (x.1 i, x.2 i)
    (replicaGoodConfigurationMarginal ι Ω k B u).submatrix
      (singletonCopiesEquiv ι Bᶜ.card r).symm
      (singletonCopiesEquiv ι Bᶜ.card r).symm = vecMulVec ψ (star ψ) ⊗ₖ τ := by
  intro Ωr w τ ψ
  change ((replicaGoodConfigurationMarginal ι Ω k B u).submatrix
      (fiveFactorCopiesEquiv ι Bᶜ.card).symm (fiveFactorCopiesEquiv ι Bᶜ.card).symm).submatrix
      ((physicalRegionCopiesEquiv ι Bᶜ.card r).prodCongr
        (Equiv.refl ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4)))).symm
      ((physicalRegionCopiesEquiv ι Bᶜ.card r).prodCongr
        (Equiv.refl ((Fin Bᶜ.card → ι 3) × (Fin Bᶜ.card → ι 4)))).symm = _
  rw [full_good_density_product ι Ω hΩ k B u]
  change ((vecMulVec (fun g : Fin Bᶜ.card → ι 0 × (ι 1 × ι 2) => ∏ i, Ω (g i))
      (star (fun g : Fin Bᶜ.card → ι 0 × (ι 1 × ι 2) => ∏ i, Ω (g i)))).submatrix
        (physicalRegionCopiesEquiv ι Bᶜ.card r).symm
        (physicalRegionCopiesEquiv ι Bᶜ.card r).symm) ⊗ₖ τ = _
  rw [ground_density_region_reindex]

private theorem norm_regional_ground (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (r : Fin 3) :
    ‖WithLp.toLp 2 (fun x => Ω ((physicalRegionEquiv ι r).symm x))‖ =
      ‖WithLp.toLp 2 Ω‖ := by
  have he : (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (physicalRegionEquiv ι r))
      (WithLp.toLp 2 Ω) = WithLp.toLp 2 (fun x => Ω ((physicalRegionEquiv ι r).symm x)) := by
    ext x
    rfl
  simpa only [he] using
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (physicalRegionEquiv ι r)).norm_map
      (WithLp.toLp 2 Ω)

private theorem centered_singleton_exp_transport (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] (m : ℕ) (r : Fin 3) (c t : ℝ) :
    (NormedSpace.exp ((t : ℂ) •
      (labelEntropy (subsystemPerm m ι {r.castSucc.castSucc}) - (c : ℂ) • 1))).submatrix
      (singletonCopiesEquiv ι m r).symm (singletonCopiesEquiv ι m r).symm =
      ((1 : Matrix (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s)
        (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ℂ) ⊗ₖ
      NormedSpace.exp ((t : ℂ) •
        (labelEntropy (copyPerm (physicalFamily ι r) m) - (c : ℂ) • 1))) ⊗ₖ
      (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
        ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
  let : (j : {j : Fin 3 // j ≠ r}) → DecidableEq (physicalFamily ι j) :=
    fun j => inferInstance
  let : DecidableEq ((j : {j : Fin 3 // j ≠ r}) → physicalFamily ι j) := inferInstance
  let : DecidableEq (Fin m → (j : {j : Fin 3 // j ≠ r}) → physicalFamily ι j) :=
    inferInstance
  let : DecidableEq (Fin m → physicalFamily ι r) := inferInstance
  let : DecidableEq ((Fin m → ι 3) × (Fin m → ι 4)) := inferInstance
  rw [exp_submatrix_equiv]
  simp only [Matrix.submatrix_smul, Matrix.submatrix_sub, Pi.smul_apply, Pi.sub_apply]
  rw [Matrix.submatrix_one_equiv, singleton_labelEntropy_transport]
  have hcenter : (t : ℂ) •
      (((1 : Matrix (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s)
          (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ℂ) ⊗ₖ
        labelEntropy (copyPerm (physicalFamily ι r) m)) ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) - (c : ℂ) • 1) =
      ((1 : Matrix (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s)
          (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ℂ) ⊗ₖ
        ((t : ℂ) • (labelEntropy (copyPerm (physicalFamily ι r) m) - (c : ℂ) • 1))) ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
    ext x y
    by_cases hT : x.1.1 = y.1.1 <;>
      by_cases hQ : x.1.2 = y.1.2 <;>
      by_cases hK : x.2 = y.2 <;>
      simp [Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Prod.ext_iff, hT, hQ, hK]
  rw [hcenter]
  calc
    _ = NormedSpace.exp
        ((1 : Matrix (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s)
          (Fin m → (s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ℂ) ⊗ₖ
          ((t : ℂ) • (labelEntropy (copyPerm (physicalFamily ι r) m) - (c : ℂ) • 1))) ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) :=
      Matrix.exp_kronecker_one _
    _ = _ := congrArg (fun X => X ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ))
      (Matrix.exp_one_kronecker ((t : ℂ) •
        (labelEntropy (copyPerm (physicalFamily ι r) m) - (c : ℂ) • 1)))

private theorem trace_centered_good_configuration_eq (ι : Fin 5 → Type*)
    [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (r : Fin 3) (s t : ℝ) :
    let Ωr := fun x : ((s : {s : Fin 3 // s ≠ r}) → physicalFamily ι s) ×
        physicalFamily ι r => Ω ((physicalRegionEquiv ι r).symm x)
    let σ := partialTraceLeft (vecMulVec Ωr (star Ωr))
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (replicaGoodConfigurationMarginal ι Ω k B u * NormedSpace.exp ((t : ℂ) •
      (labelEntropy (subsystemPerm Bᶜ.card ι {r.castSucc.castSucc}) -
        ((Bᶜ.card : ℝ) * s : ℂ) • 1))).trace =
      (‖WithLp.toLp 2 w‖ ^ 2 : ℂ) *
        (finKronecker (fun _ : Fin Bᶜ.card => σ) * NormedSpace.exp ((t : ℂ) •
          (labelEntropy (copyPerm (physicalFamily ι r) Bᶜ.card) -
            ((Bᶜ.card : ℝ) * s : ℂ) • 1))).trace := by
  intro Ωr σ w
  let e := singletonCopiesEquiv ι Bᶜ.card r
  rw [← Matrix.trace_submatrix_equiv e.symm,
    ← Matrix.submatrix_mul_equiv _ _ e.symm e.symm e.symm,
    full_good_density_region_product ι Ω hΩ k B u r]
  dsimp only [e]
  rw [← Complex.ofReal_mul, centered_singleton_exp_transport]
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.trace_kronecker,
    ← Matrix.trace_partialTraceLeft_mul, Matrix.partialTraceLeft_vecMulVec_prod Ωr Bᶜ.card,
    auxiliary_trace_mass]
  exact mul_comm _ _

end Matrix

namespace Matrix

/-- The signed centered moment of a physical singleton in the actual full
five-factor good-copy density is bounded by its literal component mass times
the independent-copy exponential estimate. The three physical tensor factors
are distinct; the middle factor is retained in this density.

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 75–85 (`comparator:mgf-data`), 227–238
(`comparator:signed-label-moments`), 501–518 and 556–560
(`comparator:component-inverse`). The only moment hypothesis concerns the
actual one-copy ground marginal. No component normalization, nonzero mass,
copy symmetry, or supplied density/transport identity is required. -/
theorem re_trace_mul_exp_centered_labelEntropy_replicaGoodConfigurationMarginal_le
    (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (r : Fin 3) (C₀ c₀ ℬ : ℝ) (hC : 0 ≤ C₀) (hc : 0 < c₀) (hℬ : 1 ≤ ℬ) :
    let Ωr : (((s : {s : Fin 3 // s ≠ r}) → ι s.1.castSucc.castSucc) ×
        ι r.castSucc.castSucc) → ℂ := fun x =>
      let q := (Equiv.piSplitAt r (fun s : Fin 3 => ι s.castSucc.castSucc)).symm
        (x.2, x.1)
      Ω (q 0, (q 1, q 2))
    let σ := partialTraceLeft (vecMulVec Ωr (star Ωr))
    let hσ := (posSemidef_vecMulVec_self_star Ωr).partialTraceLeft
    let m := Bᶜ.card
    let Γ := replicaGoodConfigurationMarginal ι Ω k B u
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    (∀ s : ℝ, |s| ≤ c₀ / Real.sqrt ℬ →
      Real.log (Entropy.surprisalMoment hσ.isHermitian.eigenvalues s) ≤
        s * vonNeumannEntropy σ hσ.isHermitian + C₀ * ℬ * s ^ 2) →
    ∀ t : ℝ, |t| ≤ ((min c₀ 1) / 2) / Real.sqrt ℬ →
      (Γ * NormedSpace.exp ((t : ℂ) •
        (labelEntropy (subsystemPerm m ι {r.castSucc.castSucc}) -
          ((m : ℝ) * vonNeumannEntropy σ hσ.isHermitian : ℂ) • 1))).trace.re ≤
        ‖WithLp.toLp 2 w‖ ^ 2 * Real.exp
          (2 * C₀ * m * ℬ * t ^ 2 +
            ((Fintype.card (ι r.castSucc.castSucc) : ℝ) ^ 2 / 2) * Real.log (m + 1)) := by
  intro Ωr σ hσ m Γ w hmgf t ht
  have hu : ‖WithLp.toLp 2 Ωr‖ = 1 :=
    (norm_regional_ground ι Ω r).trans hΩ
  have htr : σ.trace = 1 := by
    rw [trace_partialTraceLeft, trace_vecMulVec,
      ← EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 Ωr) (WithLp.toLp 2 Ωr),
      inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have hid := trace_centered_good_configuration_eq ι Ω hΩ k B u r
    (vonNeumannEntropy σ hσ.isHermitian) t
  have hlog := (TensorPower.log_centered_labelEntropy_finKronecker_le hσ htr m
    C₀ c₀ ℬ hC hc hℬ hmgf).2 t ht
  have hexp :
      (finKronecker (fun _ : Fin m => σ) * NormedSpace.exp ((t : ℂ) •
        (labelEntropy (copyPerm (physicalFamily ι r) m) -
          ((m : ℝ) * vonNeumannEntropy σ hσ.isHermitian : ℂ) • 1))).trace.re ≤
      Real.exp (2 * C₀ * m * ℬ * t ^ 2 +
        ((Fintype.card (ι r.castSucc.castSucc) : ℝ) ^ 2 / 2) * Real.log (m + 1)) :=
    (Real.le_exp_log _).trans (Real.exp_le_exp.mpr hlog)
  rw [hid]
  simp only [Complex.mul_re, ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  change ‖WithLp.toLp 2 w‖ ^ 2 *
      (finKronecker (fun _ : Fin m => σ) * NormedSpace.exp ((t : ℂ) •
        (labelEntropy (copyPerm (physicalFamily ι r) m) -
          ((m : ℝ) * vonNeumannEntropy σ hσ.isHermitian : ℂ) • 1))).trace.re ≤ _
  exact mul_le_mul_of_nonneg_left hexp (sq_nonneg ‖WithLp.toLp 2 w‖)

end Matrix
