/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.CutEnvironment
import QICLean.Entropy.RegionRank

/-!
# A cut inside a region with its whole outside environment

Splitting a subsystem and retaining the full exterior does not change the
Schmidt rank at the corresponding global region. The complement is split
into the rest of the subsystem and its exterior; neither part is discarded.

These coordinate identities support collective trimming in ALVV,
arXiv:1602.08828v2, `def:trimming` and `lem:trimming`, lines 646–697.
The uniform on-site dimension is retained explicitly.
-/

open Matrix
open scoped ComplexOrder

namespace Entropy

variable {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}

/-- The part of a global cut contained in a retained region. Supporting ALVV,
arXiv:1602.08828v2, `def:trimming`, lines 646–655. -/
def subregionCut (J A : Finset V) : Finset J :=
  Finset.univ.filter fun v ↦ v.1 ∈ A

omit [Fintype V] in
@[simp]
lemma mem_subregionCut {J A : Finset V} {v : J} :
    v ∈ subregionCut J A ↔ v.1 ∈ A := by
  simp [subregionCut]

/-- The same retained sites as a local or global subtype. Supporting ALVV,
arXiv:1602.08828v2, `def:trimming`, lines 646–655. -/
def subregionCutSubtypeEquiv {J A : Finset V} (hAJ : A ⊆ J) :
    {v : J // v ∈ subregionCut J A} ≃ A where
  toFun v := ⟨v.1.1, mem_subregionCut.mp v.2⟩
  invFun v := ⟨⟨v.1, hAJ v.2⟩, mem_subregionCut.mpr v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The complete complement of a global cut consists of the remainder of
its retained region and the exterior of that region. Supporting ALVV,
arXiv:1602.08828v2, `lem:trimming`, lines 660–697. -/
def subregionRestSubtypeEquiv {J A : Finset V} (hAJ : A ⊆ J) :
    {v : J // v ∉ subregionCut J A} ⊕ ↥(Jᶜ) ≃ {v : V // v ∉ A} where
  toFun := Sum.elim
    (fun v ↦ ⟨v.1.1, fun h ↦ v.2 (mem_subregionCut.mpr h)⟩)
    (fun v ↦ ⟨v.1, fun h ↦ (Finset.mem_compl.mp v.2) (hAJ h)⟩)
  invFun v :=
    if h : v.1 ∈ J then
      Sum.inl ⟨⟨v.1, h⟩, fun h' ↦ v.2 (mem_subregionCut.mp h')⟩
    else Sum.inr ⟨v.1, Finset.mem_compl.mpr h⟩
  left_inv v := by
    rcases v with v | v
    · simp [v.1.2]
    · simp [Finset.mem_compl.mp v.2]
  right_inv v := by
    by_cases h : v.1 ∈ J <;> simp [h]

/-- The actual region/exterior configuration split as a linear isometry.
Supporting ALVV, arXiv:1602.08828v2, Definition `d:vs`, lines 433–440. -/
noncomputable def regionConfigurationSplit (q : ℕ) (J : Finset V) :
    EuclideanSpace ℂ (V → Fin q) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((J → Fin q) × (↥(Jᶜ) → Fin q)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (FiniteProduct.splitEquiv (fun _ : V ↦ Fin q) J)

/-- A cut inside a retained region, with its full exterior kept as an
environment, has exactly the original global regional rank. Auxiliary to
ALVV, arXiv:1602.08828v2, `lem:trimming`, lines 660–697. -/
lemma schmidtRank_cutEnvVector_regionConfigurationSplit
    {J A : Finset V} (hAJ : A ⊆ J) (psi : EuclideanSpace ℂ (V → Fin q)) :
    Matrix.schmidtRank (WithLp.ofLp
      (cutEnvVector (n := fun _ : J ↦ q) (subregionCut J A)
        (regionConfigurationSplit q J psi))) =
      (regionState (n := fun _ : V ↦ q) A psi).rank := by
  classical
  rw [Matrix.schmidtRank]
  have hcoef : schmidtCoeffMatrix (WithLp.ofLp
      (cutEnvVector (n := fun _ : J ↦ q) (subregionCut J A)
        (regionConfigurationSplit q J psi))) =
      (schmidtCoeffMatrix (WithLp.ofLp (cutVector (n := fun _ : V ↦ q) A psi))).submatrix
        ((subregionCutSubtypeEquiv hAJ).arrowCongr (Equiv.refl (Fin q)))
        ((Equiv.sumArrowEquivProdArrow _ _ (Fin q)).symm.trans
          ((subregionRestSubtypeEquiv hAJ).arrowCongr (Equiv.refl (Fin q)))) := by
    ext x ⟨y, b⟩
    simp only [schmidtCoeffMatrix_apply, cutEnvVector_apply, regionConfigurationSplit,
      LinearIsometryEquiv.piLpCongrLeft_apply, submatrix_apply]
    refine congrArg (fun c : V → Fin q ↦ psi c) (funext fun v ↦ ?_)
    by_cases hvA : v ∈ A
    · have hvJ : v ∈ J := hAJ hvA
      rw [FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _ hvJ,
        cutEquiv_symm_apply_mem _ _ (mem_subregionCut.mpr hvA),
        cutEquiv_symm_apply_mem _ _ hvA]
      rfl
    · rw [cutEquiv_symm_apply_not_mem _ _ hvA]
      by_cases hvJ : v ∈ J
      · rw [FiniteProduct.splitEquiv_symm_apply_of_mem _ _ _ _ _ hvJ,
          cutEquiv_symm_apply_not_mem _ _ (fun h ↦ hvA (mem_subregionCut.mp h))]
        simp [subregionRestSubtypeEquiv, hvJ, Equiv.sumArrowEquivProdArrow]
      · rw [FiniteProduct.splitEquiv_symm_apply_of_notMem _ _ _ _ _ hvJ]
        simp [subregionRestSubtypeEquiv, hvJ, Equiv.sumArrowEquivProdArrow]
  rw [hcoef, rank_submatrix]
  rw [regionState, Matrix.partialTraceRight_vecMulVec_eq]
  exact (Matrix.rank_self_mul_conjTranspose _).symm

end Entropy
