/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.EnvironmentEmbedding
import QICLean.Channel.TensorMap
import QICLean.Channel.StinespringRectangular
import QICLean.Algebra.MatrixReindexUnitary

/-!
# Local channels with fresh pure environments

A local channel is realized by a unitary after adjoining a designated pure basis
state. The retained output is the original local system factor. All identities hold
on the complete operator space and therefore preserve arbitrary external references.
The dilation uses the Choi-rank bound in Wolf, Quantum Channels and Operations,
Theorems 2.2 and 2.5. Reindexing covers arbitrary finite system/environment bases.
Spatial locality and circuit-resource bounds are separate applications.
-/

open Matrix
open scoped BigOperators

namespace Matrix

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ}

/-- The full operator initialization, including all off-diagonal coherences. -/
def freshEnvironmentInput {η : Type*} [Fintype η] [DecidableEq η] (a : η) :
    Matrix α α ℂ →ₗ[ℂ] Matrix (α × η) (α × η) ℂ :=
  singleKrausMap (fixedEnvEmbedding a)

/-- The fresh environment is a literal pure basis state, independent of the input. -/
theorem freshEnvironmentInput_eq_kronecker {η : Type*} [Fintype η] [DecidableEq η]
    (a : η) (X : Matrix α α ℂ) :
    freshEnvironmentInput a X = Matrix.kroneckerMap (· * ·) X
      (Matrix.single a a (1 : ℂ)) := by
  classical
  have hE (u : α × η) (v : α) :
      fixedEnvEmbedding a u v =
        if u = (v, a) then (1 : ℂ) else 0 := by
    simp only [fixedEnvEmbedding, Matrix.one_apply, Prod.ext_iff]
    split_ifs <;> simp_all
  ext ⟨i, b⟩ ⟨j, c⟩
  simp only [freshEnvironmentInput, singleKrausMap_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, hE, Prod.mk.injEq, Matrix.kroneckerMap_apply,
    Matrix.single, apply_ite star]
  by_cases hb : b = a <;> by_cases hc : c = a <;> simp_all [eq_comm]

/-- Matrix blocks of a dilation unitary from one initialized environment column. -/
def environmentKraus {η : Type*} (U : Matrix (α × η) (α × η) ℂ)
    (a b : η) : Matrix α α ℂ := fun i j => U (i, b) (j, a)

/-- Discarding the environment after a fixed pure-basis input gives its column-block
Kraus map, even when the joint operator is not assumed unitary. -/
theorem partialTrace_freshEnvironmentInput {η : Type*}
    [Fintype η] [DecidableEq η] (U : Matrix (α × η) (α × η) ℂ)
    (a : η) (X : Matrix α α ℂ) :
    partialTraceRight (U * freshEnvironmentInput a X * Uᴴ) =
      rectangularKrausMap (environmentKraus U a) X := by
  rw [freshEnvironmentInput_eq_kronecker]
  change partialTraceRight (_ * _ * _) =
    ∑ b, environmentKraus U a b * X * (environmentKraus U a b)ᴴ
  ext i j
  simp only [Matrix.sum_apply, environmentKraus, partialTraceRight_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.single, Matrix.of_apply]
  simp only [ite_and, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Finset.sum_mul, mul_assoc]
  simp only [ite_mul, Finset.sum_ite_irrel, mul_assoc]
  simp

/-- A Kraus channel has a unitary dilation with the retained system in its original
factor and the environment initialized in any specified basis state. -/
theorem exists_freshEnvironment_unitary
    (K : Fin r → Matrix α α ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (a : Fin r) :
    ∃ U : Matrix.unitaryGroup (α × Fin r) ℂ,
      ∀ X : Matrix α α ℂ,
        rectangularKrausMap K X = partialTraceRight
          ((U : Matrix (α × Fin r) (α × Fin r) ℂ) * freshEnvironmentInput a X * Uᴴ) := by
  have hV : (stinespringV K)ᴴ * stinespringV K = 1 := by
    rw [stinespringV_conjTranspose_mul, hK]
  obtain ⟨U, hU⟩ := exists_unitary_mul_fixedEnvEmbedding_eq a (stinespringV K) hV
  refine ⟨U, fun X => ?_⟩
  have hrep : rectangularKrausMap K X =
      partialTraceRight (stinespringV K * X * (stinespringV K)ᴴ) := by
    ext i j
    exact stinespring_schrodinger_representation K X i j
  rw [hrep, hU]
  congr 1
  simp only [freshEnvironmentInput, singleKrausMap_apply,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Channel form of the dilation identity, suitable for tensoring with an arbitrary
reference and for deferring the environment trace through later operations. -/
theorem exists_freshEnvironment_unitary_map
    (K : Fin r → Matrix α α ℂ) (hK : ∑ j, (K j)ᴴ * K j = 1) (a : Fin r) :
    ∃ U : Matrix.unitaryGroup (α × Fin r) ℂ,
      partialTraceRightLM ∘ₗ singleKrausMap (U : Matrix (α × Fin r) (α × Fin r) ℂ) ∘ₗ
        freshEnvironmentInput a = rectangularKrausMap K := by
  obtain ⟨U, hU⟩ := exists_freshEnvironment_unitary K hK a
  refine ⟨U, LinearMap.ext fun X => ?_⟩
  exact (hU X).symm

/-- Choose the environment from the Choi-rank bound instead of the size of a supplied
Kraus representation. The retained system remains the first factor. -/
theorem exists_bounded_freshEnvironment_unitary {D R : ℕ}
    (Φ : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)) (hΦ : IsKrausCPTP Φ)
    (hR : D * D ≤ R) (a : Fin R) :
    ∃ U : Matrix.unitaryGroup (Fin D × Fin R) ℂ,
      partialTraceRightLM ∘ₗ
        singleKrausMap (U : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) ∘ₗ
        freshEnvironmentInput a = Φ := by
  obtain ⟨V, hV, hΦV⟩ :=
    ChoiRectangular.exists_stinespringV_schrodinger_of_isKrausCPTP hΦ
      ((ChoiRectangular.choiRank_le_mul Φ).trans hR)
  let E := fixedEnvEmbedding (S := Fin D) a
  obtain ⟨U, hU⟩ := exists_unitary_mul_fixedEnvEmbedding_eq a V hV
  refine ⟨U, LinearMap.ext fun X => ?_⟩
  rw [hΦV X, hU]
  change partialTraceRight
    ((U : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) * (E * X * Eᴴ) * Uᴴ) =
    partialTraceRight (((U : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) * E) * X *
      ((U : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) * E)ᴴ)
  congr 1
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Product relabeling preserves the literal fresh-basis initialization. -/
theorem freshEnvironmentInput_reindex {β η θ : Type*}
    [Fintype β] [DecidableEq β] [Fintype η] [DecidableEq η]
    [Fintype θ] [DecidableEq θ] (e : α ≃ β) (f : η ≃ θ)
    (a : η) (X : Matrix α α ℂ) :
    Matrix.reindex (e.prodCongr f) (e.prodCongr f) (freshEnvironmentInput a X) =
      freshEnvironmentInput (f a) (Matrix.reindex e e X) := by
  rw [freshEnvironmentInput_eq_kronecker, freshEnvironmentInput_eq_kronecker,
    ← Matrix.kroneckerMap_reindex]
  congr 1
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.single,
    Equiv.eq_symm_apply]

/-- The Choi-bounded dilation works on any explicitly enumerated local system and
any environment of the chosen size. This includes qudit-word environments initialized
in their all-zero word. -/
theorem exists_freshEnvironment_unitary_of_equiv {η : Type*}
    [Fintype η] [DecidableEq η] {D R : ℕ} (e : α ≃ Fin D) (f : η ≃ Fin R)
    (Φ : Module.End ℂ (Matrix α α ℂ)) (hΦ : IsKrausCPTP Φ)
    (hR : D * D ≤ R) (a : η) :
    ∃ U : Matrix.unitaryGroup (α × η) ℂ,
      ∀ X : Matrix α α ℂ,
        Φ X = partialTraceRight
          ((U : Matrix (α × η) (α × η) ℂ) * freshEnvironmentInput a X * Uᴴ) := by
  let Φ' := equivReindexMap e ∘ₗ Φ ∘ₗ equivReindexMap e.symm
  have hΦ' : IsKrausCPTP Φ' := isKrausCPTP_comp
    (isKrausCPTP_comp (equivReindexMap_isKrausCPTP e.symm) hΦ)
    (equivReindexMap_isKrausCPTP e)
  obtain ⟨U, hU⟩ := exists_bounded_freshEnvironment_unitary Φ' hΦ' hR (f a)
  let Rα := Matrix.reindexAlgEquiv ℂ ℂ e.symm
  let Rp := Matrix.reindexAlgEquiv ℂ ℂ (e.prodCongr f).symm
  let V : Matrix.unitaryGroup (α × η) ℂ :=
    ⟨Rp U, Matrix.reindex_mem_unitaryGroup (e.prodCongr f).symm U U.property⟩
  refine ⟨V, fun X => ?_⟩
  have heq := congrArg (fun F => F (equivReindexMap e X)) hU
  have hinit : Rp (freshEnvironmentInput (f a) (equivReindexMap e X)) =
      freshEnvironmentInput a X := by
    have h := freshEnvironmentInput_reindex e f a X
    exact congrArg Rp h.symm |>.trans (Rp.apply_symm_apply _)
  have hback : Rα (Φ' (equivReindexMap e X)) = Φ X := by
    simp [Φ', Rα, equivReindexMap, Matrix.coe_reindexLinearEquiv,
      Matrix.reindex_apply]
  rw [← hback, ← heq]
  change Rα (partialTraceRight
    ((U : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) *
      freshEnvironmentInput (f a) (equivReindexMap e X) * Uᴴ)) = _
  have htrace (Y : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
      Rα (partialTraceRight Y) = partialTraceRight (Rp Y) :=
    (partialTraceRight_submatrix_prod_equiv e.symm f.symm Y).symm
  rw [htrace]
  have hstar (A : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
      Rp Aᴴ = (Rp A)ᴴ := rfl
  simp only [map_mul, hstar, hinit]
  rfl

/-- Dilation equality persists after tensoring with any external reference. -/
theorem freshEnvironment_dilation_reference {δ η : Type*} [Fintype η] [DecidableEq η]
    (Φ : Module.End ℂ (Matrix α α ℂ)) (a : η)
    (U : Matrix.unitaryGroup (α × η) ℂ)
    (hU : partialTraceRightLM ∘ₗ
      singleKrausMap (U : Matrix (α × η) (α × η) ℂ) ∘ₗ
      freshEnvironmentInput a = Φ) :
    tensorMapIdLM (δ := δ) partialTraceRightLM ∘ₗ
      tensorMapIdLM (singleKrausMap (U : Matrix (α × η) (α × η) ℂ)) ∘ₗ
      tensorMapIdLM (freshEnvironmentInput a) = tensorMapIdLM Φ := by
  rw [← tensorMapIdLM_comp, ← tensorMapIdLM_comp, hU]

end

end Matrix
