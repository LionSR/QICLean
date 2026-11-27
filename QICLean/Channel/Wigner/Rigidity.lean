/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Wigner.ProjectiveCarrierBridge
import QICLean.Spectral.Perturbation.HermitianSpectrumPerturbation
import QICLean.Channel.Wigner.ProjectivePureState
import QICLean.Channel.Wigner.TwoPureStateCharpoly

/-!
# Wigner rigidity for finite-coordinate rays and pure-state matrices

This module transfers the projective Wigner rigidity theorem adapted from
`zblore/csd-lean4` commit `55ac6758832291c8b0fb94d78e10dc47b1cb8a06`
to TNLean's `Fin d → ℂ` carrier and then states Wolf's Chapter 1 theorem on the
range of normalized pure-state matrices.

The conclusion is a disjunction, not an exclusive alternative. In dimension
zero the domain is empty; in dimension one it is a singleton and the two
alternatives coincide. No uniqueness of the implementing unitary is asserted.

It also contains the following results.

* `Projectivization.exists_unitary_conj_or_transpose_of_preserves_hermitian_spectrum`:
  classification of Hermitian spectrum preservers.
-/

open scoped LinearAlgebra.Projectivization Matrix

namespace Projectivization

section Rigidity

variable {d : ℕ}

/-- Wigner rigidity in TNLean's finite-coordinate projective-ray language. -/
theorem wigner_rigidity_fin
    {f : ℙ ℂ (Fin d → ℂ) → ℙ ℂ (Fin d → ℂ)}
    (hf : ∀ p q, transitionProbability (f p) (f q) =
      transitionProbability p q) :
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      ∀ p, f p = unitaryAction U p) ∨
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      ∀ p, f p = unitaryAction U (coordinateConjugation p)) := by
  let fE : ℙ ℂ (EuclideanSpace ℂ (Fin d)) →
      ℙ ℂ (EuclideanSpace ℂ (Fin d)) :=
    fun p ↦ toEuclideanRay (f (fromEuclideanRay p))
  have hfE : TransProbPreserving fE := by
    intro p q
    apply Complex.ofReal_injective
    calc
      ((transProb (fE p) (fE q) : ℝ) : ℂ) =
          transitionProbability (f (fromEuclideanRay p))
            (f (fromEuclideanRay q)) := by
              exact transProb_toEuclideanRay_ofReal_eq _ _
      _ = transitionProbability (fromEuclideanRay p) (fromEuclideanRay q) :=
        hf _ _
      _ = ((transProb p q : ℝ) : ℂ) := by
        rw [← transProb_toEuclideanRay_ofReal_eq]
        simp
  rcases wigner_rigidity_unitaryGroup hfE with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨U, fun p ↦ by
      have h := congrArg fromEuclideanRay (hU (toEuclideanRay p))
      simpa [fE, fromEuclideanRay_unitary_smul] using h⟩
  · exact Or.inr ⟨U, fun p ↦ by
      have h := congrArg fromEuclideanRay (hU (toEuclideanRay p))
      simpa [fE, fromEuclideanRay_unitary_smul,
        fromEuclideanRay_conjProj] using h⟩

/-- Normalized pure-state matrices, represented intrinsically as the range of
the projective pure-state realization. -/
noncomputable def PureStateMatrix (d : ℕ) :=
  Set.range
    (pureStateMatrix : ℙ ℂ (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ)

/-- Projective rays are equivalent to normalized pure-state matrices in their
range realization. -/
noncomputable def pureStateMatrixEquiv :
    ℙ ℂ (Fin d → ℂ) ≃ PureStateMatrix d where
  toFun p := ⟨pureStateMatrix p, p, rfl⟩
  invFun P := Classical.choose P.property
  left_inv p := pureStateMatrix_injective (Classical.choose_spec (show
    (pureStateMatrix p) ∈ Set.range
      (pureStateMatrix : ℙ ℂ (Fin d → ℂ) → Matrix (Fin d) (Fin d) ℂ) from
        ⟨p, rfl⟩))
  right_inv P := Subtype.ext (Classical.choose_spec P.property)

/-- The range equivalence sends a ray to its normalized pure-state matrix. -/
@[simp]
theorem pureStateMatrixEquiv_val (p : ℙ ℂ (Fin d → ℂ)) :
    (pureStateMatrixEquiv p).1 = pureStateMatrix p := rfl

/-- The ray corresponding to a matrix in the range realizes that matrix. -/
@[simp]
theorem pureStateMatrix_pureStateMatrixEquiv_symm (P : PureStateMatrix d) :
    pureStateMatrix (pureStateMatrixEquiv.symm P) = P.1 := by
  exact congrArg Subtype.val (pureStateMatrixEquiv.apply_symm_apply P)

/-- Wolf's matrix-facing Wigner theorem for normalized pure states.

The bijectivity hypothesis is retained exactly as in Wolf, Theorem 1.1, although
the adapted projective rigidity theorem proves the classification from
transition-probability preservation alone. -/
theorem wolf_wigner_pureStateMatrix
    (F : PureStateMatrix d → PureStateMatrix d)
    (_hbijective : Function.Bijective F)
    (htransition : ∀ P Q,
      Matrix.trace ((F P).1 * (F Q).1) = Matrix.trace (P.1 * Q.1)) :
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ P,
      (F P).1 = (U : Matrix (Fin d) (Fin d) ℂ) * P.1 *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) ∨
    (∃ U : Matrix.unitaryGroup (Fin d) ℂ, ∀ P,
      (F P).1 = (U : Matrix (Fin d) (Fin d) ℂ) * P.1ᵀ *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  let e := pureStateMatrixEquiv (d := d)
  let f : ℙ ℂ (Fin d → ℂ) → ℙ ℂ (Fin d → ℂ) := fun p ↦ e.symm (F (e p))
  have hf : ∀ p q, transitionProbability (f p) (f q) =
      transitionProbability p q := by
    intro p q
    rw [← trace_pureStateMatrix_mul_pureStateMatrix,
      ← trace_pureStateMatrix_mul_pureStateMatrix]
    simpa [f, e] using htransition (e p) (e q)
  rcases wigner_rigidity_fin hf with ⟨U, hU⟩ | ⟨U, hU⟩
  · exact Or.inl ⟨U, fun P ↦ by
      let p := e.symm P
      calc
        (F P).1 = pureStateMatrix (f p) := by simp [f, p, e]
        _ = pureStateMatrix (unitaryAction U p) := congrArg pureStateMatrix (hU p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * pureStateMatrix p *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := pureStateMatrix_unitaryAction U p
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * P.1 *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by simp [p, e]⟩
  · exact Or.inr ⟨U, fun P ↦ by
      let p := e.symm P
      calc
        (F P).1 = pureStateMatrix (f p) := by simp [f, p, e]
        _ = pureStateMatrix (unitaryAction U (coordinateConjugation p)) :=
          congrArg pureStateMatrix (hU p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) *
            pureStateMatrix (coordinateConjugation p) *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ :=
          pureStateMatrix_unitaryAction U (coordinateConjugation p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * (pureStateMatrix p)ᵀ *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
          rw [pureStateMatrix_coordinateConjugation]
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * P.1ᵀ *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by simp [p, e]⟩

end Rigidity

section SpectrumPreserver

/-!
## Classification of Hermitian spectrum preservers

A complex-linear map on square complex matrices that commutes with the adjoint and preserves the
spectrum as a set on Hermitian matrices is either unitary conjugation or unitary conjugation after
transposition. The proof identifies the images of normalized pure-state matrices, applies Wigner
rigidity to the induced map on projective rays, and extends the resulting equality by complex
linearity.

### Main declaration

* `Projectivization.exists_unitary_conj_or_transpose_of_preserves_hermitian_spectrum`
-/

variable {d : ℕ}

/-- A complex-linear adjoint-preserving map that preserves the complex spectrum as a set on every
Hermitian matrix is either unitary conjugation or unitary conjugation after transposition.

This is the corollary "Spectrum preserving maps" in Wolf, Chapter 1, lines 289--296. The
hypothesis `hstar` is Wolf's definition of a Hermitian map at line 290. -/
theorem exists_unitary_conj_or_transpose_of_preserves_hermitian_spectrum
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hstar : ∀ X : Matrix (Fin d) (Fin d) ℂ, T (Xᴴ) = (T X)ᴴ)
    (hSpectrum : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.IsHermitian → spectrum ℂ (T A) = spectrum ℂ A) :
    ∃ U : Matrix.unitaryGroup (Fin d) ℂ,
      (∀ X, T X = (U : Matrix (Fin d) (Fin d) ℂ) * X *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) ∨
      (∀ X, T X = (U : Matrix (Fin d) (Fin d) ℂ) * Xᵀ *
        (U : Matrix (Fin d) (Fin d) ℂ)ᴴ) := by
  have hHermitian : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.IsHermitian → (T A).IsHermitian := by
    intro A hA
    rw [Matrix.IsHermitian, ← hstar A, hA]
  have hcharpoly : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.IsHermitian → (T A).charpoly = A.charpoly :=
    Matrix.charpoly_map_eq_of_preserves_hermitian_spectrum T hHermitian hSpectrum
  have himage : ∀ p : ℙ ℂ (Fin d → ℂ),
      ∃ q : ℙ ℂ (Fin d → ℂ), pureStateMatrix q = T (pureStateMatrix p) := by
    intro p
    have hp : (pureStateMatrix p).IsHermitian :=
      (isOrthogonalProjection_pureStateMatrix p).1
    exact exists_pureStateMatrix_eq_of_isHermitian_charpoly_eq
      (T (pureStateMatrix p)) p (hHermitian _ hp) (hcharpoly _ hp)
  let f : ℙ ℂ (Fin d → ℂ) → ℙ ℂ (Fin d → ℂ) := fun p ↦
    Classical.choose (himage p)
  have hfimage : ∀ p, pureStateMatrix (f p) = T (pureStateMatrix p) := fun p ↦
    Classical.choose_spec (himage p)
  have hftransition : ∀ p q, transitionProbability (f p) (f q) =
      transitionProbability p q := by
    intro p q
    rw [← trace_pureStateMatrix_mul_pureStateMatrix,
      ← trace_pureStateMatrix_mul_pureStateMatrix]
    apply trace_pureStateMatrix_mul_eq_of_charpoly_add_eq
    rw [hfimage, hfimage, ← T.map_add]
    exact hcharpoly _ ((isOrthogonalProjection_pureStateMatrix p).1.add
      (isOrthogonalProjection_pureStateMatrix q).1)
  rcases wigner_rigidity_fin hftransition with ⟨U, hU⟩ | ⟨U, hU⟩
  · let S : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
      { toFun X := (U : Matrix (Fin d) (Fin d) ℂ) * X *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ
        map_add' X Y := by rw [mul_add, add_mul]
        map_smul' c X := by
          simp only [RingHom.id_apply]
          rw [mul_smul_comm, smul_mul_assoc] }
    have hTS : T = S := linearMap_eq_of_eq_on_pureStateMatrix T S fun p ↦ by
      calc
        T (pureStateMatrix p) = pureStateMatrix (f p) := (hfimage p).symm
        _ = pureStateMatrix (unitaryAction U p) := congrArg pureStateMatrix (hU p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * pureStateMatrix p *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := pureStateMatrix_unitaryAction U p
        _ = S (pureStateMatrix p) := rfl
    exact ⟨U, Or.inl (fun X ↦ by rw [hTS]; rfl)⟩
  · let S : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ :=
      { toFun X := (U : Matrix (Fin d) (Fin d) ℂ) * Xᵀ *
          (U : Matrix (Fin d) (Fin d) ℂ)ᴴ
        map_add' X Y := by rw [Matrix.transpose_add, mul_add, add_mul]
        map_smul' c X := by
          simp only [RingHom.id_apply, Matrix.transpose_smul]
          rw [mul_smul_comm, smul_mul_assoc] }
    have hTS : T = S := linearMap_eq_of_eq_on_pureStateMatrix T S fun p ↦ by
      calc
        T (pureStateMatrix p) = pureStateMatrix (f p) := (hfimage p).symm
        _ = pureStateMatrix (unitaryAction U (coordinateConjugation p)) :=
          congrArg pureStateMatrix (hU p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) *
            pureStateMatrix (coordinateConjugation p) *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ :=
          pureStateMatrix_unitaryAction U (coordinateConjugation p)
        _ = (U : Matrix (Fin d) (Fin d) ℂ) * (pureStateMatrix p)ᵀ *
            (U : Matrix (Fin d) (Fin d) ℂ)ᴴ := by
          rw [pureStateMatrix_coordinateConjugation]
        _ = S (pureStateMatrix p) := rfl
    exact ⟨U, Or.inr (fun X ↦ by rw [hTS]; rfl)⟩

end SpectrumPreserver

end Projectivization
