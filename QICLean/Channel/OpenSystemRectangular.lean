/-
Copyright (c) 2026 Sirui Lu and QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import QICLean.Algebra.MatrixGramUnitary
import QICLean.Channel.StinespringRectangular

/-!
# Rectangular unitary open-system representation

This file formalizes Wolf, Chapter 2, Theorem 2.5, “Open-system
representation,” and Equation (2.14)
(`Notes/WolfNoteTexSource/ch02_representations.tex`, lines 409–429), for a channel
`T : M_d(ℂ) → M_{d'}(ℂ)`. The proof follows Wolf's construction: choose a
Stinespring dilation space of dimension `d * d'`, reindex the Stinespring
isometry into the square space `ℂ^d ⊗ ℂ^{d'} ⊗ ℂ^{d'}`, and extend it to a
unitary after fixing a normalized vector in `ℂ^{d'} ⊗ ℂ^{d'}`.
-/

open scoped Matrix BigOperators
open Matrix Finset

namespace Channel

variable {d d' : ℕ}

/-- Embed an input vector `x ∈ ℂ^d` as `x ⊗ φ`, where Wolf's fixed initial
environment vector has type `φ ∈ ℂ^{d'} ⊗ ℂ^{d'}`. -/
noncomputable def openSystemInputEmbedding
    (φ : Fin d' × Fin d' → ℂ) :
    Matrix (Fin d × (Fin d' × Fin d')) (Fin d) ℂ :=
  fun p i => if p.1 = i then φ p.2 else 0

/-- Wolf's fixed-state input `ρ ⊗ |φ⟩⟨φ|` from Equation (2.14), indexed as
`ℂ^d ⊗ (ℂ^{d'} ⊗ ℂ^{d'})`. -/
noncomputable def openSystemInput
    (φ : Fin d' × Fin d' → ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d' × Fin d')) (Fin d × (Fin d' × Fin d')) ℂ :=
  Matrix.kroneckerMap (· * ·) ρ (Matrix.vecMulVec φ (star φ))

/-- The fixed-state input is compression through `openSystemInputEmbedding`:
`(𝟙_d ⊗ |φ⟩) ρ (𝟙_d ⊗ ⟨φ|)`. -/
theorem openSystemInput_eq_embedding
    (φ : Fin d' × Fin d' → ℂ) (ρ : Matrix (Fin d) (Fin d) ℂ) :
    openSystemInput φ ρ =
      openSystemInputEmbedding φ * ρ * (openSystemInputEmbedding φ)ᴴ := by
  classical
  ext ⟨i, s⟩ ⟨j, t⟩
  simp only [openSystemInput, Matrix.kroneckerMap_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, RCLike.star_def, Matrix.mul_apply, openSystemInputEmbedding, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Matrix.conjTranspose_apply]
  rw [Finset.sum_eq_single j]
  · simp
    ring
  · intro x _ hx
    have hjx : j ≠ x := fun h => hx h.symm
    simp [hjx]
  · simp

/-- The environment embedding is an isometry when `φ` is normalized. -/
private theorem openSystemInputEmbedding_conjTranspose_mul_self
    (φ : Fin d' × Fin d' → ℂ)
    (hφ : ∑ x, star (φ x) * φ x = 1) :
    (openSystemInputEmbedding (d := d) φ)ᴴ *
      openSystemInputEmbedding (d := d) φ = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, openSystemInputEmbedding,
    Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  by_cases hij : i = j
  · subst j
    simpa using hφ
  · have hji : j ≠ i := Ne.symm hij
    simp [hij, hji]

/-- Reindex `ℂ^{d'} ⊗ ℂ^{d d'}` as
`ℂ^d ⊗ ℂ^{d'} ⊗ ℂ^{d'}`, identifying Wolf's `d d'`-dimensional dilation
space with the first two factors and placing the retained `d'`-dimensional
output last. -/
private def stinespringToOpenSystemEquiv (d d' : ℕ) :
    (Fin d' × Fin (d * d')) ≃ Fin d × (Fin d' × Fin d') where
  toFun p :=
    let q := finProdFinEquiv.symm p.2
    (q.1, (q.2, p.1))
  invFun p := (p.2.2, finProdFinEquiv (p.1, p.2.1))
  left_inv p := by
    rcases p with ⟨a, e⟩
    change (a, finProdFinEquiv (finProdFinEquiv.symm e)) = (a, e)
    rw [Equiv.apply_symm_apply]
  right_inv p := by
    rcases p with ⟨i, j, a⟩
    change ((finProdFinEquiv.symm (finProdFinEquiv (i, j))).1,
      ((finProdFinEquiv.symm (finProdFinEquiv (i, j))).2, a)) = (i, (j, a))
    rw [Equiv.symm_apply_apply]

/-- A rectangular Stinespring isometry, with its output reindexed into Wolf's
square three-factor open-system space. -/
private noncomputable def openSystemReindexStinespring
    (V : Matrix (Fin d' × Fin (d * d')) (Fin d) ℂ) :
    Matrix (Fin d × (Fin d' × Fin d')) (Fin d) ℂ :=
  Matrix.reindex (stinespringToOpenSystemEquiv d d') (Equiv.refl _) V

/-- Partial trace over Wolf's environment, namely the first two factors
`ℂ^d ⊗ ℂ^{d'}`, retaining the final output factor `ℂ^{d'}`. -/
noncomputable def openSystemPartialTrace
    (X : Matrix (Fin d × (Fin d' × Fin d'))
      (Fin d × (Fin d' × Fin d')) ℂ) :
    Matrix (Fin d') (Fin d') ℂ :=
  fun a b => ∑ i : Fin d, ∑ j : Fin d', X (i, (j, a)) (i, (j, b))

@[simp]
private theorem openSystemReindexStinespring_apply
    (V : Matrix (Fin d' × Fin (d * d')) (Fin d) ℂ)
    (p : Fin d × (Fin d' × Fin d')) (k : Fin d) :
    openSystemReindexStinespring V p k =
      V ((stinespringToOpenSystemEquiv d d').symm p) k := rfl

@[simp]
private theorem stinespringToOpenSystemEquiv_symm_apply
    (i : Fin d) (j a : Fin d') :
    (stinespringToOpenSystemEquiv d d').symm (i, (j, a)) =
      (a, finProdFinEquiv (i, j)) := rfl

/-- Reindexing a matrix on the Stinespring output space turns its trace over
`Fin (d * d')` into the trace over the first two open-system factors. -/
private theorem openSystemPartialTrace_reindex
    (Y : Matrix (Fin d' × Fin (d * d')) (Fin d' × Fin (d * d')) ℂ) :
    openSystemPartialTrace
        (Matrix.reindex (stinespringToOpenSystemEquiv d d')
          (stinespringToOpenSystemEquiv d d') Y) =
      Matrix.traceRight Y := by
  classical
  ext a b
  simp only [openSystemPartialTrace, Matrix.traceRight_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, stinespringToOpenSystemEquiv_symm_apply]
  simpa only [Fintype.sum_prod_type] using
    (Equiv.sum_comp finProdFinEquiv
      (fun k : Fin (d * d') => Y (a, k) (b, k)))

/-- Reindexing the Stinespring codomain turns its right partial trace into the
partial trace over the first two factors of Wolf's open-system space. -/
private theorem openSystemPartialTrace_reindexStinespring
    (V : Matrix (Fin d' × Fin (d * d')) (Fin d) ℂ)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    openSystemPartialTrace
        (openSystemReindexStinespring V * X * (openSystemReindexStinespring V)ᴴ) =
      Matrix.traceRight (V * X * Vᴴ) := by
  classical
  rw [show openSystemReindexStinespring V * X * (openSystemReindexStinespring V)ᴴ =
      Matrix.reindex (stinespringToOpenSystemEquiv d d')
        (stinespringToOpenSystemEquiv d d') (V * X * Vᴴ) by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      openSystemReindexStinespring_apply, Matrix.reindex_apply, Matrix.submatrix_apply]]
  exact openSystemPartialTrace_reindex (V * X * Vᴴ)

/-- The normalized vector used in Wolf's unitary extension: the first standard
basis vector of `ℂ^{d'} ⊗ ℂ^{d'}`. -/
private noncomputable def openSystemAncillaVector (d' : ℕ) (hd' : 0 < d') :
    Fin d' × Fin d' → ℂ :=
  fun p => if p = (⟨0, hd'⟩, ⟨0, hd'⟩) then 1 else 0

/-- `openSystemAncillaVector` is normalized. -/
private theorem openSystemAncillaVector_normalized (d' : ℕ) (hd' : 0 < d') :
    ∑ x, star (openSystemAncillaVector d' hd' x) *
      openSystemAncillaVector d' hd' x = 1 := by
  classical
  simp [openSystemAncillaVector]

/-- A rectangular CPTP map with nonzero input dimension has nonzero output
dimension. -/
theorem output_dimension_pos_of_isKrausCPTP [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCPTP T) : 0 < d' := by
  by_contra hd'
  have hd'0 : d' = 0 := Nat.eq_zero_of_not_pos hd'
  have htrace := hT.trace_map (1 : Matrix (Fin d) (Fin d) ℂ)
  have hzero : T (1 : Matrix (Fin d) (Fin d) ℂ) = 0 := by
    ext i j
    exact (Nat.not_lt_zero i.val (by simpa [hd'0] using i.isLt)).elim
  rw [hzero] at htrace
  have hdcast : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  exact hdcast (by simpa [Matrix.trace] using htrace.symm)

/-- **Wolf, Chapter 2, Theorem 2.5, “Open-system representation,” Equation
(2.14): rectangular unitary form.**

See `Notes/WolfNoteTexSource/ch02_representations.tex`, lines 409–429.

For every CPTP map `T : M_d(ℂ) → M_{d'}(ℂ)` with nonzero input dimension, there
are a unitary `U ∈ M_{d(d')^2}(ℂ)`, acting on
`ℂ^d ⊗ ℂ^{d'} ⊗ ℂ^{d'}`, and a normalized
`φ ∈ ℂ^{d'} ⊗ ℂ^{d'}` such that

`T(ρ) = tr_E[U (ρ ⊗ |φ⟩⟨φ|) Uᴴ]`,

where `tr_E` traces the first two factors, of total dimension `d * d'`, and
retains the final `d'`-dimensional output factor. -/
theorem IsKrausCPTP.exists_openSystem_unitary [NeZero d]
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ}
    (hT : IsKrausCPTP T) :
    ∃ (U : Matrix.unitaryGroup (Fin d × (Fin d' × Fin d')) ℂ)
      (φ : Fin d' × Fin d' → ℂ),
      (∑ x, star (φ x) * φ x = 1) ∧
      ∀ ρ : Matrix (Fin d) (Fin d) ℂ,
        T ρ = openSystemPartialTrace
          ((U : Matrix (Fin d × (Fin d' × Fin d'))
            (Fin d × (Fin d' × Fin d')) ℂ) *
            openSystemInput φ ρ * Uᴴ) := by
  classical
  have hd' : 0 < d' := output_dimension_pos_of_isKrausCPTP hT
  obtain ⟨V, hViso, hV⟩ :=
    ChoiRectangular.exists_stinespringV_schrodinger_of_isKrausCPTP hT
      (ChoiRectangular.choiRank_le_mul T)
  let V' := openSystemReindexStinespring V
  have hV'iso : V'ᴴ * V' = 1 := by
    ext i j
    have hentry := congr_fun (congr_fun hViso i) j
    simp only [V', Matrix.mul_apply, Matrix.conjTranspose_apply,
      openSystemReindexStinespring_apply] at hentry ⊢
    exact (Equiv.sum_comp (stinespringToOpenSystemEquiv d d').symm
      (fun q => star (V q i) * V q j)).trans hentry
  let φ := openSystemAncillaVector d' hd'
  have hφ : ∑ x, star (φ x) * φ x = 1 :=
    openSystemAncillaVector_normalized d' hd'
  let W := openSystemInputEmbedding (d := d) φ
  have hWiso : Wᴴ * W = 1 :=
    openSystemInputEmbedding_conjTranspose_mul_self φ hφ
  obtain ⟨U, hUW⟩ := Matrix.exists_unitary_mul_eq_of_conjTranspose_mul_eq
    (B := V') (A := W) (by rw [hV'iso, hWiso])
  refine ⟨U, φ, hφ, ?_⟩
  intro ρ
  rw [hV ρ, ← openSystemPartialTrace_reindexStinespring V ρ]
  congr 1
  rw [openSystemInput_eq_embedding]
  simp only [W, V', Matrix.conjTranspose_mul, Matrix.mul_assoc, hUW]

end Channel
