/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixGramUnitary
import QICLean.Channel.KrausFamilyEncoding
import QICLean.Channel.KrausFamilyProd

/-!
# The unitary dilation of a trace-preserving Kraus family

A trace-preserving finite Kraus family `K` from `α` to `β` is a unitary channel on an enlarged
system followed by a partial trace (Wolf, *Quantum Channels & Operations*, Thm. 2.5): with the
environments `E = β × K.Index` on the input and `F = α × K.Index` on the output, there are a
basis vector `e₀` of `E` and a unitary `U` from `α × E` to `β × F` with
`K(ρ) = tr_F (U (ρ ⊗ |e₀⟩⟨e₀|) Uᴴ)`. The two enlarged systems have the same dimension
`|α| |β| |K.Index|`, and the environments are given by the family itself, not by a bound on its
Kraus rank.

The construction: for a basis vector `a₀` of `α`, the matrix `W` with
`W (b, (a', i)) a = [a' = a₀] (Kᵢ)_{ba}` is an isometry, because `K` is trace-preserving, and
`tr_F (W ρ Wᴴ) = K(ρ)`. It is extended from the inclusion `a ↦ (a, e₀)` to a unitary.

## Main results

* `KrausFamily.IsTP.exists_unitary_dilation` — the unitary dilation.
-/

open Matrix

namespace KrausFamily

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The reordering `α × (β × I) ≃ β × (α × I)` of the two enlarged systems. -/
private def dilationEquiv (α β I : Type) : α × (β × I) ≃ β × (α × I) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun q := (q.2.1, (q.1, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- A trace-preserving Kraus family on a nonempty basis is a unitary family on the system and
the environment `β × K.Index`, started in a basis vector `e₀` of the environment, followed by
the partial trace over the environment `α × K.Index` (Wolf, Thm. 2.5). The basis vector `a₀` of
`α` that the construction needs comes from `[Nonempty α]`, which also makes the environment
nonempty. -/
theorem IsTP.exists_unitary_dilation [Nonempty α] {K : KrausFamily α β} [DecidableEq K.Index]
    (hK : K.IsTP) :
    ∃ (e₀ : β × K.Index) (U : KrausFamily (α × (β × K.Index)) (β × (α × K.Index))),
      U.IsUnitary ∧ K.map = (traceRight β (α × K.Index)).map ∘ₗ U.map ∘ₗ
        (embed ⟨fun a ↦ (a, e₀), fun _ _ h ↦ congrArg Prod.fst h⟩).map := by
  obtain ⟨i₀⟩ := hK.nonempty_index
  obtain ⟨b₀⟩ := hK.nonempty_target
  let a₀ : α := Classical.arbitrary α
  let e₀ : β × K.Index := (b₀, i₀)
  let ι : α ↪ α × (β × K.Index) := ⟨fun a ↦ (a, e₀), fun _ _ h ↦ congrArg Prod.fst h⟩
  let σ := dilationEquiv α β K.Index
  let W : Matrix (β × (α × K.Index)) α ℂ :=
    of fun q a ↦ if q.2.1 = a₀ then K.op q.2.2 q.1 a else 0
  have hW : Wᴴ * W = 1 := by
    rw [← hK]
    ext a a'
    simp [W, effect, mul_apply, Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_comm (γ := β)]
  let J : Matrix (β × (α × K.Index)) α ℂ := (initializedBasisMatrix ι).submatrix σ.symm id
  have hJ : Jᴴ * J = 1 := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv _ _ _ σ.symm, submatrix_id_id]
    exact initializedBasisMatrix_isIsometry ι
  obtain ⟨U₁, hU₀⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq W J (hW.trans hJ.symm)
  set U₀ : Matrix (β × (α × K.Index)) (β × (α × K.Index)) ℂ := U₁.1 with hU₀def
  let P : Matrix (β × (α × K.Index)) (α × (β × K.Index)) ℂ := (1 : Matrix _ _ ℂ).submatrix id σ
  have hPP : Pᴴ * P = 1 := by
    rw [conjTranspose_submatrix, conjTranspose_one,
      show (1 : Matrix (β × (α × K.Index)) _ ℂ).submatrix σ id * P =
        (1 : Matrix (β × (α × K.Index)) _ ℂ).submatrix σ (Equiv.refl _) *
          (1 : Matrix (β × (α × K.Index)) _ ℂ).submatrix (Equiv.refl _) σ from rfl,
      submatrix_mul_equiv, Matrix.one_mul, submatrix_one_equiv]
  have hPP' : P * Pᴴ = 1 := by
    rw [conjTranspose_submatrix, conjTranspose_one, submatrix_mul_equiv _ _ _ σ, Matrix.one_mul,
      submatrix_id_id]
  have hU : U₀ᴴ * U₀ = 1 := mem_unitaryGroup_iff'.mp U₁.2
  have hU' : U₀ * U₀ᴴ = 1 := mem_unitaryGroup_iff.mp U₁.2
  have hPJ : P * initializedBasisMatrix ι = J := by
    ext q a
    simp only [P, J, initializedBasisMatrix, mul_apply, submatrix_apply, id, one_apply]
    rw [Finset.sum_eq_single (σ.symm q) (fun p _ hp ↦ by
      have : q ≠ σ p := fun h ↦ hp (by rw [h, Equiv.symm_apply_apply])
      simp [this]) (by simp)]
    simp
  let V := U₀ * P
  refine ⟨e₀, single V, ⟨⟨inferInstanceAs (Unique Unit)⟩, fun _ ↦ ⟨?_, ?_⟩⟩, ?_⟩
  · simp only [single_op, V, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ P, hU,
      Matrix.one_mul, hPP]
  · simp only [single_op, V, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP',
      Matrix.one_mul, hU']
  refine LinearMap.ext fun ρ ↦ ?_
  have hVW : V * initializedBasisMatrix ι = W := by
    rw [Matrix.mul_assoc, hPJ, hU₀]
  rw [LinearMap.comp_apply, LinearMap.comp_apply, map_embed_apply, map_single, map_traceRight,
    show V * (initializedBasisMatrix ι * ρ * (initializedBasisMatrix ι)ᴴ) * Vᴴ = W * ρ * Wᴴ by
      rw [← hVW, conjTranspose_mul V (initializedBasisMatrix ι)]; simp only [Matrix.mul_assoc]]
  ext b b'
  rw [map_apply, partialTraceRight_apply, Matrix.sum_apply, Fintype.sum_prod_type,
    Finset.sum_eq_single a₀ (fun a _ ha ↦ by
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      simp [W, mul_apply, ha]) (by simp)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [W, mul_apply]

end KrausFamily
