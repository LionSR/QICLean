/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Unitary.MatrixGramUnitary
import QICLean.Channel.KrausMap.KrausFamilyEncoding
import QICLean.Channel.KrausMap.KrausFamilyProd
import QICLean.Channel.Dilation.Stinespring

/-!
# The unitary dilation of a trace-preserving Kraus family

A trace-preserving finite Kraus family `K` from `α` to `β` is a unitary channel on an enlarged
system followed by a partial trace: with the environments `E = β × K.Index` on the input and
`F = α × K.Index` on the output, there are a basis vector `e₀` of `E` and a unitary `U` from
`α × E` to `β × F` with `K(ρ) = tr_F (U (ρ ⊗ |e₀⟩⟨e₀|) Uᴴ)`. The two enlarged systems have the
same dimension `|α| |β| |K.Index|`, and the environments are given by the family itself.

This is the Stinespring construction used in the proof of Wolf, *Quantum Channels &
Operations*, Thm. 2.5, not that theorem's statement: Wolf's theorem fixes an environment of
dimension `d (d')²`, independent of the Kraus representation, at the price of a general normalized
vector instead of a basis vector (`Channel.IsKrausCPTP.exists_openSystem_unitary`). Here the
environment depends on the family and its initial state is a basis vector, which is what a
circuit of local gates needs; `Matrix.exists_rectangular_unitary_dilation` is the same
construction for a channel on `Fin`-indexed spaces with an unspecified Kraus rank.

The construction: for a basis vector `a₀` of `α`, the Stinespring isometry
`V : |a⟩ ↦ ∑ᵢ Kᵢ|a⟩ ⊗ |i⟩` followed by the inclusion `|i⟩ ↦ |a₀, i⟩` is an isometry `W` from
`α` to `β × F`, because `K` is trace-preserving, and `tr_F (W ρ Wᴴ) = K(ρ)`. It is extended
from the inclusion `a ↦ (a, e₀)` to a unitary.

## Main results

* `KrausFamily.IsTP.exists_unitary_dilation` — the unitary dilation.
-/

open Matrix
open scoped Kronecker

namespace KrausFamily

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A trace-preserving Kraus family on a nonempty basis is a unitary family on the system and
the environment `β × K.Index`, started in a basis vector `e₀` of the environment, followed by
the partial trace over the environment `α × K.Index` (the construction in the proof of Wolf,
Thm. 2.5). The basis vector `a₀` of `α` that the construction needs comes from `[Nonempty α]`,
which also makes the environment nonempty. -/
theorem IsTP.exists_unitary_dilation [Nonempty α] {K : KrausFamily α β} [DecidableEq K.Index]
    (hK : K.IsTP) :
    ∃ (e₀ : β × K.Index) (U : KrausFamily (α × (β × K.Index)) (β × (α × K.Index))),
      U.IsUnitary ∧ K.map = (traceRight β (α × K.Index)).map ∘ₗ U.map ∘ₗ
        (embed (Function.Embedding.sectL α e₀)).map := by
  obtain ⟨i₀⟩ := hK.nonempty_index
  obtain ⟨b₀⟩ := hK.nonempty_target
  let e₀ : β × K.Index := (b₀, i₀)
  let σ : α × (β × K.Index) ≃ β × (α × K.Index) :=
    ((Equiv.prodAssoc α β K.Index).symm.trans
      ((Equiv.prodComm α β).prodCongr (Equiv.refl _))).trans (Equiv.prodAssoc β α K.Index)
  let B := basisInclusion (Function.Embedding.sectR (Classical.arbitrary α) K.Index)
  have hB : Bᴴ * B = 1 := basisInclusion_isIsometry _
  -- the Stinespring isometry, with the environment `α` in the basis vector `a₀`
  let W := ((1 : Matrix β β ℂ) ⊗ₖ B) * stinespringVGen K.op
  let J := basisInclusion ((Function.Embedding.sectL α e₀).trans σ.toEmbedding)
  have hW : Wᴴ * W = Jᴴ * J := by
    rw [basisInclusion_isIsometry, ← isTP_iff_effect_eq_one.mp hK,
      ← stinespringVGen_conjTranspose_mul]
    simp only [W, conjTranspose_mul, conjTranspose_kronecker, conjTranspose_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (1 ⊗ₖ Bᴴ), ← mul_kronecker_mul, Matrix.one_mul, hB, one_kronecker_one,
      Matrix.one_mul]
  obtain ⟨U₀, hU₀⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq W J hW
  let U := Matrix.reindex (Equiv.refl _) σ.symm U₀.1
  let ι := basisInclusion (Function.Embedding.sectL α e₀)
  have hUJ : U * ι = W := by
    rw [hU₀]
    ext q a
    simp only [U, J, ι, mul_basisInclusion_apply]
    rfl
  refine ⟨e₀, single U, ⟨⟨inferInstanceAs (Unique Unit)⟩, fun _ ↦ IsUnitaryBetween.reindex _
    ⟨mem_unitaryGroup_iff'.mp U₀.2, mem_unitaryGroup_iff.mp U₀.2⟩ _ _⟩, LinearMap.ext fun ρ ↦ ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, map_embed_apply, map_single, map_traceRight,
    show U * (ι * ρ * ιᴴ) * Uᴴ = W * ρ * Wᴴ by
      rw [← hUJ, conjTranspose_mul]; simp only [Matrix.mul_assoc],
    show W * ρ * Wᴴ = (1 ⊗ₖ B) * (stinespringVGen K.op * ρ * (stinespringVGen K.op)ᴴ) *
      (1 ⊗ₖ B)ᴴ by simp only [W, conjTranspose_mul, Matrix.mul_assoc],
    partialTraceRight_kronecker_conj_of_right_isometry _ _ hB, Matrix.one_mul, conjTranspose_one,
    Matrix.mul_one, map_eq_partialTraceRight]

end KrausFamily
