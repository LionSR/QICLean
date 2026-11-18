/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixUnitaryBetween
import QICLean.Channel.KrausFamily

/-!
# Encoding Kraus families along embeddings of bases

An embedding `e : α ↪ α'` of bases is the isometry `J_e = Matrix.initializedBasisMatrix e`, and
the Kraus family `KrausFamily.embed e` of this one operator encodes `ℂ^α` into `ℂ^{α'}`. A
family `K` from `α` to `β` is carried to a family `K.encode e f y₀` from `α'` to `β'` with the
operators `J_f Kᵢ J_eᴴ` on the code space and `|y₀⟩⟨a| (1 - J_e J_eᴴ)` off it: the second kind
sends the part of the input outside the code to the fixed output `y₀`, so that the encoded family
is trace-preserving when `K` is. On the code the encoded operators act as `K`:
`(K.encode e f y₀).op (inl i) * J_e = J_f * K.op i`, and the others vanish there. Decoding is the
encoding of the identity family with the output embedding the identity.

## Main definitions

* `KrausFamily.embed` — the encoding along an embedding of bases.
* `KrausFamily.encode` — a family carried along embeddings of its input and output bases.
* `KrausFamily.decode` — the decoding along an embedding, with a fallback basis vector.

## Main results

* `KrausFamily.isTP_embed`, `KrausFamily.IsTP.encode`, `KrausFamily.isTP_decode` — trace
  preservation.
* `KrausFamily.encode_op_inl_mul`, `KrausFamily.encode_op_inr_mul` — the encoded operators on
  the code.
* `KrausFamily.map_encode_map_embed` — the encoded family after the encoding is the encoding
  after the family.
* `KrausFamily.map_decode_map_embed` — decoding after encoding is the identity.
-/

open Matrix

namespace KrausFamily

variable {α β α' β' : Type}

/-- The encoding along an embedding of bases: the one operator `|a⟩ ↦ |e a⟩`. -/
def embed [DecidableEq β] (e : α ↪ β) : KrausFamily α β :=
  single (initializedBasisMatrix e)

theorem isTP_embed [Fintype β] [DecidableEq α] [DecidableEq β] (e : α ↪ β) : (embed e).IsTP := by
  rw [IsTP, embed, effect_single]
  exact initializedBasisMatrix_isIsometry e

variable [Fintype α] [Fintype β] [Fintype α'] [DecidableEq α'] [DecidableEq β']

/-- The family `K` carried along embeddings `e` of its input and `f` of its output basis: the
operators `J_f Kᵢ J_eᴴ`, and `|y₀⟩⟨a| (1 - J_e J_eᴴ)` for every `a`, which send the part of the
input outside the code to the output `y₀`. -/
def encode (K : KrausFamily α β) (e : α ↪ α') (f : β ↪ β') (y₀ : β') : KrausFamily α' β' :=
  ⟨K.Index ⊕ α', Sum.elim
    (fun i ↦ initializedBasisMatrix f * K.op i * (initializedBasisMatrix e)ᴴ)
    (fun a ↦ Matrix.single y₀ a (1 : ℂ) *
      (1 - initializedBasisMatrix e * (initializedBasisMatrix e)ᴴ))⟩

/-- On the code, an encoded operator acts as the operator. -/
theorem encode_op_inl_mul (K : KrausFamily α β) (e : α ↪ α') (f : β ↪ β') (y₀ : β')
    (i : K.Index) :
    (K.encode e f y₀).op (Sum.inl i : K.Index ⊕ α') * initializedBasisMatrix e =
      initializedBasisMatrix f * K.op i := by
  classical
  change initializedBasisMatrix f * K.op i * (initializedBasisMatrix e)ᴴ *
    initializedBasisMatrix e = _
  rw [Matrix.mul_assoc, initializedBasisMatrix_isIsometry e, Matrix.mul_one]

/-- On the code, the operators sending the rest to `y₀` vanish. -/
theorem encode_op_inr_mul (K : KrausFamily α β) (e : α ↪ α') (f : β ↪ β') (y₀ : β') (a : α') :
    (K.encode e f y₀).op (Sum.inr a : K.Index ⊕ α') * initializedBasisMatrix e = 0 := by
  classical
  change Matrix.single y₀ a (1 : ℂ) *
    (1 - initializedBasisMatrix e * (initializedBasisMatrix e)ᴴ) * initializedBasisMatrix e = 0
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
    initializedBasisMatrix_isIsometry e, Matrix.mul_one, sub_self, Matrix.mul_zero]

/-- An encoded trace-preserving family is trace-preserving. -/
theorem IsTP.encode [DecidableEq α] [Fintype β'] {K : KrausFamily α β} (hK : K.IsTP) (e : α ↪ α')
    (f : β ↪ β') (y₀ : β') : (K.encode e f y₀).IsTP := by
  classical
  set J := initializedBasisMatrix e
  have hJ : Jᴴ * J = 1 := initializedBasisMatrix_isIsometry e
  have hf : (initializedBasisMatrix f)ᴴ * initializedBasisMatrix f = 1 :=
    initializedBasisMatrix_isIsometry f
  have hP : (1 - J * Jᴴ)ᴴ = 1 - J * Jᴴ := by simp
  have hPP : (1 - J * Jᴴ) * (1 - J * Jᴴ) = 1 - J * Jᴴ := by
    have : J * Jᴴ * (J * Jᴴ) = J * Jᴴ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, this, sub_self, sub_zero]
  have h1 : ∑ i, (initializedBasisMatrix f * K.op i * Jᴴ)ᴴ *
      (initializedBasisMatrix f * K.op i * Jᴴ) = J * Jᴴ := by
    have : ∀ i, (initializedBasisMatrix f * K.op i * Jᴴ)ᴴ *
        (initializedBasisMatrix f * K.op i * Jᴴ) = J * ((K.op i)ᴴ * K.op i) * Jᴴ := fun i ↦ by
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (initializedBasisMatrix f)ᴴ, hf, Matrix.one_mul]
    rw [Finset.sum_congr rfl fun i _ ↦ this i, ← Matrix.sum_mul, ← Matrix.mul_sum]
    change J * K.effect * Jᴴ = _
    rw [hK, Matrix.mul_one]
  have h2 : ∑ a : α', (Matrix.single y₀ a (1 : ℂ) * (1 - J * Jᴴ))ᴴ *
      (Matrix.single y₀ a (1 : ℂ) * (1 - J * Jᴴ)) = 1 - J * Jᴴ := by
    have : ∀ a : α', (Matrix.single y₀ a (1 : ℂ) * (1 - J * Jᴴ))ᴴ *
        (Matrix.single y₀ a (1 : ℂ) * (1 - J * Jᴴ)) =
          (1 - J * Jᴴ) * Matrix.single a a (1 : ℂ) * (1 - J * Jᴴ) := fun a ↦ by
      rw [conjTranspose_mul, hP, conjTranspose_single, star_one, Matrix.mul_assoc,
        ← Matrix.mul_assoc (Matrix.single a y₀ (1 : ℂ)), single_mul_single_same, mul_one,
        ← Matrix.mul_assoc]
    rw [Finset.sum_congr rfl fun a _ ↦ this a, ← Matrix.sum_mul, ← Matrix.mul_sum,
      (sum_single_one : ∑ a : α', Matrix.single a a (1 : ℂ) = 1), Matrix.mul_one, hPP]
  change ∑ p : K.Index ⊕ α', ((K.encode e f y₀).op p)ᴴ * (K.encode e f y₀).op p = 1
  rw [Fintype.sum_sum_type]
  change (∑ i, (initializedBasisMatrix f * K.op i * Jᴴ)ᴴ *
      (initializedBasisMatrix f * K.op i * Jᴴ)) +
    ∑ a : α', (Matrix.single y₀ a (1 : ℂ) * (1 - J * Jᴴ))ᴴ *
      (Matrix.single y₀ a (1 : ℂ) * (1 - J * Jᴴ)) = 1
  rw [h1, h2, add_sub_cancel]

/-- The encoded family after the encoding is the encoding after the family. -/
theorem map_encode_map_embed (K : KrausFamily α β) (e : α ↪ α') (f : β ↪ β') (y₀ : β')
    (ρ : Matrix α α ℂ) : (K.encode e f y₀).map ((embed e).map ρ) = (embed f).map (K.map ρ) := by
  have he : (embed e).map ρ = initializedBasisMatrix e * ρ * (initializedBasisMatrix e)ᴴ :=
    (map_apply _ _).trans (Fintype.sum_unique (ι := Unit) _)
  have hf : ∀ M : Matrix β β ℂ, (embed f).map M =
      initializedBasisMatrix f * M * (initializedBasisMatrix f)ᴴ := fun M ↦
    (map_apply _ _).trans (Fintype.sum_unique (ι := Unit) _)
  rw [he, hf, map_apply, map_apply, Matrix.mul_sum, Matrix.sum_mul]
  change ∑ p : K.Index ⊕ α', _ = _
  rw [Fintype.sum_sum_type]
  have hr : ∀ a, (K.encode e f y₀).op (Sum.inr a : K.Index ⊕ α') *
      (initializedBasisMatrix e * ρ * (initializedBasisMatrix e)ᴴ) *
        ((K.encode e f y₀).op (Sum.inr a : K.Index ⊕ α'))ᴴ = 0 := fun a ↦ by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, encode_op_inr_mul]
    simp
  rw [Finset.sum_eq_zero fun a _ ↦ hr a, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hl := K.encode_op_inl_mul e f y₀ i
  have hl' : (initializedBasisMatrix e)ᴴ * ((K.encode e f y₀).op (Sum.inl i : K.Index ⊕ α'))ᴴ =
      (K.op i)ᴴ * (initializedBasisMatrix f)ᴴ := by
    rw [← conjTranspose_mul, hl, conjTranspose_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hl, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.mul_assoc, hl']
  simp only [Matrix.mul_assoc]

end KrausFamily
