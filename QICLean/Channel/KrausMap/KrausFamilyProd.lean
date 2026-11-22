/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.Unitary.MatrixUnitaryBetween
import QICLean.Channel.KrausMap.KrausFamily

/-!
# Tensor products of Kraus families and the partial trace

The tensor product of finite Kraus families `K` from `α` to `β` and `L` from `α'` to `β'` is
the family of the Kronecker products `Kᵢ ⊗ Lⱼ`, from `α × α'` to `β × β'`. Its map sends
`ρ ⊗ σ` to `K(ρ) ⊗ L(σ)`, which determines it (`Matrix.linearMap_ext_kronecker`). Trace
preservation and unitarity pass to the tensor product. The family `K` acting on the left factor
only is `K.tensorRight W = K.prod (single 1)`.

The partial trace over a factor `F` is the family `traceRight β F` of the operators `1 ⊗ ⟨f|`;
its map is `partialTraceRight`.

## Main definitions

* `KrausFamily.prod` — the tensor product of two Kraus families.
* `KrausFamily.tensorRight` — a family on the left factor, the identity on the right one.
* `KrausFamily.traceRight` — the partial trace over the right factor.

## Main results

* `KrausFamily.map_prod` — `(K ⊗ L)(ρ ⊗ σ) = K(ρ) ⊗ L(σ)`.
* `KrausFamily.IsTP.prod`, `KrausFamily.IsUnitary.prod` — trace preservation and unitarity.
* `KrausFamily.map_traceRight`, `KrausFamily.isTP_traceRight` — the partial trace.
* `KrausFamily.IsTP.tensorRight`, `KrausFamily.IsUnitary.tensorRight`.
-/

open Matrix
open scoped Kronecker

namespace KrausFamily

variable {α β α' β' : Type}

/-- The tensor product of two Kraus families: the Kronecker products of their operators. -/
def prod (K : KrausFamily α β) (L : KrausFamily α' β') : KrausFamily (α × α') (β × β') :=
  ⟨K.Index × L.Index, fun i ↦ K.op i.1 ⊗ₖ L.op i.2⟩

@[simp] theorem prod_op (K : KrausFamily α β) (L : KrausFamily α' β')
    (i : (K.prod L).Index) : (K.prod L).op i = K.op i.1 ⊗ₖ L.op i.2 :=
  rfl

variable [Fintype α] [Fintype β] [Fintype α'] [Fintype β']

omit [Fintype β] [Fintype β'] in
/-- The map of a tensor product on a Kronecker product. -/
theorem map_prod (K : KrausFamily α β) (L : KrausFamily α' β') (ρ : Matrix α α ℂ)
    (σ : Matrix α' α' ℂ) : (K.prod L).map (ρ ⊗ₖ σ) = K.map ρ ⊗ₖ L.map σ := by
  ext ⟨b, b'⟩ ⟨c, c'⟩
  simp only [map_apply, prod_op, conjTranspose_kronecker, ← mul_kronecker_mul,
    Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul_sum]
  exact Fintype.sum_prod_type _

omit [Fintype α] [Fintype α'] in
theorem effect_prod (K : KrausFamily α β) (L : KrausFamily α' β') :
    (K.prod L).effect = K.effect ⊗ₖ L.effect := by
  ext ⟨b, b'⟩ ⟨c, c'⟩
  simp only [effect, prod_op, conjTranspose_kronecker, ← mul_kronecker_mul,
    Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul_sum]
  exact Fintype.sum_prod_type _

variable [DecidableEq α] [DecidableEq α']

omit [Fintype α] [Fintype α'] in
theorem IsTP.prod {K : KrausFamily α β} {L : KrausFamily α' β'} (hK : K.IsTP) (hL : L.IsTP) :
    (K.prod L).IsTP := by
  rw [isTP_iff_effect_eq_one, effect_prod, isTP_iff_effect_eq_one.mp hK,
    isTP_iff_effect_eq_one.mp hL, one_kronecker_one]

theorem IsUnitary.prod [DecidableEq β] [DecidableEq β'] {K : KrausFamily α β}
    {L : KrausFamily α' β'} (hK : K.IsUnitary) (hL : L.IsUnitary) : (K.prod L).IsUnitary := by
  obtain ⟨⟨u⟩, hK⟩ := hK
  obtain ⟨⟨v⟩, hL⟩ := hL
  refine ⟨⟨{ default := (u.default, v.default), uniq := fun i ↦ Prod.ext (u.uniq _) (v.uniq _) }⟩,
    fun i ↦ ?_⟩
  rw [prod_op, conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul,
    (hK i.1).1, (hK i.1).2, (hL i.2).1, (hL i.2).2, one_kronecker_one, one_kronecker_one]
  exact ⟨rfl, rfl⟩

/-- The family `K` on the left factor and the identity on the right factor `W`. -/
def tensorRight (K : KrausFamily α β) (W : Type) [DecidableEq W] :
    KrausFamily (α × W) (β × W) :=
  K.prod (single 1)

omit [Fintype α] [Fintype α'] in
theorem IsTP.tensorRight {K : KrausFamily α β} (hK : K.IsTP) (W : Type) [Fintype W]
    [DecidableEq W] : (K.tensorRight W).IsTP :=
  hK.prod (IsUnitary.isTP (isUnitary_single (one_mem _)))

theorem IsUnitary.tensorRight [DecidableEq β] {K : KrausFamily α β} (hK : K.IsUnitary)
    (W : Type) [Fintype W] [DecidableEq W] : (K.tensorRight W).IsUnitary :=
  hK.prod (isUnitary_single (one_mem _))

/-- The partial trace over the right factor `F`: the operators `1 ⊗ ⟨f|`, the adjoints of the
basis inclusions `b ↦ (b, f)`. -/
abbrev traceRight (β F : Type) [DecidableEq β] [Fintype F] [DecidableEq F] :
    KrausFamily (β × F) β :=
  ⟨F, fun f ↦ (basisInclusion (Function.Embedding.sectL β f))ᴴ⟩

omit [Fintype α] [Fintype β] [Fintype α'] [Fintype β'] [DecidableEq α] [DecidableEq α'] in
@[simp] theorem traceRight_op [DecidableEq β] {F : Type} [Fintype F] [DecidableEq F]
    (f : F) : (traceRight β F).op f = (basisInclusion (Function.Embedding.sectL β f))ᴴ :=
  rfl

omit [Fintype α] [Fintype α'] [DecidableEq α] [DecidableEq α'] in
theorem map_traceRight [DecidableEq β] {F : Type} [Fintype F] [DecidableEq F]
    (ρ : Matrix (β × F) (β × F) ℂ) : (traceRight β F).map ρ = partialTraceRight ρ := by
  ext b b'
  simp only [map_apply, conjTranspose_conjTranspose, Matrix.sum_apply,
    partialTraceRight_apply, mul_basisInclusion_apply,
    conjTranspose_basisInclusion_mul_apply]
  rfl

omit [Fintype α] [Fintype α'] [DecidableEq α] [DecidableEq α'] in
theorem isTP_traceRight [DecidableEq β] {F : Type} [Fintype F] [DecidableEq F] :
    (traceRight β F).IsTP := by
  rw [isTP_iff_effect_eq_one]
  ext ⟨b, g⟩ q
  rw [effect, Matrix.sum_apply, Finset.sum_eq_single (show (traceRight β F).Index from g)
    (fun f _ hf ↦ ?_) (fun h ↦ absurd (Finset.mem_univ _) h)]
  · rw [traceRight_op, conjTranspose_conjTranspose,
      show ((b, g) : β × F) = Function.Embedding.sectL β g b from rfl,
      basisInclusion_mul_apply_self]
    simp [basisInclusion, one_apply, eq_comm]
  · rw [traceRight_op, conjTranspose_conjTranspose]
    exact basisInclusion_mul_apply_of_notMem _ _ (by simpa using hf) _

end KrausFamily
