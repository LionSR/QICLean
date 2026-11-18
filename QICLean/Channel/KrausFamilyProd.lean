/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.RingTheory.MatrixAlgebra
import QICLean.Channel.KrausFamily

/-!
# Tensor products of Kraus families and the partial trace

The tensor product of finite Kraus families `K` from `α` to `β` and `L` from `α'` to `β'` is
the family of the Kronecker products `Kᵢ ⊗ Lⱼ`, from `α × α'` to `β × β'`. Its map sends
`ρ ⊗ σ` to `K(ρ) ⊗ L(σ)`, and a linear map on matrices of `α × α'` is determined by its values
on Kronecker products. Trace preservation and unitarity pass to the tensor product. The family
`K` acting on the left factor only is `K.tensorRight W = K.prod (single 1)`.

The partial trace over a factor `F` is the family `traceRight β F` of the operators `1 ⊗ ⟨f|`;
its map is `partialTraceRight`.

## Main definitions

* `KrausFamily.prod` — the tensor product of two Kraus families.
* `KrausFamily.tensorRight` — a family on the left factor, the identity on the right one.
* `KrausFamily.traceRight` — the partial trace over the right factor.

## Main results

* `KrausFamily.map_prod` — `(K ⊗ L)(ρ ⊗ σ) = K(ρ) ⊗ L(σ)`.
* `Matrix.linearMap_ext_kronecker` — linear maps agreeing on Kronecker products are equal.
* `KrausFamily.IsTP.prod`, `KrausFamily.IsUnitary.prod` — trace preservation and unitarity.
* `KrausFamily.map_traceRight`, `KrausFamily.isTP_traceRight` — the partial trace.
-/

open Matrix
open scoped Kronecker

namespace Matrix

/-- Two linear maps on the matrices of `α × α'` that agree on all Kronecker products are equal:
the Kronecker products span. -/
theorem linearMap_ext_kronecker {α α' M : Type} [Fintype α] [DecidableEq α] [Fintype α']
    [DecidableEq α'] [AddCommMonoid M] [Module ℂ M]
    {f g : Matrix (α × α') (α × α') ℂ →ₗ[ℂ] M} (h : ∀ x y, f (x ⊗ₖ y) = g (x ⊗ₖ y)) : f = g := by
  have : f ∘ₗ (kroneckerLinearEquiv α α α' α' ℂ).toLinearMap =
      g ∘ₗ (kroneckerLinearEquiv α α α' α' ℂ).toLinearMap :=
    TensorProduct.ext' fun x y ↦ h x y
  ext X
  simpa using LinearMap.congr_fun this ((kroneckerLinearEquiv α α α' α' ℂ).symm X)

end Matrix

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
  rw [IsTP, effect_prod, hK, hL, one_kronecker_one]

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

/-- The partial trace over the right factor `F`: the operators `1 ⊗ ⟨f|`. -/
def traceRight (β F : Type) [DecidableEq β] [Fintype F] [DecidableEq F] :
    KrausFamily (β × F) β :=
  ⟨F, fun f ↦ of fun b q ↦ if q = (b, f) then 1 else 0⟩

omit [Fintype α] [Fintype α'] [DecidableEq α] [DecidableEq α'] in
theorem map_traceRight [DecidableEq β] {F : Type} [Fintype F] [DecidableEq F]
    (ρ : Matrix (β × F) (β × F) ℂ) : (traceRight β F).map ρ = partialTraceRight ρ := by
  ext b b'
  simp only [map_apply, Matrix.sum_apply, partialTraceRight_apply]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  simp [traceRight, mul_apply]

omit [Fintype α] [Fintype α'] [DecidableEq α] [DecidableEq α'] in
theorem isTP_traceRight [DecidableEq β] {F : Type} [Fintype F] [DecidableEq F] :
    (traceRight β F).IsTP := by
  have h (f : F) (q q' : β × F) :
      (((traceRight β F).op f)ᴴ * (traceRight β F).op f) q q' =
        if q = q' ∧ q.2 = f then 1 else 0 := by
    obtain ⟨b, g⟩ := q
    obtain ⟨b', g'⟩ := q'
    rw [mul_apply, Finset.sum_eq_single b]
    · by_cases hb : b = b' <;> by_cases hg : g = f <;> by_cases hg' : g' = f <;>
        simp [traceRight, hb, hg, hg'] <;> grind
    · intro c _ hc
      simp [traceRight, Prod.ext_iff, Ne.symm hc]
    · simp
  ext q q'
  rw [effect, Matrix.sum_apply]
  change ∑ f : F, (((traceRight β F).op f)ᴴ * (traceRight β F).op f) q q' = _
  simp only [h, one_apply]
  by_cases hq : q = q' <;> simp [hq]

end KrausFamily
