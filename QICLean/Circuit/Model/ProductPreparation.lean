/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Gate.UnitaryExtension
import QICLean.Circuit.Model.Unitary

/-!
# Preparation from a product basis vector

A vector prepared in depth `T` (`QuantumCircuit.IsPreparedInDepth`) is a unitary circuit of depth
at most `T` applied to some product vector `σ ↦ ∏ₛ vₛ(σₛ)`. When it is nonzero, the product
vector can be taken to be a fixed product basis vector `σ ↦ ∏ₛ [σₛ = x₀ₛ]`, up to a scalar, at no
cost in depth: every nonzero vector at a site is a multiple of a unitary applied to a basis
vector, and the one-site unitaries form an onsite family of depth `0`.

These facts compose the preparations of two vectors into a circuit mapping one to the other
(arXiv:2307.01696, main text before Theorem 1, on states prepared from product states).

The declarations restate `Matrix.exists_mem_unitary_eq_smul_mulVec_single_zero`,
`QuantumCircuit.exists_productVector_eq_smul_finKronecker_mulVec` and
`QuantumCircuit.IsPreparedInDepth.exists_eq_smul_mulVec_productVector_single_zero` of
`TNLean/Circuit/ProductStateCircuit.lean` at commit `414a18fb88` (Apache-2.0). The changes: any
finite basis with a chosen basis vector in place of `Fin d` with `|0⟩`; any finite set of sites
with any bases; any geometry; the one-site unitaries are an onsite family of depth `0`, so the
depth stays `T` instead of `T + 2`, and the depth-two circuit of one-site unitaries on the ring,
`isLocalCircuitOfDepth_finKronecker`, is not needed.

## Main results

* `Matrix.exists_mem_unitaryGroup_eq_smul_mulVec_single` — a nonzero vector is a multiple of a
  unitary applied to a basis vector.
* `QuantumCircuit.exists_prod_eq_smul_piKronecker_mulVec` — a nonzero product vector is a
  multiple of a product of one-site unitaries applied to a product basis vector.
* `QuantumCircuit.IsPreparedInDepth.exists_eq_smul_mulVec_prod_single` — a nonzero vector
  prepared in depth `T` is a multiple of a unitary circuit of depth at most `T` applied to a
  product basis vector.
-/

open Matrix ManyBody

namespace Matrix

/-- **A vector from a basis vector.** A nonzero vector `x` of `ℂ^ι` is a nonzero multiple of the
image of the basis vector `|i₀⟩` under a unitary. -/
theorem exists_mem_unitaryGroup_eq_smul_mulVec_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i₀ : ι) {x : ι → ℂ} (hx : x ≠ 0) :
    ∃ u ∈ unitaryGroup ι ℂ, ∃ c : ℂ, c ≠ 0 ∧ x = c • (u *ᵥ Pi.single i₀ 1) := by
  set r : ℝ := ‖WithLp.toLp 2 x‖
  have hr : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
    fun h ↦ hx (by simpa using congrArg WithLp.ofLp h))
  let V : Matrix ι Unit ℂ := of fun i _ ↦ (r : ℂ)⁻¹ * x i
  have hsum : ∑ i, star (x i) * x i = (r : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq]
    push_cast
    exact Finset.sum_congr rfl fun i _ ↦ by rw [← Complex.conj_mul']; rfl
  have hV : V.IsIsometry := by
    ext ⟨⟩ ⟨⟩
    rw [mul_apply, one_apply_eq]
    calc ∑ i, Vᴴ () i * V i () = ((r : ℂ) ^ 2)⁻¹ * ∑ i, star (x i) * x i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simp only [conjTranspose_apply, V, of_apply, star_mul', star_inv₀, Complex.star_def,
            Complex.conj_ofReal]
          ring
      _ = 1 := by rw [hsum, inv_mul_cancel₀ (pow_ne_zero 2 hr)]
  obtain ⟨U, hU, hUV⟩ := exists_mem_unitaryGroup_apply_embedding_eq hV
    ⟨fun _ ↦ i₀, fun _ _ _ ↦ rfl⟩
  refine ⟨U, hU, r, hr, funext fun i ↦ ?_⟩
  rw [mulVec_single_one, Pi.smul_apply, smul_eq_mul]
  change x i = (r : ℂ) * U i ((⟨fun _ ↦ i₀, fun _ _ _ ↦ rfl⟩ : Unit ↪ ι) ())
  rw [hUV]
  simp only [V, of_apply]
  rw [← mul_assoc, mul_inv_cancel₀ hr, one_mul]

end Matrix

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- **Product vectors from a product basis vector.** A nonzero product vector `σ ↦ ∏ₛ vₛ(σₛ)` is
a multiple of a product of one-site unitaries applied to the product basis vector
`σ ↦ ∏ₛ [σₛ = x₀ₛ]`. -/
theorem exists_prod_eq_smul_piKronecker_mulVec (x₀ : Config X) {v : (s : S) → X s → ℂ}
    (hv : (fun σ : Config X ↦ ∏ s, v s (σ s)) ≠ 0) :
    ∃ u : (s : S) → Matrix (X s) (X s) ℂ, (∀ s, u s ∈ unitaryGroup (X s) ℂ) ∧ ∃ c : ℂ,
      (fun σ : Config X ↦ ∏ s, v s (σ s)) =
        c • (piKronecker u *ᵥ fun σ ↦ ∏ s, (Pi.single (x₀ s) 1 : X s → ℂ) (σ s)) := by
  have hvs (s : S) : v s ≠ 0 := fun h ↦ hv (funext fun σ ↦
    Finset.prod_eq_zero (Finset.mem_univ s) (by simp [h]))
  choose u hu c _ hc using fun s ↦ exists_mem_unitaryGroup_eq_smul_mulVec_single (x₀ s) (hvs s)
  refine ⟨u, hu, ∏ s, c s, ?_⟩
  rw [piKronecker_mulVec_prod]
  funext σ
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun s _ ↦ by rw [hc s, Pi.smul_apply, smul_eq_mul]

/-- **Preparation from a product basis vector.** A nonzero vector prepared in depth `T` is a
multiple of a unitary circuit of depth at most `T` applied to the product basis vector
`σ ↦ ∏ₛ [σₛ = x₀ₛ]`: its product vector is a multiple of one-site unitaries applied to it, and
these form an onsite family of depth `0`.

Source: arXiv:2307.01696, main text before Theorem 1 (states prepared by depth-`T` local circuits
from product states). -/
theorem IsPreparedInDepth.exists_eq_smul_mulVec_prod_single (x₀ : Config X) {T : ℕ}
    {ψ : Config X → ℂ} (h : IsPreparedInDepth Γ T ψ) (hψ : ψ ≠ 0) :
    ∃ U, IsUnitaryCircuit Γ T U ∧ ∃ c : ℂ,
      ψ = c • (U *ᵥ fun σ ↦ ∏ s, (Pi.single (x₀ s) 1 : X s → ℂ) (σ s)) := by
  obtain ⟨U, hU, v, rfl⟩ := h
  obtain ⟨u, hu, c, hc⟩ := exists_prod_eq_smul_piKronecker_mulVec x₀
    fun h0 ↦ hψ (by rw [h0, mulVec_zero])
  exact ⟨U * piKronecker u, hU.mul (IsUnitaryCircuit.piKronecker hu 0), c,
    by rw [hc, mulVec_smul, mulVec_mulVec]⟩

end QuantumCircuit
