/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.MatrixFramePerturbation
import QICLean.Circuit.Gate.UniformPostselection
import QICLean.Circuit.Model.Unitary

/-!
# Reflections about implemented images, and conversion of encoders

If a unitary `U` implements an isometry on an initialized subspace, the reflection about its
image is the conjugate by `U` of the reflection about the initialized subspace. As products of
gates on any geometry, the reflection about the image therefore costs twice the gates of `U`
plus those of the initialized reflection, and one round of the two-reflection amplification,
whose global phase `-1` is a one-site phase and costs nothing, costs the gates of its two
reflections. Source: Section 5 of TNLean `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

Two unitary circuits applied to a common seed `J` give one circuit converting their approximate
encoders `F ≈ U_A J` and `G ≈ U_B J`, with operator-norm error the sum of the two encoding errors
(Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, discussion and outlook). The seed is an
algebraic intermediary: no preparation of it is asserted. With a finite external reference the
same error bound holds by `Matrix.norm_encoder_conversion_reference_le`.

The declarations restate those of `TNLean/Circuit/ImageReflectionCircuit.lean` and
`TNLean/Circuit/CoherentEncoder.lean` at commit `414a18fb88` (Apache-2.0). The changes: products
of neighbouring-pair gates and local circuits on the ring become products of gates and unitary
circuits on any geometry; the global phase of the amplification round is a one-site unitary of
cost `0` on a nonempty set of sites, instead of `2 n` neighbouring-pair gates.

## Main results

* `Matrix.subspaceReflection_image` — conjugating a subspace reflection by a unitary.
* `QuantumCircuit.IsGateProduct.subspaceReflection_image` — `2 K + L` gates.
* `QuantumCircuit.IsGateProduct.postselectionAmplificationStep` — `K + L` gates.
* `QuantumCircuit.IsUnitaryCircuit.norm_encoder_conversion_le` — conversion of encoders.
-/

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- **Reflection about a transported image.** Conjugation by a unitary `U` carries the
reflection about the image of `E` to the reflection about the image of `U E`.

Source: the image reflection of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem subspaceReflection_image (U : Matrix n n ℂ) (E : Matrix n m ℂ)
    (hU : U ∈ unitaryGroup n ℂ) :
    subspaceReflection ((U * E) * (U * E)ᴴ) = U * subspaceReflection (E * Eᴴ) * Uᴴ := by
  have hu : U * Uᴴ = 1 := mem_unitaryGroup_iff.mp hU
  simp only [subspaceReflection, conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hu, Matrix.mul_assoc]

end Matrix

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S} {X : S → Type}
  [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

namespace IsGateProduct

variable {K L : ℕ}

/-- **Reflection about an implemented image.** If `U` is a product of `K` gates and the
reflection about the image of `E` a product of `L` gates, the reflection about the image of
`U E` is a product of `2 K + L` gates: `U`, the reflection, and the adjoint of `U`.

Source: the image reflection of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem subspaceReflection_image {m : Type*} [Fintype m] (E : Matrix (Config X) m ℂ)
    {U : Matrix (Config X) (Config X) ℂ} (hU : IsGateProduct Γ K U)
    (hR : IsGateProduct Γ L (subspaceReflection (E * Eᴴ))) :
    IsGateProduct Γ (2 * K + L) (subspaceReflection ((U * E) * (U * E)ᴴ)) := by
  rw [Matrix.subspaceReflection_image U E hU.mem_unitaryGroup]
  exact ((hU.mul hR).mul hU.conjTranspose).mono (by omega)

/-- **One amplification round.** On a nonempty set of sites, if the reflections about the image
of `V` and about `P` are products of `K` and `L` gates, one round of the two-reflection
amplification, with its global phase `-1`, is a product of `K + L` gates.

Source: the amplification with exact phase of Section 5 of TNLean
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem postselectionAmplificationStep [Nonempty S] {m : Type*} [Fintype m]
    (V : Matrix (Config X) m ℂ) (P : Matrix (Config X) (Config X) ℂ)
    (hV : IsGateProduct Γ K (subspaceReflection (V * Vᴴ)))
    (hP : IsGateProduct Γ L (subspaceReflection P)) :
    IsGateProduct Γ (K + L) (postselectionAmplificationStep V P) := by
  have h := (smul_one (Γ := Γ) (X := X) (μ := -1) (by simp) 0).mul (hV.mul hP)
  rwa [neg_one_smul, neg_mul, Matrix.one_mul, zero_add] at h

end IsGateProduct

/-- **Conversion of encoders through a common seed.** If `U_A` and `U_B` are unitary circuits of
depths `T_A` and `T_B`, then `U_B U_Aᴴ` is a unitary circuit of depth `T_A + T_B` converting `F`
into `G` with operator-norm error at most `‖F - U_A J‖ + ‖G - U_B J‖`, for any seed `J`. It acts
on all logical amplitudes at once.

Source: Malz, Styliaris, Wei, and Cirac, arXiv:2307.01696, discussion and outlook; the
operator-norm form is formalization-side. -/
theorem IsUnitaryCircuit.norm_encoder_conversion_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {UA UB : Matrix (Config X) (Config X) ℂ} {TA TB : ℕ} (hUA : IsUnitaryCircuit Γ TA UA)
    (hUB : IsUnitaryCircuit Γ TB UB) (F G J : Matrix (Config X) ι ℂ) :
    IsUnitaryCircuit Γ (TA + TB) (UB * UAᴴ) ∧
      ‖UB * UAᴴ * F - G‖ ≤ ‖F - UA * J‖ + ‖G - UB * J‖ := by
  have hU : IsUnitaryCircuit Γ (TA + TB) (UB * UAᴴ) := add_comm TB TA ▸ hUB.mul hUA.conjTranspose
  refine ⟨hU, ?_⟩
  have hcancel : (UB * UAᴴ) * (UA * J) = UB * J := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc UAᴴ,
      show UAᴴ * UA = 1 from mem_unitaryGroup_iff'.mp hUA.mem_unitaryGroup, Matrix.one_mul]
  have heq : UB * UAᴴ * F - G = (UB * UAᴴ) * (F - UA * J) + (UB * J - G) := by
    rw [Matrix.mul_sub, hcancel]
    abel
  rw [heq]
  calc
    _ ≤ ‖(UB * UAᴴ) * (F - UA * J)‖ + ‖UB * J - G‖ := norm_add_le _ _
    _ ≤ ‖UB * UAᴴ‖ * ‖F - UA * J‖ + ‖UB * J - G‖ := add_le_add (Matrix.l2_opNorm_mul _ _) le_rfl
    _ ≤ _ := add_le_add (mul_le_of_le_one_left (norm_nonneg _)
      (l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
        (mem_unitaryGroup_iff'.mp hU.mem_unitaryGroup))) (norm_sub_rev (UB * J) G).le

end QuantumCircuit
