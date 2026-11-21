/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausFamilyProd

/-!
# Ancillas in mixed states, and classical feedforward after an instrument

Attaching an ancilla `ℂ^γ` in the state `τ = ∑ₖ wₖ wₖᴴ` is the Kraus family of the operators
`|x⟩ ↦ |x⟩ ⊗ wₖ` (`KrausFamily.attach`); its map is `ρ ↦ ρ ⊗ τ`, it is trace-preserving when
`∑ₖ ‖wₖ‖² = 1`, and discarding the ancilla afterwards by the partial trace gives back `ρ`.
Attaching a basis vector is the case of one vector `wₖ = |c⟩`.

A Kraus family `K` read as an instrument records the index `i` of the operator `Kᵢ` that
occurred. Applying afterwards a channel `Sᵢ` chosen by the outcome, and forgetting the outcome,
gives the map `ρ ↦ ∑ᵢ Sᵢ(Kᵢ ρ Kᵢᴴ)`, the sum of the unnormalized branches. It is a channel
whenever `K` is trace-preserving and every `Sᵢ` is a channel; no division by the outcome
probabilities is needed. When the continuation ignores the outcome, the map is `S ∘ K`.

## Main definitions

* `KrausFamily.ancillaState` — the state `∑ₖ wₖ wₖᴴ` of an ancilla given by vectors `wₖ`.
* `KrausFamily.attach` — attaching an ancilla in the state `∑ₖ wₖ wₖᴴ`.

## Main results

* `KrausFamily.map_attach`, `KrausFamily.isTP_attach`,
  `KrausFamily.map_traceRight_map_attach` — the map of an attachment, its normalization, and
  the discard after an attachment.
* `KrausFamily.IsTP.isKrausCPTP_sum_comp` — classical feedforward after an instrument gives a
  channel.
* `KrausFamily.sum_comp_singleKrausMap_const` — a continuation that ignores the outcome.

The declarations restate the ancilla attachment of `TNLean/Circuit/Channel/Conversion.lean`
(`OnsiteChannel.attach`, `attach_siteMap_apply`, `discard_siteMap_attach_siteMap`) and the
feedforward of `TNLean/Circuit/Channel/Feedforward.lean` (`feedforwardMap_isKrausCPTP`,
`feedforwardMap_const`) at commit `414a18fb882d1b8c41c8d28d4b0c66d0d6ef2a2e` (Apache-2.0).
The changes: one site with any finite bases instead of the product over a chain with the pair
`(x, b)` encoded in `Fin (d * a)`; the instrument is any trace-preserving Kraus family.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, main text, paragraph "Quantum circuits and
  LOCC" (ancillas initialized in a product state, and later operations conditioned on earlier
  measurement outcomes), and paragraph "Phases of matter" (ancillas traced out at the end).
-/

open Matrix
open scoped Kronecker

namespace KrausFamily

/-! ### Attaching an ancilla -/

section Attach

variable {α γ ι : Type} [Fintype ι]

/-- The state `τ = ∑ₖ wₖ wₖᴴ` of an ancilla given by the vectors `wₖ`. -/
def ancillaState (w : ι → γ → ℂ) : Matrix γ γ ℂ :=
  ∑ k, vecMulVec (w k) (star (w k))

/-- Attaching an ancilla `ℂ^γ` in the state `∑ₖ wₖ wₖᴴ`: the operators `|x⟩ ↦ |x⟩ ⊗ wₖ`.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (ancillas
"initialized in a product state" at each site), here in a mixed state. -/
def attach (α : Type) [DecidableEq α] (w : ι → γ → ℂ) : KrausFamily α (α × γ) :=
  ⟨ι, fun k ↦ Matrix.of fun p x ↦ if p.1 = x then w k p.2 else 0⟩

variable [DecidableEq α]

@[simp] theorem attach_op_apply (w : ι → γ → ℂ) (k : (attach α w).Index) (p : α × γ) (x : α) :
    (attach α w).op k p x = if p.1 = x then w k p.2 else 0 :=
  rfl

variable [Fintype α]

/-- Attaching an ancilla maps `ρ` to `ρ ⊗ τ` with `τ = ∑ₖ wₖ wₖᴴ`. -/
theorem map_attach (w : ι → γ → ℂ) (ρ : Matrix α α ℂ) :
    (attach α w).map ρ = ρ ⊗ₖ ancillaState w := by
  ext ⟨x, a⟩ ⟨y, b⟩
  simp only [map_apply, Matrix.sum_apply, mul_apply, conjTranspose_apply, attach_op_apply,
    kroneckerMap_apply, ancillaState, vecMulVec_apply, Pi.star_apply, apply_ite star,
    star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  ring

variable [Fintype γ]

/-- Each operator of an attachment satisfies `KₖᴴKₖ = ‖wₖ‖² • 1`. -/
theorem conjTranspose_attach_op_mul (w : ι → γ → ℂ) (k : (attach α w).Index) :
    ((attach α w).op k)ᴴ * (attach α w).op k = (star (w k) ⬝ᵥ w k) • (1 : Matrix α α ℂ) := by
  ext x y
  simp only [mul_apply, conjTranspose_apply, attach_op_apply, Fintype.sum_prod_type,
    apply_ite star, star_zero, ite_mul, zero_mul, mul_ite, mul_zero, Matrix.smul_apply,
    one_apply, smul_eq_mul, dotProduct, Pi.star_apply]
  by_cases h : x = y
  · subst h
    rw [Finset.sum_eq_single x (fun a _ ha ↦ by simp [ha]) (by simp)]
    simp
  · simp only [h, ite_false]
    exact Finset.sum_eq_zero fun a _ ↦ Finset.sum_eq_zero fun c _ ↦ by
      split_ifs with h₁ h₂ <;> simp_all

/-- The effect of an attachment is `(∑ₖ ‖wₖ‖²) • 1`. -/
theorem effect_attach (w : ι → γ → ℂ) :
    (attach α w).effect = (∑ k, star (w k) ⬝ᵥ w k) • (1 : Matrix α α ℂ) := by
  rw [effect, Finset.sum_smul]
  exact Finset.sum_congr rfl fun k _ ↦ conjTranspose_attach_op_mul w k

/-- An attachment is trace-preserving when `∑ₖ ‖wₖ‖² = 1`. -/
theorem isTP_attach {w : ι → γ → ℂ} (hw : ∑ k, star (w k) ⬝ᵥ w k = 1) :
    (attach α w).IsTP := by
  rw [isTP_iff_effect_eq_one, effect_attach, hw, one_smul]

/-- The trace of the ancilla state is `∑ₖ ‖wₖ‖²`. -/
theorem trace_ancillaState (w : ι → γ → ℂ) :
    (ancillaState w).trace = ∑ k, star (w k) ⬝ᵥ w k := by
  simp only [ancillaState, trace_sum, trace_vecMulVec, dotProduct, Pi.star_apply]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun a _ ↦ mul_comm _ _

/-- Discarding an attached ancilla gives back the input: `tr_γ (ρ ⊗ τ) = ρ` for a state `τ`.

Source: arXiv:2103.13367, main text, paragraph "Phases of matter" (protocols "where ancillas
are traced out at the end"). -/
theorem map_traceRight_map_attach {w : ι → γ → ℂ} (hw : ∑ k, star (w k) ⬝ᵥ w k = 1)
    [DecidableEq γ] (ρ : Matrix α α ℂ) : (traceRight α γ).map ((attach α w).map ρ) = ρ := by
  rw [map_traceRight, map_attach, partialTraceRight_kronecker, trace_ancillaState, hw, one_smul]

end Attach

/-! ### Classical feedforward -/

section Feedforward

variable {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ]
  [DecidableEq γ]

/-- **Classical feedforward after an instrument.** For a trace-preserving Kraus family `K`,
read as an instrument with outcome `i`, and channels `Sᵢ` chosen by the outcome, the map
`ρ ↦ ∑ᵢ Sᵢ(Kᵢ ρ Kᵢᴴ)` is a channel. Its Kraus operators are the products `Aᵢⱼ Kᵢ` with `Aᵢⱼ`
Kraus operators of `Sᵢ`.

Source: arXiv:2103.13367, main text, paragraphs "Quantum circuits and LOCC" and "State
transformations with QC and LOCC" (later operations conditioned on earlier measurement
outcomes). -/
theorem IsTP.isKrausCPTP_sum_comp {K : KrausFamily α β} (hK : K.IsTP)
    {S : K.Index → Matrix β β ℂ →ₗ[ℂ] Matrix γ γ ℂ} (hS : ∀ i, IsKrausCPTP (S i)) :
    IsKrausCPTP (∑ i, S i ∘ₗ singleKrausMap (K.op i)) := by
  choose r A hA hnorm using hS
  let B (p : Σ i : K.Index, Fin (r i)) : Matrix γ α ℂ := A p.1 p.2 * K.op p.1
  have hmap : ∑ i, S i ∘ₗ singleKrausMap (K.op i) = rectangularKrausMap B := by
    refine LinearMap.ext fun ρ ↦ ?_
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, singleKrausMap_apply]
    change ∑ i, S i (K.op i * ρ * (K.op i)ᴴ) = ∑ p, B p * ρ * (B p)ᴴ
    simp only [hA, Fintype.sum_sigma, B, conjTranspose_mul, Matrix.mul_assoc]
  rw [hmap]
  refine rectangularKrausMap_isKrausCPTP B ?_
  calc ∑ p, (B p)ᴴ * B p = ∑ i, (K.op i)ᴴ * (∑ j, (A i j)ᴴ * A i j) * K.op i := by
        simp only [B, Fintype.sum_sigma, conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul,
          Matrix.mul_assoc]
    _ = 1 := by simp only [hnorm, Matrix.mul_one]; exact hK

omit [DecidableEq α] [DecidableEq β] [Fintype γ] [DecidableEq γ] in
/-- When the continuation ignores the outcome, feedforward after the instrument `K` is the
composition `S ∘ K`. -/
theorem sum_comp_singleKrausMap_const (K : KrausFamily α β)
    (S : Matrix β β ℂ →ₗ[ℂ] Matrix γ γ ℂ) :
    ∑ i, S ∘ₗ singleKrausMap (K.op i) = S ∘ₗ K.map := by
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.sum_apply, LinearMap.comp_apply, singleKrausMap_apply, map_apply,
    map_sum]

end Feedforward

end KrausFamily
