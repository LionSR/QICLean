/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Kraus.BlockingTransfer
import QICLean.Kraus.PrimitiveFixedPoint.FromPeripheral
import QICLean.Kraus.PrimitiveFixedPoint.Irreducible
import QICLean.Channel.Peripheral.Irreducible.IrreducibleChannel

/-!
# Primitive fixed points under blocking and relabelling

Blocking a finite family $A = (A_i)_{i}$ at length $L$ replaces its transfer map $E_A$ by
$E_A^L$; relabelling the index set by a bijection changes neither the transfer map nor
trace preservation (`QICLean.Kraus.BlockingTransfer`).

This file shows that positive blocking preserves the irreducibility of a
trace-preserving primitive irreducible family, and that both
operations preserve a complementary fixed-point gap together with its distinguished fixed
point $\rho$, rather than another representative of its ray.

## Main results

* `Kraus.isIrreducibleFamily_block_of_tp_primitive_irr`,
  `Kraus.tp_primitive_irreducible_extra_blocking`: blocking a trace-preserving primitive
  irreducible family at a positive length keeps all three properties.
* `Kraus.HasComplementaryFixedPointGap.block`,
  `Kraus.HasComplementaryFixedPointGap.reindexPhysical`: a complementary fixed-point gap
  with positive-definite fixed point survives positive blocking, and any complementary
  fixed-point gap survives relabelling.

## References

* B. Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b), lines 1394--1435, and
  the grouping argument of Section 6, lines 2649--2675.
* G. De las Cuevas, J. I. Cirac, N. Schuch, D. Pérez-García, arXiv:1708.00029,
  Lemma lem:blocking-arbitrary, lines 434--451.
* J. I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, arXiv:1606.00608, Section 2.3
  and Appendix A.
-/

open scoped Matrix Matrix.Norms.Operator ComplexOrder BigOperators
open Matrix

namespace Kraus

section PrimitiveBlocking

variable {ι : Type*} [Fintype ι] {D : ℕ} [NeZero D]

/-- Blocking a trace-preserving family with primitive transfer map that is irreducible
gives an irreducible family at every positive length `P`.

The positive-definite fixed point `ρ` of the transfer map `E` of `A` is fixed by `E ^ P`,
the transfer map of the blocked family. A fixed point `σ` of `E ^ P` differs from
`(tr σ / tr ρ) ρ` by a traceless matrix `σ'` fixed by `(E - P_ρ) ^ (P k)` for every `k`,
since `E ^ n = P_ρ + (E - P_ρ) ^ n` for `n ≥ 1`. The powers of `E - P_ρ` tend to zero, so
`σ' = 0`; uniqueness of the positive-definite fixed point gives irreducibility.
Source: arXiv:1606.00608, Section 2.3 and Appendix A. -/
theorem isIrreducibleFamily_block_of_tp_primitive_irr
    (A : ι → Matrix (Fin D) (Fin D) ℂ) (hTP : IsTP A)
    (hPrim : _root_.IsPrimitive (transferMap A)) (hIrr : IsIrreducibleFamily A)
    {P : ℕ} (hP : 0 < P) :
    IsIrreducibleFamily (block A P) := by
  obtain ⟨ρ, hρ⟩ :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hIrr hTP hPrim
  have hPD : ρ.PosDef := hρ.posDef_of_isIrreducibleFamily hIrr
  have hCh : IsChannel (transferMap (block A P)) :=
    isChannel_mapLM (block A P) (hTP.block P)
  have hρ_fix_blocked : transferMap (block A P) ρ = ρ := by
    rw [transferMap_block, Module.End.pow_apply, Function.iterate_fixed hρ.fixedPoint_is_fixed]
  have huniq : ∀ σ : Matrix (Fin D) (Fin D) ℂ, σ.PosSemidef →
      transferMap (block A P) σ = σ → ∃ c : ℂ, σ = c • ρ := by
    intro σ _ hσ_fix
    rw [transferMap_block] at hσ_fix hρ_fix_blocked
    set E := transferMap A
    set Pρ := fixedPointProj (D := D) ρ hρ.trace_ne_zero
    set N := E - Pρ
    refine ⟨trace σ / trace ρ, eq_of_sub_eq_zero ?_⟩
    set σ' := σ - (trace σ / trace ρ) • ρ
    have htr : trace σ' = 0 := by
      simp [σ', Matrix.trace_sub, Matrix.trace_smul, div_mul_cancel₀ _ hρ.trace_ne_zero]
    have hEP : (E ^ P) σ' = σ' := by
      simp only [σ', map_sub, LinearMap.map_smul_of_tower, hσ_fix, hρ_fix_blocked]
    -- `σ'` is fixed by `N ^ (P * (k + 1))` for every `k`.
    have hN : ∀ k : ℕ, (N ^ (P * (k + 1))) σ' = σ' := by
      intro k
      have hdecomp : (E ^ (P * (k + 1))) σ' = Pρ σ' + (N ^ (P * (k + 1))) σ' := by
        rw [pow_eq_fixedPointProj_add_compl_pow E hρ.trace_ne_zero
          (isChannel_mapLM _ hρ.norm).tp hρ.fixedPoint_is_fixed
          (Nat.mul_pos hP k.succ_pos)]
        rfl
      have hPσ : Pρ σ' = 0 := by simp [Pρ, fixedPointProj, htr]
      have hE : (E ^ (P * (k + 1))) σ' = σ' := by
        rw [pow_mul, Module.End.pow_apply, Function.iterate_fixed hEP]
      rw [hE, hPσ, zero_add] at hdecomp
      exact hdecomp.symm
    -- The powers of `N` tend to zero, so the constant sequence `σ'` tends to zero.
    let V := Matrix (Fin D) (Fin D) ℂ
    let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
    have hN_tendsto : Filter.Tendsto (fun n => (N ^ n) σ') Filter.atTop (nhds 0) := by
      -- Evaluation at `σ'` as a continuous map; `ContinuousLinearMap.apply` would need an
      -- `IsNormableSpace` instance for `V`.
      have heval : Filter.Tendsto (fun T : V →L[ℂ] V => T σ') (nhds 0) (nhds 0) := by
        simpa using (LinearMap.toContinuousLinearMap
          ({ toFun := fun T => T σ'
             map_add' := fun _ _ => rfl
             map_smul' := fun _ _ => rfl } : (V →L[ℂ] V) →ₗ[ℂ] V)).continuous.tendsto 0
      refine (heval.comp hρ.complement_pow_tendsto_zero).congr fun m => ?_
      change (Φ N ^ m) σ' = (N ^ m) σ'
      rw [← map_pow]
      rfl
    have hsub : Filter.Tendsto (fun k : ℕ => P * (k + 1)) Filter.atTop Filter.atTop :=
      (Filter.tendsto_add_atTop_nat 1).const_mul_atTop' hP
    have hconst := hN_tendsto.comp hsub
    rw [show (fun n => (N ^ n) σ') ∘ (fun k : ℕ => P * (k + 1)) = fun _ => σ' from
      funext hN] at hconst
    exact tendsto_nhds_unique tendsto_const_nhds hconst
  exact isIrreducibleFamily_of_isIrreducibleMap_mapLM (block A P)
    (isIrreducibleMap_of_channel_posDef_fixedPoint_unique _ hCh ρ hPD hρ_fix_blocked huniq)

/-- Blocking a trace-preserving family with primitive transfer map that is irreducible
at a positive length `k` keeps all three properties: trace preservation, primitivity of
the transfer map, and irreducibility. -/
theorem tp_primitive_irreducible_extra_blocking
    (A : ι → Matrix (Fin D) (Fin D) ℂ) (hTP : IsTP A)
    (hPrim : _root_.IsPrimitive (transferMap A)) (hIrr : IsIrreducibleFamily A)
    {k : ℕ} (hk : 0 < k) :
    IsTP (block A k) ∧ _root_.IsPrimitive (transferMap (block A k)) ∧
      IsIrreducibleFamily (block A k) := by
  refine ⟨hTP.block k, ?_, isIrreducibleFamily_block_of_tp_primitive_irr A hTP hPrim hIrr hk⟩
  rw [transferMap_block]
  exact isPrimitive_pow_of_isPrimitive _ k hk hPrim

/-- Every positive blocking keeps a complementary fixed-point gap with positive-definite
fixed point, with the same fixed point `ρ`. Source: arXiv:1708.00029,
Lemma lem:blocking-arbitrary, lines 434--451, for a family of period one; Nachtergaele,
arXiv:cond-mat/9410110, Section 6, lines 2649--2675. -/
theorem HasComplementaryFixedPointGap.block {A : ι → Matrix (Fin D) (Fin D) ℂ}
    {ρ : Matrix (Fin D) (Fin D) ℂ} (hP : HasComplementaryFixedPointGap A ρ)
    (hρ : ρ.PosDef) {q : ℕ} (hq : 0 < q) :
    HasComplementaryFixedPointGap (Kraus.block A q) ρ := by
  obtain ⟨hTP, hPrim, hIrr⟩ := tp_primitive_irreducible_extra_blocking A
    hP.norm hP.isPrimitive (hP.isIrreducibleFamily_of_posDef hρ) hq
  have hFix : transferMap (Kraus.block A q) ρ = ρ := by
    rw [transferMap_block, Module.End.pow_apply,
      Function.iterate_fixed hP.fixedPoint_is_fixed]
  obtain ⟨_, hGap⟩ :=
    spectralRadius_compl_lt_one_of_primitive_fixedPoint_of_irreducible_channel
      (transferMap (Kraus.block A q)) (isChannel_mapLM _ hTP)
      (isIrreducibleMap_mapLM_of_isIrreducibleFamily _ hIrr)
      hPrim ρ hP.fixedPoint_psd hP.fixedPoint_ne_zero hFix
  exact ⟨hTP, hP.fixedPoint_ne_zero, hP.fixedPoint_psd, hFix, hGap⟩

/-- A bijective relabelling of the index set keeps a complementary fixed-point gap with
the same fixed point, since the normalization and the transfer map are unchanged.
Source: Nachtergaele, arXiv:cond-mat/9410110, equations (3.1)--(3.2b),
lines 1394--1435. -/
theorem HasComplementaryFixedPointGap.reindexPhysical {ι' : Type*} [Fintype ι']
    {A : ι → Matrix (Fin D) (Fin D) ℂ} {ρ : Matrix (Fin D) (Fin D) ℂ}
    (hP : HasComplementaryFixedPointGap A ρ) (e : ι' ≃ ι) :
    HasComplementaryFixedPointGap (Kraus.reindexPhysical e A) ρ := by
  have hMap : mapLM (Kraus.reindexPhysical e A) = mapLM A :=
    transferMap_reindexPhysical_equiv e A
  refine ⟨(isTP_reindexPhysical_iff e A).2 hP.norm,
    hP.fixedPoint_ne_zero, hP.fixedPoint_psd, ?_, ?_⟩
  · simpa only [hMap] using hP.fixedPoint_is_fixed
  · simpa only [hMap] using hP.complementary_transfer_map_gap

end PrimitiveBlocking

end Kraus
