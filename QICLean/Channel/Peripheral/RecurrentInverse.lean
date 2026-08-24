/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.Peripheral.AsymptoticImage
import QICLean.Channel.Determinant.Bound
import QICLean.Channel.Schwarz.Closure
import QICLean.Channel.Schwarz.TwoPositive
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# The recurrent inverse on Wolf's asymptotic image

In the proof of Wolf Theorem 6.16, a Dirichlet subsequence satisfies
`T ^ (n i) → I`, and a further subsequence of the predecessor powers satisfies
`T ^ (n i - 1) → S`.  Wolf writes this limit as `T⁻¹`, but uses it only on the
asymptotic image `X_T`: the formal identities are

`S.comp T = T.peripheralProjection` and
`T.comp S = T.peripheralProjection`.

This file follows that construction literally.  Pointwise boundedness of the
powers is upgraded to operator-norm boundedness by Banach--Steinhaus; finite
dimensional compactness then supplies the convergent predecessor subsequence.
No global inverse and no alternative spectral inverse are introduced.

The corrected source-facing Schwarz contract is also kept explicit.  Schwarz
closure is applied separately to `T` and to `Matrix.traceAdjointMap T`; no
implication between the two orientations is asserted.

## Main results

* `IsPositiveMap.exists_strictMono_tendsto_pow_peripheralProjection_and_predecessor`:
  the shared recurrent subsequence and predecessor-power limit.
* `IsPositiveMap.exists_peripheralRestrictedInverse`: the positive,
  trace-preserving restricted inverse and its absorption/range identities.
* `IsPositiveMap.peripheralProjection_isSchwarzMap` and
  `IsPositiveMap.traceAdjointMap_peripheralProjection_isSchwarzMap`: the two
  independent Schwarz orientations for the recurrent projection.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, proof of Theorem 6.16,
  local source `Notes/WolfNoteTexSource/ch06_spectral_properties.tex`,
  lines 1626--1640.
-/

open Filter Matrix TNLean
open scoped Topology TNOperatorSpace Matrix ComplexOrder MatrixOrder

noncomputable section

/-! ## Wolf's recurrent predecessor-power limit -/

namespace IsPositiveMap

variable {D : ℕ} [NeZero D]
  {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}

/-- **Wolf Theorem 6.16, recurrent predecessor-power construction.**

For a positive trace-preserving `T`, there is one strictly increasing
subsequence `n` and a matrix endomorphism `S` such that

* `T ^ (n i) → T.peripheralProjection`, and
* `T ^ (n i - 1) → S`

in operator norm.  The first limit is the Dirichlet recurrent subsequence from
Wolf Proposition 6.3.  Banach--Steinhaus and finite-dimensional compactness
supply the predecessor limit used at local source lines 1629--1640. -/
theorem exists_strictMono_tendsto_pow_peripheralProjection_and_predecessor
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ n : ℕ → ℕ, ∃ S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ),
      StrictMono n ∧ 0 < n 0 ∧
      Tendsto (fun i : ℕ ↦ endEquiv (T ^ n i)) atTop
        (𝓝 (endEquiv T.peripheralProjection)) ∧
      Tendsto (fun i : ℕ ↦ endEquiv (T ^ (n i - 1))) atTop
        (𝓝 (endEquiv S)) := by
  obtain ⟨n, hnmono, hn0, _hnpoint, hnclm⟩ :=
    hPos.exists_strictMono_tendsto_pow_peripheralProjection_clm hTP
  let U : ℕ → MatrixCLM (Fin D) := fun i ↦ endEquiv (T ^ (n i - 1))
  have hb := hPos.hasBoundedOrbits_of_tracePreserving hTP
  have hbU : Bornology.IsBounded (Set.range U) := by
    let _ : CompleteSpace (Matrix (Fin D) (Fin D) ℂ) :=
      FiniteDimensional.complete ℂ (Matrix (Fin D) (Fin D) ℂ)
    obtain ⟨C, hC⟩ := banach_steinhaus (g := U) (fun X ↦ by
      obtain ⟨CX, hCX⟩ := isBounded_iff_forall_norm_le.mp (hb X)
      refine ⟨CX, fun i ↦ ?_⟩
      change ‖(T ^ (n i - 1)) X‖ ≤ CX
      simpa only [Module.End.coe_pow] using
        hCX (T^[n i - 1] X) ⟨n i - 1, rfl⟩)
    rw [isBounded_iff_forall_norm_le]
    exact ⟨C, fun A hA ↦ by obtain ⟨i, rfl⟩ := hA; exact hC i⟩
  let hFinite : FiniteDimensional ℂ (MatrixCLM (Fin D)) :=
    (endEquiv (D := D)).toLinearEquiv.finiteDimensional
  let hProper : ProperSpace (MatrixCLM (Fin D)) :=
    @FiniteDimensional.proper ℂ _ (MatrixCLM (Fin D)) _ _ _ hFinite
  let : ProperSpace (MatrixCLM (Fin D)) := hProper
  obtain ⟨R, hR⟩ := hbU.subset_closedBall 0
  obtain ⟨Sclm, _hSball, k, hkmono, hklim⟩ :=
    (ProperSpace.isCompact_closedBall (0 : MatrixCLM (Fin D)) R).tendsto_subseq
      (fun i ↦ hR ⟨i, rfl⟩)
  let S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    (endEquiv (D := D)).symm Sclm
  refine ⟨n ∘ k, S, hnmono.comp hkmono, ?_, ?_, ?_⟩
  · exact hn0.trans_le (hnmono.monotone (Nat.zero_le (k 0)))
  · exact hnclm.comp hkmono.tendsto_atTop
  · change Tendsto (U ∘ k) atTop (𝓝 (endEquiv S))
    have hES : endEquiv S = Sclm := by
      simp only [S, AlgEquiv.apply_symm_apply]
    rw [hES]
    exact hklim

/-- The recurrent/peripheral projection of a positive trace-preserving Schwarz
map is Schwarz.  This transports only the Schwarz hypothesis for `T` through
the recurrent powers; it makes no assertion about `Matrix.traceAdjointMap T`.

Source: Wolf Theorem 6.16 proof, local source lines 1629--1633. -/
theorem peripheralProjection_isSchwarzMap
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hSchwarz : IsSchwarzMap T) : IsSchwarzMap T.peripheralProjection := by
  obtain ⟨n, _hnmono, _hn0, _hnpoint, hnclm⟩ :=
    hPos.exists_strictMono_tendsto_pow_peripheralProjection_clm hTP
  let Mat := Matrix (Fin D) (Fin D) ℂ
  have hP (X : Mat) : Tendsto (fun i : ℕ ↦ (T ^ n i) X) atTop
      (𝓝 (T.peripheralProjection X)) :=
    ((ContinuousLinearMap.apply ℂ Mat X).continuous.tendsto
      (endEquiv T.peripheralProjection)).comp hnclm
  exact IsSchwarzMap.of_tendsto (fun i ↦ hSchwarz.pow hPos (n i)) hP

/-- Under the separate Schwarz hypothesis for `T*`, the trace-pairing adjoint
of the recurrent/peripheral projection is Schwarz.  This is the orientation
needed when Wolf applies Theorem 6.14 to the recurrent projection `I`.

The proof uses `(T ^ n)* = (T*) ^ n` and transports the operator-norm recurrent
limit through the trace-pairing adjoint.  It does not infer adjoint Schwarz
from Schwarz for `T`.

Source: Wolf Theorems 6.14 and 6.16, and the corrected contract recorded in
`docs/paper-gaps/wolf_theorem6_16_schwarz_orientation.tex`. -/
theorem traceAdjointMap_peripheralProjection_isSchwarzMap
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    (hAdjointSchwarz : IsSchwarzMap (Matrix.traceAdjointMap T)) :
    IsSchwarzMap (Matrix.traceAdjointMap T.peripheralProjection) := by
  obtain ⟨n, _hnmono, _hn0, _hnpoint, hnclm⟩ :=
    hPos.exists_strictMono_tendsto_pow_peripheralProjection_clm hTP
  let Mat := Matrix (Fin D) (Fin D) ℂ
  have hP (X : Mat) : Tendsto (fun i : ℕ ↦ (T ^ n i) X) atTop
      (𝓝 (T.peripheralProjection X)) :=
    ((ContinuousLinearMap.apply ℂ Mat X).continuous.tendsto
      (endEquiv T.peripheralProjection)).comp hnclm
  have hAdjointPos : IsPositiveMap (Matrix.traceAdjointMap T) :=
    hPos.traceAdjointMap
  exact IsSchwarzMap.of_tendsto
    (fun i ↦ by
      rw [Matrix.traceAdjointMap_pow]
      exact hAdjointSchwarz.pow hAdjointPos (n i))
    (fun X ↦ Matrix.tendsto_traceAdjointMap hP X)

private theorem recurrentPredecessor_properties
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T)
    {n : ℕ → ℕ} {S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hnmono : StrictMono n) (hn0 : 0 < n 0)
    (hnP : Tendsto (fun i : ℕ ↦ endEquiv (T ^ n i)) atTop
      (𝓝 (endEquiv T.peripheralProjection)))
    (hnS : Tendsto (fun i : ℕ ↦ endEquiv (T ^ (n i - 1))) atTop
      (𝓝 (endEquiv S))) :
    IsPositiveMap S ∧ IsTracePreservingMap S ∧
      S.comp T = T.peripheralProjection ∧
      T.comp S = T.peripheralProjection ∧
      S.comp T.peripheralProjection = S ∧
      T.peripheralProjection.comp S = S ∧
      LinearMap.range S = LinearMap.range T.peripheralProjection := by
  let Mat := Matrix (Fin D) (Fin D) ℂ
  have hnpos (i : ℕ) : 0 < n i :=
    hn0.trans_le (hnmono.monotone (Nat.zero_le i))
  have hP (X : Mat) : Tendsto (fun i : ℕ ↦ (T ^ n i) X) atTop
      (𝓝 (T.peripheralProjection X)) :=
    ((ContinuousLinearMap.apply ℂ Mat X).continuous.tendsto
      (endEquiv T.peripheralProjection)).comp hnP
  have hS (X : Mat) : Tendsto (fun i : ℕ ↦ (T ^ (n i - 1)) X) atTop
      (𝓝 (S X)) :=
    ((ContinuousLinearMap.apply ℂ Mat X).continuous.tendsto (endEquiv S)).comp hnS
  have hSpos : IsPositiveMap S :=
    IsPositiveMap.of_tendsto (fun i ↦ hPos.pow (n i - 1)) hS
  have hStp : IsTracePreservingMap S :=
    IsTracePreservingMap.of_tendsto (fun i ↦ hTP.pow (n i - 1)) hS
  have hST : S.comp T = T.peripheralProjection := by
    apply LinearMap.ext
    intro X
    have hleft : Tendsto (fun i : ℕ ↦ (T ^ n i) X) atTop (𝓝 (S (T X))) :=
      (hS (T X)).congr' (Filter.Eventually.of_forall fun i ↦ by
        have hni : n i - 1 + 1 = n i := Nat.sub_add_cancel (hnpos i)
        calc
          (T ^ (n i - 1)) (T X) = ((T ^ (n i - 1)).comp T) X := rfl
          _ = (T ^ (n i - 1 + 1)) X := by
            rw [pow_succ, Module.End.mul_eq_comp]
          _ = (T ^ n i) X := by rw [hni])
    exact tendsto_nhds_unique hleft (hP X)
  have hTS : T.comp S = T.peripheralProjection := by
    apply LinearMap.ext
    intro X
    have hright0 : Tendsto (fun i : ℕ ↦ T ((T ^ (n i - 1)) X)) atTop
        (𝓝 (T (S X))) :=
      ((endEquiv T).continuous.tendsto (S X)).comp (hS X)
    have hright : Tendsto (fun i : ℕ ↦ (T ^ n i) X) atTop (𝓝 (T (S X))) :=
      hright0.congr' (Filter.Eventually.of_forall fun i ↦ by
        have hni : n i - 1 + 1 = n i := Nat.sub_add_cancel (hnpos i)
        calc
          T ((T ^ (n i - 1)) X) = (T.comp (T ^ (n i - 1))) X := rfl
          _ = (T ^ (n i - 1 + 1)) X := by
            rw [pow_succ', Module.End.mul_eq_comp]
          _ = (T ^ n i) X := by rw [hni])
    exact tendsto_nhds_unique hright (hP X)
  have hnPred : Tendsto (fun i : ℕ ↦ n i - 1) atTop atTop :=
    (tendsto_sub_atTop_nat 1).comp hnmono.tendsto_atTop
  have hEig : ∀ μ : ℂ, T.HasEigenvalue μ → ‖μ‖ ≤ 1 := fun μ hμ ↦
    hPos.eigenvalue_norm_le_one_of_tracePreserving hTP μ hμ
  have hSP : S.comp T.peripheralProjection = S := by
    apply LinearMap.ext
    intro X
    change S (T.peripheralProjection X) = S X
    have hzero : Tendsto
        (fun i : ℕ ↦ (T ^ (n i - 1)) (X - T.peripheralProjection X)) atTop
        (𝓝 0) :=
      (T.tendsto_pow_apply_zero_of_mem_nonPeripheralSubspace hEig
        (T.sub_peripheralProjection_mem X)).comp hnPred
    have hsum := (hS (T.peripheralProjection X)).add hzero
    have hsame : Tendsto (fun i : ℕ ↦ (T ^ (n i - 1)) X) atTop
        (𝓝 (S (T.peripheralProjection X))) := by
      simpa only [← map_add, add_sub_cancel, add_zero] using hsum
    exact tendsto_nhds_unique hsame (hS X)
  have hPS : T.peripheralProjection.comp S = S := by
    apply LinearMap.ext
    intro X
    change T.peripheralProjection (S X) = S X
    calc
      T.peripheralProjection (S X) = S (T (S X)) :=
        (LinearMap.congr_fun hST (S X)).symm
      _ = S (T.peripheralProjection X) :=
        congrArg S (LinearMap.congr_fun hTS X)
      _ = S X := LinearMap.congr_fun hSP X
  have hrange : LinearMap.range S = LinearMap.range T.peripheralProjection := by
    apply le_antisymm
    · rintro Y ⟨X, rfl⟩
      exact ⟨S X, LinearMap.congr_fun hPS X⟩
    · rintro Y ⟨X, rfl⟩
      exact ⟨T X, LinearMap.congr_fun hST X⟩
  exact ⟨hSpos, hStp, hST, hTS, hSP, hPS, hrange⟩

/-- **Wolf Theorem 6.16, positive peripheral restricted inverse.**

There is a positive trace-preserving map `S`, constructed as a limit of the
predecessor powers `T ^ (n i - 1)`, which is a two-sided inverse for `T` on
the asymptotic image.  The ambient identities have the peripheral projection
on the right-hand side; in particular this theorem does not assert that `T`
has a global inverse.  The absorption and range identities say precisely that
`S` acts on the same peripheral/asymptotic image. -/
theorem exists_peripheralRestrictedInverse
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ∃ S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ),
      IsPositiveMap S ∧ IsTracePreservingMap S ∧
      S.comp T = T.peripheralProjection ∧
      T.comp S = T.peripheralProjection ∧
      S.comp T.peripheralProjection = S ∧
      T.peripheralProjection.comp S = S ∧
      LinearMap.range S = LinearMap.range T.peripheralProjection := by
  obtain ⟨n, S, hnmono, hn0, hnP, hnS⟩ :=
    hPos.exists_strictMono_tendsto_pow_peripheralProjection_and_predecessor hTP
  exact ⟨S, hPos.recurrentPredecessor_properties hTP hnmono hn0 hnP hnS⟩

end IsPositiveMap

/-! ### Restricted inverse identities on the asymptotic image -/

namespace Module.End

variable {D : ℕ} {T : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}

/-- If `S.comp T` is the peripheral projection, then `S (T X) = X` for
every `X` in the asymptotic image. -/
theorem peripheralRestrictedInverse_apply_map_of_mem_range
    {S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hST : S.comp T = T.peripheralProjection) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ LinearMap.range T.peripheralProjection) :
    S (T X) = X := by
  have hPX : T.peripheralProjection X = X := by
    rw [T.range_peripheralProjection] at hX
    exact T.peripheralProjection_apply_of_mem hX
  calc
    S (T X) = T.peripheralProjection X := LinearMap.congr_fun hST X
    _ = X := hPX

/-- If `T.comp S` is the peripheral projection, then `T (S X) = X` for
every `X` in the asymptotic image. -/
theorem map_peripheralRestrictedInverse_apply_of_mem_range
    {S : Module.End ℂ (Matrix (Fin D) (Fin D) ℂ)}
    (hTS : T.comp S = T.peripheralProjection) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X ∈ LinearMap.range T.peripheralProjection) :
    T (S X) = X := by
  have hPX : T.peripheralProjection X = X := by
    rw [T.range_peripheralProjection] at hX
    exact T.peripheralProjection_apply_of_mem hX
  calc
    T (S X) = T.peripheralProjection X := LinearMap.congr_fun hTS X
    _ = X := hPX

end Module.End
