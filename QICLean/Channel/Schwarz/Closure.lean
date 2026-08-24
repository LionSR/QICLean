/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Algebra.MatrixTracePairing
import QICLean.Channel.Schwarz.AbstractMultiplicativeDomain

/-!
# Closure properties for positive, trace-preserving, and Schwarz maps

This file collects the composition, power, and finite-dimensional pointwise
limit closures used in Wolf's recurrent-projection argument.  It also records
that trace-pairing adjoints commute with powers and pointwise limits.

The Schwarz results are orientation-specific: applying them to a map and to
its trace-pairing adjoint requires two separate Schwarz hypotheses.
-/

open Filter Matrix
open scoped Topology TNOperatorSpace Matrix ComplexOrder MatrixOrder

noncomputable section

namespace IsPositiveMap

variable {n : Type*} {S T : Module.End ℂ (Matrix n n ℂ)}

/-- Positive matrix endomorphisms are closed under composition. -/
theorem comp (hS : IsPositiveMap S) (hT : IsPositiveMap T) :
    IsPositiveMap (S.comp T) := by
  intro X hX
  exact hS _ (hT X hX)

/-- Every natural power of a positive matrix endomorphism is positive. -/
theorem pow (hT : IsPositiveMap T) (m : ℕ) : IsPositiveMap (T ^ m) := by
  induction m with
  | zero =>
      intro X hX
      simpa using hX
  | succ m ih =>
      rw [pow_succ', Module.End.mul_eq_comp]
      exact hT.comp ih

/-- A pointwise finite-dimensional limit of positive matrix endomorphisms is
positive. -/
theorem of_tendsto
    {E : ℕ → Module.End ℂ (Matrix n n ℂ)}
    {S : Module.End ℂ (Matrix n n ℂ)}
    (hE : ∀ i, IsPositiveMap (E i))
    (hlim : ∀ X, Tendsto (fun i : ℕ ↦ E i X) atTop (𝓝 (S X))) :
    IsPositiveMap S := by
  intro X hX
  exact Matrix.posSemidef_is_closed.mem_of_tendsto (hlim X)
    (Filter.Eventually.of_forall fun i ↦ hE i X hX)

end IsPositiveMap

namespace IsTracePreservingMap

variable {n : Type*} [Fintype n]
  {S T : Module.End ℂ (Matrix n n ℂ)}

/-- Trace-preserving matrix endomorphisms are closed under composition. -/
theorem comp (hS : IsTracePreservingMap S) (hT : IsTracePreservingMap T) :
    IsTracePreservingMap (S.comp T) := by
  intro X
  rw [LinearMap.comp_apply, hS, hT]

/-- Every natural power of a trace-preserving matrix endomorphism is
trace-preserving. -/
theorem pow (hT : IsTracePreservingMap T) (m : ℕ) :
    IsTracePreservingMap (T ^ m) := by
  induction m with
  | zero => simp [IsTracePreservingMap]
  | succ m ih =>
      rw [pow_succ', Module.End.mul_eq_comp]
      exact hT.comp ih

/-- A pointwise finite-dimensional limit of trace-preserving matrix
endomorphisms is trace-preserving. -/
theorem of_tendsto
    {E : ℕ → Module.End ℂ (Matrix n n ℂ)}
    {S : Module.End ℂ (Matrix n n ℂ)}
    (hE : ∀ i, IsTracePreservingMap (E i))
    (hlim : ∀ X, Tendsto (fun i : ℕ ↦ E i X) atTop (𝓝 (S X))) :
    IsTracePreservingMap S := by
  intro X
  have htr : Tendsto (fun i : ℕ ↦ Matrix.trace (E i X)) atTop
      (𝓝 (Matrix.trace (S X))) :=
    ((Matrix.traceLinearMap n ℂ ℂ).continuous_of_finiteDimensional.tendsto
      (S X)).comp (hlim X)
  have hconst : (fun i : ℕ ↦ Matrix.trace (E i X)) = fun _ ↦ Matrix.trace X :=
    funext fun i ↦ hE i X
  rw [hconst] at htr
  exact tendsto_nhds_unique htr tendsto_const_nhds

end IsTracePreservingMap

namespace IsSchwarzMap

variable {n : Type*} [Fintype n]
  {S T : Module.End ℂ (Matrix n n ℂ)}

/-- Schwarz matrix endomorphisms are closed under composition when both maps
are positive.  Positivity of the outer map transports the inner Schwarz
defect; positivity of the inner map identifies `T(Aᴴ)` with `(T A)ᴴ`. -/
theorem comp (hS : IsSchwarzMap S) (hT : IsSchwarzMap T)
    (hSPos : IsPositiveMap S) (hTPos : IsPositiveMap T) :
    IsSchwarzMap (S.comp T) := by
  intro A
  have hinner := hSPos _ (hT A)
  have houter := hS (T A)
  have heq :
      (S.comp T) (Aᴴ * A) - (S.comp T) Aᴴ * (S.comp T) A =
        S (T (Aᴴ * A) - T Aᴴ * T A) +
          (S ((T A)ᴴ * T A) - S (T A)ᴴ * S (T A)) := by
    simp only [LinearMap.comp_apply, map_sub, hTPos.map_conjTranspose]
    module
  rw [heq]
  exact hinner.add houter

/-- Every natural power of a positive Schwarz matrix endomorphism is
Schwarz. -/
theorem pow (hT : IsSchwarzMap T) (hTPos : IsPositiveMap T) (m : ℕ) :
    IsSchwarzMap (T ^ m) := by
  induction m with
  | zero =>
      intro A
      simpa using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  | succ m ih =>
      rw [pow_succ', Module.End.mul_eq_comp]
      exact hT.comp ih hTPos (hTPos.pow m)

/-- A pointwise finite-dimensional limit of Schwarz matrix endomorphisms is
Schwarz. -/
theorem of_tendsto
    {E : ℕ → Module.End ℂ (Matrix n n ℂ)}
    {S : Module.End ℂ (Matrix n n ℂ)}
    (hE : ∀ i, IsSchwarzMap (E i))
    (hlim : ∀ X, Tendsto (fun i : ℕ ↦ E i X) atTop (𝓝 (S X))) :
    IsSchwarzMap S := by
  intro A
  exact Matrix.posSemidef_is_closed.mem_of_tendsto
    ((hlim (Aᴴ * A)).sub ((hlim Aᴴ).mul (hlim A)))
    (Filter.Eventually.of_forall fun i ↦ hE i A)

end IsSchwarzMap

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The trace-pairing adjoint of the identity matrix endomorphism is the
identity. -/
theorem traceAdjointMap_id :
    traceAdjointMap (LinearMap.id : Module.End ℂ (Matrix n n ℂ)) =
      LinearMap.id := by
  classical
  apply LinearMap.ext
  intro X
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro Y
  rw [trace_traceAdjointMap_mul]
  simp

/-- The trace-pairing adjoint of a power is the corresponding power of the
trace-pairing adjoint. -/
theorem traceAdjointMap_pow (T : Module.End ℂ (Matrix n n ℂ)) (m : ℕ) :
    traceAdjointMap (T ^ m) = (traceAdjointMap T) ^ m := by
  classical
  induction m with
  | zero =>
      simp only [pow_zero]
      exact traceAdjointMap_id
  | succ m ih =>
      rw [pow_succ, Module.End.mul_eq_comp, traceAdjointMap_comp, ih,
        pow_succ', Module.End.mul_eq_comp]

/-- Pointwise convergence of matrix endomorphisms transports through the
trace-pairing adjoint.  The proof uses the matrix-unit formula for the adjoint
and finite-dimensional entrywise convergence. -/
theorem tendsto_traceAdjointMap
    {E : ℕ → Module.End ℂ (Matrix n n ℂ)}
    {S : Module.End ℂ (Matrix n n ℂ)}
    (hlim : ∀ X, Tendsto (fun i : ℕ ↦ E i X) atTop (𝓝 (S X)))
    (X : Matrix n n ℂ) :
    Tendsto (fun i : ℕ ↦ traceAdjointMap (E i) X) atTop
      (𝓝 (traceAdjointMap S X)) := by
  classical
  change Tendsto
    (fun i : ℕ ↦ fun a b ↦ traceAdjointMap (E i) X a b) atTop
      (𝓝 (fun a b ↦ traceAdjointMap S X a b))
  rw [tendsto_pi_nhds]
  intro a
  rw [tendsto_pi_nhds]
  intro b
  simp_rw [traceAdjointMap_apply_apply]
  have hcont : Continuous (fun Y : Matrix n n ℂ ↦ Matrix.trace (X * Y)) :=
    (Matrix.traceLinearMap n ℂ ℂ).continuous_of_finiteDimensional.comp
      (continuous_const.mul continuous_id)
  exact (hcont.tendsto _).comp (hlim (Matrix.single b a 1))

end Matrix
