/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.EnvironmentDilation
import QICLean.Channel.DeferredEnvironmentTrace

/-!
# Pure-environment dilation and deferred-trace regression tests

These tests retain the original system factor, use a specified nonzero environment
basis vector, and preserve arbitrary reference correlations. The deferred-trace tests
allow arbitrary intermediate operators and arbitrary initial environment matrices.
-/

open Matrix Matrix.DeferredEnvironment
open scoped Kronecker

-- The public insertion survives its extraction from the Markov-dilation module.
example (a : Fin 5) :
    (fixedEnvEmbedding (S := Fin 3) a)ᴴ * fixedEnvEmbedding (S := Fin 3) a = 1 :=
  fixedEnvEmbedding_conjTranspose_mul_self a

-- Every qutrit channel uses an environment of dimension nine and the chosen basis eight.
example (Φ : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix.unitaryGroup (Fin 3 × Fin 9) ℂ,
      partialTraceRightLM ∘ₗ
        singleKrausMap (U : Matrix (Fin 3 × Fin 9) (Fin 3 × Fin 9) ℂ) ∘ₗ
        freshEnvironmentInput (8 : Fin 9) = Φ :=
  exists_bounded_freshEnvironment_unitary Φ hΦ (by decide) 8

-- The same retained-system dilation equality holds on all system/reference operators.
example {δ : Type*} (Φ : Module.End ℂ (Matrix (Fin 3) (Fin 3) ℂ))
    (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix.unitaryGroup (Fin 3 × Fin 9) ℂ,
      tensorMapIdLM (δ := δ) partialTraceRightLM ∘ₗ
        tensorMapIdLM (singleKrausMap (U : Matrix (Fin 3 × Fin 9) (Fin 3 × Fin 9) ℂ)) ∘ₗ
        tensorMapIdLM (freshEnvironmentInput (8 : Fin 9)) = tensorMapIdLM Φ := by
  obtain ⟨U, hU⟩ := exists_bounded_freshEnvironment_unitary Φ hΦ (by decide) (8 : Fin 9)
  exact ⟨U, freshEnvironment_dilation_reference Φ 8 U hU⟩

-- A zero-wire register still has one configuration; no positive wire-count is assumed.
example (Φ : Module.End ℂ (Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ))
    (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix.unitaryGroup ((Fin 0 → Fin 2) × (Fin 0 → Fin 2)) ℂ,
      ∀ X : Matrix (Fin 0 → Fin 2) (Fin 0 → Fin 2) ℂ,
        Φ X = partialTraceRight
          ((U : Matrix ((Fin 0 → Fin 2) × (Fin 0 → Fin 2))
            ((Fin 0 → Fin 2) × (Fin 0 → Fin 2)) ℂ) *
            freshEnvironmentInput (0 : Fin 0 → Fin 2) X * Uᴴ) := by
  exact exists_freshEnvironment_unitary_of_equiv finFunctionFinEquiv finFunctionFinEquiv
    Φ hΦ (by decide) 0

-- Y may correlate the system with the entire old environment; it need not factor.
example (V : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ)
    (Y : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ)
    (τ : Matrix (Fin 4) (Fin 4) ℂ) :
    partialTraceRight (partialTraceRight
      (freshEnvironmentOp (Fin 3) V * (Y ⊗ₖ τ) * (freshEnvironmentOp (Fin 3) V)ᴴ)) =
      partialTraceRight (V * (partialTraceRight Y ⊗ₖ τ) * Vᴴ) :=
  trace_deferred_freshEnvironment V Y τ

-- The composed operator is unitary, and its final discard equals successive reductions.
example (U : Matrix.unitaryGroup (Fin 2 × Fin 3) ℂ)
    (V : Matrix.unitaryGroup (Fin 2 × Fin 4) ℂ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) (σ : Matrix (Fin 3) (Fin 3) ℂ)
    (τ : Matrix (Fin 4) (Fin 4) ℂ) :
    let C := freshEnvironmentOp (Fin 3)
      (V : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ) *
      ((U : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℂ))
    C ∈ unitary (Matrix ((Fin 2 × Fin 3) × Fin 4) ((Fin 2 × Fin 3) × Fin 4) ℂ) ∧
      partialTraceRight (partialTraceRight (C * ((X ⊗ₖ σ) ⊗ₖ τ) * Cᴴ)) =
        partialTraceRight
          ((V : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ) *
            (partialTraceRight
              ((U : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ) * (X ⊗ₖ σ) * Uᴴ) ⊗ₖ τ) *
            Vᴴ) :=
  ⟨deferredEnvironment_comp_mem_unitary U.property V.property,
    deferredEnvironment_comp
      (U : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ)
      (V : Matrix (Fin 2 × Fin 4) (Fin 2 × Fin 4) ℂ) X σ τ⟩

section AxiomChecks
set_option linter.hashCommand false

/--
info: 'Matrix.exists_bounded_freshEnvironment_unitary' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_bounded_freshEnvironment_unitary

/--
info: 'Matrix.exists_freshEnvironment_unitary_of_equiv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_freshEnvironment_unitary_of_equiv

/--
info: 'Matrix.freshEnvironment_dilation_reference' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.freshEnvironment_dilation_reference

/--
info: 'Matrix.DeferredEnvironment.trace_deferred_freshEnvironment' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.DeferredEnvironment.trace_deferred_freshEnvironment

/--
info: 'Matrix.DeferredEnvironment.deferredEnvironment_comp' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.DeferredEnvironment.deferredEnvironment_comp

/--
info: 'Matrix.DeferredEnvironment.deferredEnvironment_comp_mem_unitary' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.DeferredEnvironment.deferredEnvironment_comp_mem_unitary

end AxiomChecks
