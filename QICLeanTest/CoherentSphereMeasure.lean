/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.CoherentMeasure

/-! Literal sphere coordinates, arbitrary-matrix finiteness, and coherent-state mass. -/

open Matrix MeasureTheory TensorPower PermutationRepresentation
open scoped ComplexOrder Matrix.Norms.L2Operator

noncomputable section

namespace CoherentSphereMeasureTest

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (k : ℕ) (a : Ω)

example (U : unitaryGroup Ω ℂ) : ‖(coherentSphereMap a U).1‖ = 1 :=
  (coherentSphereMap a U).2

example (U : unitaryGroup Ω ℂ) (x : Ω) :
    (coherentSphereMap a U).1 x = ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) x := rfl

example (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) :
    IsFiniteMeasure (coherentMeasure k a ρ) := inferInstance

example : coherentMeasure k a (0 : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) = 0 := by simp

example (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ) (hρ : ρ.PosSemidef)
    {f : (Ω → ℂ) → ℝ} (hf : Continuous f) :
    (∫ θ, f (fun x => θ.1 x) ∂coherentMeasure k a ρ) = realCoherentIntegral k a ρ f :=
  integral_coherentMeasure k a ρ hρ hf

-- The trace-one and symmetric-support facts are derived from the actual coherent
-- projector. There is no supplied normalization or integral-identification premise.
example (U : unitaryGroup Ω ℂ) :
    (coherentMeasure k a
      (coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1))).real Set.univ = 1 :=
  coherentMeasure_real_univ k a _ (posSemidef_vecMulVec_self_star _)
    (trace_coherentProj_unitary_mulVec_single U a) (symProj_mul_coherentProj k _)

-- Zero copies are included in the same literal construction.
example (U : unitaryGroup Ω ℂ) :
    (coherentMeasure 0 a
      (coherentProj 0 ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1))).real Set.univ = 1 :=
  coherentMeasure_real_univ 0 a _ (posSemidef_vecMulVec_self_star _)
    (trace_coherentProj_unitary_mulVec_single U a) (symProj_mul_coherentProj 0 _)

end CoherentSphereMeasureTest
