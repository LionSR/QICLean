/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.PoissonContractionDecay

/-! Boundary consumers of the actual probability expectation, without an assumed law. -/

open Matrix MeasureTheory
open scoped NNReal Kronecker InnerProductSpace MatrixOrder ComplexOrder

namespace PoissonContractionDecayTest

variable {n a ι : Type*} [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a] [Fintype ι]

-- At time zero the actual word law preserves the initial squared norm.
example (k : ι → Matrix n n ℂ) (ξ : EuclideanSpace ℂ (n × a)) :
    (∫ w, poissonContractionWordEnergy k ξ w ∂PoissonWord.measure ι 0) = ‖ξ‖ ^ 2 := by
  simp [PoissonWord.measure_zero, PoissonWord.nil, poissonContractionWordEnergy]

-- With no labels, every time has exactly the empty-word energy.
example (k : Empty → Matrix n n ℂ) (ξ : EuclideanSpace ℂ (n × a)) (t : ℝ≥0) :
    (∫ w, poissonContractionWordEnergy k ξ w ∂PoissonWord.measure Empty t) = ‖ξ‖ ^ 2 := by
  simp [PoissonWord.measure_of_isEmpty, PoissonWord.nil, poissonContractionWordEnergy]

-- A genuinely empty spectator has zero energy for every random word.
example (k : ι → Matrix n n ℂ) (ξ : EuclideanSpace ℂ (n × Empty)) (t : ℝ≥0) :
    (∫ w, poissonContractionWordEnergy k ξ w ∂PoissonWord.measure ι t) = 0 := by
  have hξ : ξ = 0 := by ext x; exact isEmptyElim x.2
  simp [hξ, poissonContractionWordEnergy]

private noncomputable def ground : EuclideanSpace ℂ (Fin 2) := PiLp.single 2 0 1

private noncomputable def excited : EuclideanSpace ℂ (Fin 2 × Unit) :=
  PiLp.single 2 (1, ()) 1

private noncomputable def deficit : Matrix (Fin 2) (Fin 2) ℂ :=
  1 - vecMulVec (WithLp.ofLp ground) (star (WithLp.ofLp ground))

-- The initial observable is genuinely nonzero.
example : poissonContractionWordEnergy (fun _ : Unit => deficit) excited PoissonWord.nil = 1 := by
  simp [poissonContractionWordEnergy, PoissonWord.nil, excited]

-- Positive time and a nonzero excited input exercise the final rate cancellation.
example :
    Integrable (poissonContractionWordEnergy (fun _ : Unit => deficit) excited)
        (PoissonWord.measure Unit 1) ∧
      (∫ w, poissonContractionWordEnergy (fun _ : Unit => deficit) excited w
        ∂PoissonWord.measure Unit 1) ≤ Real.exp (-1) := by
  have hk : deficit ≤ 1 :=
    sub_le_self _ (posSemidef_vecMulVec_self_star (WithLp.ofLp ground)).nonneg
  have hground : toEuclideanLin deficit ground = 0 := by
    simp only [deficit, map_sub, LinearMap.sub_apply, toLpLin_one, LinearMap.id_apply,
      toEuclideanLin_vecMulVec_star_self_apply, inner_self_eq_norm_sq_to_K]
    simp [ground]
  have hgap : (1 : ℂ) • (1 - vecMulVec (WithLp.ofLp ground)
      (star (WithLp.ofLp ground))) ≤ ∑ _ : Unit, deficit := by simp [deficit]
  have hslices (r : Unit) :
      ⟪ground, WithLp.toLp 2 (fun i => excited (i, r))⟫_ℂ = 0 := by
    simp [ground, excited, EuclideanSpace.inner_single_left]
  have h := poissonContractionWordEnergy_integrable_and_le (fun _ : Unit => deficit)
    (fun _ => hk) (fun _ => hground) hgap hslices 1
  exact ⟨h.1, by simpa [excited] using h.2⟩

end PoissonContractionDecayTest
