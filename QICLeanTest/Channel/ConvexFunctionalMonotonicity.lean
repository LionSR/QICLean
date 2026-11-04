/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.ConvexFunctionalMonotonicity
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Regression tests for Wolf's generic tuple monotonicity theorem. -/

open scoped Matrix Kronecker ComplexOrder
open Matrix

namespace ConvexFunctionalMonotonicityTest

noncomputable section

/-- The real trace of any chosen component, on all complex matrix tuples. -/
def componentTrace {ι : Type} (k : ι) : MatrixTupleFunctional ι :=
  fun _ _ _ A => (A k).trace.re

theorem componentTrace_convex {ι : Type} (k : ι) :
    ConvexMatrixFunctional (fun _ => Set.univ) (componentTrace k) where
  convex α := by
    refine ⟨convex_univ, ?_⟩
    intro A _ B _ a b _ _ _
    simp [componentTrace, trace_add, trace_smul]
  unitary_mem := by intros; exact Set.mem_univ _
  unitary_eq := by
    intro α _ _ A _ U
    dsimp [componentTrace]
    rw [trace_mul_cycle, ← star_eq_conjTranspose,
      Unitary.star_mul_self_of_mem U.property, Matrix.one_mul]
  tensor_mem := by intros; exact Set.mem_univ _
  tensor_eq := by
    intro α β _ _ _ _ A _ τ _ htr
    simp [componentTrace, trace_kronecker, htr]
  reindex_mem := by intros; exact Set.mem_univ _
  reindex_eq := by
    intro α β _ _ _ _ A _ e
    dsimp [componentTrace]
    congr 1
    exact Matrix.trace_submatrix_equiv e.symm _

-- A generic three-component example, with no Hermiticity or positivity inputs.
example {d d' : ℕ} [NeZero d]
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d') (Fin d') ℂ)
    (hT : IsKrausCPTP T) (A : MatrixTuple (Fin 3) (Fin d)) :
    (T (A 2)).trace.re ≤ (A 2).trace.re :=
  (componentTrace_convex (2 : Fin 3)).map_le_univ hT A

-- The actual real Weyl average, with a non-cyclic coordinate type and a
-- rectangular retained/environment split (retained dimension 3, environment 2).
example (M : Matrix (Fin 3 × Bool) (Fin 3 × Bool) ℂ)
    (e : Bool ≃ ZMod (Fintype.card Bool)) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card Bool)) :
    ((Fintype.card Bool : ℝ) ^ 2)⁻¹ •
        ∑ p : ZMod (Fintype.card Bool) × ZMod (Fintype.card Bool),
          ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ reindexedWeyl e ζ p.1 p.2) * M *
            ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ reindexedWeyl e ζ p.1 p.2)ᴴ =
      partialTraceRight M ⊗ₖ ((Fintype.card Bool : ℝ)⁻¹ • (1 : Matrix Bool Bool ℂ)) :=
  ConvexMatrixFunctional.weyl_average_eq_partialTraceRight e hζ M

-- The tensor permutations in the rectangular unitary dilation remain explicit.
example {T : Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 3) (Fin 3) ℂ}
    (hT : IsKrausCPTP T) :
    ∃ (r : ℕ), Nonempty (Fin r) ∧
      ∃ (τ : Matrix (Fin 3 × Fin r) (Fin 3 × Fin r) ℂ),
        τ.PosSemidef ∧ τ.trace = 1 ∧
          ∃ U : unitaryGroup ((Fin 3 × Fin r) × Fin 2) ℂ,
            ∀ X : Matrix (Fin 2) (Fin 2) ℂ,
              T X = partialTraceRight
                (reindex (Equiv.prodAssoc (Fin 3) (Fin r) (Fin 2))
                  (Equiv.prodAssoc (Fin 3) (Fin r) (Fin 2))
                  ((U : Matrix _ _ ℂ) *
                    reindex (Equiv.prodComm (Fin 2) (Fin 3 × Fin r))
                      (Equiv.prodComm (Fin 2) (Fin 3 × Fin r)) (X ⊗ₖ τ) * Uᴴ)) :=
  exists_rectangular_unitary_dilation hT

-- A singleton environment is valid; so is an empty retained system.
example {ι : Type} {D : MatrixTupleDomains ι} {F : MatrixTupleFunctional ι}
    (hF : ConvexMatrixFunctional D F) (A : MatrixTuple ι (Fin 0 × Fin 1))
    (hA : A ∈ D _) (htrA : (fun i => partialTraceRight (A i)) ∈ D (Fin 0)) :
    F (Fin 0) (fun i => partialTraceRight (A i)) ≤ F (Fin 0 × Fin 1) A :=
  hF.partialTraceRight_le hA htrA

-- Empty tuples impose no special requirement on the proof.
example {F : MatrixTupleFunctional (Fin 0)}
    (hF : ConvexMatrixFunctional (fun _ => Set.univ) F)
    {T : Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ}
    (hT : IsKrausCPTP T) (A : MatrixTuple (Fin 0) (Fin 1)) :
    F (Fin 2) (fun i => T (A i)) ≤ F (Fin 1) A := hF.map_le_univ hT A

-- There is no density ancilla of dimension zero.
example (τ : Matrix (Fin 0) (Fin 0) ℂ) : τ.trace ≠ 1 := by
  simp [Matrix.trace]

-- A positive-dimensional input cannot have a zero-dimensional TP output.
example (T : Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ] Matrix (Fin 0) (Fin 0) ℂ) :
    ¬ IsKrausCPTP T := by
  intro hT
  have h := hT.trace_map (1 : Matrix (Fin 1) (Fin 1) ℂ)
  simp [Matrix.trace] at h

/-- Even-dimensional full domains are tensor closed but need not contain
partial-trace outputs. This tests the need for explicit marginal membership. -/
def evenDomains : MatrixTupleDomains (Fin 3) :=
  fun α _ _ => { _A | 2 ∣ Fintype.card α }

theorem evenDomains_convex :
    ConvexMatrixFunctional evenDomains (fun _ _ _ _ => 0) where
  convex := by
    intro α _ _
    apply convexOn_const
    intro A hA B _ a b _ _ _
    exact hA
  unitary_mem := by intros; assumption
  unitary_eq := by intros; rfl
  tensor_mem := by
    intro α β _ _ _ _ A hA τ _ _
    simpa only [evenDomains, Set.mem_ofPred_eq, Fintype.card_prod] using
      dvd_mul_of_dvd_left hA (Fintype.card β)
  tensor_eq := by intros; rfl
  reindex_mem := by
    intro α β _ _ _ _ A hA e
    change 2 ∣ Fintype.card β
    rw [← Fintype.card_congr e]
    exact hA
  reindex_eq := by intros; rfl

example (A : MatrixTuple (Fin 3) (Fin 1 × Fin 2)) :
    A ∈ evenDomains (Fin 1 × Fin 2) ∧
      (fun i => partialTraceRight (A i)) ∉ evenDomains (Fin 1) := by
  norm_num [evenDomains, Fintype.card_prod]

/-- The zero-dimension exception to the printed source statement. -/
def dimensionIndicator : MatrixTupleFunctional (Fin 3) :=
  fun α _ _ _ => if Fintype.card α = 0 then 0 else 1

theorem dimensionIndicator_convex :
    ConvexMatrixFunctional (fun _ => Set.univ) dimensionIndicator where
  convex α := convexOn_const _ convex_univ
  unitary_mem := by intros; exact Set.mem_univ _
  unitary_eq := by intros; rfl
  tensor_mem := by intros; exact Set.mem_univ _
  tensor_eq := by
    intro α β _ _ _ _ A _ τ _ htr
    have hβ : Fintype.card β ≠ 0 := by
      intro h
      have : IsEmpty β := Fintype.card_eq_zero_iff.mp h
      simp [Matrix.trace] at htr
    simp [dimensionIndicator, Fintype.card_prod, hβ]
  reindex_mem := by intros; exact Set.mem_univ _
  reindex_eq := by
    intro α β _ _ _ _ A _ e
    simp [dimensionIndicator, Fintype.card_congr e]

theorem zero_input_channel :
    IsKrausCPTP (0 : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) := by
  refine ⟨0, Fin.elim0, ?_, ?_⟩
  · intro X
    simp
  · ext i
    exact Fin.elim0 i

-- All three source properties hold, yet 1 ≤ 0 fails for the zero-input map.
example (A : MatrixTuple (Fin 3) (Fin 0)) :
    ¬ dimensionIndicator (Fin 1) (fun i =>
      (0 : Matrix (Fin 0) (Fin 0) ℂ →ₗ[ℂ] Matrix (Fin 1) (Fin 1) ℂ) (A i)) ≤
        dimensionIndicator (Fin 0) A := by
  norm_num [dimensionIndicator]

end

end ConvexFunctionalMonotonicityTest

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let decls := #[``Matrix.ConvexMatrixFunctional.weyl_average_eq_partialTraceRight,
    ``Matrix.ConvexMatrixFunctional.partialTraceRight_le,
    ``Matrix.exists_rectangular_unitary_dilation,
    ``Matrix.ConvexMatrixFunctional.map_le, ``Matrix.ConvexMatrixFunctional.map_le_univ,
    ``ConvexFunctionalMonotonicityTest.componentTrace_convex,
    ``ConvexFunctionalMonotonicityTest.evenDomains_convex,
    ``ConvexFunctionalMonotonicityTest.dimensionIndicator_convex,
    ``ConvexFunctionalMonotonicityTest.zero_input_channel]
  for decl in decls do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"
