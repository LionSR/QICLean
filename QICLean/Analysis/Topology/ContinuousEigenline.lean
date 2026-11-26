/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UnitInterval
import QICLean.Algebra.Matrix.RankOneFactorization
import QICLean.Algebra.Matrix.RankOneSandwich

/-!
# Symmetry eigenvalues of continuous ground lines

A fixed finite-dimensional symmetry operator has a finite spectrum. Thus
its eigenvalue on a continuous invariant line is constant on a connected
parameter interval. The eigenvalue is extracted continuously by the trace
against the rank-one ground projection.

This is a finite-chain ingredient for the character rephasing permitted in
Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2614–2632. The projection continuity
must be derived separately from the Hamiltonian path. These results do not
construct canonical tensors across a change of minimal bond dimension.

Moved from TNLean, `TNLean/MPS/Symmetry/GroundPath/GroundLineSymmetryCharacter.lean`,
`TNLean/MPS/Symmetry/GroundPath/FixedBondPhysicalPathInvariance.lean`,
`TNLean/MPS/Symmetry/GroundPath/VaryingBondPhysicalCharacter.lean` at commit `021ba0bd19`
(Apache-2.0).
-/

section

open scoped Matrix Matrix.Norms.L2Operator

namespace Matrix

/-- An operator commuting with a rank-one idempotent acts on its range by
the trace against that idempotent. Orthogonal ground projections are a
special case. Source context: arXiv:1010.3732, Section II.C.2,
lines 440–453, and Appendix B, lines 2614–2632. -/
theorem mul_rankOne_idempotent_eq_trace_smul
    {n : Type*} [Fintype n]
    (U P : Matrix n n ℂ) (hrank : P.rank = 1) (hid : P * P = P)
    (hComm : Commute P U) : U * P = (U * P).trace • P := by
  classical
  obtain ⟨v, w, _, _, hP⟩ := exists_eq_vecMulVec_of_rank_eq_one P hrank
  have hsand : P * U * P = (U * P).trace • P := by
    simpa only [hP] using vecMulVec_mul_mul_vecMulVec_eq_trace_smul v w U
  simpa only [hComm.eq, Matrix.mul_assoc, hid] using hsand

/-- The scalar action on a nonzero rank-one invariant line belongs to the
spectrum of the fixed symmetry operator. Source context: arXiv:1010.3732,
Section II.C.2, lines 440–453, and Appendix B, lines 2614–2632. -/
theorem trace_mul_mem_spectrum_of_rankOne_idempotent_commute
    {n : Type*} [Fintype n] [DecidableEq n]
    (U P : Matrix n n ℂ) (hrank : P.rank = 1) (hid : P * P = P)
    (hComm : Commute P U) : (U * P).trace ∈ spectrum ℂ U := by
  rw [spectrum.mem_iff]
  intro hunit
  have hzero : (algebraMap ℂ (Matrix n n ℂ) (U * P).trace - U) * P = 0 := by
    rw [Matrix.sub_mul, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
    exact sub_eq_zero.mpr (mul_rankOne_idempotent_eq_trace_smul U P hrank hid hComm).symm
  have hPzero : P = 0 := hunit.mul_left_cancel (hzero.trans (Matrix.mul_zero _).symm)
  simp only [hPzero, Matrix.rank_zero, zero_ne_one] at hrank

/-- The eigenvalue of a fixed operator on a continuous invariant rank-one
projection is constant on a connected parameter space. No finiteness
assumption on a symmetry group is involved. Source context:
arXiv:1010.3732, Section II.C.2, lines 440–453, and Appendix B,
lines 2614–2632. -/
theorem trace_mul_constant_of_continuous_rankOne_idempotent
    {T n : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [Fintype n]
    (U : Matrix n n ℂ) (P : T → Matrix n n ℂ) (hP : Continuous P)
    (hrank : ∀ t, (P t).rank = 1) (hid : ∀ t, P t * P t = P t)
    (hComm : ∀ t, Commute (P t) U) (t t₀ : T) :
    (U * P t).trace = (U * P t₀).trace := by
  classical
  let c : T → spectrum ℂ U := fun t =>
    ⟨(U * P t).trace,
      trace_mul_mem_spectrum_of_rankOne_idempotent_commute U (P t)
        (hrank t) (hid t) (hComm t)⟩
  have hc : Continuous c :=
    ((continuous_const.matrix_mul hP).matrix_trace).subtype_mk _
  exact congrArg Subtype.val (TotallyDisconnectedSpace.eq_of_continuous c hc t t₀)

/-- A one-dimensional invariant range of a group representation carries a
character, extracted by the trace against its idempotent. Source context:
arXiv:1010.3732, Section II.C.2, lines 440–453, and Appendix B,
lines 2614–2632. -/
theorem exists_character_of_rankOne_idempotent_commute
    {G n : Type*} [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (P : Matrix n n ℂ)
    (hrank : P.rank = 1) (hid : P * P = P)
    (hComm : ∀ g, Commute P (U g)) :
    ∃ χ : G →* ℂ, ∀ g, χ g = (U g * P).trace := by
  have hPne : P ≠ 0 := by
    intro hzero
    simp only [hzero, Matrix.rank_zero, zero_ne_one] at hrank
  have hcov := fun g => mul_rankOne_idempotent_eq_trace_smul (U g) P hrank hid (hComm g)
  refine ⟨{ toFun := fun g => (U g * P).trace, map_one' := ?_, map_mul' := ?_ }, fun _ => rfl⟩
  · apply smul_left_injective ℂ hPne
    simpa only [map_one, Matrix.one_mul, one_smul] using (hcov 1).symm
  · intro g h
    apply smul_left_injective ℂ hPne
    calc
      (U (g * h) * P).trace • P = U (g * h) * P := (hcov (g * h)).symm
      _ = U g * (U h * P) := by rw [map_mul, Matrix.mul_assoc]
      _ = U g * ((U h * P).trace • P) := congrArg (U g * ·) (hcov h)
      _ = (U h * P).trace • (U g * P) := Matrix.mul_smul _ _ _
      _ = (U h * P).trace • ((U g * P).trace • P) :=
        congrArg ((U h * P).trace • ·) (hcov g)
      _ = ((U g * P).trace * (U h * P).trace) • P := by rw [smul_smul, mul_comm]

/-- Continuous rank-one invariant ground projections carry one fixed unitary
character throughout a connected parameter space. Source context:
arXiv:1010.3732, Section II.C.2, lines 440–453, and Appendix B,
lines 2614–2632. -/
theorem exists_constant_character_of_continuous_rankOne_idempotent
    {T G n : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ unitaryGroup n ℂ)
    (P : T → Matrix n n ℂ) (hP : Continuous P)
    (hrank : ∀ t, (P t).rank = 1) (hid : ∀ t, P t * P t = P t)
    (hComm : ∀ t g, Commute (P t) (U g)) (t₀ : T) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      ∀ t g, U g * P t = χ g • P t := by
  obtain ⟨χ, hχ⟩ := exists_character_of_rankOne_idempotent_commute U (P t₀)
    (hrank t₀) (hid t₀) (hComm t₀)
  refine ⟨χ, ?_, ?_⟩
  · intro g
    rw [hχ g]
    exact spectrum.norm_eq_one_of_unitary (hU g)
      (trace_mul_mem_spectrum_of_rankOne_idempotent_commute (U g) (P t₀)
        (hrank t₀) (hid t₀) (hComm t₀ g))
  · intro t g
    rw [hχ g, mul_rankOne_idempotent_eq_trace_smul (U g) (P t)
      (hrank t) (hid t) (hComm t g)]
    rw [trace_mul_constant_of_continuous_rankOne_idempotent (U g) P hP hrank hid
      (fun t => hComm t g) t t₀]

end Matrix

end

section

open scoped ScalarCohomology

open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate

namespace Matrix

/-- A nonzero invariant line admits an eigenvalue which is extracted by a
quadratic quotient. Source context: arXiv:1010.3732, Section II.F.2,
lines 930–954. -/
theorem eigenvector_of_mem_span_singleton
    {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (v : EuclideanSpace ℂ n) (hv : v ≠ 0)
    (hline : toEuclideanLin U v ∈ Submodule.span ℂ {v}) :
    toEuclideanLin U v =
      (inner ℂ v (toEuclideanLin U v) / inner ℂ v v) • v := by
  obtain ⟨z, hz⟩ := Submodule.mem_span_singleton.mp hline
  rw [← hz, inner_smul_right]
  simp only [mul_div_cancel_right₀ z (inner_self_ne_zero.mpr hv)]

/-- The eigenvalue on a continuous nonzero invariant line is constant on a
connected parameter space, since the fixed physical operator has finite
spectrum. Source context: arXiv:1010.3732, Section II.F.2, lines 930–954. -/
theorem eigenvalue_constant_of_continuous_invariant_line
    {T n : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [Fintype n] [DecidableEq n]
    (U : Matrix n n ℂ) (v : T → EuclideanSpace ℂ n) (hv : Continuous v)
    (hne : ∀ t, v t ≠ 0)
    (hline : ∀ t, toEuclideanLin U (v t) ∈ Submodule.span ℂ {v t})
    (t t₀ : T) :
    inner ℂ (v t) (toEuclideanLin U (v t)) / inner ℂ (v t) (v t) =
      inner ℂ (v t₀) (toEuclideanLin U (v t₀)) / inner ℂ (v t₀) (v t₀) := by
  let c : T → ℂ := fun t => inner ℂ (v t) (toEuclideanLin U (v t)) / inner ℂ (v t) (v t)
  have hcov (t : T) : toEuclideanLin U (v t) = c t • v t :=
    eigenvector_of_mem_span_singleton U (v t) (hne t) (hline t)
  have hspec (t : T) : c t ∈ spectrum ℂ U := by
    rw [← spectrum_toLpLin (A := U) 2]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hcov t), hne t⟩).mem_spectrum
  have hc : Continuous c :=
    (hv.inner ((toEuclideanLin U).continuous_of_finiteDimensional.comp hv)).div
      (hv.inner hv) (fun t => inner_self_ne_zero.mpr (hne t))
  let cs : T → spectrum ℂ U := fun t => ⟨c t, hspec t⟩
  exact congrArg Subtype.val (TotallyDisconnectedSpace.eq_of_continuous cs
    (hc.subtype_mk _) t t₀)

/-- A continuous nonzero invariant vector family carries a constant unitary
character of the physical representation. Source context:
arXiv:1010.3732, Section II.F.2, lines 930–954. -/
theorem exists_constant_character_of_continuous_invariant_line
    {T G n : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    [Group G] [Fintype n] [DecidableEq n]
    (U : G →* Matrix n n ℂ) (hU : ∀ g, U g ∈ unitaryGroup n ℂ)
    (v : T → EuclideanSpace ℂ n) (hv : Continuous v) (hne : ∀ t, v t ≠ 0)
    (hline : ∀ t g, toEuclideanLin (U g) (v t) ∈ Submodule.span ℂ {v t})
    (t₀ : T) :
    ∃ χ : G →* ℂ, (∀ g, ‖χ g‖ = 1) ∧
      ∀ t g, toEuclideanLin (U g) (v t) = χ g • v t := by
  let c : G → ℂ := fun g =>
    inner ℂ (v t₀) (toEuclideanLin (U g) (v t₀)) / inner ℂ (v t₀) (v t₀)
  have hcov (t : T) (g : G) : toEuclideanLin (U g) (v t) = c g • v t := by
    rw [eigenvector_of_mem_span_singleton (U g) (v t) (hne t) (hline t g),
      eigenvalue_constant_of_continuous_invariant_line (U g) v hv hne
        (fun t => hline t g) t t₀]
  let χ : G →* ℂ :=
    { toFun := c
      map_one' := by
        apply smul_left_injective ℂ (hne t₀)
        simpa only [map_one, toLpLin_one, LinearMap.id_apply, one_smul] using (hcov t₀ 1).symm
      map_mul' := by
        intro g h
        apply smul_left_injective ℂ (hne t₀)
        calc
          c (g * h) • v t₀ = toEuclideanLin (U (g * h)) (v t₀) := (hcov t₀ (g * h)).symm
          _ = toEuclideanLin (U g) (toEuclideanLin (U h) (v t₀)) := by
            simp only [map_mul, toLpLin_mul_same, LinearMap.comp_apply]
          _ = c h • (c g • v t₀) := by rw [hcov t₀ h, map_smul, hcov t₀ g]
          _ = (c g * c h) • v t₀ := by rw [smul_smul, mul_comm] }
  refine ⟨χ, ?_, hcov⟩
  intro g
  have hspec : c g ∈ spectrum ℂ (U g) := by
    rw [← spectrum_toLpLin (A := U g) 2]
    exact (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr (hcov t₀ g), hne t₀⟩).mem_spectrum
  exact spectrum.norm_eq_one_of_unitary (hU g) hspec

end Matrix

end

section

open scoped Matrix

namespace LinearMap

/-- Equality of vector spans transfers a scalar eigenvalue. Source context:
arXiv:1010.3732, Appendix B, lines 2614–2632. -/
theorem map_eq_smul_of_span_singleton_eq
    {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : M →ₗ[ℂ] M) (x y : M) (c : ℂ)
    (hspan : Submodule.span ℂ {x} = Submodule.span ℂ {y}) (hx : f x = c • x) :
    f y = c • y := by
  have hy : y ∈ Submodule.span ℂ {x} := by
    rw [hspan]
    exact Submodule.mem_span_singleton_self y
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hy
  rw [← ha, map_smul, hx, smul_comm]

end LinearMap

end
