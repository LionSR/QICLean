/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.MergeDimensions
import QICLean.Representation.CommutantDimension

/-!
# Conditional merge probabilities and the merge moment

This file completes part 3 of Lemma 6.1 (`lem:schur`) of the area-law paper
(*A two-dimensional area law from a global spectral gap*, `05-replicas.tex`,
lines 112–115, proof lines 189–201). For a state invariant under the copy permutations of
`Q` and of `E` separately (in particular for a tensor product of permutation-invariant
density matrices on `Q^{⊗k}` and `E^{⊗k}`), the conditional probability of the label `ν`
on `QE` given the labels `λ, μ` is at most `m_ν d_ν / (d_λ d_μ)`, where the multiplicity
`m_ν ≤ (k+1)^{q²}` with `q = d_Q d_E`; consequently, for `0 ≤ b ≤ 1`,
`E (d_λ d_μ / d_ν)^b ≤ (k+1)^{q²}`.

## Method

Write `P = π^λ π^μ`. For every matrix `ρ` commuting with both actions and every product
`Y = U_Q(σ) U_E(τ) P`, `Tr(ρ Y) tr P = Tr(ρ P) tr Y`: in the matrix units of the two
blocks, `Tr(ρ A_{ij} B_{ab}) = δ_{ij} δ_{ab} Tr(ρ A_{00} B_{00})`. Hence the conditional
probability of `ν` is `tr(π^ν P) / tr P`, with `tr P ≥ d_λ d_μ` when `P ≠ 0` and
`tr(π^ν P) ≤ tr π^ν = d_ν m_ν`.

## Main declarations

* `PermutationRepresentation.trace_mul_trace_eq` — the trace factorization.
* `PermutationRepresentation.merge_conditional_le` — the conditional probability bound.
* `TensorPower.merge_moment_le` — **Lemma 6.1(3)**, the merge moment.
-/

open MonoidAlgebra Matrix Module
open scoped ComplexOrder

namespace PermutationRepresentation

variable {G H X : Type*} [Group G] [Fintype G] [Group H] [Fintype H] [Fintype X]
  [DecidableEq X]

/-- A permutation operator times a label projector, in the matrix units of the block. -/
theorem permOp_mul_labelProj (φ : G →* Equiv.Perm X) (g : G) (l : IrrepLabel G) :
    permOp φ g * labelProj φ l =
      ∑ j, ∑ p, IrrepLabel.wedderburnEquiv G (single g 1) l p j • matrixUnitOp φ l p j := by
  rw [← sum_matrixUnitOp_diag, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => permOp_mul_matrixUnitOp φ g l j j

variable {φ₁ : G →* Equiv.Perm X} {φ₂ : H →* Equiv.Perm X}

variable (φ₁ φ₂) in
/-- The joint matrix units `E_{(i,a),(j,b)} = A_{ij} B_{ab}` of two commuting actions. -/
noncomputable def pairUnit (α : IrrepLabel G) (β : IrrepLabel H)
    (x y : Fin α.dim × Fin β.dim) : Matrix X X ℂ :=
  matrixUnitOp φ₁ α x.1 y.1 * matrixUnitOp φ₂ β x.2 y.2

variable (hcomm : ∀ g h, Commute (φ₁ g) (φ₂ h))
include hcomm

theorem pairUnit_mul_pairUnit (α : IrrepLabel G) (β : IrrepLabel H)
    (x y y' z : Fin α.dim × Fin β.dim) :
    pairUnit φ₁ φ₂ α β x y * pairUnit φ₁ φ₂ α β y' z =
      if y = y' then pairUnit φ₁ φ₂ α β x z else 0 := by
  simp only [pairUnit]
  rw [mul_assoc, ← mul_assoc (matrixUnitOp φ₂ β x.2 y.2),
    ← (commute_matrixUnitOp_pair hcomm α β y'.1 z.1 x.2 y.2).eq, mul_assoc, ← mul_assoc,
    matrixUnitOp_mul_matrixUnitOp, matrixUnitOp_mul_matrixUnitOp]
  by_cases h1 : y.1 = y'.1 <;> by_cases h2 : y.2 = y'.2 <;> simp [h1, h2, Prod.ext_iff]

theorem pairUnit_mul_pairUnit_self (α : IrrepLabel G) (β : IrrepLabel H)
    (x y z : Fin α.dim × Fin β.dim) :
    pairUnit φ₁ φ₂ α β x y * pairUnit φ₁ φ₂ α β y z = pairUnit φ₁ φ₂ α β x z := by
  simp [pairUnit_mul_pairUnit hcomm]

omit hcomm in
theorem commute_pairUnit {M : Matrix X X ℂ} (hM₁ : ∀ g, Commute (permOp φ₁ g) M)
    (hM₂ : ∀ h, Commute (permOp φ₂ h) M) (α : IrrepLabel G) (β : IrrepLabel H)
    (x y : Fin α.dim × Fin β.dim) : Commute (pairUnit φ₁ φ₂ α β x y) M :=
  (commute_groupAlgebraRep_of_forall_commute φ₁ hM₁ _).mul_left
    (commute_groupAlgebraRep_of_forall_commute φ₂ hM₂ _)

/-- In the joint matrix units, the trace against an operator commuting with both actions
only sees the diagonal. -/
theorem trace_mul_pairUnit {M : Matrix X X ℂ} (hM₁ : ∀ g, Commute (permOp φ₁ g) M)
    (hM₂ : ∀ h, Commute (permOp φ₂ h) M) (α : IrrepLabel G) (β : IrrepLabel H)
    (x y : Fin α.dim × Fin β.dim) :
    (M * pairUnit φ₁ φ₂ α β x y).trace =
      if x = y then (M * pairUnit φ₁ φ₂ α β (⟨0, α.dim_pos⟩, ⟨0, β.dim_pos⟩)
        (⟨0, α.dim_pos⟩, ⟨0, β.dim_pos⟩)).trace else 0 := by
  set o : Fin α.dim × Fin β.dim := (⟨0, α.dim_pos⟩, ⟨0, β.dim_pos⟩)
  rw [← pairUnit_mul_pairUnit_self hcomm α β x o y, ← mul_assoc, trace_mul_comm, ← mul_assoc,
    (commute_pairUnit hM₁ hM₂ α β o y).eq, mul_assoc, pairUnit_mul_pairUnit hcomm]
  by_cases h : y = x
  · subst h; simp
  · simp [h, Ne.symm h]

/-- The joint span of the matrix units. -/
noncomputable def pairUnitSpan (α : IrrepLabel G) (β : IrrepLabel H) :
    Submodule ℂ (Matrix X X ℂ) :=
  Submodule.span ℂ (Set.range fun xy : (Fin α.dim × Fin β.dim) × (Fin α.dim × Fin β.dim) =>
    pairUnit φ₁ φ₂ α β xy.1 xy.2)

omit hcomm in
theorem pairUnit_mem_pairUnitSpan (α : IrrepLabel G) (β : IrrepLabel H)
    (x y : Fin α.dim × Fin β.dim) :
    pairUnit φ₁ φ₂ α β x y ∈ pairUnitSpan (φ₁ := φ₁) (φ₂ := φ₂) α β :=
  Submodule.subset_span ⟨(x, y), rfl⟩

/-- On the joint span, the trace against a commuting operator factors through a coefficient
that does not depend on the operator. -/
theorem exists_trace_mul_eq {Z : Matrix X X ℂ} (α : IrrepLabel G) (β : IrrepLabel H)
    (hZ : Z ∈ pairUnitSpan (φ₁ := φ₁) (φ₂ := φ₂) α β) :
    ∃ κ : ℂ, ∀ M : Matrix X X ℂ, (∀ g, Commute (permOp φ₁ g) M) →
      (∀ h, Commute (permOp φ₂ h) M) →
      (M * Z).trace = κ * (M * pairUnit φ₁ φ₂ α β (⟨0, α.dim_pos⟩, ⟨0, β.dim_pos⟩)
        (⟨0, α.dim_pos⟩, ⟨0, β.dim_pos⟩)).trace := by
  refine Submodule.span_induction (fun Y hY => ?_) ⟨0, fun M _ _ => by simp⟩
    (fun Y Y' _ _ ⟨κ, hκ⟩ ⟨κ', hκ'⟩ => ⟨κ + κ', fun M h1 h2 => by
      rw [mul_add, trace_add, hκ M h1 h2, hκ' M h1 h2, add_mul]⟩)
    (fun c Y _ ⟨κ, hκ⟩ => ⟨c * κ, fun M h1 h2 => by
      rw [mul_smul_comm, trace_smul, hκ M h1 h2, smul_eq_mul, mul_assoc]⟩) hZ
  obtain ⟨⟨x, y⟩, rfl⟩ := hY
  exact ⟨if x = y then 1 else 0, fun M h1 h2 => by
    rw [trace_mul_pairUnit hcomm h1 h2]; split_ifs <;> simp⟩

omit hcomm in
theorem labelProj_mul_labelProj_eq_sum (α : IrrepLabel G) (β : IrrepLabel H) :
    labelProj φ₁ α * labelProj φ₂ β = ∑ x, pairUnit φ₁ φ₂ α β x x := by
  rw [← sum_matrixUnitOp_diag, ← sum_matrixUnitOp_diag, Finset.sum_mul, Fintype.sum_prod_type]
  simp only [Finset.mul_sum, pairUnit]

theorem permOp_mul_permOp_mul_pairUnit_mem (α : IrrepLabel G) (β : IrrepLabel H) (g : G)
    (h : H) (x : Fin α.dim × Fin β.dim) :
    permOp φ₁ g * permOp φ₂ h * pairUnit φ₁ φ₂ α β x x ∈
      pairUnitSpan (φ₁ := φ₁) (φ₂ := φ₂) α β := by
  have hc : Commute (permOp φ₂ h) (matrixUnitOp φ₁ α x.1 x.1) := by
    rw [matrixUnitOp]
    simpa using (commute_groupAlgebraRep_of_commute φ₁ φ₂ hcomm _ (single h 1)).symm
  have e : permOp φ₁ g * permOp φ₂ h * pairUnit φ₁ φ₂ α β x x =
      (permOp φ₁ g * matrixUnitOp φ₁ α x.1 x.1) * (permOp φ₂ h * matrixUnitOp φ₂ β x.2 x.2) := by
    simp only [pairUnit, mul_assoc]
    rw [← mul_assoc (permOp φ₂ h), hc.eq, mul_assoc]
  rw [e, permOp_mul_matrixUnitOp, permOp_mul_matrixUnitOp, Finset.sum_mul]
  refine Submodule.sum_mem _ fun p _ => ?_
  rw [Finset.mul_sum]
  refine Submodule.sum_mem _ fun q _ => ?_
  rw [smul_mul_assoc, mul_smul_comm]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
    (pairUnit_mem_pairUnitSpan (φ₁ := φ₁) (φ₂ := φ₂) α β (p, q) x))

/-- **Trace factorization.** For `ρ` commuting with both actions, `P = π^α π^β` and `Z`
in the joint span, `Tr(ρ Z) · tr P = Tr(ρ P) · tr Z`. -/
theorem trace_mul_trace_eq {ρ : Matrix X X ℂ}
    (hρ₁ : ∀ g, Commute (permOp φ₁ g) ρ) (hρ₂ : ∀ h, Commute (permOp φ₂ h) ρ)
    (α : IrrepLabel G) (β : IrrepLabel H) {Z : Matrix X X ℂ}
    (hZ : Z ∈ pairUnitSpan (φ₁ := φ₁) (φ₂ := φ₂) α β) :
    (ρ * Z).trace * (labelProj φ₁ α * labelProj φ₂ β).trace =
      (ρ * (labelProj φ₁ α * labelProj φ₂ β)).trace * Z.trace := by
  have h1 : ∀ g, Commute (permOp φ₁ g) (1 : Matrix X X ℂ) := fun _ => Commute.one_right _
  have h2 : ∀ h, Commute (permOp φ₂ h) (1 : Matrix X X ℂ) := fun _ => Commute.one_right _
  have hP : labelProj φ₁ α * labelProj φ₂ β ∈ pairUnitSpan (φ₁ := φ₁) (φ₂ := φ₂) α β := by
    rw [labelProj_mul_labelProj_eq_sum]
    exact Submodule.sum_mem _ fun x _ => pairUnit_mem_pairUnitSpan α β x x
  obtain ⟨κ, hκ⟩ := exists_trace_mul_eq hcomm α β hZ
  obtain ⟨κP, hκP⟩ := exists_trace_mul_eq hcomm α β hP
  have e1 := hκ ρ hρ₁ hρ₂
  have e2 := hκ 1 h1 h2
  have e3 := hκP ρ hρ₁ hρ₂
  have e4 := hκP 1 h1 h2
  rw [one_mul] at e2 e4
  rw [one_mul] at e2 e4
  rw [e1, e2, e3, e4]
  ring

end PermutationRepresentation

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]

omit [Fintype G] [DecidableEq X] in
theorem isHermitian_mul_of_commute {A B : Matrix X X ℂ} (hAB : Commute A B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) : (A * B).IsHermitian := by
  rw [IsHermitian, conjTranspose_mul, hA.eq, hB.eq, hAB.eq]

omit [Fintype G] [DecidableEq X] in
theorem re_trace_mul_nonneg {ρ E : Matrix X X ℂ} (hρ : ρ.PosSemidef) (hE : E.IsHermitian)
    (hEE : E * E = E) : 0 ≤ (ρ * E).trace.re := by
  have h : (ρ * E).trace = (Eᴴ * ρ * E).trace := by
    calc (ρ * E).trace = (ρ * (E * E)).trace := by rw [hEE]
      _ = (Eᴴ * ρ * E).trace := by
        rw [hE.eq, ← mul_assoc, trace_mul_comm, ← mul_assoc]
  rw [h]
  exact (Complex.nonneg_iff.mp ((hρ.conjTranspose_mul_mul_same E).trace_nonneg)).1

variable {φQ φE φQE : G →* Equiv.Perm X}

/-- **Conditional merge probability** (`05-replicas.tex`, lines 112–113, 189–197). Let `ρ` be
positive semidefinite and invariant under the copy permutations of `Q` and of `E`. Then
`Tr(ρ π^λ π^μ π^ν) d_λ d_μ ≤ m_ν d_ν Tr(ρ π^λ π^μ)`: the conditional probability of `ν`
given `λ, μ` is at most `m_ν d_ν / (d_λ d_μ)`. -/
theorem merge_conditional_le (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef)
    (hρQ : ∀ g, Commute (permOp φQ g) ρ) (hρE : ∀ g, Commute (permOp φE g) ρ)
    (l μ ν : IrrepLabel G) :
    (ρ * (labelProj φQ l * labelProj φE μ * labelProj φQE ν)).trace.re * (l.dim * μ.dim) ≤
      multiplicity φQE ν * ν.dim *
        (ρ * (labelProj φQ l * labelProj φE μ)).trace.re := by
  have hprod' : ∀ g, φQE g = φE g * φQ g := fun g => by rw [hprod, (hcomm g g).eq]
  have hνl : Commute (labelProj φQ l) (labelProj φQE ν) :=
    commute_groupAlgebraRep_of_eq_mul φQ φE φQE hprod hcomm
      (IrrepLabel.centralIdem_mem_center l) _
  have hνμ : Commute (labelProj φE μ) (labelProj φQE ν) :=
    commute_groupAlgebraRep_of_eq_mul φE φQ φQE hprod'
      (fun g h => (hcomm h g).symm) (IrrepLabel.centralIdem_mem_center μ) _
  have hlμ : Commute (labelProj φQ l) (labelProj φE μ) :=
    commute_groupAlgebraRep_of_commute φQ φE hcomm _ _
  set P := labelProj φQ l * labelProj φE μ
  have hPν : Commute P (labelProj φQE ν) := hνl.mul_left hνμ
  have hPP : P * P = P := by
    simp only [P]
    rw [mul_assoc, ← mul_assoc (labelProj φE μ), ← hlμ.eq, mul_assoc, labelProj_mul_self,
      ← mul_assoc, labelProj_mul_self]
  have hPH : P.IsHermitian :=
    isHermitian_mul_of_commute hlμ (isHermitian_labelProj _ _) (isHermitian_labelProj _ _)
  set Z := labelProj φQE ν * P
  have hZeq : labelProj φQ l * labelProj φE μ * labelProj φQE ν = Z := hPν.eq
  rw [hZeq]
  have hZZ : Z * Z = Z := by
    simp only [Z]
    rw [mul_assoc, ← mul_assoc P, hPν.eq, mul_assoc, hPP, ← mul_assoc, labelProj_mul_self]
  have hZH : Z.IsHermitian :=
    isHermitian_mul_of_commute hPν.symm (isHermitian_labelProj _ _) hPH
  have hZ0 := re_trace_mul_nonneg hρ hZH hZZ
  have hP0 := re_trace_mul_nonneg hρ hPH hPP
  -- `Z` lies in the joint span.
  have hZspan : Z ∈ pairUnitSpan (φ₁ := φQ) (φ₂ := φE) l μ := by
    have e : labelProj φQE ν =
        ∑ σ, (IrrepLabel.centralIdem ν).coeff σ • permOp φQE σ := by
      rw [labelProj, groupAlgebraRep_eq_sum]
    simp only [Z, P]
    rw [e, labelProj_mul_labelProj_eq_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [smul_mul_assoc, Finset.mul_sum, permOp_of_eq_mul φQ φE φQE hprod σ]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun x _ =>
      permOp_mul_permOp_mul_pairUnit_mem hcomm l μ σ σ x)
  have hfact := trace_mul_trace_eq hcomm hρQ hρE l μ hZspan
  rw [trace_eq_finrank_range_of_mul_self hPP, trace_eq_finrank_range_of_mul_self hZZ] at hfact
  have hre := congrArg Complex.re hfact
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero] at hre
  -- `tr Z ≤ d_ν m_ν`.
  have hZle : finrank ℂ (LinearMap.range (toLin' Z)) ≤ ν.dim * multiplicity φQE ν := by
    have h1 : finrank ℂ (LinearMap.range (toLin' Z)) ≤
        finrank ℂ (LinearMap.range (toLin' (labelProj φQE ν))) := by
      apply Submodule.finrank_mono
      rintro _ ⟨v, rfl⟩
      exact ⟨P *ᵥ v, by simp [Z, mulVec_mulVec]⟩
    have h2 := trace_labelProj φQE ν
    rw [trace_eq_finrank_range_of_mul_self (labelProj_mul_self _ _)] at h2
    exact h1.trans (le_of_eq (by exact_mod_cast h2))
  by_cases hP : P = 0
  · have : Z = 0 := by simp [Z, hP]
    rw [this, mul_zero, trace_zero, Complex.zero_re, zero_mul]
    exact mul_nonneg (by positivity) hP0
  -- `tr P ≥ d_λ d_μ`.
  have hPge : l.dim * μ.dim ≤ finrank ℂ (LinearMap.range (toLin' P)) := by
    refine mul_dim_le_finrank_of_invariant hcomm l μ (fun g w hw => ?_) (fun g w hw => ?_)
      (fun w hw => ?_) (fun w hw => ?_) ?_
    · obtain ⟨v, rfl⟩ := hw
      refine ⟨permOp φQ g *ᵥ v, ?_⟩
      have h' : Commute (permOp φQ g) (labelProj φE μ) := by
        rw [labelProj]
        simpa using commute_groupAlgebraRep_of_commute φQ φE hcomm
          (single g 1) (IrrepLabel.centralIdem μ)
      have : Commute (permOp φQ g) P := (commute_labelProj_permOp φQ l g).symm.mul_right h'
      simp [mulVec_mulVec, this.eq]
    · obtain ⟨v, rfl⟩ := hw
      refine ⟨permOp φE g *ᵥ v, ?_⟩
      have h' : Commute (permOp φE g) (labelProj φQ l) := by
        rw [labelProj]
        simpa using (commute_groupAlgebraRep_of_commute φQ φE hcomm
          (IrrepLabel.centralIdem l) (single g 1)).symm
      have : Commute (permOp φE g) P := h'.mul_right (commute_labelProj_permOp φE μ g).symm
      simp [mulVec_mulVec, this.eq]
    · obtain ⟨v, rfl⟩ := hw
      simp only [toLin'_apply, mulVec_mulVec, P, ← mul_assoc, labelProj_mul_self]
    · obtain ⟨v, rfl⟩ := hw
      simp only [toLin'_apply, mulVec_mulVec, P]
      rw [← mul_assoc, ← hlμ.eq, mul_assoc, labelProj_mul_self, hlμ.eq]
    · rw [Ne, LinearMap.range_eq_bot, ← map_zero toLin', toLin'.injective.eq_iff]
      exact hP
  calc (ρ * Z).trace.re * (l.dim * μ.dim)
      ≤ (ρ * Z).trace.re * finrank ℂ (LinearMap.range (toLin' P)) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hPge) hZ0
    _ = (ρ * P).trace.re * finrank ℂ (LinearMap.range (toLin' Z)) := hre
    _ ≤ (ρ * P).trace.re * (ν.dim * multiplicity φQE ν) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hZle) hP0
    _ = multiplicity φQE ν * ν.dim * (ρ * P).trace.re := by ring

/-- The merge probability `Tr(ρ π^λ π^μ π^ν)` of a positive semidefinite `ρ` is
nonnegative. -/
theorem re_trace_merge_nonneg (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef)
    (l μ ν : IrrepLabel G) :
    0 ≤ (ρ * (labelProj φQ l * labelProj φE μ * labelProj φQE ν)).trace.re := by
  have hprod' : ∀ g, φQE g = φE g * φQ g := fun g => by rw [hprod, (hcomm g g).eq]
  have hνl : Commute (labelProj φQ l) (labelProj φQE ν) :=
    commute_groupAlgebraRep_of_eq_mul φQ φE φQE hprod hcomm
      (IrrepLabel.centralIdem_mem_center l) _
  have hνμ : Commute (labelProj φE μ) (labelProj φQE ν) :=
    commute_groupAlgebraRep_of_eq_mul φE φQ φQE hprod'
      (fun g h => (hcomm h g).symm) (IrrepLabel.centralIdem_mem_center μ) _
  have hlμ : Commute (labelProj φQ l) (labelProj φE μ) :=
    commute_groupAlgebraRep_of_commute φQ φE hcomm _ _
  have hPP : labelProj φQ l * labelProj φE μ * (labelProj φQ l * labelProj φE μ) =
      labelProj φQ l * labelProj φE μ := by
    rw [mul_assoc, ← mul_assoc (labelProj φE μ), ← hlμ.eq, mul_assoc, labelProj_mul_self,
      ← mul_assoc, labelProj_mul_self]
  have hPν := hνl.mul_left hνμ
  refine re_trace_mul_nonneg hρ (isHermitian_mul_of_commute hPν
    (isHermitian_mul_of_commute hlμ (isHermitian_labelProj _ _) (isHermitian_labelProj _ _))
    (isHermitian_labelProj _ _)) ?_
  generalize labelProj φQ l * labelProj φE μ = P at hPP hPν ⊢
  rw [mul_assoc, ← mul_assoc (labelProj φQE ν), ← hPν.eq, mul_assoc, labelProj_mul_self,
    ← mul_assoc, hPP]

/-- **Merge moment, general form** (`05-replicas.tex`, lines 113–115, 197–201). For a
density matrix `ρ` invariant under the copy permutations of `Q` and of `E` and `b ≤ 1`,
`∑_{λ,μ,ν} Tr(ρ π^λ π^μ π^ν) (d_λ d_μ / d_ν)^b ≤ ∑_ν m_ν`. -/
theorem merge_moment_le_sum_multiplicity (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) {ρ : Matrix X X ℂ} (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (hρQ : ∀ g, Commute (permOp φQ g) ρ)
    (hρE : ∀ g, Commute (permOp φE g) ρ) {b : ℝ} (hb : b ≤ 1) :
    ∑ l, ∑ μ, ∑ ν, (ρ * (labelProj φQ l * labelProj φE μ * labelProj φQE ν)).trace.re *
        (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b ≤ ∑ ν, (multiplicity φQE ν : ℝ) := by
  have hterm : ∀ l μ ν,
      (ρ * (labelProj φQ l * labelProj φE μ * labelProj φQE ν)).trace.re *
          (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b ≤
        multiplicity φQE ν * (ρ * (labelProj φQ l * labelProj φE μ)).trace.re := by
    intro l μ ν
    have hp := re_trace_merge_nonneg hcomm hprod hρ l μ ν
    have hd : (0 : ℝ) < ν.dim := by exact_mod_cast ν.dim_pos
    have hcond := merge_conditional_le hcomm hprod hρ hρQ hρE l μ ν
    by_cases h0 : labelProj φQ l * labelProj φE μ * labelProj φQE ν = 0
    · rw [h0, mul_zero, trace_zero, Complex.zero_re, zero_mul]
      have := re_trace_merge_nonneg hcomm hprod hρ l μ ν
      have hq : 0 ≤ (ρ * (labelProj φQ l * labelProj φE μ)).trace.re := by
        have hlμ : Commute (labelProj φQ l) (labelProj φE μ) :=
          commute_groupAlgebraRep_of_commute φQ φE hcomm _ _
        refine re_trace_mul_nonneg hρ (isHermitian_mul_of_commute hlμ
          (isHermitian_labelProj _ _) (isHermitian_labelProj _ _)) ?_
        rw [mul_assoc, ← mul_assoc (labelProj φE μ), ← hlμ.eq, mul_assoc, labelProj_mul_self,
          ← mul_assoc, labelProj_mul_self]
      positivity
    have hcompat := dim_le_mul_dim_of_compatible hcomm hprod h0
    have hR1 : (1 : ℝ) ≤ ((l.dim * μ.dim : ℕ) : ℝ) / ν.dim := by
      rw [one_le_div hd]; exact_mod_cast hcompat
    calc _ ≤ (ρ * (labelProj φQ l * labelProj φE μ * labelProj φQE ν)).trace.re *
            (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) := by
          refine mul_le_mul_of_nonneg_left ?_ hp
          simpa using Real.rpow_le_rpow_of_exponent_le hR1 hb
      _ ≤ _ := by
          rw [← mul_div_assoc, div_le_iff₀ hd]
          push_cast
          linarith
  calc _ ≤ ∑ l, ∑ μ, ∑ ν, (multiplicity φQE ν : ℝ) *
        (ρ * (labelProj φQ l * labelProj φE μ)).trace.re :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun μ _ =>
          Finset.sum_le_sum fun ν _ => hterm l μ ν
    _ = (∑ ν, (multiplicity φQE ν : ℝ)) *
          (ρ * ∑ l, ∑ μ, labelProj φQ l * labelProj φE μ).trace.re := by
        simp only [← Finset.sum_mul, Finset.mul_sum, trace_sum, Complex.re_sum]
    _ = ∑ ν, (multiplicity φQE ν : ℝ) := by
        simp_rw [← Finset.mul_sum, sum_labelProj, ← Finset.sum_mul, sum_labelProj, one_mul,
          mul_one, htr, Complex.one_re, mul_one]

end PermutationRepresentation

namespace TensorPower

open PermutationRepresentation

variable {F : Type*} [Fintype F] [DecidableEq F] {ι : F → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {k : ℕ}

omit [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)] in
theorem copyPerm_eq_mul_compl (Q : Finset F) (σ : Equiv.Perm (Fin k)) :
    copyPerm ((f : F) → ι f) k σ = subsystemPerm k ι Q σ * subsystemPerm k ι Qᶜ σ := by
  rw [← subsystemPerm_univ, ← Finset.union_compl Q]
  exact subsystemPerm_union k ι disjoint_compl_right σ

/-- **Lemma 6.1(3), conditional merge probability** (`05-replicas.tex`, lines 112–113).
Let `V = Q ⊗ E` with `E = Qᶜ`, `q = dim V`, and let `ρ` be a density matrix on `V^{⊗k}`
invariant under the copy permutations of `Q` and of `E` (for instance a tensor product of
permutation-invariant density matrices on `Q^{⊗k}` and `E^{⊗k}`). Then the conditional
probability of the label `ν` on `QE` given `λ, μ` is at most `(k+1)^{q²} d_ν / (d_λ d_μ)`:
`Tr(ρ π^λ π^μ π^ν) d_λ d_μ ≤ (k+1)^{q²} d_ν Tr(ρ π^λ π^μ)`. -/
theorem merge_conditional_le (Q : Finset F) {ρ : Matrix (Config k ι) (Config k ι) ℂ}
    (hρ : ρ.PosSemidef) (hρQ : ∀ σ, Commute (permOp (subsystemPerm k ι Q) σ) ρ)
    (hρE : ∀ σ, Commute (permOp (subsystemPerm k ι Qᶜ) σ) ρ)
    (l μ ν : IrrepLabel (Equiv.Perm (Fin k))) :
    (ρ * (labelProj (subsystemPerm k ι Q) l * labelProj (subsystemPerm k ι Qᶜ) μ *
        labelProj (copyPerm ((f : F) → ι f) k) ν)).trace.re * (l.dim * μ.dim) ≤
      ((k + 1) ^ (Fintype.card ((f : F) → ι f) ^ 2) : ℕ) * ν.dim *
        (ρ * (labelProj (subsystemPerm k ι Q) l *
          labelProj (subsystemPerm k ι Qᶜ) μ)).trace.re := by
  have hcomm := commute_subsystemPerm_of_disjoint k ι (disjoint_compl_right (a := Q))
  have h := PermutationRepresentation.merge_conditional_le hcomm (copyPerm_eq_mul_compl Q)
    hρ hρQ hρE l μ ν
  refine h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
    (re_trace_mul_nonneg hρ (isHermitian_mul_of_commute
      (commute_groupAlgebraRep_of_commute _ _ hcomm _ _) (isHermitian_labelProj _ _)
      (isHermitian_labelProj _ _)) ?_))
  · have hle : multiplicity (copyPerm ((f : F) → ι f) k) ν ≤
        ∑ ν', multiplicity (copyPerm ((f : F) → ι f) k) ν' :=
      Finset.single_le_sum (f := fun ν' => multiplicity (copyPerm ((f : F) → ι f) k) ν')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)
    exact_mod_cast hle.trans (sum_multiplicity_le _ k)
  · have hlμ : Commute (labelProj (subsystemPerm k ι Q) l)
        (labelProj (subsystemPerm k ι Qᶜ) μ) :=
      commute_groupAlgebraRep_of_commute _ _ hcomm _ _
    rw [mul_assoc, ← mul_assoc (labelProj _ μ), ← hlμ.eq, mul_assoc, labelProj_mul_self,
      ← mul_assoc, labelProj_mul_self]

/-- **Lemma 6.1(3), merge moment** (`05-replicas.tex`, lines 113–115, equation
`replicas:merge-moment`). With `ρ` as in `merge_conditional_le` and `0 ≤ b ≤ 1` (indeed
every `b ≤ 1`), `E (d_λ d_μ / d_ν)^b ≤ (k+1)^{q²}`, uniformly in `ρ`. -/
theorem merge_moment_le (Q : Finset F) {ρ : Matrix (Config k ι) (Config k ι) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hρQ : ∀ σ, Commute (permOp (subsystemPerm k ι Q) σ) ρ)
    (hρE : ∀ σ, Commute (permOp (subsystemPerm k ι Qᶜ) σ) ρ) {b : ℝ} (hb : b ≤ 1) :
    ∑ l, ∑ μ, ∑ ν, (ρ * (labelProj (subsystemPerm k ι Q) l *
        labelProj (subsystemPerm k ι Qᶜ) μ * labelProj (copyPerm ((f : F) → ι f) k) ν)).trace.re *
        (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b ≤
      ((k + 1) ^ (Fintype.card ((f : F) → ι f) ^ 2) : ℕ) := by
  have hcomm := commute_subsystemPerm_of_disjoint k ι (disjoint_compl_right (a := Q))
  refine (merge_moment_le_sum_multiplicity hcomm (copyPerm_eq_mul_compl Q) hρ htr hρQ hρE
    hb).trans ?_
  exact_mod_cast sum_multiplicity_le _ k

end TensorPower
