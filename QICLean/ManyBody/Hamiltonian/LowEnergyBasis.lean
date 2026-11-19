/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Complex.Module
import QICLean.Analysis.LowEnergyBasis.SpectralSplit
import QICLean.Analysis.LowEnergyBasis.Construction
import QICLean.ManyBody.Hamiltonian.LowEnergyCommutatorSum

/-!
# A ground-space basis with summable off-diagonal parts

Hastings, arXiv:cond-mat/0508554v3, lines 1678–1708, chooses a basis of the ground space in
which the compressions of the filtered terms have summable off-diagonal parts. The basis
constructions themselves are in `Analysis/LowEnergyBasis/Construction`.

* `groundSpaceCompression`: the compression of a matrix to the ground space, as
  `subspaceCompression`.
* `exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le`: eq. `oibu` with the condition
  number of the commutator map.
* `exists_twoDimensional_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le`: a
  two-dimensional ground space.

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyBasisConstruction.lean`,
`LowEnergyBasisTwoDimensional.lean` and `LowEnergyBasisUniform.lean`, their Hamiltonian parts.
Changes as in `LowEnergyCommutator`.
-/

noncomputable section

open LowEnergyBasis
open scoped InnerProductSpace

namespace ManyBody


noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) :
    InnerProductSpace ℂ (groundSpace H E₀) :=
  (groundSpace H E₀).innerProductSpace

section GroundSpace

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

variable {ν : Type*} [Fintype ν] [DecidableEq ν]

local instance (H : Matrix ν ν ℂ) (E₀ : ℝ) : CompleteSpace (groundSpace H E₀) :=
  FiniteDimensional.complete ℂ (groundSpace H E₀)

/-- The compression `P W P` of `W` to the ground eigenspace, acting on that eigenspace.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1678–1708. -/
noncomputable abbrev groundSpaceCompression (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ) :
    groundSpace H E₀ →L[ℂ] groundSpace H E₀ :=
  subspaceCompression (groundSpace H E₀) (toEuclideanCLM (n := ν) (𝕜 := ℂ) W)

@[simp]
theorem coe_groundSpaceCompression_apply (H : Matrix ν ν ℂ) (E₀ : ℝ) (W : Matrix ν ν ℂ)
    (x : groundSpace H E₀) :
    (groundSpaceCompression H E₀ W x : EuclideanSpace ℂ ν) = groundCompression H E₀ W x := by
  simp [coe_subspaceCompression_apply, groundCompression, mul_apply_eq_comp,
    (groundSpace H E₀).starProjection_eq_self_iff.mpr x.2]

end GroundSpace

section Graph

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]

/-- A constructed orthonormal basis of the nonzero ground space satisfies a summed
off-diagonal estimate using at most `n²` local terms. The geometric constant is that
of the commutator row sum, and the additional factor is the explicitly displayed quotient
conditioning of the selected ground-space commutator map, which may depend on the system
size. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu` and lines 1695–1708. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE) :
    let B : κ → groundSpace Φ.hamiltonian E₀ →L[ℂ]
        groundSpace Φ.hamiltonian E₀ :=
      fun i => groundSpaceCompression Φ.hamiltonian E₀ (Φ.term i)
    haveI : NeZero (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)) :=
      ⟨fun h0 ↦ hgap.1 (Submodule.finrank_eq_zero.mp h0)⟩
    ∃ (m : ℕ) (j : Fin m → κ)
      (b : OrthonormalBasis
        (Fin (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀))) ℂ
          (groundSpace Φ.hamiltonian E₀)),
      m ≤ (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)) ^ 2 ∧
      ∑ i, ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i)))‖ ≤
        (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀) - 1 : ℕ) *
          compressionConditionNumber (realCompressionSpan B) (B ∘ j) *
          ∑ k, commutatorConst R vR b₀ Kg kg *
            Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1)) * ‖Φ.term (j k)‖ *
              (|b₀| * (Kg * Real.shellSumConst (commutatorRate R vR b₀ ΔE) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have : NeZero (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)) :=
    ⟨fun h0 ↦ hgap.1 (Submodule.finrank_eq_zero.mp h0)⟩
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let K := groundSpace Φ.hamiltonian E₀
  let B := fun i => groundSpaceCompression Φ.hamiltonian E₀ (Φ.term i)
  obtain ⟨m, j, b, hm, _, hb⟩ := exists_orthonormalBasis_norm_inner_le_commutators B
    (fun i => isSelfAdjoint_subspaceCompression _ _ ((hHerm i).isSelfAdjoint.map toEuclideanCLM))
  refine ⟨m, j, b, hm, ?_⟩
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  let C := compressionConditionNumber (realCompressionSpan B) (B ∘ j)
  have hC : 0 ≤ C := compressionConditionNumber_nonneg _ _
  have hv : Orthonormal ℂ (fun c => (b c : EuclideanSpace ℂ (Config X))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hent (i : κ) :
      ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (Φ.term i))‖ ≤
        (Module.finrank ℂ K - 1 : ℕ) * (C * ∑ k, ‖B (j k) * B i - B i * B (j k)‖) := by
    refine norm_offDiagonalPartFamily_le hv _ (by positivity) fun c e hce => ?_
    have h := hb i c e hce
    rwa [Submodule.coe_inner, coe_groundSpaceCompression_apply] at h
  calc _ ≤ ∑ i, (Module.finrank ℂ K - 1 : ℕ) *
        (C * ∑ k, ‖B (j k) * B i - B i * B (j k)‖) :=
      Finset.sum_le_sum fun i _ => hent i
    _ = (Module.finrank ℂ K - 1 : ℕ) * C *
        ∑ k, ∑ i, ‖B (j k) * B i - B i * B (j k)‖ := by
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) hC)
      refine Finset.sum_le_sum fun k _ => ?_
      refine (Finset.sum_le_sum fun i _ =>
        (norm_subspaceCompression_commutator (groundSpace Φ.hamiltonian E₀) _ _).le).trans ?_
      exact sum_norm_groundCompression_commutator_le G a ha Φ hHerm R hDiam vR
        hCard b₀ hBudget Kg kg hGrowth hΔE hgap (j k)

end Graph




noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) : InnerProductSpace ℂ (groundSpace H E₀) :=
  (groundSpace H E₀).innerProductSpace

section Graph

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]

/-- There is an orthonormal basis of a two-dimensional ground space for which the
sum of the off-diagonal parts is bounded only by the local norm budget, range, gap and
graph growth. The rate is half
the commutator decay rate. This proves the qualitative size independence of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `oibu`, lines 1678–1694, with an explicit
corrected constant; see `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`. -/
theorem exists_twoDimensional_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    (hdim : Module.finrank ℂ (groundSpace Φ.hamiltonian E₀) = 2) :
    ∃ b : OrthonormalBasis (Fin 2) ℂ (groundSpace Φ.hamiltonian E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i)))‖ ≤
        Real.sqrt (commutatorConst R vR b₀ |Kg| kg *
          Real.exp (commutatorRate R vR b₀ ΔE * (2 * R + 1))) *
          (|b₀| * (|Kg| * Real.shellSumConst (commutatorRate R vR b₀ ΔE / 2) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let K := groundSpace Φ.hamiltonian E₀
  let B := fun i => groundSpaceCompression Φ.hamiltonian E₀ (Φ.term i)
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
  have hC : 0 ≤ C := mul_nonneg
    (le_trans (by norm_num) (six_le_commutatorConst R vR b₀ (abs_nonneg Kg) kg))
    (Real.exp_pos _).le
  have hGrow : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r => (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  let f := fun j i => if G.edist (a j) (a i) = ⊤ then 0 else
    Real.exp (-(γ / 2 * ((G.edist (a j) (a i)).toNat : ℝ)))
  have hf (j i : κ) : 0 ≤ f j i := by dsimp only [f]; split_ifs <;> positivity
  have hnorm (i : κ) : ‖B i‖ ≤ ‖Φ.term i‖ := norm_subspaceCompression_le _ _
  have hcomm (i j : κ) : ‖B j * B i - B i * B j‖ ≤ C * ‖Φ.term j‖ * ‖Φ.term i‖ * (f j i) ^ 2 := by
    have heq : (f j i) ^ 2 = if G.edist (a j) (a i) = ⊤ then 0 else
        Real.exp (-(γ * ((G.edist (a j) (a i)).toNat : ℝ))) := by
      dsimp only [f]
      split_ifs
      · simp
      · rw [← Real.exp_nat_mul]
        congr 1
        ring
    rw [heq]
    exact ((norm_subspaceCompression_commutator _ _ _).le).trans
      (norm_groundCompression_commutator_le_exp_edist G a ha Φ hHerm R hDiam vR
        hCard b₀ hBudget |Kg| kg hGrow hΔE hgap i j)
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_norm_inner_le_sqrt_commutator_decay B
    (fun i => isSelfAdjoint_subspaceCompression _ _
      ((hHerm i).isSelfAdjoint.map toEuclideanCLM)) hdim
    (fun i => ‖Φ.term i‖) (fun i => norm_nonneg _) hnorm hC f hf hcomm
  refine ⟨b, ?_⟩
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  have hv : Orthonormal ℂ (fun c => (b c : EuclideanSpace ℂ (Config X))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hbound0 : 0 ≤ Real.sqrt C * (|b₀| * (|Kg| * Real.shellSumConst (γ / 2) kg)) := by
    have := Real.shellSumConst_nonneg (show 0 < γ / 2 by positivity) kg
    positivity
  rcases hb with hzero | ⟨j, hb⟩
  · refine (show ∑ i, ‖offDiagonalPartFamily _ _‖ ≤ 0 from ?_).trans hbound0
    apply Finset.sum_nonpos
    intro i _
    simpa only [mul_zero] using norm_offDiagonalPartFamily_le hv
      (groundCompression Φ.hamiltonian E₀ (Φ.term i)) le_rfl (fun c e hce => by
        have heq := hzero i c e hce
        rw [Submodule.coe_inner, coe_groundSpaceCompression_apply] at heq
        simpa only [heq, norm_zero] using (le_rfl : (0 : ℝ) ≤ 0))
  · have hterm (i : κ) :
        ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
          (groundCompression Φ.hamiltonian E₀ (Φ.term i))‖ ≤ Real.sqrt C * ‖Φ.term i‖ * f j i := by
      simpa only [Nat.reduceSub, Nat.cast_one, one_mul] using norm_offDiagonalPartFamily_le hv
        (groundCompression Φ.hamiltonian E₀ (Φ.term i))
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (hf j i))
        (fun c e hce => by
          have h := hb i c e hce
          rwa [Submodule.coe_inner, coe_groundSpaceCompression_apply] at h)
    calc _ ≤ ∑ i, Real.sqrt C * ‖Φ.term i‖ * f j i := Finset.sum_le_sum fun i _ => hterm i
      _ = Real.sqrt C * ∑ i, ‖Φ.term i‖ * f j i := by simp only [← mul_assoc, Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply sum_weight_mul_exp_neg_edist_le G a (fun i => ‖Φ.term i‖) (fun i => norm_nonneg _)
          |b₀| _ (a j) |Kg| kg (hGrow (a j)) (by positivity : 0 < γ / 2)
        exact fun x ↦ (sum_weight_anchor_le_of_support_budget T a ha
          (fun i ↦ ‖Φ.term i‖) (fun i ↦ norm_nonneg _) b₀ hBudget x).trans (le_abs_self b₀)

end Graph

end ManyBody
