/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.LowEnergyBasis.SpectralSplit
import QICLean.Analysis.LowEnergyBasis.Recursive
import QICLean.ManyBody.Hamiltonian.LowEnergyBasis

/-!
# A uniform ground-space basis

Hastings, arXiv:cond-mat/0508554v3, eq. `oibu` and lines 1695–1708, refines the basis
recursively along spectral splits. With the decay kernel of the low-energy commutators this
gives a basis of the ground space whose summed off-diagonal parts are bounded uniformly in the
system size.

* `recursiveCommutatorCoeff`, `recursiveBasisCoeff`, `exists_orthonormalBasis_uniform_kernel`.
* `exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_of_commutator_le` and
  `exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_uniform`.

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyBasisRecursive.lean` and
`LowEnergyBasisUniformGeneral.lean`. Changes as in `LowEnergyCommutator`.
-/

noncomputable section

open LowEnergyBasis
open scoped InnerProductSpace

namespace ManyBody



noncomputable local instance {ν : Type*} [Fintype ν] [DecidableEq ν]
    (H : Matrix ν ν ℂ) (E₀ : ℝ) : InnerProductSpace ℂ (groundSpace H E₀) :=
  (groundSpace H E₀).innerProductSpace

section Graph

open Matrix
open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]

set_option backward.isDefEq.respectTransparency false in
/-- **The basis construction from a decaying commutator bound.** Let `M_i` be Hermitian with
`‖M_i‖ ≤ ‖h_i‖`, where the weights `‖h_i‖` obey the support budget `b₀`, and let the ground-space
compressions `B_i = P M_i P` satisfy `‖[B_i, B_j]‖ ≤ C ‖h_i‖ ‖h_j‖ k(a_i, a_j)` for the graph
decay kernel `k` of rate `γ > 0`. Then some orthonormal basis of the ground space bounds the summed
off-diagonal parts of the `P M_i P` by `(n - 1)² c_n(C) |b₀| |K_g| S_{γ/2ⁿ,k}`. This is the
common part of the plain and the truncated basis estimates.
Hastings, arXiv:cond-mat/0508554v3, eq. `oibu` and lines 1698–1708. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_of_commutator_le
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (h M : κ → Matrix (Config X) (Config X) ℂ) (hMherm : ∀ k, (M k).IsHermitian)
    (hMnorm : ∀ k, ‖M k‖ ≤ ‖h k‖) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖h j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    (H : Matrix (Config X) (Config X) ℂ) (E₀ : ℝ) {γ C : ℝ} (hγ : 0 < γ) (hC : 0 ≤ C)
    (hcomm : ∀ i j, ‖groundSpaceCompression H E₀ (M i) * groundSpaceCompression H E₀ (M j) -
        groundSpaceCompression H E₀ (M j) * groundSpaceCompression H E₀ (M i)‖ ≤
      C * ‖h i‖ * ‖h j‖ * graphDecayKernel G γ (a i) (a j))
    [NeZero (Module.finrank ℂ (groundSpace H E₀))] :
    let n := Module.finrank ℂ (groundSpace H E₀)
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundSpace H E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression H E₀ (M i))‖ ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
          (|b₀| * (|Kg| * Real.shellSumConst (γ / 2 ^ n) kg)) := by
  classical
  let K := groundSpace H E₀
  let n := Module.finrank ℂ K
  have hGrow : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r ↦ (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  let k := fun i j ↦ graphDecayKernel G γ (a i) (a j)
  have hk0 : ∀ i j, 0 ≤ k i j := fun i j ↦ graphDecayKernel_nonneg G γ (a i) (a j)
  obtain ⟨b, s, hs, hb⟩ := exists_orthonormalBasis_uniform_weighted_kernel
    (fun i ↦ groundSpaceCompression H E₀ (M i))
    (fun i ↦ isSelfAdjoint_groundSpaceCompression _ _ (hMherm i)) (fun i ↦ ‖h i‖)
    (fun i ↦ norm_nonneg _) (fun i ↦ (norm_groundSpaceCompression_le _ _ _).trans (hMnorm i))
    k hk0
    (fun i j ↦ graphDecayKernel_le_one G hγ.le (a i) (a j))
    (fun i j ↦ graphDecayKernel_symm G γ (a i) (a j))
    (fun i j l ↦ graphDecayKernel_mul_le G hγ.le (a i) (a j) (a l)) hC hcomm
  refine ⟨b, ?_⟩
  have hv : Orthonormal ℂ (fun c ↦ (b c : EuclideanSpace ℂ (Config X))) :=
    b.orthonormal.comp_linearIsometry K.subtypeₗᵢ
  have hterm (i : κ) :
      ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression H E₀ (M i))‖ ≤
      (n - 1 : ℕ) * (recursiveBasisCoeff n C * ‖h i‖ * listKernelSum (sqrtKernel k n) s i) :=
    norm_offDiagonalPartFamily_le hv _
      (mul_nonneg (mul_nonneg (recursiveBasisCoeff_nonneg n C) (norm_nonneg _))
        (listKernelSum_nonneg (sqrtKernel_nonneg hk0 n) s i))
      (fun c e hce ↦ hb i c e hce)
  have hβ : 0 < γ / 2 ^ n := div_pos hγ (pow_pos (by norm_num) n)
  have hBudget' : ∀ x, ∑ i ∈ Finset.univ.filter (fun i ↦ a i = x), ‖h i‖ ≤ |b₀| :=
    fun x ↦ (sum_weight_anchor_le_of_support_budget T a ha
      (fun i ↦ ‖h i‖) (fun i ↦ norm_nonneg _) b₀ hBudget x).trans (le_abs_self b₀)
  have hkpow (i j : κ) : sqrtKernel k n i j =
      graphDecayKernel G (γ / 2 ^ n) (a i) (a j) := by
    rw [show k = (fun i j ↦ graphDecayKernel G γ (a i) (a j)) from rfl,
      sqrtKernel_comp, sqrtKernel_graphDecayKernel]
  have hrow : ∑ i, ‖h i‖ * listKernelSum (sqrtKernel k n) s i ≤
      (s.length : ℝ) * (|b₀| * (|Kg| * Real.shellSumConst (γ / 2 ^ n) kg)) := by
    rw [show sqrtKernel k n = (fun i j ↦ graphDecayKernel G (γ / 2 ^ n) (a i) (a j))
      from funext fun i ↦ funext fun j ↦ hkpow i j]
    exact sum_weight_list_graphDecayKernel_le G a
      (fun i ↦ ‖h i‖) (fun i ↦ norm_nonneg _) |b₀| hBudget' |Kg| kg hGrow hβ s
  have hlen : (s.length : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast hs
  have hrow0 : 0 ≤ |b₀| * (|Kg| * Real.shellSumConst (γ / 2 ^ n) kg) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (Real.shellSumConst_nonneg hβ kg))
  calc
    _ ≤ ∑ i, (n - 1 : ℕ) *
        (recursiveBasisCoeff n C * ‖h i‖ * listKernelSum (sqrtKernel k n) s i) :=
      Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (n - 1 : ℕ) * recursiveBasisCoeff n C *
        ∑ i, ‖h i‖ * listKernelSum (sqrtKernel k n) s i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (n - 1 : ℕ) * recursiveBasisCoeff n C *
        ((n - 1 : ℕ) * (|b₀| * (|Kg| * Real.shellSumConst (γ / 2 ^ n) kg))) :=
      mul_le_mul_of_nonneg_left (hrow.trans (mul_le_mul_of_nonneg_right hlen hrow0))
        (mul_nonneg (Nat.cast_nonneg _) (recursiveBasisCoeff_nonneg n C))
    _ = _ := by ring

set_option backward.isDefEq.respectTransparency false in
/-- An basis of an arbitrary nonzero finite-dimensional ground space has a
summed off-diagonal bound independent of the number of sites. Its constant depends
only on the ground-space dimension, the local norm budget, interaction geometry and gap.
Hastings, arXiv:cond-mat/0508554v3, eq. `oibu` and lines 1698–1708, with the retained
cross terms and weakened rate recorded in `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_uniform
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    [NeZero (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀))] :
    let n := Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)
    let γ := commutatorRate R vR b₀ ΔE
    let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundSpace Φ.hamiltonian E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm q ΔE Φ.hamiltonian (Φ.term i)))‖ ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
          (|b₀| * (|Kg| * Real.shellSumConst (γ / 2 ^ n) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
  have hC : 0 ≤ C := mul_nonneg
    (le_trans (by norm_num) (six_le_commutatorConst R vR b₀ (abs_nonneg Kg) kg))
    (Real.exp_pos _).le
  have hGrow : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ |Kg| * ((r : ℝ) + 1) ^ kg :=
    fun x r ↦ (hGrowth x r).trans
      (mul_le_mul_of_nonneg_right (le_abs_self Kg) (by positivity))
  simp only [groundCompression_gaussianFilteredTerm hq hH]
  exact exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_of_commutator_le G a ha Φ.term
    Φ.term
    hHerm (fun _ ↦ le_rfl) b₀ hBudget Kg kg hGrowth _ E₀ hγ hC fun i j ↦
      (norm_groundSpaceCompression_commutator_le _ _ _ _).trans
        (norm_groundCompression_commutator_le_exp_edist G a ha Φ hHerm R hDiam vR
          hCard b₀ hBudget |Kg| kg hGrow hΔE hgap j i)

end Graph

end ManyBody
