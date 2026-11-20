/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Hamiltonian.LowEnergyBasisUniform
import QICLean.ManyBody.Hamiltonian.GaussianFilterTruncation

/-!
# A ground-space basis for the truncated terms

Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eqs. `mid`, `apb` and `oibu`
(lines 285–320 and 1678–1708), chooses the ground-space basis for the truncated terms `M_i`.

* `exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_truncated_le`: the summed off-diagonal
  parts of the truncated terms, uniformly in the system size.
* `exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_truncated_perturbation_le`: a basis
  chosen for the filtered terms works for every truncated family, up to the total truncation
  error.

**Scope restriction (polynomial growth):** both theorems assume the polynomial growth `hGrowth`
of the spheres of `G`. Hastings' lines 169–190 assume only finite-range local bounds and a metric,
which do not imply polynomial growth, and the unrestricted metric-lattice assertion is false;
the correction, with the retained cross terms and weakened rate of `LowEnergyBasisUniform`, is
recorded in `docs/paper-gaps/hastings05_two_dim_ground_basis.tex`.

Moved from TNLean (`e113e005`): `TNLean/Lattice/LowEnergyBasisTruncatedUniform.lean` and the
ground-space part of `LowEnergyBasisPerturbation.lean`. Changes as in `LowEnergyCommutator`.
-/

noncomputable section

open LowEnergyBasis

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace


namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

noncomputable local instance (H : Matrix (Config X) (Config X) ℂ) (E₀ : ℝ) :
    InnerProductSpace ℂ (groundSpace H E₀) := (groundSpace H E₀).innerProductSpace

/-- A constructed basis bounds the summed off-diagonal parts of the actual truncated
operators, uniformly in the number of sites for fixed local data and ground-space dimension.
The truncation regions are arbitrary admissible local regions containing all generator
supports used there; their diameter and cardinality are displayed separately from those
of the Hamiltonian. No supplied basis, spectral separation or conditioning is assumed.
Hastings, arXiv:cond-mat/0508554v3, eq. `mid` (lines 285–307), second filtering at
lines 1548–1564, and eq. `oibu` with lines 1698–1708. -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_truncated_le
    (G : SimpleGraph V) {T : V → Finset V} (hX : ∀ i, i ∈ T i)
    (Φ : Interaction X T) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (R : ℕ) (hDiam : ∀ i, ∀ x ∈ T i, ∀ z ∈ T i, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ i, (T i).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y ↦ G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    (r : ℝ) (s : V → Finset V) (K : V → Finset V)
    (hsK : ∀ i, ∀ j ∈ s i, T j ⊆ K i) (hXK : ∀ i, T i ⊆ K i)
    (Robs : ℕ) (hKDiam : ∀ i, ∀ x ∈ K i, ∀ z ∈ K i, G.edist x z ≤ Robs)
    (vObs : ℕ) (hKCard : ∀ i, (K i).card ≤ vObs) :
    let n := Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)
    haveI : NeZero n := ⟨fun h0 ↦ hgap.1 (Submodule.finrank_eq_zero.mp h0)⟩
    let γ := commutatorRate R vR b₀ ΔE
    let C := commutatorConst R vObs b₀ |Kg| kg * Real.exp (γ * (2 * Robs + 1))
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundSpace Φ.hamiltonian E₀),
      ∑ i, ‖offDiagonalPartFamily (fun c ↦ (b c : EuclideanSpace ℂ (Config X)))
        (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k' ∈ s i, Φ.term k')
            (Φ.term i)))‖ ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
          (|b₀| * (|Kg| * Real.shellSumConst (γ / 2 ^ n) kg)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have : NeZero (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)) :=
    ⟨fun h0 ↦ hgap.1 (Submodule.finrank_eq_zero.mp h0)⟩
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let M : V → Matrix (Config X) (Config X) ℂ :=
    fun k ↦ gaussianFilteredTerm r ΔE (∑ k' ∈ s k, Φ.term k') (Φ.term k)
  let γ := commutatorRate R vR b₀ ΔE
  have hγ : 0 < γ := commutatorRate_pos hΔE R vR b₀
  let C := commutatorConst R vObs b₀ |Kg| kg * Real.exp (γ * (2 * Robs + 1))
  have hC : 0 ≤ C := mul_nonneg
    (le_trans (by norm_num) (six_le_commutatorConst R vObs b₀ (abs_nonneg Kg) kg))
    (Real.exp_pos _).le
  have hMnorm (i : V) : ‖M i‖ ≤ ‖Φ.term i‖ := norm_gaussianFilteredTerm_le r ΔE
    (isSelfAdjoint_sum _ fun j _ ↦ (hHerm j).isSelfAdjoint).isHermitian (Φ.term i)
  have hMherm (i : V) : (M i).IsHermitian := isHermitian_gaussianFilteredTerm r ΔE
    (isSelfAdjoint_sum _ fun j _ ↦ (hHerm j).isSelfAdjoint).isHermitian (hHerm i)
  have hMsupp (i : V) : M i ∈ supportedOperators X (K i : Finset V) :=
    gaussianFilteredTerm_mem_supportedOperators r ΔE
      (sum_mem fun j hj ↦
        supportedOperators_mono (by exact_mod_cast hsK i j hj) (Φ.mem j))
      (supportedOperators_mono (by exact_mod_cast hXK i) (Φ.mem i))
  refine exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_of_commutator_le G id hX Φ.term M
    hMherm hMnorm b₀ hBudget Kg kg hGrowth _ E₀ hγ hC fun i j ↦ ?_
  refine (norm_subspaceCompression_commutator _ _ _).le.trans ?_
  refine (norm_groundCompression_observables_commutator_le_exp_edist G Φ hHerm R hDiam vR hCard b₀
      hBudget Kg kg hGrowth hΔE hgap
    K id (fun i ↦ hXK i (hX i)) M hMsupp Robs hKDiam vObs hKCard j i).trans ?_
  change C * ‖M i‖ * ‖M j‖ * _ ≤ C * ‖Φ.term i‖ * ‖Φ.term j‖ * _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_left (hMnorm i) hC) (hMnorm j)
      (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))) (graphDecayKernel_nonneg G γ _ _)

end ManyBody

namespace ManyBody

section GroundSpace

open Matrix
open scoped Matrix.Norms.L2Operator

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

noncomputable local instance (H : Matrix (Config X) (Config X) ℂ) (E₀ : ℝ) :
    InnerProductSpace ℂ (groundSpace H E₀) := (groundSpace H E₀).innerProductSpace

/-- A basis chosen from the original terms works for every truncated family, up to the
total truncation error. In particular, a radius depending on the system size is allowed
when that total error is controlled. No uniform bound along such a choice is inferred
from a fixed observable radius. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `apb` (lines 300–320 and 1521–1533) and eq. `oibu` (lines 1678–1708). -/
theorem exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_truncated_perturbation_le
    (G : SimpleGraph V) {T : V → Finset V} (hX : ∀ i, i ∈ T i)
    (Φ : Interaction X T) (hHerm : ∀ i, (Φ.term i).IsHermitian)
    (R : ℕ) (hDiam : ∀ i, ∀ x ∈ T i, ∀ z ∈ T i, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ i, (T i).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (Kg : ℝ) (kg : ℕ) (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {ΔE : ℝ} (hΔE : 0 < ΔE) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ ΔE) :
    let n := Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)
    haveI : NeZero n := ⟨fun h0 ↦ hgap.1 (Submodule.finrank_eq_zero.mp h0)⟩
    let γ := commutatorRate R vR b₀ ΔE
    let C := commutatorConst R vR b₀ |Kg| kg * Real.exp (γ * (2 * R + 1))
    ∃ b : OrthonormalBasis (Fin n) ℂ (groundSpace Φ.hamiltonian E₀),
      ∀ r : ℝ, 0 ≤ r → ∀ s : V → Finset V,
        ∑ i, ‖offDiagonalPartFamily (fun c => (b c : EuclideanSpace ℂ (Config X)))
          (groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k' ∈ s i, Φ.term k')
              (Φ.term i)))‖ ≤
          ((n - 1 : ℕ) : ℝ) ^ 2 * recursiveBasisCoeff n C *
              (|b₀| * (|Kg| * Real.shellSumConst (γ / 2 ^ n) kg)) +
            (n - 1 : ℕ) * ∑ i,
              ‖gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i) - gaussianFilteredTerm r ΔE
                  (∑ k' ∈ s i, Φ.term k') (Φ.term i)‖ := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have : NeZero (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)) :=
    ⟨fun h0 ↦ hgap.1 (Submodule.finrank_eq_zero.mp h0)⟩
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  let V := groundSpace Φ.hamiltonian E₀
  obtain ⟨b, hb⟩ := exists_groundSpaceBasis_sum_norm_offDiagonalPartFamily_le_uniform
    G id hX Φ hHerm R hDiam vR hCard b₀ hBudget Kg kg hGrowth
    (q := 0) le_rfl hΔE hgap
  refine ⟨b, fun r hr s => ?_⟩
  have hv : Orthonormal ℂ (fun c => (b c : EuclideanSpace ℂ (Config X))) :=
    b.orthonormal.comp_linearIsometry V.subtypeₗᵢ
  have hpert := sum_norm_offDiagonalPartFamily_groundCompression_le hv Φ.hamiltonian E₀
    (fun k ↦ gaussianFilteredTerm r ΔE (∑ k' ∈ s k, Φ.term k') (Φ.term k))
        (fun i => gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i))
  simp only [groundCompression_gaussianFilteredTerm hr hH] at hpert
  simp only [groundCompression_gaussianFilteredTerm (q := 0) le_rfl hH] at hb
  simpa only [norm_sub_rev] using hpert.trans (add_le_add hb le_rfl)

end GroundSpace

end ManyBody
