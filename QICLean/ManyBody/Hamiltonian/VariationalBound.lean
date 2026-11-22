/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Spectral.Eigenvalue.VariationalBound
import QICLean.ManyBody.Hamiltonian.GaussianFilter
import QICLean.ManyBody.Sites.SiteAction

/-!
# A variational lower bound from Gaussian-filtered terms

Let `H = ∑ᵢ Uᵢ H₀ Uᵢ†`, where the `Uᵢ` are unitaries commuting with `H`.
The Gaussian-filtered term `K = gaussianFilteredTerm q ΔE H H₀` satisfies
`H = ∑ᵢ Uᵢ K Uᵢ†`. Consequently `E₀ ≥ N λ_min(K)`, with `N` the number of terms.
For translations of a periodic lattice this is Hastings' filtered instance of the
variational lower bound, arXiv:cond-mat/0508554v3, eq. `varnum` (lines 856–877)
and the discussion of filtered terms at lines 1005–1009.

The proof uses the actual Gaussian integral, its covariance and preservation of the
Hamiltonian sum. It does not require a gap or an approximation by finite polynomials.
QICLean identifies that integral with the norm-convergent even-commutator series;
the correction to the printed coefficients is documented at
`docs/paper-gaps/hastings05_gaussian_series_coefficients.tex`.
-/

open GaussianFilter Matrix
open scoped Matrix.Norms.L2Operator

namespace ManyBody

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The conjugates of an actual Gaussian-filtered term sum to the original Hamiltonian.
Hastings, arXiv:cond-mat/0508554v3, eq. `hsum` (lines 247–249) and lines 1005–1009. -/
theorem sum_conj_gaussianFilteredTerm {ι : Type*} [Fintype ι] (q ΔE : ℝ)
    (U : ι → Matrix n n ℂ) (hU : ∀ i, U i ∈ unitaryGroup n ℂ)
    (H₀ : Matrix n n ℂ) (hH₀ : H₀.IsHermitian)
    (hcomm : ∀ i, Commute (U i) (∑ j, U j * H₀ * (U j)ᴴ)) :
    ∑ i, U i * gaussianFilteredTerm q ΔE (∑ j, U j * H₀ * (U j)ᴴ) H₀ * (U i)ᴴ =
      ∑ j, U j * H₀ * (U j)ᴴ := by
  let H := ∑ j, U j * H₀ * (U j)ᴴ
  have hH : H.IsHermitian :=
    isSelfAdjoint_sum _ fun j _ ↦ isHermitian_mul_mul_conjTranspose (U j) hH₀
  have hconj (i : ι) : U i * H * (U i)ᴴ = H := by
    rw [(hcomm i).eq, Matrix.mul_assoc]
    have hUU : U i * (U i)ᴴ = 1 := by
      simpa [star_eq_conjTranspose] using (mem_unitaryGroup_iff).mp (hU i)
    rw [hUU, Matrix.mul_one]
  calc
    _ = ∑ i, gaussianFilteredTerm q ΔE H (U i * H₀ * (U i)ᴴ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← gaussianFilteredTerm_conj q ΔE (hU i) hH H₀, hconj]
    _ = H := sum_gaussianFilteredTerm Finset.univ q ΔE hH rfl

/-- The lowest eigenvalue of an actual Gaussian-filtered term gives a lower bound
on every eigenvalue of the Hamiltonian. Hastings, arXiv:cond-mat/0508554v3,
eq. `varnum` (lines 856–877), with the filtered choice at lines 1005–1009. -/
theorem card_mul_sInf_spectrum_gaussianFilteredTerm_le_of_conj {ι : Type*} [Fintype ι]
    (q ΔE : ℝ) (U : ι → Matrix n n ℂ) (hU : ∀ i, U i ∈ unitaryGroup n ℂ)
    (H₀ : Matrix n n ℂ) (hH₀ : H₀.IsHermitian)
    (hcomm : ∀ i, Commute (U i) (∑ j, U j * H₀ * (U j)ᴴ))
    {E : ℝ} {Ω : n → ℂ} (hΩ : Ω ≠ 0)
    (hE : (∑ j, U j * H₀ * (U j)ᴴ) *ᵥ Ω = (E : ℂ) • Ω) :
    Fintype.card ι * sInf (spectrum ℝ
      (gaussianFilteredTerm q ΔE (∑ j, U j * H₀ * (U j)ᴴ) H₀)) ≤ E := by
  let H := ∑ j, U j * H₀ * (U j)ᴴ
  let K := gaussianFilteredTerm q ΔE H H₀
  have hH : H.IsHermitian :=
    isSelfAdjoint_sum _ fun j _ ↦ isHermitian_mul_mul_conjTranspose (U j) hH₀
  have hsum : ∑ j, U j * K * (U j)ᴴ = H :=
    sum_conj_gaussianFilteredTerm q ΔE U hU H₀ hH₀ hcomm
  have hcommK : ∀ i, Commute (U i) (∑ j, U j * K * (U j)ᴴ) := by
    intro i
    rw [hsum]
    exact hcomm i
  have hEK : (∑ j, U j * K * (U j)ᴴ) *ᵥ Ω = (E : ℂ) • Ω := by
    rw [hsum]
    exact hE
  simpa using Matrix.card_mul_sInf_spectrum_le_of_conj U hU K
    (isHermitian_gaussianFilteredTerm q ΔE hH hH₀) hcommK (fun _ ↦ 0) 0 hΩ hEK


section SitePermutation

open Finset
open scoped ComplexOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [Group G] [MulAction G V]
  {α : Type*} [Fintype α] [DecidableEq α]

/-- **The variational lower bound for translates on finitely many sites.** Let a finite group
`G`, such as the translations of a periodic lattice or any group of automorphisms of a finite
graph, act on the sites `V`, and let `H = ∑_{g ∈ G} P_g H₀ P_g†` be the sum of the translates of
one term `H₀`. For real constants `a_k` and
`K = H₀ + ∑_{k=1}^{m} a_k iᵏ ad_Hᵏ(H₀)`, if `K − λ ≥ 0` then every eigenvalue `E` of `H`, in
particular the ground energy `E₀`, satisfies `E ≥ |G| λ`: with `λ = λ_min(K)` and `N = |G|` the
number of summands, `E₀/N ≥ λ_min(K)`. When `G` acts simply transitively on the sites, as the
translations of a periodic lattice do, `N` is the number of sites.
Hastings, arXiv:cond-mat/0508554v3, eq. `varnum`, lines 856–877. -/
theorem card_mul_le_of_mulVec_eq_smul_of_sitePermOp [Fintype G]
    (H₀ : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) (a : ℕ → ℝ)
        (m : ℕ) {c : ℝ}
    (hK : (H₀ + ∑ k ∈ range m, ((a (k + 1) : ℂ) * Complex.I ^ (k + 1)) •
        (GaussianFilter.commutatorCLM (∑ g : G, sitePermOp (α := α) (MulAction.toPerm g)
            * H₀ * (sitePermOp (α := α) (MulAction.toPerm g))ᴴ) ^ (k + 1)) H₀ -
          (c : ℂ) • 1).PosSemidef)
    {E : ℝ} {Ω : (Config fun _ : V ↦ α) → ℂ} (hΩ : Ω ≠ 0)
    (hE : (∑ g : G, sitePermOp (α := α) (MulAction.toPerm g) * H₀ * (sitePermOp (α := α)
        (MulAction.toPerm g))ᴴ) *ᵥ Ω = (E : ℂ) • Ω) :
    Fintype.card G * c ≤ E :=
  Matrix.card_mul_le_of_mulVec_eq_smul_of_conj (fun g ↦ sitePermOp (α := α)
      (MulAction.toPerm g))
    (fun g ↦ sitePermOp_mem_unitary (MulAction.toPerm g)) H₀
        (isSiteInvariant_sum_conj H₀) a m hK hΩ hE

/-- The least-eigenvalue specialization for translates on finitely many sites.
Hastings, arXiv:cond-mat/0508554v3, eq. `varnum`, lines 856–877. -/
theorem card_mul_sInf_spectrum_le_of_sitePermOp [Fintype G]
    (H₀ : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) (hH₀ : H₀.IsHermitian)
    (a : ℕ → ℝ) (m : ℕ) {E : ℝ} {Ω : (Config fun _ : V ↦ α) → ℂ} (hΩ : Ω ≠ 0)
    (hE : (∑ g : G, sitePermOp (α := α) (MulAction.toPerm g) * H₀ * (sitePermOp (α := α)
        (MulAction.toPerm g))ᴴ) *ᵥ Ω = (E : ℂ) • Ω) :
    Fintype.card G * sInf (spectrum ℝ
      (H₀ + ∑ k ∈ range m, ((a (k + 1) : ℂ) * Complex.I ^ (k + 1)) •
        (GaussianFilter.commutatorCLM (∑ g : G, sitePermOp (α := α) (MulAction.toPerm g)
            * H₀ * (sitePermOp (α := α) (MulAction.toPerm g))ᴴ) ^ (k + 1)) H₀)) ≤ E :=
  Matrix.card_mul_sInf_spectrum_le_of_conj (fun g ↦ sitePermOp (α := α) (MulAction.toPerm g))
    (fun g ↦ sitePermOp_mem_unitary (MulAction.toPerm g)) H₀ hH₀
        (isSiteInvariant_sum_conj H₀) a m hΩ hE

end SitePermutation

section SiteAction

variable {V : Type*} [Fintype V] [DecidableEq V] {G : Type*} [Group G] [MulAction G V]
  {α : Type*} [Fintype α] [DecidableEq α]

/-- For translates of one term on a finite set of sites, the least eigenvalue of the
Gaussian-filtered term bounds the ground energy per translate. For a simply transitive
site action, the number of translates is the number of sites. Hastings,
arXiv:cond-mat/0508554v3, eq. `varnum` (lines 856–877) and lines 1005–1009. -/
theorem card_mul_sInf_spectrum_gaussianFilteredTerm_le_of_sitePermOp [Fintype G]
    (q ΔE : ℝ) (H₀ : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ)
    (hH₀ : H₀.IsHermitian) {E : ℝ} {Ω : (Config fun _ : V ↦ α) → ℂ} (hΩ : Ω ≠ 0)
    (hE : (∑ g : G, sitePermOp (α := α) (MulAction.toPerm g) * H₀ * (sitePermOp (α := α)
        (MulAction.toPerm g))ᴴ) *ᵥ Ω =
      (E : ℂ) • Ω) :
    Fintype.card G * sInf (spectrum ℝ (gaussianFilteredTerm q ΔE
      (∑ g : G, sitePermOp (α := α) (MulAction.toPerm g) * H₀ * (sitePermOp (α := α)
          (MulAction.toPerm g))ᴴ) H₀)) ≤ E :=
  card_mul_sInf_spectrum_gaussianFilteredTerm_le_of_conj q ΔE
    (fun g ↦ sitePermOp (α := α) (MulAction.toPerm g)) (fun g ↦ sitePermOp_mem_unitary
        (MulAction.toPerm g)) H₀ hH₀
    (isSiteInvariant_sum_conj H₀) hΩ hE


end SiteAction

end ManyBody
