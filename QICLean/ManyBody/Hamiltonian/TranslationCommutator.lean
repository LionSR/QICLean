/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.FiniteOrbit
import QICLean.ManyBody.Hamiltonian.LowEnergyBasisUniform
import QICLean.ManyBody.Hamiltonian.Translation
import QICLean.ManyBody.Hamiltonian.GaussianFilterTruncation

/-!
# Low-energy commutators of translation-invariant interactions

For a translation-invariant interaction with a gap, Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1603–1654, bounds the low-energy commutators of the filtered terms by
translating one term far away within the supercell, or, for arbitrary momentum denominators,
through the finite-orbit recurrence of `Analysis/FiniteOrbit`.

* `norm_groundCompression_commutator_le_of_momenta(_exp)`: eq. `blecm` for momenta of bounded
  denominator (lines 1620–1641).
* `norm_groundCompression_commutator_le_of_norm_sub_le`,
  `norm_groundCompression_commutator_truncated_le_of_momenta`: the truncated terms of eq. `mid`, up
  to the errors of eq. `apb`.
* `norm_groundCompression_commutator_le_finite_translation_exp` and its truncated form: decay in
  the system size with no condition on the momenta (lines 1644–1654).
* `gaussianFilteredTerm_truncation_smul`,
  `norm_groundCompression_truncatedTerm_commutator_le_of_momenta`: covariant truncations.

The truncated term `M_k` is written as `gaussianFilteredTerm r ΔE (∑ k' ∈ s k, Φ.term k')
(Φ.term k)`, as in `Hamiltonian/GaussianFilterTruncation`.

Moved from TNLean (`e113e005`): `TNLean/Lattice/TranslationSupercellCommutator.lean`,
`TranslationFiniteOrbitCommutator.lean` and `TranslationSupercellTruncated.lean`. Changes as in
`Translation`; the definition `truncatedTerm` is replaced by its expression.
-/

noncomputable section

open LowEnergyBasis

open Matrix GaussianFilter 
open scoped Matrix.Norms.L2Operator

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

/-- **The low-energy commutator of a translation-invariant lattice is exponentially small in its
linear size.** Let the terms `h_k` be indexed by the sites, with `h_k` acting on a set `X_k ∋ k`
of diameter at most `R` in the lattice graph `G`, as in eq. `blecm`. Let an abelian group `Γ` of
translations act on the sites with `h_{g•k} = P_g h_k P_g†` (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 862 and 1603–1613), and let every eigenvalue of
`H = ∑_k h_k` equal `E₀` or be at least `E₀ + ΔE`. Suppose the momenta have denominator `N`:
`χ(g)^N = 1` for every character with a nonzero momentum sector (lines 1620–1625). Let `π` be the
cell coordinate along one lattice direction, with `n` cells, such that edges join cells at most
one apart, and let `e` translate by one cell in that direction. Then for every `l` with
`2R + l + N ≤ n / 2`, the low-energy commutator of the filtered terms at `i` and `j` obeys the
bound of eq. `blecm` at separation `l` with the norms of `h_i` and `h_j`. This is the
conclusion of lines 1634–1641 for the filtered terms `H_tilde_i`; for the source's truncated `M_i`,
up to the errors of eq. `apb`, see `norm_groundCompression_commutator_truncated_le_of_momenta`. -/
theorem norm_groundCompression_commutator_le_of_momenta
    (G : SimpleGraph V) {T : V → Finset V} (hX : ∀ k, k ∈ T k)
    (Φ : Interaction (fun _ : V ↦ α) T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
    (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    (hcov : ∀ (g : Γ) k, Φ.term (g • k) = sitePermOp (α := α) (MulAction.toPerm g)
        * Φ.term k * (sitePermOp (α := α) (MulAction.toPerm g))ᴴ)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {r q ΔE : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
        (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    {N : ℕ} (hN : 0 < N)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ Φ.hamiltonian E₀ χ ≠ ⊥ → ∀ g, χ g ^ N = 1)
    {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (i j : V) (l : ℕ) (hl : 2 * R + l + N ≤ n / 2) {τ : ℝ} (hT : 0 ≤ τ) :
    ‖groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term j)) -
        groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term j)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i))‖ ≤
      2 * ‖Φ.term j‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * ((T i).card : ℝ) ^ 2 * ‖Φ.term i‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
            2 * ‖Φ.term i‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q))) +
        2 * ‖Φ.term i‖ * ‖Φ.term j‖ * Real.exp (-q / 2) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  have hInv : IsSiteInvariant Γ Φ.hamiltonian := isSiteInvariant_sum_of_covariant Φ.term hcov
  obtain ⟨g, hg, hfar⟩ :=
    exists_mem_supercell_lt_edist hN hden G π hπ e he (2 * R + l) hl i j
  have hsep := disjoint_biUnion_graphBall_of_lt_edist G (T := T) id hX R hDiam
    (g • j) i l hfar
  have hmain
      := norm_groundCompression_commutator_le_of_supercell_separation G Φ hHerm R hDiam vR hCard b₀
    hBudget hcov Kg kg hGrowth hr hq hΔE hgap
    (supercell Γ Φ.hamiltonian E₀)
    (fun g hg ↦ (mem_supercell_iff hInv).mp hg) hg i j l hsep hT
  rwa [hcov, norm_sitePermOp_mul_mul_conjTranspose] at hmain


/-- **Truncated terms near filtered terms.** If the low-energy commutator of the filtered terms
`H_tilde_i`, `H_tilde_j` is at most `B`, and the operators `M_i`, `M_j` are within `ε_i`, `ε_j`
of them with `‖M_j‖ ≤ ‖h_j‖`, then `‖[P M_i P, P M_j P]‖ ≤ B + 2 ε_i ‖h_j‖ + 2 ‖h_i‖ ε_j`. -/
theorem norm_groundCompression_commutator_le_of_norm_sub_le
    {H : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ} (hH : H.IsHermitian)
        (E₀ r ΔE : ℝ) (hr : 0 ≤ r)
    {hi hj Mi Mj : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ} {B εi εj : ℝ}
    (hB : ‖groundCompression H E₀ (gaussianFilteredTerm r ΔE H hi) *
          groundCompression H E₀ (gaussianFilteredTerm r ΔE H hj) -
        groundCompression H E₀ (gaussianFilteredTerm r ΔE H hj) *
          groundCompression H E₀ (gaussianFilteredTerm r ΔE H hi)‖ ≤ B)
    (hεi : ‖gaussianFilteredTerm r ΔE H hi - Mi‖ ≤ εi)
    (hεj : ‖gaussianFilteredTerm r ΔE H hj - Mj‖ ≤ εj) (hMj : ‖Mj‖ ≤ ‖hj‖) :
    ‖groundCompression H E₀ Mi * groundCompression H E₀ Mj -
        groundCompression H E₀ Mj * groundCompression H E₀ Mi‖ ≤
      B + 2 * εi * ‖hj‖ + 2 * ‖hi‖ * εj := by
  have hsub (W W' : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ) :
      groundCompression H E₀ W - groundCompression H E₀ W' = groundCompression H E₀ (W - W') := by
    unfold groundCompression
    rw [map_sub, mul_sub, sub_mul]
  set A := groundCompression H E₀ (gaussianFilteredTerm r ΔE H hi)
  set Bc := groundCompression H E₀ (gaussianFilteredTerm r ΔE H hj)
  set A' := groundCompression H E₀ Mi
  set B' := groundCompression H E₀ Mj
  have key : A' * B' - B' * A' =
      (A * Bc - Bc * A) + ((A' - A) * B' - B' * (A' - A)) + (A * (B' - Bc) - (B' - Bc) * A) := by
    simp only [sub_mul, mul_sub]
    abel
  rw [key]
  have e1 : ‖(A' - A) * B' - B' * (A' - A)‖ ≤ 2 * εi * ‖hj‖ := by
    have hc := norm_groundCompression_commutator_le_two_mul H E₀
      (Mi - gaussianFilteredTerm r ΔE H hi) Mj
    rw [← hsub] at hc
    have hε : ‖Mi - gaussianFilteredTerm r ΔE H hi‖ ≤ εi := by rw [norm_sub_rev]; exact hεi
    have h1 := mul_le_mul hε hMj (norm_nonneg _) ((norm_nonneg _).trans hε)
    change ‖(A' - A) * B' - B' * (A' - A)‖ ≤ _ at hc
    nlinarith
  have e2 : ‖A * (B' - Bc) - (B' - Bc) * A‖ ≤ 2 * ‖hi‖ * εj := by
    have hc := norm_groundCompression_commutator_le_two_mul H E₀ hi
      (Mj - gaussianFilteredTerm r ΔE H hj)
    have hAeq : A = groundCompression H E₀ hi := by
      simp only [A, groundCompression_gaussianFilteredTerm hr hH]
    rw [← hsub, ← hAeq] at hc
    have hε : ‖Mj - gaussianFilteredTerm r ΔE H hj‖ ≤ εj := by rw [norm_sub_rev]; exact hεj
    have h1 := mul_le_mul (le_refl ‖hi‖) hε (norm_nonneg _) (norm_nonneg _)
    change ‖A * (B' - Bc) - (B' - Bc) * A‖ ≤ _ at hc
    nlinarith
  have h3 := norm_add₃_le (a := A * Bc - Bc * A) (b := (A' - A) * B' - B' * (A' - A))
    (c := A * (B' - Bc) - (B' - Bc) * A)
  linarith

/-- **The low-energy commutator of Hastings' truncated terms.** In the setting of
`norm_groundCompression_commutator_le_of_momenta`, let `M_k` be the filter of `h_k` under the
truncated Hamiltonian `∑_{k' ∈ s_k} h_{k'}`, the operator of eq. `mid` (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 285–307), and let `ε_i`, `ε_j` bound
`‖H_tilde_i - M_i‖`, `‖H_tilde_j - M_j‖`, as eq. `apb` does
(`norm_gaussianFilteredTerm_sub_truncated_le`). Then `‖[P M_i P, P M_j P]‖` is at most the bound of
`norm_groundCompression_commutator_le_of_momenta` plus `2 ε_i ‖h_j‖ + 2 ‖h_i‖ ε_j`. The errors
`ε` of eq. `apb` do not decrease with `n`; for the exponential smallness in `n` of the `M_i`
see `norm_groundCompression_truncatedTerm_commutator_le_of_momenta`. -/
theorem norm_groundCompression_commutator_truncated_le_of_momenta
    (G : SimpleGraph V) {T : V → Finset V} (hX : ∀ k, k ∈ T k)
    (Φ : Interaction (fun _ : V ↦ α) T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
    (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    (hcov : ∀ (g : Γ) k, Φ.term (g • k) = sitePermOp (α := α) (MulAction.toPerm g)
        * Φ.term k * (sitePermOp (α := α) (MulAction.toPerm g))ᴴ)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {r q ΔE : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ}
        (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    {N : ℕ} (hN : 0 < N)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ Φ.hamiltonian E₀ χ ≠ ⊥ → ∀ g, χ g ^ N = 1)
    {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (i j : V) (l : ℕ) (hl : 2 * R + l + N ≤ n / 2) {τ : ℝ} (hT : 0 ≤ τ)
    (s : V → Finset V) {εi εj : ℝ}
    (hεi : ‖gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i) -
      gaussianFilteredTerm r ΔE (∑ k ∈ s i, Φ.term k) (Φ.term i)‖ ≤ εi)
    (hεj : ‖gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term j) -
      gaussianFilteredTerm r ΔE (∑ k ∈ s j, Φ.term k) (Φ.term j)‖ ≤ εj) :
    ‖groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k ∈ s i, Φ.term k)
        (Φ.term i)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k ∈ s j, Φ.term k)
              (Φ.term j)) -
        groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k ∈ s j, Φ.term k)
            (Φ.term j)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k ∈ s i, Φ.term k)
              (Φ.term i))‖ ≤
      (2 * ‖Φ.term j‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * ((T i).card : ℝ) ^ 2 * ‖Φ.term i‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
            2 * ‖Φ.term i‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q))) +
        2 * ‖Φ.term i‖ * ‖Φ.term j‖ * Real.exp (-q / 2))
        + 2 * εi * ‖Φ.term j‖ + 2 * ‖Φ.term i‖ * εj :=
  norm_groundCompression_commutator_le_of_norm_sub_le
      (Interaction.isHermitian_hamiltonian hHerm) E₀ r ΔE hr
    (norm_groundCompression_commutator_le_of_momenta G hX Φ hHerm R hDiam vR hCard b₀
      hBudget hcov Kg kg hGrowth hr hq hΔE hgap hN hden π hπ e he i j l hl hT) hεi hεj
    (norm_gaussianFilteredTerm_le _ _ (isSelfAdjoint_sum _ fun k _ ↦
        (hHerm k).isSelfAdjoint).isHermitian _)


/-- A closed exponential bound for the low-energy commutator of the
Gaussian-filtered local terms. The rate is `commutatorRate`, and the
constant is `commutatorConst`; the exponent uses real subtraction.
The estimate includes systems with fewer than `2 * (N + 2 * R)` cells,
where the trivial commutator bound suffices. All original nonnegative
Gaussian parameters are retained because their ground-space compressions
agree. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `blecm`,
lines 1562–1601, and the supercell argument, lines 1620–1641.
The filtered-term scope is recorded in
`docs/paper-gaps/hastings05_translation_supercell.tex`. -/
theorem norm_groundCompression_commutator_le_of_momenta_exp
    (G : SimpleGraph V) {T : V → Finset V} (hX : ∀ k, k ∈ T k)
    (Φ : Interaction (fun _ : V ↦ α) T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
    (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    (hcov : ∀ (g : Γ) k, Φ.term (g • k) = sitePermOp (α := α) (MulAction.toPerm g)
        * Φ.term k * (sitePermOp (α := α) (MulAction.toPerm g))ᴴ)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {r ΔE : ℝ} (hr : 0 ≤ r) (hΔE : 0 < ΔE) {E₀ : ℝ} (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    {N : ℕ} (hN : 0 < N)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ Φ.hamiltonian E₀ χ ≠ ⊥ → ∀ g, χ g ^ N = 1)
    {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (i j : V) :
    ‖groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term j)) -
        groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term j)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE Φ.hamiltonian (Φ.term i))‖ ≤
      commutatorConst R vR b₀ Kg kg * ‖Φ.term i‖ * ‖Φ.term j‖ *
        Real.exp (-(commutatorRate R vR b₀ ΔE *
          (((n / 2 : ℕ) : ℝ) - N - 2 * R))) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  have hInv : IsSiteInvariant Γ Φ.hamiltonian := isSiteInvariant_sum_of_covariant Φ.term hcov
  by_cases hsize : N + 2 * R ≤ n / 2
  · let l := n / 2 - (N + 2 * R)
    have hl : 2 * R + l + N ≤ n / 2 := by
      dsimp only [l]
      omega
    obtain ⟨g, hg, hfar⟩ :=
      exists_mem_supercell_lt_edist hN hden G π hπ e he (2 * R + l) hl i j
    have hsep := disjoint_biUnion_graphBall_of_lt_edist G (T := T) id hX R hDiam
      (g • j) i l hfar
    have hnorm : ‖Φ.term (g • j)‖ = ‖Φ.term j‖ := by
      rw [hcov, norm_sitePermOp_mul_mul_conjTranspose]
    have hcast : (l : ℝ) = ((n / 2 : ℕ) : ℝ) - N - 2 * R := by
      dsimp only [l]
      rw [Nat.cast_sub hsize]
      push_cast
      ring
    have hmain := norm_groundCompression_commutator_le_exp G id Φ hHerm R
      hDiam vR hCard b₀ hBudget Kg kg hGrowth hΔE hgap (g • j) i l hsep
    rw [← groundCompression_commutator_eq_of_mem_supercell r ΔE hInv hH hcov
      (supercell Γ Φ.hamiltonian E₀)
      (fun g hg ↦ (mem_supercell_iff hInv).mp hg) hg i j]
    simpa only [groundCompression_gaussianFilteredTerm hr hH, hnorm, hcast] using hmain
  · have hKg : 0 ≤ Kg := by
      have hzero := hGrowth i 0
      simp only [CharP.cast_eq_zero, zero_add, one_pow, mul_one] at hzero
      exact (Nat.cast_nonneg _).trans hzero
    have hC6 := six_le_commutatorConst R vR b₀ hKg kg
    have hC2 : (2 : ℝ) ≤ commutatorConst R vR b₀ Kg kg := by linarith
    have hC0 : 0 ≤ commutatorConst R vR b₀ Kg kg := by linarith
    have hγ := commutatorRate_pos hΔE R vR b₀
    have hlength : ((n / 2 : ℕ) : ℝ) - N - 2 * R ≤ 0 := by
      have hnat : n / 2 ≤ N + 2 * R := by omega
      have hreal : ((n / 2 : ℕ) : ℝ) ≤ (N : ℝ) + 2 * R := by
        exact_mod_cast hnat
      linarith
    have hexp : 1 ≤ Real.exp (-(commutatorRate R vR b₀ ΔE *
        (((n / 2 : ℕ) : ℝ) - N - 2 * R))) :=
      Real.one_le_exp (by nlinarith)
    have hpref : 0 ≤ commutatorConst R vR b₀ Kg kg * ‖Φ.term i‖ * ‖Φ.term j‖ := by positivity
    calc
      _ ≤ 2 * ‖Φ.term i‖ * ‖Φ.term j‖ := by
        simpa only [groundCompression_gaussianFilteredTerm hr hH] using
          norm_groundCompression_commutator_le_two_mul Φ.hamiltonian E₀ (Φ.term i) (Φ.term j)
      _ ≤ commutatorConst R vR b₀ Kg kg * ‖Φ.term i‖ * ‖Φ.term j‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hC2 (norm_nonneg _)) (norm_nonneg _)
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hpref

end ManyBody

open Matrix 
open scoped Matrix.Norms.L2Operator InnerProductSpace


namespace ManyBody

/-- Translating the observable itself removes any covariance requirement on a chosen
local decomposition. Hastings, arXiv:cond-mat/0508554v3, lines 1603–1654. -/
theorem norm_groundCompression_commutator_le_of_finite_observable_orbit
    {V Γ : Type*} [Fintype V] [DecidableEq V] [CommGroup Γ] [MulAction Γ V] {α : Type*} [Fintype
        α] [DecidableEq α]
    {H : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ}
        (hInv : IsSiteInvariant Γ H) (E₀ : ℝ)
    (W B : Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ)
    (G : SimpleGraph V) {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (m L : ℕ) (hm : 1 ≤ m)
    (hdim : (Module.finrank ℂ (groundSpace H E₀)) ^ 2 ≤ m)
    (hn : 2 * (m + 1) * L ≤ n) (i j : V) {C : ℝ} (hC : 0 ≤ C)
    (hfar : ∀ g : Γ, ((L / 2 : ℕ) : ℕ∞) ≤ G.edist i (g • j) →
      ‖groundCompression H E₀ W * groundCompression H E₀
          (sitePermOp (α := α) (MulAction.toPerm g) * B * (sitePermOp (α := α)
              (MulAction.toPerm g))ᴴ) -
        groundCompression H E₀ (sitePermOp (α := α) (MulAction.toPerm g) * B * (sitePermOp
            (MulAction.toPerm g))ᴴ) *
          groundCompression H E₀ W‖ ≤ C) :
    ‖groundCompression H E₀ W * groundCompression H E₀ B -
      groundCompression H E₀ B * groundCompression H E₀ W‖ ≤ ((2 : ℝ) ^ m - 1) * C := by
  have hcoeff := one_le_two_pow_sub_one m hm
  have horiginal (hsep : ((L / 2 : ℕ) : ℕ∞) ≤ G.edist i j) :
      ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ ≤ C := by
    have hf := hfar 1 (by simpa only [one_smul] using hsep)
    simpa only [sitePermOp_toPerm_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one] using hf
  by_cases hLzero : L = 0
  · exact (horiginal (by simp [hLzero])).trans (le_mul_of_one_le_left hC hcoeff)
  have hL : 0 < L := Nat.pos_of_ne_zero hLzero
  by_cases hnear : (π j - π i).valMinAbs.natAbs ≤ L / 2
  · let τ := (groundTranslationConjugation hInv E₀ (e ^ L)).toLinearMap
    let Ag := groundSpaceCompression H E₀ W
    let Bg := groundSpaceCompression H E₀ B
    have hT (A : groundSpace H E₀ →L[ℂ] groundSpace H E₀) : ‖τ A‖ = ‖A‖ :=
      (groundTranslationConjugation hInv E₀ (e ^ L)).norm_map A
    have hb (k : Fin ((Module.finrank ℂ (groundSpace H E₀)) ^ 2)) :
        ‖Ag * ((τ ^ ((k : ℕ) + 1)) Bg) - ((τ ^ ((k : ℕ) + 1)) Bg) * Ag‖ ≤ C := by
      have hk : (k : ℕ) + 1 ≤ m := (Nat.succ_le_iff.mpr k.isLt).trans hdim
      have hsep := SimpleGraph.edist_pow_mul_ge_of_near hL hn G π hπ e he i j hnear
        (by omega : 1 ≤ (k : ℕ) + 1) hk
      have horbit := groundTranslationConjugation_pow_compression
        hInv E₀ (e ^ L) ((k : ℕ) + 1) B
      change (τ ^ ((k : ℕ) + 1)) Bg = _ at horbit
      rw [horbit]
      dsimp only [Ag]
      rw [norm_subspaceCompression_commutator]
      have hp : (e ^ L) ^ ((k : ℕ) + 1) = e ^ (((k : ℕ) + 1) * L) := by
        rw [← pow_mul, Nat.mul_comm]
      rw [hp]
      exact hfar (e ^ (((k : ℕ) + 1) * L)) hsep
    have hf := norm_commutator_le_of_finite_translation_orbit_bounds τ hT Ag Bg hC hb
    have hc : (2 : ℝ) ^ ((Module.finrank ℂ (groundSpace H E₀)) ^ 2) - 1 ≤
        (2 : ℝ) ^ m - 1 := sub_le_sub_right (pow_le_pow_right₀ (by norm_num) hdim) 1
    rw [show ‖groundCompression H E₀ W * groundCompression H E₀ B -
        groundCompression H E₀ B * groundCompression H E₀ W‖ = _ from
      (norm_subspaceCompression_commutator (groundSpace H E₀) (toEuclideanCLM (𝕜 := ℂ) W)
        (toEuclideanCLM (𝕜 := ℂ) B)).symm]
    exact hf.trans (mul_le_mul_of_nonneg_right hc hC)
  · have hc : L / 2 ≤ (π j - π i).valMinAbs.natAbs := (lt_of_not_ge hnear).le
    have hd := SimpleGraph.natAbs_valMinAbs_sub_le_edist (by decide : 0 < (1 : ℕ)) π hπ i j
    have hsep : ((L / 2 : ℕ) : ℕ∞) ≤ G.edist i j := by
      simpa only [Nat.cast_one, one_mul] using (show
        ((L / 2 : ℕ) : ℕ∞) ≤ ((π j - π i).valMinAbs.natAbs : ℕ∞) by
          exact_mod_cast hc).trans hd
    exact (horiginal hsep).trans (le_mul_of_one_le_left hC hcoeff)

private theorem finiteOrbit_support_separation {V : Type*} (G : SimpleGraph V)
    {i j x y : V} {D ρ : ℕ} (hfar : (D : ℕ∞) ≤ G.edist i j)
    (hix : G.edist i x ≤ ρ) (hyj : G.edist y j ≤ ρ) :
    ((D - 2 * ρ : ℕ) : ℕ∞) ≤ G.edist x y := by
  by_cases hxy : G.edist x y = ⊤
  · simp only [hxy, le_top]
  have hp : (D : ℕ∞) ≤ ρ + G.edist x y + ρ :=
    hfar.trans <| (G.edist_triangle (u := i) (v := y) (w := j)).trans <|
      (add_le_add (G.edist_triangle (u := i) (v := x) (w := y)) hyj).trans
        (add_le_add (add_le_add hix le_rfl) le_rfl)
  rw [← ENat.natCast_toNat hxy] at hp ⊢
  have hn : D ≤ ρ + (G.edist x y).toNat + ρ := by exact_mod_cast hp
  exact_mod_cast (show D - 2 * ρ ≤ (G.edist x y).toNat by omega)

private theorem finiteOrbit_support_radius_lower (L ρ : ℕ) :
    (L : ℝ) / 2 - 2 * (ρ : ℝ) - 1 ≤ ((L / 2 - 2 * ρ : ℕ) : ℝ) := by
  have hhalf : (L : ℝ) ≤ 2 * ((L / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show L ≤ 2 * (L / 2) + 1 by omega)
  have hsub : ((L / 2 : ℕ) : ℝ) ≤ ((L / 2 - 2 * ρ : ℕ) : ℝ) + 2 * (ρ : ℝ) := by
    exact_mod_cast (show L / 2 ≤ (L / 2 - 2 * ρ) + 2 * ρ by omega)
  nlinarith




/-- Translation invariance of the original Hamiltonian gives exponentially small
low-energy commutators of arbitrary local observables. No covariance of its chosen
local decomposition is required. Hastings, arXiv:cond-mat/0508554v3, lines 1603–1654. -/
theorem norm_groundCompression_commutator_le_finite_translation_exp
    {V Γ : Type*} [Fintype V] [DecidableEq V] [CommGroup Γ] [MulAction Γ V] {α : Type*} [Fintype
        α] [DecidableEq α]
    (G : SimpleGraph V)
    (hAut : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (T : V → Finset V) (hX : ∀ k, k ∈ T k)
    (Φ : Interaction (fun _ : V ↦ α) T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, G.edist x y ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (hInv : IsSiteInvariant Γ Φ.hamiltonian)
    {Δ : ℝ} (hΔ : 0 < Δ) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (nGroundBound : ℕ)
    (hDim : Module.finrank ℂ (groundSpace Φ.hamiltonian E₀) ≤ nGroundBound)
    {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (i j : V) (S Y : Finset V) {W B : Matrix (Config fun _ : V ↦ α)
        (Config fun _ : V ↦ α) ℂ}
    (hW : W ∈ supportedOperators (fun _ ↦ α) S)
    (hB : B ∈ supportedOperators (fun _ ↦ α) Y) (ρ vObs : ℕ)
    (hSrad : ∀ x ∈ S, G.edist i x ≤ ρ) (hYrad : ∀ y ∈ Y, G.edist j y ≤ ρ)
    (hSCard : S.card ≤ vObs) :
    let m := max 1 (nGroundBound ^ 2)
    let v := 4 * vR * |b₀| * Real.exp (2 * (R : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀ B -
      groundCompression Φ.hamiltonian E₀ B * groundCompression Φ.hamiltonian E₀ W‖ ≤
      ((2 : ℝ) ^ m - 1) * ((4 * (vObs : ℝ) + 4) * ‖W‖ * ‖B‖) *
        Real.exp (γ * (2 * (ρ : ℝ) + 2)) *
          Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * n)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  classical
  intro m v γ
  let L := n / (2 * (m + 1))
  let C := (4 * (vObs : ℝ) + 4) * ‖W‖ * ‖B‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hγ : 0 < γ := lt_min (by norm_num) (div_pos hΔ (by positivity))
  have hm : 1 ≤ m := le_max_left _ _
  have hdim : (Module.finrank ℂ (groundSpace Φ.hamiltonian E₀)) ^ 2 ≤ m :=
    (Nat.pow_le_pow_left hDim 2).trans (le_max_right _ _)
  have hn : 2 * (m + 1) * L ≤ n := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self n (2 * (m + 1))
  have hvR : 1 ≤ vR := (Finset.one_le_card.mpr ⟨i, hX i⟩).trans (hCard i)
  have hpoint (g : Γ) (D : ℕ) (hsep : (D : ℕ∞) ≤ G.edist i (g • j)) :
      ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀
          (sitePermOp (α := α) (MulAction.toPerm g) * B * (sitePermOp (α := α)
              (MulAction.toPerm g))ᴴ) -
        groundCompression Φ.hamiltonian E₀ (sitePermOp (α := α) (MulAction.toPerm g) * B *
            (sitePermOp (α := α) (MulAction.toPerm g))ᴴ) *
          groundCompression Φ.hamiltonian E₀ W‖ ≤
      C * Real.exp (-(γ * ((D - 2 * ρ : ℕ) : ℝ))) := by
    let Yg := Y.map (MulAction.toPerm g).toEmbedding
    have hBg : sitePermOp (α := α) (MulAction.toPerm g) * B * (sitePermOp (α := α)
        (MulAction.toPerm g))ᴴ ∈
        supportedOperators (fun _ ↦ α) Yg := by
      have heq : ((MulAction.toPerm g).toEmbedding : V → V) = (g • ·) := rfl
      simpa only [Yg, Finset.map_eq_image, Equiv.coe_toEmbedding] using
        sitePermOp_mul_mul_conjTranspose_mem_supportedOperators (MulAction.toPerm g) hB
    have hYg (y : V) (hy : y ∈ Yg) : G.edist (g • j) y ≤ ρ := by
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hy
      change G.edist (g • j) (g • w) ≤ ρ
      rw [SimpleGraph.edist_smul_of_adj_iff G hAut]
      exact hYrad w hw
    have hseps (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ Yg) :
        ((D - 2 * ρ : ℕ) : ℕ∞) ≤ G.edist x y :=
      finiteOrbit_support_separation G hsep (hSrad x hx)
        (by simpa only [G.edist_comm] using hYg y hy)
    have hp := norm_groundCompression_commutator_le_graphSeparation G Φ hHerm R hDiam vR hvR hCard
        b₀ hBudget hΔ hgap S Yg hW hBg
      (D - 2 * ρ) hseps
    rw [norm_sitePermOp_mul_mul_conjTranspose] at hp
    change ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀
          (sitePermOp (α := α) (MulAction.toPerm g) * B * (sitePermOp (α := α)
              (MulAction.toPerm g))ᴴ) -
        groundCompression Φ.hamiltonian E₀ (sitePermOp (α := α) (MulAction.toPerm g) * B *
            (sitePermOp (α := α) (MulAction.toPerm g))ᴴ) *
          groundCompression Φ.hamiltonian E₀ W‖ ≤
      (4 * (S.card : ℝ) + 4) * ‖W‖ * ‖B‖ *
        Real.exp (-(γ * ((D - 2 * ρ : ℕ) : ℝ))) at hp
    refine hp.trans ?_
    dsimp only [C]
    gcongr
  have htriv := hpoint 1 0 (by simp)
  simp only [sitePermOp_toPerm_one, Matrix.conjTranspose_one, Matrix.one_mul, zero_tsub,
    Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, mul_one] at htriv
  have h4 : (2 * ((2 * (m + 1) : ℕ) : ℝ)) = 4 * ((m : ℝ) + 1) := by push_cast; ring
  rw [← h4]
  apply translation_finiteOrbit_decay_of_near_far n (q := 2 * (m + 1)) (by omega) m hm hγ hC htriv
  intro _hlarge
  have hfar (g : Γ) (hsep : ((L / 2 : ℕ) : ℕ∞) ≤ G.edist i (g • j)) :
      ‖groundCompression Φ.hamiltonian E₀ W * groundCompression Φ.hamiltonian E₀
          (sitePermOp (α := α) (MulAction.toPerm g) * B * (sitePermOp (α := α)
              (MulAction.toPerm g))ᴴ) -
        groundCompression Φ.hamiltonian E₀ (sitePermOp (α := α) (MulAction.toPerm g) * B *
            (sitePermOp (α := α) (MulAction.toPerm g))ᴴ) *
          groundCompression Φ.hamiltonian E₀ W‖ ≤
      C * Real.exp (-(γ * ((L : ℝ) / 2 - 2 * (ρ : ℝ) - 1))) := by
    refine (hpoint g (L / 2) hsep).trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left
      (finiteOrbit_support_radius_lower L ρ) hγ.le))
  simpa only [L, mul_assoc] using
    norm_groundCompression_commutator_le_of_finite_observable_orbit hInv E₀ W B
      G π hπ e he m L hm hdim hn i j (by positivity) hfar


/-- The source's actual truncated Gaussian terms have exponentially small low-energy
commutators whenever their original Hamiltonian is translation invariant. The chosen local
terms and retained sets need not transform covariantly. Hastings,
arXiv:cond-mat/0508554v3, eq. `mid`, lines 285–307, and lines 1603–1654. -/
theorem norm_groundCompression_truncated_commutator_le_finite_translation_exp
    {V Γ : Type*} [Fintype V] [DecidableEq V] [CommGroup Γ] [MulAction Γ V] {α : Type*} [Fintype
        α] [DecidableEq α]
    (G : SimpleGraph V)
    (hAut : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (T : V → Finset V) (hX : ∀ k, k ∈ T k)
    (Φ : Interaction (fun _ : V ↦ α) T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, G.edist x y ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (hInv : IsSiteInvariant Γ Φ.hamiltonian)
    {Δ : ℝ} (hΔ : 0 < Δ) {E₀ : ℝ}
    (hgap : IsGapped Φ.hamiltonian E₀ Δ)
    (nGroundBound : ℕ)
    (hDim : Module.finrank ℂ (groundSpace Φ.hamiltonian E₀) ≤ nGroundBound)
    {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (s K : V → Finset V) (hsK : ∀ i, ∀ k ∈ s i, T k ⊆ K i)
    (hXK : ∀ i, T i ⊆ K i) (ρ vObs : ℕ)
    (hKrad : ∀ i, ∀ x ∈ K i, G.edist i x ≤ ρ)
    (hKCard : ∀ i, (K i).card ≤ vObs) (J : ℝ) (hJ : 0 ≤ J) (hNorm : ∀ i, ‖Φ.term i‖ ≤ J)
    (q : ℝ) (i j : V) :
    let m := max 1 (nGroundBound ^ 2)
    let v := 4 * vR * |b₀| * Real.exp (2 * (R : ℝ)) + 1
    let γ := min (1 / 4) (Δ / (8 * v))
    let Mi := gaussianFilteredTerm q Δ (∑ k ∈ s i, Φ.term k) (Φ.term i)
    let Mj := gaussianFilteredTerm q Δ (∑ k ∈ s j, Φ.term k) (Φ.term j)
    ‖groundCompression Φ.hamiltonian E₀ Mi * groundCompression Φ.hamiltonian E₀ Mj -
      groundCompression Φ.hamiltonian E₀ Mj * groundCompression Φ.hamiltonian E₀ Mi‖ ≤
      ((2 : ℝ) ^ m - 1) * ((4 * (vObs : ℝ) + 4) * J ^ 2) *
        Real.exp (γ * (2 * (ρ : ℝ) + 2)) *
          Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * n)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  intro m v γ Mi Mj
  have hMsupp (a : V) : gaussianFilteredTerm q Δ (∑ k ∈ s a, Φ.term k) (Φ.term a) ∈
      supportedOperators (fun _ ↦ α) (K a : Finset V) :=
    gaussianFilteredTerm_mem_supportedOperators q Δ
      (sum_mem fun k hk ↦ supportedOperators_mono
        (Finset.coe_subset.mpr (hsK a k hk)) (Φ.mem k))
      (supportedOperators_mono (Finset.coe_subset.mpr (hXK a)) (Φ.mem a))
  have hMnorm (a : V) : ‖gaussianFilteredTerm q Δ (∑ k ∈ s a, Φ.term k) (Φ.term a)‖ ≤ J :=
    (norm_gaussianFilteredTerm_le q Δ
      (isSelfAdjoint_sum _ fun k _ ↦ (hHerm k).isSelfAdjoint).isHermitian (Φ.term a)).trans
      (hNorm a)
  have hg := norm_groundCompression_commutator_le_finite_translation_exp G hAut T hX Φ hHerm R
      hDiam vR hCard b₀ hBudget hInv hΔ hgap nGroundBound hDim π hπ e he
    i j (K i) (K j) (hMsupp i) (hMsupp j) ρ vObs (hKrad i) (hKrad j) (hKCard i)
  have hcoeff : 0 ≤ (2 : ℝ) ^ m - 1 :=
    le_trans (by norm_num) (one_le_two_pow_sub_one m (le_max_left _ _))
  refine hg.trans ?_
  calc
    _ ≤ ((2 : ℝ) ^ m - 1) * ((4 * (vObs : ℝ) + 4) * J * J) *
        Real.exp (γ * (2 * (ρ : ℝ) + 2)) *
          Real.exp (-((γ / (4 * ((m : ℝ) + 1))) * n)) := by
      gcongr
      · exact hMnorm i
      · exact hMnorm j
    _ = _ := by ring

end ManyBody

open Matrix GaussianFilter 
open scoped Matrix.Norms.L2Operator

namespace ManyBody

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

/-- **Covariance of the truncated terms** `M_k`, the Gaussian filter of `h_k` under the
truncated Hamiltonian `∑_{k' ∈ s_k} h_{k'}` (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
eq. `mid`, lines 285–307). If the terms are covariant,
`h_{g•k} = P_g h_k P_g†`, and so are the truncations, `s_{g•k} = g • s_k`, then
`M_{g•k} = P_g M_k P_g†`. -/
theorem gaussianFilteredTerm_truncation_smul {Γ : Type*} [Group Γ] [MulAction Γ V] (r ΔE : ℝ)
    {T : V → Finset V} {Φ : Interaction (fun _ : V ↦ α) T} (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (hcov : ∀ (g : Γ) k, Φ.term (g • k) = sitePermOp (α := α) (MulAction.toPerm g)
        * Φ.term k * (sitePermOp (α := α) (MulAction.toPerm g))ᴴ)
    {s : V → Finset V} (hs : ∀ (g : Γ) k, s (g • k) = (s k).map (MulAction.toPerm g).toEmbedding)
    (g : Γ) (k : V) :
    gaussianFilteredTerm r ΔE (∑ k' ∈ s (g • k), Φ.term k') (Φ.term (g • k)) =
      sitePermOp (α := α) (MulAction.toPerm g) * gaussianFilteredTerm r ΔE (∑ k' ∈ s k
          , Φ.term k') (Φ.term k) * (sitePermOp (α := α) (MulAction.toPerm g))ᴴ := by
  have hsum : ∑ k' ∈ s (g • k), Φ.term k' =
      sitePermOp (α := α) (MulAction.toPerm g) * (∑ k' ∈ s k, Φ.term k') * (sitePermOp (α
          := α) (MulAction.toPerm g))ᴴ := by
    rw [hs, Finset.sum_map, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k' _ ↦ hcov g k'
  rw [hsum, hcov, gaussianFilteredTerm_conj r ΔE (sitePermOp_mem_unitary (MulAction.toPerm g))
    (isSelfAdjoint_sum _ fun k' _ ↦ (hHerm k').isSelfAdjoint).isHermitian]

/-- **The low-energy commutator of the truncated terms is exponentially small in the linear
size.** Let the terms `h_k` be indexed by the sites, with `h_k` acting on `X_k ∋ k` of diameter at
most `R`, covariant under an abelian group `Γ` of translations, and let every eigenvalue of
`H = ∑_k h_k` equal `E₀` or be at least `E₀ + ΔE`. Let the momenta have denominator `N`, and let
`π`, `e` be a cell coordinate with `n` cells and the unit translation along it. Let the
truncations `s_k` be covariant, with the terms of `s_k` and `h_k` itself acting on a set
`K_k ∋ k` of diameter at most `R'`. Then for every `l` with `2R' + l + N ≤ n / 2`, the low-energy
commutator of the truncated terms `M_i`, `M_j` of eq. `mid` obeys the bound of eq. `blecm` at
separation `l`. This is the conclusion of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1603–1641, for the source's `M_i`, with eq. `blecm` (lines 1555–1601) applied to the
`M_i` themselves. -/
theorem norm_groundCompression_truncatedTerm_commutator_le_of_momenta
    (G : SimpleGraph V) {T : V → Finset V} (hX : ∀ k, k ∈ T k)
    (Φ : Interaction (fun _ : V ↦ α) T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
    (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
    (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    {Γ : Type*} [CommGroup Γ] [MulAction Γ V]
    (hcov : ∀ (g : Γ) k, Φ.term (g • k) = sitePermOp (α := α) (MulAction.toPerm g)
        * Φ.term k * (sitePermOp (α := α) (MulAction.toPerm g))ᴴ)
    (Kg : ℝ) (kg : ℕ)
    (hGrowth : ∀ x (r : ℕ),
      ((Finset.univ.filter fun y => G.edist x y = r).card : ℝ) ≤ Kg * ((r : ℝ) + 1) ^ kg)
    {r q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ} (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    {N : ℕ} (hN : 0 < N)
    (hden : ∀ χ : Γ →* ℂ, momentumSector Γ Φ.hamiltonian E₀ χ ≠ ⊥ → ∀ g, χ g ^ N = 1)
    {n : ℕ} [NeZero n] (π : V → ZMod n)
    (hπ : ∀ u v, G.Adj u v → (π v - π u).valMinAbs.natAbs ≤ 1)
    (e : Γ) (he : ∀ v, π (e • v) = π v + 1)
    (s : V → Finset V)
    (hs : ∀ (g : Γ) k, s (g • k) = (s k).map (MulAction.toPerm g).toEmbedding)
    (K : V → Finset V) (hsK : ∀ k, ∀ k' ∈ s k, T k' ⊆ K k) (hXK : ∀ k, T k ⊆ K k)
    (R' : ℕ) (hKdiam : ∀ k, ∀ x ∈ K k, ∀ z ∈ K k, G.edist x z ≤ R')
    (i j : V) (l : ℕ) (hl : 2 * R' + l + N ≤ n / 2) {τ : ℝ} (hT : 0 ≤ τ) :
    ‖groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k' ∈ s i, Φ.term k')
        (Φ.term i)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k' ∈ s j, Φ.term k')
              (Φ.term j)) -
        groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k' ∈ s j, Φ.term k')
            (Φ.term j)) *
          groundCompression Φ.hamiltonian E₀ (gaussianFilteredTerm r ΔE (∑ k' ∈ s i, Φ.term k')
              (Φ.term i))‖ ≤
      2 * ‖gaussianFilteredTerm r ΔE (∑ k' ∈ s j, Φ.term k') (Φ.term j)‖ *
          ((2 + 4 * |b₀| * Real.exp (2 * R)) * ((K i).card : ℝ) ^ 2 *
              ‖gaussianFilteredTerm r ΔE (∑ k' ∈ s i, Φ.term k') (Φ.term i)‖ * Kg *
              (2 ^ kg * kg.factorial * Real.exp (1 / 2) / (1 - Real.exp (-(1 / 2)))) *
              Real.exp ((2 * vR * |b₀| * Real.exp (2 * R) + 1) * τ - l / 2) +
            2 * ‖gaussianFilteredTerm r ΔE (∑ k' ∈ s i, Φ.term k') (Φ.term i)‖ * Real.exp (-(τ
                * ΔE) ^ 2 / (2 * q))) +
        2 * ‖gaussianFilteredTerm r ΔE (∑ k' ∈ s i, Φ.term k') (Φ.term i)‖
            * ‖gaussianFilteredTerm r ΔE (∑ k' ∈ s j, Φ.term k') (Φ.term j)‖ * Real.exp
                (-q / 2) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hgapE := ((isGapped_iff_eigenvalues hH).mp hgap).2
  set M : V → Matrix (Config fun _ : V ↦ α) (Config fun _ : V ↦ α) ℂ :=
    fun k ↦ gaussianFilteredTerm r ΔE (∑ k' ∈ s k, Φ.term k') (Φ.term k)
  have hInv : IsSiteInvariant Γ Φ.hamiltonian := isSiteInvariant_sum_of_covariant Φ.term hcov
  have hkK (k : V) : k ∈ K k := hXK k (hX k)
  have hMsupp (k : V) : M k ∈ supportedOperators (fun _ ↦ α) (K k : Finset V) :=
    gaussianFilteredTerm_mem_supportedOperators r ΔE
      (sum_mem fun k' hk' ↦
        supportedOperators_mono (by exact_mod_cast hsK k k' hk') (Φ.mem k'))
      (supportedOperators_mono (by exact_mod_cast hXK k) (Φ.mem k))
  obtain ⟨g, hg, hfar⟩ :=
    exists_mem_supercell_lt_edist hN hden G π hπ e he (2 * R' + l) hl i j
  have hsep := disjoint_biUnion_graphBall_of_lt_edist G (T := K) id hkK R' hKdiam
    (g • j) i l hfar
  have hMg : M (g • j) = sitePermOp (α := α) (MulAction.toPerm g) * M j * (sitePermOp (α
      := α) (MulAction.toPerm g))ᴴ :=
    gaussianFilteredTerm_truncation_smul r ΔE hHerm hcov hs g j
  have hcomp : groundCompression Φ.hamiltonian E₀ (M (g • j)) =
      groundCompression Φ.hamiltonian E₀ (M j) := by
    rw [hMg]
    exact groundCompression_sitePermOp_conj (supercell Γ Φ.hamiltonian E₀)
      (fun g hg ↦ (mem_supercell_iff hInv).mp hg) hg _
  have hmain := norm_groundCompression_commutator_le_graphNeighborhood G Φ hHerm R hDiam vR hCard b₀
    hBudget Kg kg hGrowth hq hΔE hgap (K i) (hMsupp i) l _ hsep
    (hMsupp (g • j)) hT
  rwa [hcomp, hMg, norm_sitePermOp_mul_mul_conjTranspose] at hmain

end ManyBody
