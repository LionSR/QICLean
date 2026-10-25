/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceRandomSampling
import QICLean.Analysis.ViableSubspaceSpectralProjector

/-!
# The bootstrapping step for viable subspaces

Arad, Landau, Vazirani and Vidick (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Proposition
`prop:albootstrap-dg`, lines 1062–1075) bound the minimal dimension of a `0.015`-viable subspace
for the ground space `T` by alternating random sampling (Lemma `l:rs`) and error reduction
(Lemma `l:er`). The operators `A_i` come from Theorem `t:ais`: there are `D²` operators on the
middle factor and a subspace `T̃` mutually `0.005`-close to `T` such that applying the `A_i` to a
`δ`-viable set for `T̃` gives a `Δ / (1 - δ) ^ 2`-viable set, with `D ^ 12 Δ ≤ 10⁻⁵`.

Here the bootstrapping argument is proved for these data as hypotheses. If `W` is `0.015`-viable
for `T` and has dimension `q ≥ 4 D²`, and the failure probability of Lemma `l:rs` for samples of
dimension `s = ⌊q / (2 D²)⌋` is below `1`, then a sample `W' ⊆ W` and the span `S` of the
`A_i W'` give a `0.015`-viable subspace of dimension at most `q / 2`
(`exists_isViable_finrank_le_half`). Iterating from the whole factor, there is a `0.015`-viable
subspace of dimension below any threshold `q₁ ≥ 4 D²` above which the sampling condition holds
(`exists_isViable_finrank_lt_of_bootstrap`). With the bound on `D` from Theorem `t:ais`, the
sampling condition `eq:bootstrap-cond-dg` holds for `q = r e^{Õ(γ⁻¹ log³ d)}`.

**Local fix (constants of the bootstrapping step):** the source applies Lemma `l:rs` with the
target `T` where `T̃` is meant (line 1068) and with its printed failure probability; here
the sample is drawn for `T̃` with the corrected failure probability of `l:rs`, and the
condition is the requirement that this probability be below `1`. The chain of constants
`(32 D²)² Δ + 0.005 ≤ 0.1 ≤ 0.15` (line 1074) does not close against the threshold `0.015`;
since `l:close` doubles the error, the argument needs `Δ / δ'² ≤ 0.0025`, which follows from
`D ^ 12 Δ ≤ 10⁻⁵` for `D ≥ 2` and samples of dimension at least `q / (4 D²)`. The source's `D`
is `e^{Õ(γ⁻¹ log³ d)} ≥ 2`. Documented in `docs/paper-gaps/alvv16_bootstrap_constants.tex`.

## Main statements

* `Submodule.IsCloseTo.of_le`: closeness is monotone in the parameter.
* `Submodule.exists_isViable_finrank_le_half`: one bootstrapping step.
* `Submodule.exists_isViable_finrank_lt_of_bootstrap`: Proposition `prop:albootstrap-dg`.
-/

open scoped TensorProduct InnerProductSpace
open TensorProduct Module

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- Closeness is monotone in the parameter: a `δ`-close subspace is `δ'`-close for `δ ≤ δ'`. -/
theorem IsCloseTo.of_le {δ δ' : ℝ} {U T : Submodule 𝕜 E} (h : IsCloseTo δ U T) (hδ : δ ≤ δ') :
    IsCloseTo δ' U T := by
  rw [isCloseTo_iff] at h ⊢
  intro t ht
  refine le_trans ?_ (h t ht)
  nlinarith [sq_nonneg ‖t‖]

section Bootstrap

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- The failure probability of Lemma `l:rs` for a `0.04`-viable set of dimension `q`, samples of
dimension `s = ⌊q / (2 D²)⌋` and a target of dimension `r`:
`(1 + 2 / √((1 - 0.04) s / (8 q)))^{2r} q e^{-s/16}`. The bootstrapping condition
`eq:bootstrap-cond-dg` of arXiv:1602.08828v2 (line 1070) is that this is below `1`. -/
noncomputable def bootstrapFailure (D q r : ℕ) : ℝ :=
  (1 + 2 / √((1 - 0.04) * ((q / (2 * D ^ 2) : ℕ) : ℝ) / (8 * q))) ^ (2 * r) * q *
    Real.exp (-(((q / (2 * D ^ 2) : ℕ) : ℝ) / 16))

/-- The whole first factor is viable for every target. -/
theorem isViable_top (δ : ℝ) (hδ : 0 ≤ δ) (T : Submodule ℂ (M ⊗[ℂ] F)) :
    IsViable δ (⊤ : Submodule ℂ M) T := by
  have htop : (⊤ : Submodule ℂ M).tensorProd (⊤ : Submodule ℂ F) = ⊤ :=
    LinearMap.range_eq_top.mpr (TensorProduct.map_surjective
      (fun x => ⟨⟨x, trivial⟩, rfl⟩) (fun x => ⟨⟨x, trivial⟩, rfl⟩))
  unfold IsViable
  rw [htop, isCloseTo_iff]
  intro t _
  rw [starProjection_top, ContinuousLinearMap.id_apply]
  nlinarith [sq_nonneg ‖t‖]

/-- **One bootstrapping step** (proof of Proposition `prop:albootstrap-dg`, arXiv:1602.08828v2,
lines 1065–1074). Let `T` and `T'` be mutually `0.005`-close, and let `D ≥ 2` operators `A_i`,
`i < D²`, improve every `δ`-viable set for `T'` to a `Δ / (1 - δ) ^ 2`-viable one, with
`D ^ 12 Δ ≤ 10⁻⁵`. If `W` is `0.015`-viable for `T`, has dimension `q ≥ 4 D²`, and the sampling
condition `bootstrapFailure D q (dim T') < 1` holds, then some `0.015`-viable subspace for `T`
has dimension at most `q / 2`. -/
theorem exists_isViable_finrank_le_half {D : ℕ} {Δ : ℝ} {T T' : Submodule ℂ (M ⊗[ℂ] F)}
    (hTT' : IsCloseTo 0.005 T T') (hT'T : IsCloseTo 0.005 T' T)
    (A : Fin (D ^ 2) → M →L[ℂ] M)
    (hA : ∀ δ < 1, ∀ S : Submodule ℂ M, IsViable δ S T' →
      IsViable (Δ / (1 - δ) ^ 2) (⨆ i, S.map (A i : M →ₗ[ℂ] M)) T')
    (hD : 2 ≤ D) (hΔ : (D : ℝ) ^ 12 * Δ ≤ 0.00001)
    {W : Submodule ℂ M} (hW : IsViable 0.015 W T) (hq : 4 * D ^ 2 ≤ finrank ℂ W)
    (hη : bootstrapFailure D (finrank ℂ W) (finrank ℂ T') < 1) :
    ∃ S : Submodule ℂ M, finrank ℂ S ≤ finrank ℂ W / 2 ∧ IsViable 0.015 S T := by
  set q := finrank ℂ W with hq_def
  set s := q / (2 * D ^ 2) with hs_def
  have hD2 : 0 < 2 * D ^ 2 := by positivity
  have hs1 : 1 ≤ s := (Nat.le_div_iff_mul_le hD2).mpr (by nlinarith)
  have hsq : s ≤ q := Nat.div_le_self _ _
  -- `W` is `0.04`-viable for `T'`.
  have hW' : IsViable 0.04 W T' :=
    (IsCloseTo.trans hW hTT' (by norm_num)).of_le (by norm_num)
  -- a random sample of dimension `s`
  let Aset : Finset (Fin q) := Finset.univ.map (Fin.castLEEmb hsq)
  have hcard : Aset.card = s := by simp [Aset]
  have hι : Fintype.card (Fin q) = q := Fintype.card_fin q
  have hη' : (1 + 2 / √((1 - 0.04) * Aset.card / (8 * Fintype.card (Fin q)))) ^
      (2 * finrank ℂ T') * Fintype.card (Fin q) * Real.exp (-(Aset.card / 16)) < 1 := by
    rw [hcard, hι]
    exact hη
  obtain ⟨U, hU⟩ := exists_isViable_randomSubspace (stdOrthonormalBasis ℂ W) Aset hW' hη'
  rw [hcard, hι] at hU
  set W' := randomSubspace (stdOrthonormalBasis ℂ W) Aset U
  set δ' : ℝ := (1 - 0.04) * s / (8 * q) with hδ'_def
  have hqpos : (0 : ℝ) < q := by
    have : 1 ≤ q := hs1.trans hsq
    exact_mod_cast this
  have hspos : (1 : ℝ) ≤ s := by exact_mod_cast hs1
  have hδ'pos : 0 < δ' := by rw [hδ'_def]; positivity
  -- error reduction of the sample
  have hS := hA (1 - δ') (by linarith) W' hU
  rw [sub_sub_cancel] at hS
  -- the constant `Δ / δ'^2` is at most `0.0025`
  have hqs : (q : ℝ) ≤ 4 * (D : ℝ) ^ 2 * s := by
    have h1 := Nat.div_add_mod q (2 * D ^ 2)
    have h2 := Nat.mod_lt q hD2
    have h3 : q ≤ 4 * D ^ 2 * s := by
      rw [← hs_def] at h1
      nlinarith
    exact_mod_cast h3
  have hDpos : (0 : ℝ) < D := by
    have : 0 < D := by omega
    exact_mod_cast this
  have hD8 : (256 : ℝ) ≤ (D : ℝ) ^ 8 := by
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    calc (256 : ℝ) = 2 ^ 8 := by norm_num
      _ ≤ (D : ℝ) ^ 8 := by gcongr
  have hδ'lb : 0.03 / (D : ℝ) ^ 2 ≤ δ' := by
    rw [hδ'_def, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hbound : Δ / δ' ^ 2 ≤ 0.0025 := by
    rcases le_or_gt Δ 0 with hΔ0 | hΔ0
    · exact (div_nonpos_of_nonpos_of_nonneg hΔ0 (sq_nonneg _)).trans (by norm_num)
    · have h1 : Δ / δ' ^ 2 ≤ Δ / (0.03 / (D : ℝ) ^ 2) ^ 2 :=
        div_le_div_of_nonneg_left hΔ0.le (by positivity) (by gcongr)
      have h2 : Δ / (0.03 / (D : ℝ) ^ 2) ^ 2 = Δ * (D : ℝ) ^ 4 / 0.0009 := by
        field_simp
        ring
      have h3 : Δ * (D : ℝ) ^ 4 * 256 ≤ 0.00001 := by
        have : Δ * (D : ℝ) ^ 4 * (D : ℝ) ^ 8 = (D : ℝ) ^ 12 * Δ := by ring
        nlinarith [mul_pos hΔ0 (pow_pos hDpos 4)]
      rw [h2] at h1
      refine h1.trans ?_
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
  -- back to `T`
  have hST : IsViable 0.015 (⨆ i, W'.map (A i : M →ₗ[ℂ] M)) T :=
    (IsCloseTo.trans (hS.of_le hbound) hT'T (by norm_num)).of_le (by norm_num)
  refine ⟨_, ?_, hST⟩
  -- the dimension of the span of the `A_i W'`
  have hW'dim : finrank ℂ W' = s := by
    rw [finrank_randomSubspace, hcard]
  calc finrank ℂ ↥(⨆ i, W'.map (A i : M →ₗ[ℂ] M))
      ≤ ∑ i, finrank ℂ ↥(W'.map (A i : M →ₗ[ℂ] M)) := finrank_iSup_le_sum _
    _ ≤ ∑ _i : Fin (D ^ 2), s :=
        Finset.sum_le_sum fun i _ => (finrank_map_le _ _).trans hW'dim.le
    _ = D ^ 2 * s := by simp
    _ ≤ q / 2 := by
        rw [Nat.le_div_iff_mul_le (by norm_num)]
        have := Nat.div_mul_le_self q (2 * D ^ 2)
        rw [← hs_def] at this
        nlinarith

/-- **Proposition `prop:albootstrap-dg`** (abstract form; arXiv:1602.08828v2, lines 1062–1075).
Under the data of Theorem `t:ais` (`D ≥ 2` operators improving viability for `T'`, `T'` mutually
`0.005`-close to `T`, `D ^ 12 Δ ≤ 10⁻⁵`), if the sampling condition holds for every dimension
`q ≥ q₁` and `q₁ ≥ 4 D²`, then some `0.015`-viable subspace for `T` has dimension below `q₁`.
See the module docstring for the local fix of the constants. -/
theorem exists_isViable_finrank_lt_of_bootstrap {D : ℕ} {Δ : ℝ}
    {T T' : Submodule ℂ (M ⊗[ℂ] F)}
    (hTT' : IsCloseTo 0.005 T T') (hT'T : IsCloseTo 0.005 T' T)
    (A : Fin (D ^ 2) → M →L[ℂ] M)
    (hA : ∀ δ < 1, ∀ S : Submodule ℂ M, IsViable δ S T' →
      IsViable (Δ / (1 - δ) ^ 2) (⨆ i, S.map (A i : M →ₗ[ℂ] M)) T')
    (hD : 2 ≤ D) (hΔ : (D : ℝ) ^ 12 * Δ ≤ 0.00001) {q₁ : ℕ} (hq₁ : 4 * D ^ 2 ≤ q₁)
    (hcond : ∀ q, q₁ ≤ q → bootstrapFailure D q (finrank ℂ T') < 1) :
    ∃ W : Submodule ℂ M, finrank ℂ W < q₁ ∧ IsViable 0.015 W T := by
  suffices h : ∀ n, ∀ W : Submodule ℂ M, finrank ℂ W = n → IsViable 0.015 W T →
      ∃ W' : Submodule ℂ M, finrank ℂ W' < q₁ ∧ IsViable 0.015 W' T from
    h _ ⊤ rfl (isViable_top _ (by norm_num) T)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hWn hW
    rcases lt_or_ge n q₁ with hn | hn
    · exact ⟨W, hWn ▸ hn, hW⟩
    · obtain ⟨S, hSdim, hS⟩ := exists_isViable_finrank_le_half hTT' hT'T A hA hD hΔ hW
        (hWn ▸ hq₁.trans hn) (hWn ▸ hcond n hn)
      have hn1 : 1 ≤ n := by
        have : 1 ≤ 4 * D ^ 2 := by nlinarith
        omega
      exact ih _ (by rw [hWn] at hSdim; omega) S rfl hS

end Bootstrap

end Submodule
