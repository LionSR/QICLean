/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceCoordinates
import QICLean.Analysis.ViableSubspaceRandomSampling
import QICLean.Analysis.ViableSubspaceSpectralProjector

/-!
# The bootstrapping step for viable subspaces

Arad, Landau, Vazirani and Vidick (arXiv:1602.08828v2, `local_alg_arxiv_v2.tex`, Proposition
`prop:albootstrap-dg`, lines 1062–1075) bound the minimal dimension of a `0.015`-viable subspace
for the ground space `T` by alternating random sampling (Lemma `l:rs`) and error reduction
(Lemma `l:er`). The operators `A_i` come from Theorem `t:ais`: there are `D²` operators on the
middle factor and a subspace `T'` mutually `0.005`-close to `T` such that applying the `A_i` to a
`δ`-viable set for `T'` gives a `Δ / (1 - δ) ^ 2`-viable set, with `D ^ 12 Δ ≤ 10⁻⁵`.

Here the bootstrapping argument is proved for these data as hypotheses. If `W` is `0.015`-viable
for `T` and has dimension `q ≥ 4 D²`, and the failure probability of Lemma `l:rs` for samples of
dimension `s = ⌊q / (2 D²)⌋` is below `1`, then a sample `W' ⊆ W` and the span `S` of the
`A_i W'` give a `0.015`-viable subspace of dimension at most `q / 2`
(`exists_isViable_finrank_le_half`). Iterating from the whole factor, there is a `0.015`-viable
subspace of dimension below any threshold `q₁ ≥ 4 D²` above which the sampling condition holds
(`exists_isViable_finrank_lt_of_bootstrap`). With the bound on `D` from Theorem `t:ais`, the
sampling condition `eq:bootstrap-cond-dg` holds for `q = r e^{Õ(γ⁻¹ log³ d)}`.

**Local fix (constants of the bootstrapping step):** the source applies Lemma `l:rs` with the
target `T` where `T'` is meant (line 1068) and with its printed failure probability; here
the sample is drawn for `T'` with the corrected failure probability of `l:rs`, and the
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
      ≤ D ^ 2 * finrank ℂ W' := by
        simpa only [Fintype.card_fin] using
          (finrank_iSup_map_le_card_mul W' (fun i ↦ (A i).toLinearMap))
    _ = D ^ 2 * s := by rw [hW'dim]
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

namespace Submodule

/-- The integer sample size loses at most a factor of two once the sampled space
has dimension at least four times the square of the operator-family parameter.
This is an auxiliary estimate for ALVV, arXiv:1602.08828v2,
Proposition `prop:albootstrap-dg`, condition `eq:bootstrap-cond-dg`,
lines 1065–1074 of the checked source. -/
private theorem bootstrap_sample_floor_lower_bound (D q : ℕ)
    (hD : 2 ≤ D) (hq : 4 * D ^ 2 ≤ q) :
    (q : ℝ) / (4 * (D : ℝ) ^ 2) ≤ ((q / (2 * D ^ 2) : ℕ) : ℝ) := by
  let s : ℕ := q / (2 * D ^ 2)
  have hD0 : 0 < D := by omega
  have hden : 0 < 2 * D ^ 2 :=
    Nat.mul_pos (by decide) (pow_pos hD0 2)
  have hs0 : 0 < s := Nat.div_pos (by omega) hden
  have hsplus : s + 1 ≤ 2 * s := by omega
  have hNat : q ≤ 4 * D ^ 2 * s := by
    calc
      q ≤ (2 * D ^ 2) * (s + 1) := le_of_lt (Nat.lt_mul_div_succ q hden)
      _ ≤ (2 * D ^ 2) * (2 * s) := Nat.mul_le_mul_left _ hsplus
      _ = 4 * D ^ 2 * s := by ring
  have hcast : (q : ℝ) ≤ 4 * (D : ℝ) ^ 2 * (s : ℝ) := by
    have hc : (q : ℝ) ≤ ((4 * D ^ 2 * s : ℕ) : ℝ) := Nat.cast_le.mpr hNat
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hc
    exact hc
  have hDR : 0 < (D : ℝ) := Nat.cast_pos.mpr hD0
  have hdenR : 0 < 4 * (D : ℝ) ^ 2 :=
    mul_pos (by norm_num) (pow_pos hDR 2)
  change (q : ℝ) / (4 * (D : ℝ) ^ 2) ≤ (s : ℝ)
  exact (div_le_iff₀ hdenR).mpr (by nlinarith only [hcast])

/-- The covering-net base in the ALVV bootstrap is at most linear in the
operator-family parameter. This is an auxiliary numerical estimate for
arXiv:1602.08828v2, condition `eq:bootstrap-cond-dg`, lines 1065–1074.
The sample dimension is the actual integer quotient, not additional data. -/
private theorem bootstrap_net_base_le (D q : ℕ)
    (hD : 2 ≤ D) (hq : 4 * D ^ 2 ≤ q) :
    1 + 2 / Real.sqrt ((1 - 0.04) *
      ((q / (2 * D ^ 2) : ℕ) : ℝ) / (8 * (q : ℝ))) ≤ 21 * (D : ℝ) := by
  let s : ℝ := ((q / (2 * D ^ 2) : ℕ) : ℝ)
  let x : ℝ := (1 - 0.04) * s / (8 * (q : ℝ))
  have hDn : 0 < D := by omega
  have hqn : 0 < q :=
    lt_of_lt_of_le (Nat.mul_pos (by decide) (pow_pos hDn 2)) hq
  have hD1 : (1 : ℝ) ≤ (D : ℝ) := Nat.one_le_cast.mpr (by omega)
  have hDR : 0 < (D : ℝ) := lt_of_lt_of_le zero_lt_one hD1
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hqn
  have hD4 : 0 < 4 * (D : ℝ) ^ 2 :=
    mul_pos (by norm_num) (pow_pos hDR 2)
  have hD100 : 0 < 100 * (D : ℝ) ^ 2 :=
    mul_pos (by norm_num) (pow_pos hDR 2)
  have hq8 : 0 < 8 * (q : ℝ) := mul_pos (by norm_num) hqR
  have hsample : (q : ℝ) ≤ 4 * (D : ℝ) ^ 2 * s := by
    have h := (div_le_iff₀ hD4).mp (bootstrap_sample_floor_lower_bound D q hD hq)
    change (q : ℝ) ≤ s * (4 * (D : ℝ) ^ 2) at h
    nlinarith only [h]
  have hx : 1 / (100 * (D : ℝ) ^ 2) ≤ x := by
    dsimp only [x]
    apply (le_div_iff₀ hq8).mpr
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hD100).mpr
    nlinarith only [hsample, hqR.le]
  have hsqrt : 1 / (10 * (D : ℝ)) ≤ Real.sqrt x := by
    apply Real.le_sqrt_of_sq_le
    calc
      (1 / (10 * (D : ℝ))) ^ 2 = 1 / (100 * (D : ℝ) ^ 2) := by
        norm_num [div_pow, mul_pow]
      _ ≤ x := hx
  have hrecip : 0 < 1 / (10 * (D : ℝ)) :=
    one_div_pos.mpr (mul_pos (by norm_num) hDR)
  have hinv := one_div_le_one_div_of_le hrecip hsqrt
  have htwo : 2 / Real.sqrt x ≤ 20 * (D : ℝ) := by
    calc
      2 / Real.sqrt x = 2 * (1 / Real.sqrt x) := by ring
      _ ≤ 2 * (1 / (1 / (10 * (D : ℝ)))) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 20 * (D : ℝ) := by rw [one_div_one_div]; ring
  change 1 + 2 / Real.sqrt x ≤ 21 * (D : ℝ)
  nlinarith only [htwo, hD1]

/-- A logarithmic budget for the net and the viable-space dimension.
This elementary estimate is auxiliary to ALVV, arXiv:1602.08828v2,
condition `eq:bootstrap-cond-dg`, lines 1065–1074. -/
private theorem bootstrap_logarithmic_budget_mul (d r q : ℝ)
    (hd : 2 ≤ d) (hr : 1 ≤ r) (hq : r * d ^ 24 ≤ q) :
    (2 * r * Real.log (21 * d) + Real.log q) * (256 * d ^ 2) ≤ 2 * q := by
  have hd0 : 0 < d := by linarith
  have hr0 : 0 < r := by linarith
  have hd24 : 0 < d ^ 24 := pow_pos hd0 24
  have hqpow : d ^ 24 ≤ q := by
    calc
      d ^ 24 ≤ r * d ^ 24 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hr hd24.le
      _ ≤ q := hq
  have hq0 : 0 < q := hd24.trans_le hqpow
  have hd20 : (262144 : ℝ) ≤ d ^ 20 := by
    calc
      (262144 : ℝ) ≤ (2 : ℝ) ^ 20 := by norm_num
      _ ≤ d ^ 20 := pow_le_pow_left₀ (by norm_num) hd 20
  have hd21 : (10752 : ℝ) ≤ d ^ 21 := by
    calc
      (10752 : ℝ) ≤ (2 : ℝ) ^ 21 := by norm_num
      _ ≤ d ^ 21 := pow_le_pow_left₀ (by norm_num) hd 21
  have hqsquare : (512 * d ^ 2) ^ 2 ≤ q := by
    calc
      (512 * d ^ 2) ^ 2 = 262144 * d ^ 4 := by ring
      _ ≤ d ^ 20 * d ^ 4 :=
        mul_le_mul_of_nonneg_right hd20 (pow_nonneg hd0.le 4)
      _ = d ^ 24 := by ring
      _ ≤ q := hqpow
  have hroot : 512 * d ^ 2 ≤ Real.sqrt q := Real.le_sqrt_of_sq_le hqsquare
  have hlogq : Real.log q * (256 * d ^ 2) ≤ q := by
    have hlog : Real.log q ≤ 2 * Real.sqrt q := by
      have h := Real.log_le_self (Real.sqrt_nonneg q)
      rw [Real.log_sqrt hq0.le] at h
      linarith only [h]
    calc
      Real.log q * (256 * d ^ 2) ≤ (2 * Real.sqrt q) * (256 * d ^ 2) :=
        mul_le_mul_of_nonneg_right hlog (mul_nonneg (by norm_num) (sq_nonneg d))
      _ = (512 * d ^ 2) * Real.sqrt q := by ring
      _ ≤ Real.sqrt q * Real.sqrt q :=
        mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg q)
      _ = q := Real.mul_self_sqrt hq0.le
  have hpolynomial : 10752 * r * d ^ 3 ≤ q := by
    calc
      10752 * r * d ^ 3 = (r * d ^ 3) * 10752 := by ring
      _ ≤ (r * d ^ 3) * d ^ 21 :=
        mul_le_mul_of_nonneg_left hd21 (mul_nonneg hr0.le (pow_nonneg hd0.le 3))
      _ = r * d ^ 24 := by ring
      _ ≤ q := hq
  have hlognet : (2 * r * Real.log (21 * d)) * (256 * d ^ 2) ≤ q := by
    have hlog := Real.log_le_self (mul_nonneg (by norm_num : (0 : ℝ) ≤ 21) hd0.le)
    calc
      (2 * r * Real.log (21 * d)) * (256 * d ^ 2) ≤
          (2 * r * (21 * d)) * (256 * d ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlog (mul_nonneg (by norm_num) hr0.le))
          (mul_nonneg (by norm_num) (sq_nonneg d))
      _ = 10752 * r * d ^ 3 := by ring
      _ ≤ q := hpolynomial
  nlinarith only [hlogq, hlognet]

/-- The explicit sampling dimension `r * D^24` satisfies the random-sampling
condition in ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-dg`,
condition `eq:bootstrap-cond-dg`, lines 1065–1074.
This is a sufficient numerical threshold, with no optimality assertion. -/
private theorem bootstrapFailure_lt_one_of_ge_mul_pow (D r q : ℕ)
    (hD : 2 ≤ D) (hr : 1 ≤ r) (hq : r * D ^ 24 ≤ q) :
    bootstrapFailure D q r < 1 := by
  have hD0 : 0 < D := by omega
  have h22 : 4 ≤ D ^ 22 := by
    calc
      4 ≤ (2 : ℕ) ^ 22 := by decide
      _ ≤ D ^ 22 := Nat.pow_le_pow_left hD 22
  have hq4 : 4 * D ^ 2 ≤ q := by
    calc
      4 * D ^ 2 ≤ D ^ 22 * D ^ 2 := Nat.mul_le_mul_right _ h22
      _ = D ^ 24 := by ring
      _ ≤ r * D ^ 24 := by
        simpa only [one_mul] using Nat.mul_le_mul_right (D ^ 24) hr
      _ ≤ q := hq
  have hqn : 0 < q :=
    lt_of_lt_of_le (Nat.mul_pos (by decide) (pow_pos hD0 2)) hq4
  have hDR : 0 < (D : ℝ) := Nat.cast_pos.mpr hD0
  have hqR : 0 < (q : ℝ) := Nat.cast_pos.mpr hqn
  have hden : 0 < 256 * (D : ℝ) ^ 2 :=
    mul_pos (by norm_num) (pow_pos hDR 2)
  let s : ℝ := ((q / (2 * D ^ 2) : ℕ) : ℝ)
  let net : ℝ := 1 + 2 / Real.sqrt ((1 - 0.04) * s / (8 * (q : ℝ)))
  have hsample : (q : ℝ) ≤ 4 * (D : ℝ) ^ 2 * s := by
    have h := (div_le_iff₀
      (mul_pos (by norm_num : (0 : ℝ) < 4) (pow_pos hDR 2))).mp
      (bootstrap_sample_floor_lower_bound D q hD hq4)
    change (q : ℝ) ≤ s * (4 * (D : ℝ) ^ 2) at h
    nlinarith only [h]
  have hqcast : (r : ℝ) * (D : ℝ) ^ 24 ≤ (q : ℝ) := by
    have h : ((r * D ^ 24 : ℕ) : ℝ) ≤ (q : ℝ) := Nat.cast_le.mpr hq
    norm_num only [Nat.cast_mul, Nat.cast_pow] at h
    exact h
  have hbudget := bootstrap_logarithmic_budget_mul (D : ℝ) (r : ℝ) (q : ℝ)
    (Nat.ofNat_le_cast.mpr hD) (Nat.one_le_cast.mpr hr) hqcast
  have hnegative : ((2 * r : ℕ) : ℝ) * Real.log (21 * (D : ℝ)) +
      Real.log (q : ℝ) - s / 16 < 0 := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    apply (mul_lt_mul_iff_of_pos_right hden).mp
    nlinarith only [hbudget, hsample, hqR]
  have hnet : net ≤ 21 * (D : ℝ) := bootstrap_net_base_le D q hD hq4
  have hnet0 : 0 ≤ net :=
    add_nonneg zero_le_one (div_nonneg (by norm_num) (Real.sqrt_nonneg _))
  have hpower := pow_le_pow_left₀ hnet0 hnet (2 * r)
  have hexp : (21 * (D : ℝ)) ^ (2 * r) * (q : ℝ) * Real.exp (-(s / 16)) =
      Real.exp (((2 * r : ℕ) : ℝ) * Real.log (21 * (D : ℝ)) +
        Real.log (q : ℝ) - s / 16) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_nat_mul,
      Real.exp_log (mul_pos (by norm_num : (0 : ℝ) < 21) hDR), Real.exp_log hqR]
  change net ^ (2 * r) * (q : ℝ) * Real.exp (-(s / 16)) < 1
  calc
    net ^ (2 * r) * (q : ℝ) * Real.exp (-(s / 16)) ≤
        (21 * (D : ℝ)) ^ (2 * r) * (q : ℝ) * Real.exp (-(s / 16)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpower hqR.le)
        (Real.exp_pos _).le
    _ = Real.exp (((2 * r : ℕ) : ℝ) * Real.log (21 * (D : ℝ)) +
        Real.log (q : ℝ) - s / 16) := hexp
    _ < 1 := Real.exp_lt_one_iff.mpr hnegative

/-- A common improving family gives a quantitative viable subspace without
assuming a random-sampling inequality. The threshold is linear in the target
dimension and polynomial in the family parameter. Auxiliary to ALVV,
arXiv:1602.08828v2, Proposition `prop:albootstrap-dg`, lines 1062–1075.
The improving family and the two nearby target spaces are explicit inputs;
the physical construction discharges these inputs separately.

**Local fix (bootstrapping constants):** The canonical sampling and error
constants are documented in the companion note
https://sirui-lu.com/QICLean/paper-gaps/alvv16_bootstrap_constants.pdf. -/
theorem exists_isViable_finrank_lt_rank_mul_pow
    {M F : Type*}
    [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    {D : ℕ} {Delta : ℝ} {T T' : Submodule ℂ (M ⊗[ℂ] F)}
    (hTT' : IsCloseTo 0.005 T T') (hT'T : IsCloseTo 0.005 T' T)
    (A : Fin (D ^ 2) → M →L[ℂ] M)
    (hA : ∀ delta < 1, ∀ S : Submodule ℂ M, IsViable delta S T' →
      IsViable (Delta / (1 - delta) ^ 2) (⨆ i, S.map (A i : M →ₗ[ℂ] M)) T')
    (hD : 2 ≤ D) (hDelta : (D : ℝ) ^ 12 * Delta ≤ 0.00001)
    (hr : 1 ≤ Module.finrank ℂ T') :
    ∃ W : Submodule ℂ M,
      Module.finrank ℂ W < Module.finrank ℂ T' * D ^ 24 ∧ IsViable 0.015 W T := by
  have h22 : 4 ≤ D ^ 22 := by
    calc
      4 ≤ (2 : ℕ) ^ 22 := by decide
      _ ≤ D ^ 22 := Nat.pow_le_pow_left hD 22
  have hthreshold : 4 * D ^ 2 ≤ Module.finrank ℂ T' * D ^ 24 := by
    calc
      4 * D ^ 2 ≤ D ^ 22 * D ^ 2 := Nat.mul_le_mul_right _ h22
      _ = D ^ 24 := by ring
      _ ≤ Module.finrank ℂ T' * D ^ 24 := by
        simpa only [one_mul] using Nat.mul_le_mul_right (D ^ 24) hr
  apply exists_isViable_finrank_lt_of_bootstrap hTT' hT'T A hA hD hDelta hthreshold
  intro q hq
  exact bootstrapFailure_lt_one_of_ge_mul_pow D (Module.finrank ℂ T') q hD hr hq

end Submodule

open scoped BigOperators TensorProduct

namespace Submodule

/-- A dimension-dependent improving error is small enough for a second
closeness transfer. Auxiliary scalar estimate for ALVV,
arXiv:1602.08828v2, Lemma `l:close`, lines 484–489, and the argument for
Theorem `thm:al-dg`, lines 1079–1093. -/
private theorem improving_error_le_inverse_scale (m D : ℕ) (Delta : ℝ)
    (hm : 1 ≤ m) (hmD : m ≤ D)
    (hbudget : (D : ℝ) ^ 12 * Delta ≤ 0.00001) :
    Delta / (1 - (0.04 : ℝ)) ^ 2 ≤ 1 / (8 * (m : ℝ)) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr hm
  have hm0 : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have hpow : m ≤ D ^ 12 := hmD.trans (Nat.le_self_pow (by decide : 12 ≠ 0) D)
  have hcast : (m : ℝ) ≤ (D : ℝ) ^ 12 := by
    have h : (m : ℝ) ≤ ((D ^ 12 : ℕ) : ℝ) := Nat.cast_le.mpr hpow
    norm_num only [Nat.cast_pow] at h
    exact h
  by_cases hDelta : Delta ≤ 0
  · exact (div_nonpos_of_nonpos_of_nonneg hDelta (sq_nonneg _)).trans
      (one_div_nonneg.mpr (mul_nonneg (by norm_num) hm0.le))
  · have hDelta0 : 0 < Delta := lt_of_not_ge hDelta
    have hcross : Delta * (m : ℝ) ≤ 0.00001 := by
      have h := mul_le_mul_of_nonneg_right hcast hDelta0.le
      nlinarith only [h, hbudget]
    apply (div_le_iff₀ (by norm_num : 0 < (1 - (0.04 : ℝ)) ^ 2)).mpr
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hm0)).mpr
    nlinarith only [hcross]

section

variable {H M E : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- One fixed improving family transfers a constant-viable base subspace
to viability error at most the inverse scale. The isometry is fixed for both
targets. This is an explicitly abstract auxiliary to ALVV,
arXiv:1602.08828v2, Lemma `l:close`, lines 484–489, Lemma `l:er`,
lines 597–622, and Theorem `thm:al-dg`, lines 1079–1093. -/
theorem viable_enlargement_of_close_improving_target
    (u : H ≃ₗᵢ[ℂ] (M ⊗[ℂ] E)) (G T : Submodule ℂ H)
    (W0 : Submodule ℂ M) (b m D : ℕ) (Delta : ℝ)
    (hm : 1 ≤ m) (hmD : m ≤ D)
    (hW0 : IsViable (F := E) 0.015 W0 (G.map u.toLinearEquiv.toLinearMap))
    (hWdim : Module.finrank ℂ W0 ≤ b)
    (hGT : IsCloseTo (1 / (200 * (m : ℝ))) G T)
    (hTG : IsCloseTo (1 / (200 * (m : ℝ))) T G)
    (A : Fin (D ^ 2) → M →L[ℂ] M)
    (hbudget : (D : ℝ) ^ 12 * Delta ≤ 0.00001)
    (hA : ∀ delta < 1, ∀ S : Submodule ℂ M,
      IsViable (F := E) delta S (T.map u.toLinearEquiv.toLinearMap) →
      IsViable (F := E) (Delta / (1 - delta) ^ 2)
        ((⨆ i : Fin (D ^ 2), S.map (A i).toLinearMap) : Submodule ℂ M)
        (T.map u.toLinearEquiv.toLinearMap)) :
    let V : Submodule ℂ M := ⨆ i : Fin (D ^ 2), W0.map (A i).toLinearMap
    Module.finrank ℂ V ≤ b * D ^ 2 ∧
      IsViable (F := E) (1 / (2 * (m : ℝ))) V (G.map u.toLinearEquiv.toLinearMap) := by
  intro V
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr hm
  have hm0 : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm1
  have heps : 1 / (200 * (m : ℝ)) ≤ 0.005 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 200) hm0)).mpr
    nlinarith only [hm1]
  have hGTmap := (isCloseTo_map_iff u).mpr hGT
  have hTGmap := (isCloseTo_map_iff u).mpr hTG
  have hstart : IsViable (F := E) 0.04 W0 (T.map u.toLinearEquiv.toLinearMap) :=
    (IsCloseTo.trans hW0 hGTmap (by norm_num)).of_le (by linarith only [heps])
  have hraw : IsViable (F := E) (Delta / (1 - (0.04 : ℝ)) ^ 2) V
      (T.map u.toLinearEquiv.toLinearMap) := hA 0.04 (by norm_num) W0 hstart
  have himproved : IsViable (F := E) (1 / (8 * (m : ℝ))) V
      (T.map u.toLinearEquiv.toLinearMap) :=
    hraw.of_le (improving_error_le_inverse_scale m D Delta hm hmD hbudget)
  have hfinal : 2 * (1 / (8 * (m : ℝ)) + 1 / (200 * (m : ℝ))) ≤
      1 / (2 * (m : ℝ)) := by
    calc
      2 * (1 / (8 * (m : ℝ)) + 1 / (200 * (m : ℝ))) =
          (13 / 50 : ℝ) * (m : ℝ)⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (1 / 2 : ℝ) * (m : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr hm0.le)
      _ = 1 / (2 * (m : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  have hreturn : IsViable (F := E) (1 / (2 * (m : ℝ))) V
      (G.map u.toLinearEquiv.toLinearMap) :=
    (IsCloseTo.trans himproved hTGmap
      (one_div_nonneg.mpr (mul_nonneg (by norm_num) hm0.le))).of_le hfinal
  have hdim : Module.finrank ℂ V ≤ D ^ 2 * Module.finrank ℂ W0 := by
    change Module.finrank ℂ
      (↥((⨆ i : Fin (D ^ 2), W0.map (A i).toLinearMap) : Submodule ℂ M)) ≤ _
    simpa only [Fintype.card_fin] using
      (finrank_iSup_map_le_card_mul W0 (fun i : Fin (D ^ 2) ↦ (A i).toLinearMap))
  refine ⟨?_, hreturn⟩
  calc
    Module.finrank ℂ V ≤ D ^ 2 * Module.finrank ℂ W0 := hdim
    _ ≤ D ^ 2 * b := Nat.mul_le_mul_left _ hWdim
    _ = b * D ^ 2 := Nat.mul_comm _ _

end

end Submodule
