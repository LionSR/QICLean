/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ClusterExpansion.ClusterPart
import QICLean.Analysis.ClusterExpansion.Percolation
import QICLean.Analysis.TraceNormVariational

/-!
# The truncated expansion at every temperature

Hastings extends the high-temperature expansion to every temperature by eq. `mplt`:
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` with `n` even and `β/n` below the percolation temperature.
This file chooses the even number of factors, proves that the even power of the Hermitian
truncated operator is positive semidefinite, bounds the error of the power at every temperature
by the percolation bound of each factor (Hastings, `proj3new.tex`, lines 1303–1347), and passes
from trace pairings to the trace norm. The product form of the power is a statement about
operators on sites and is not part of this file.

Moved from TNLean (`e113e005`): `TNLean/Lattice/ClusterExpansion/AllTemperatures.lean` (without
`HasProductForm.pow_of_even`), `TruncatedPositivity.lean`, `TemperatureError.lean` and
`TraceNorm.lean`, in the namespace `ClusterExpansion`.
-/

/-!
## Positivity and the number of factors at every temperature

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1303–1320), extends the high-temperature
matrix product form to every temperature. For `β > β₀` he sets
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` (eq. `mplt`) with `n` the smallest even integer such that
`β/n ≤ β₀`. Taking `n` even makes `ρ(β, l_proj)` positive, and the `n` indices at each site, one
from each factor, group into a single index, so the power is again in the form of eq. `mpf`.

This section proves the parts of that step that do not refer to sites.

* An even power of a Hermitian matrix is positive semidefinite: `A^{2k} = (A^k)ᴴ A^k`.
* For `β ≥ 0` and `β₀ > 0` an even `n ≥ 2` with `β/n ≤ β₀` exists; the least positive even
  factor count at positive temperature lies in the interval `[β/β₀, β/β₀ + 2)`.

The grouping of indices in the product form is a statement about operators on sites and is
not part of this file.

**Local fix (positivity at every temperature):** the source states that `ρ(β, l_proj)` is
positive definite. An even power of a Hermitian operator is positive semidefinite, and positive
definite only when the base `ρ(β/n, l_proj)` is invertible, which the source does not establish.
The results here state positive semidefiniteness, which is what the even power is used for.
Documented in https://sirui-lu.com/TNLean/paper-gaps/hastings05_mplt_positivity.pdf.

### Main results

* `ClusterExpansion.posSemidef_pow_of_even`: `A^m ≥ 0` for Hermitian `A` and even
  `m`.
* `ClusterExpansion.exists_even_div_le`: an even number of factors suffices.

### References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mplt`, lines 1303–1320.
-/

open Matrix
open scoped MatrixOrder ComplexOrder

namespace ClusterExpansion

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An even power `A^{2k} = (A^k)ᴴ A^k` of a Hermitian matrix is positive semidefinite. -/
theorem posSemidef_pow_two_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (k : ℕ) :
    (A ^ (2 * k)).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (A ^ k)
  rwa [(hA.pow k).eq, ← pow_add, ← two_mul] at h

/-- **Positivity at every temperature.** An even power of a Hermitian matrix is positive
semidefinite. This is why Hastings takes the number of factors in eq. `mplt` even.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1313–1314. -/
theorem posSemidef_pow_of_even {A : Matrix n n ℂ} (hA : A.IsHermitian) {m : ℕ} (hm : Even m) :
    (A ^ m).PosSemidef := by
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul]
  exact posSemidef_pow_two_mul hA k

/-- The least even integer not below the temperature ratio. For positive temperatures
this integer is positive. Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312. -/
noncomputable def evenTemperatureFactors (β β₀ : ℝ) : ℕ := 2 * ⌈(β / β₀) / 2⌉₊

/-- The canonical even factor count is positive, reaches the high-temperature regime,
and differs from `β/β₀` by less than two.
Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312 and 1334–1347. -/
theorem evenTemperatureFactors_spec {β β₀ : ℝ} (hβ : 0 < β) (hβ₀ : 0 < β₀) :
    Even (evenTemperatureFactors β β₀) ∧ 2 ≤ evenTemperatureFactors β β₀ ∧
      β / evenTemperatureFactors β β₀ ≤ β₀ ∧
      β / β₀ ≤ evenTemperatureFactors β β₀ ∧
      (evenTemperatureFactors β β₀ : ℝ) < β / β₀ + 2 := by
  have hhalf : 0 < (β / β₀) / 2 := div_pos (div_pos hβ hβ₀) (by norm_num)
  have hceil : 0 < ⌈(β / β₀) / 2⌉₊ := Nat.ceil_pos.mpr hhalf
  have hm : 2 ≤ evenTemperatureFactors β β₀ := by unfold evenTemperatureFactors; omega
  have hmreal : (0 : ℝ) < evenTemperatureFactors β β₀ := by exact_mod_cast (by omega :
    0 < evenTemperatureFactors β β₀)
  have hlo : β / β₀ ≤ evenTemperatureFactors β β₀ := by
    have := Nat.le_ceil ((β / β₀) / 2)
    unfold evenTemperatureFactors
    push_cast
    nlinarith
  refine ⟨even_two_mul _, hm, ?_, hlo, ?_⟩
  · rw [div_le_iff₀ hmreal]
    have := (div_le_iff₀ hβ₀).mp hlo
    nlinarith
  · have := Nat.ceil_lt_add_one hhalf.le
    unfold evenTemperatureFactors
    push_cast
    nlinarith

/-- The canonical factor count is minimal among positive even choices that enter the
high-temperature regime. Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312. -/
theorem evenTemperatureFactors_le {β β₀ : ℝ} (hβ₀ : 0 < β₀) {m : ℕ}
    (hm : Even m) (hmpos : 0 < m) (hdiv : β / m ≤ β₀) : evenTemperatureFactors β β₀ ≤ m := by
  obtain ⟨k, rfl⟩ := hm
  have hmreal : (0 : ℝ) < ((k + k : ℕ) : ℝ) := by exact_mod_cast hmpos
  have hbound := (div_le_iff₀ hmreal).mp hdiv
  have hceil : ⌈(β / β₀) / 2⌉₊ ≤ k := by
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), div_le_iff₀ hβ₀]
    push_cast at hbound
    nlinarith
  unfold evenTemperatureFactors
  omega

/-- The factor count yields the corrected `β/β₀ + 2` exponential bound for every
nonnegative cluster weight. Hastings, arXiv:cond-mat/0508554v3, lines 1334–1347;
`docs/paper-gaps/hastings05_temperature_factor_count.tex`. -/
theorem exp_evenTemperatureFactors_mul_sub_one_le {β β₀ A : ℝ}
    (hβ : 0 < β) (hβ₀ : 0 < β₀) (hA : 0 ≤ A) :
    Real.exp ((evenTemperatureFactors β β₀ : ℝ) * A) - 1 ≤
      Real.exp ((β / β₀ + 2) * A) - 1 := by
  have hcount := (evenTemperatureFactors_spec hβ hβ₀).2.2.2.2
  exact sub_le_sub_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcount.le hA)) 1

/-- **The number of factors in eq. `mplt`.** For `β ≥ 0` and `β₀ > 0` there is an even
`n ≥ 2` with `β/n ≤ β₀`. At positive temperature the witness is the least such even integer;
at `β = 0` take two factors. Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312. -/
theorem exists_even_div_le {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : 0 < β₀) :
    ∃ m : ℕ, Even m ∧ 2 ≤ m ∧ β / m ≤ β₀ := by
  rcases hβ.eq_or_lt with hzero | hpos
  · refine ⟨2, by decide, le_rfl, ?_⟩
    simpa only [← hzero, zero_div] using hβ₀.le
  · have hs := evenTemperatureFactors_spec hpos hβ₀
    exact ⟨evenTemperatureFactors β β₀, hs.1, hs.2.1, hs.2.2.1⟩

end ClusterExpansion

/-!
## Positivity of the truncated operator at every temperature

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1303–1314), sets
`ρ(β, l_proj) = ρ(β/n, l_proj)^n` (eq. `mplt`) with `n` even, and states that the even power is
positive definite. The positivity of even powers in the first section applies to Hermitian
operators. This file shows that the truncated operator `ρ(β, l)` of the cluster expansion is
Hermitian when the terms `H_k` are, so the even power of the actual truncated operator is positive
semidefinite.

`ρ(β, l)` is the finite inclusion–exclusion sum `∑_U (-1)^{|U|} ρ(β, U)` (`truncatedExp_eq_sum`),
and each `ρ(β, C) = ∑_{D ⊆ C} (-1)^{|D|} e^{-β (H - H_B - H_D)}` is a sum of exponentials of
Hermitian operators with real coefficients.

**Local fix (positivity at every temperature):** the source states that `ρ(β, l_proj)` is
positive definite. The result here is positive semidefiniteness, as in the first section.
Documented in https://sirui-lu.com/TNLean/paper-gaps/hastings05_mplt_positivity.pdf.

### Main results

* `ClusterExpansion.isHermitian_clusterPart`: `ρ(β, C)` is Hermitian.
* `ClusterExpansion.isHermitian_truncatedExp`: `ρ(β, l)` is Hermitian.
* `ClusterExpansion.posSemidef_truncatedExp_pow`: `ρ(β/n, l)^n` is positive
  semidefinite for even `n`.

### References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, eq. `mplt`, lines 1303–1314.
-/

open Finset Matrix
open scoped MatrixOrder ComplexOrder

namespace ClusterExpansion

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
/-- A power of `-1` is self-adjoint, so it preserves Hermitian matrices as a scalar. -/
private theorem isHermitian_neg_one_pow_smul {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (k : ℕ) :
    ((-1 : ℂ) ^ k • A).IsHermitian :=
  hA.smul ((IsSelfAdjoint.one ℂ).neg.pow k)

/-- **The cluster part is Hermitian.** If `H` and the terms `h_k` with `k ∈ B ∪ C` are Hermitian,
then `ρ(β, C) = ∑_{D ⊆ C} (-1)^{|D|} e^{-β (H - H_B - H_D)}` is Hermitian. The cluster part is
Hastings' `ρ(β, C)`, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1174–1177. -/
theorem isHermitian_clusterPart {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {h : κ → Matrix ι ι ℂ}
    {B C : Finset κ} (hh : ∀ k ∈ B ∪ C, (h k).IsHermitian) (β : ℝ) :
    (clusterPart H h B C β).IsHermitian := by
  refine (isSelfAdjoint_sum _ fun D hD ↦
    (isHermitian_neg_one_pow_smul ?_ _).isSelfAdjoint).isHermitian
  have hsum : ∀ T ⊆ B ∪ C, (∑ k ∈ T, h k).IsHermitian := fun T hT ↦
    (isSelfAdjoint_sum _ fun i hi ↦ (hh i (hT hi)).isSelfAdjoint).isHermitian
  have hD' : D ⊆ B ∪ C := (mem_powerset.1 hD).trans subset_union_right
  exact (((hH.sub (hsum B subset_union_left)).sub (hsum D hD')).smul
    (IsSelfAdjoint.all β)).neg.exp

variable [Fintype κ] (G : SimpleGraph κ) [DecidableRel G.Adj]
  (large : Finset κ → Prop)

/-- **The truncated operator is Hermitian.** If every term `h_k` is Hermitian, then
`ρ(β, l)` is Hermitian: it is the inclusion–exclusion sum `∑_U (-1)^{|U|} ρ(β, U)` of Hermitian
cluster parts. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1101–1104 and
1197–1225. -/
theorem isHermitian_truncatedExp {h : κ → Matrix ι ι ℂ} (hh : ∀ k, (h k).IsHermitian)
    (β : ℝ) : (truncatedExp G large h β).IsHermitian := by
  classical
  have hH : (∑ k, h k).IsHermitian :=
    (isSelfAdjoint_sum _ fun k _ ↦ (hh k).isSelfAdjoint).isHermitian
  rw [truncatedExp_eq_sum G large (H := ∑ k, h k) rfl β]
  exact (isSelfAdjoint_sum _ fun U _ ↦ (isHermitian_neg_one_pow_smul
    (isHermitian_clusterPart hH (fun k _ ↦ hh k) β) _).isSelfAdjoint).isHermitian

/-- **The even power of the truncated operator is positive** (Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1303–1314, eq. `mplt`). If every term `h_k` is
Hermitian and `m` is even, then `ρ(β, l)^m` is positive semidefinite; with `β/n` in place of
`β` and `m = n`, this is the positivity of `ρ(β/n, l_proj)^n`. The source states positive
definiteness; see the module docstring. -/
theorem posSemidef_truncatedExp_pow {h : κ → Matrix ι ι ℂ} (hh : ∀ k, (h k).IsHermitian)
    (β : ℝ) {m : ℕ} (hm : Even m) : ((truncatedExp G large h β) ^ m).PosSemidef :=
  posSemidef_pow_of_even (isHermitian_truncatedExp G large hh β) hm

end ClusterExpansion

/-!
## The error of the truncated expansion at every temperature

At arbitrary temperature, Hastings, *Solving gapped Hamiltonians locally*
(arXiv:cond-mat/0508554v3, `References/cond-mat_0508554/proj3new.tex`, lines 1303–1347), replaces
`e^{-βH}` by the product `ρ(β, l) = ρ(β/n, l)^n` of `n` truncated factors (equation `mplt`), and
bounds the error by the operators `ρ_m` of the terms with at least `m` large clusters across the
`n` factors (lines 1334–1341), "following the same arguments as before" (line 1342).

This file proves that bound. Each factor is the inclusion–exclusion sum
`ρ(β/n, l) = ∑_U (-1)^{|U|} ρ(β/n, U)` over the admissible families `U` of large connected sets
(`truncatedExp_eq_sum`), and the empty family gives `e^{-βH/n}`. Expanding the `n`-th power gives a
sum over words `w` of `n` families, in which the word of empty families is `e^{-βH}`. Every other
word is a product of cluster parts whose trace against `O` has modulus at most
`‖O‖ (∏_j ∏_{C ∈ w_j} y^{n_C}) Tr e^{-βH}`
(`norm_trace_mul_list_prod_clusterPart_le_pow`), with `y = (e^{Jβ/n} - 1) e^{SJβ/n}`. Summing
over the words,

`|Tr (O (e^{-βH} - ρ(β/n, l)^n))| ≤ ‖O‖ ((∑_U ∏_{C ∈ U} y^{n_C})^n - 1) Tr e^{-βH}`,

and `∑_U ∏_{C ∈ U} y^{n_C} ≤ exp(∑_C y^{n_C})` over the large connected sets `C`. This is the
source's estimate of `∑_{m ≥ 1} ρ_m` by `∑_{m ≥ 1} (1/m!) (∑_C n y^{n_C})^m`.

**Local fix (number of factors):** the source prints the final bound (lines 1342–1347) with
`β/β₀` in the exponent, where its bound on `ρ_m` (lines 1334–1341) gives the number `n` of
factors. For the source's `n`, the smallest even integer with `β/n ≤ β₀`, one has
`β/β₀ ≤ n < β/β₀ + 2`, so the printed bound does not follow. The bound here has `n` and holds for
every `n > 0`. Documented in `docs/paper-gaps/hastings05_temperature_factor_count.tex`.

**Local fix (size threshold):** the percolation form takes the threshold `l` on the number of
terms of a large connected set, not on its diameter. Documented in
`docs/paper-gaps/hastings05_percolation_cluster_size.tex`.

### Main results

* `ClusterExpansion.sum_prod_le_exp_of_subset_powerset`: for families of subsets
  of `T` and nonnegative weights, `∑_U ∏_{i ∈ U} a_i ≤ exp(∑_{i ∈ T} a_i)`.
* `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le`:
  `|Tr (O (e^{-βH} - ρ(β/n, l)^n))| ≤ ‖O‖ (exp(n ∑_C y^{n_C}) - 1) Tr e^{-βH}`.
* `ClusterExpansion.norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation`: the
  source's form `‖O‖ (exp(n N e^{-l/ξ}) - 1) Tr e^{-βH}` from the count of large connected sets.

### References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1303–1347.
-/

open Finset Matrix
open scoped Matrix.Norms.L2Operator

namespace ClusterExpansion

/-- Scalars extract from an ordered product as their commutative product. -/
private theorem prod_ofFn_smul {𝕜 R : Type*} [CommSemiring 𝕜] [Semiring R] [Algebra 𝕜 R]
    {N : ℕ} (c : Fin N → 𝕜) (A : Fin N → R) :
    (List.ofFn fun n : Fin N ↦ c n • A n).prod =
      (∏ n : Fin N, c n) • (List.ofFn A).prod := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.ofFn_succ, List.prod_cons, ih (fun n ↦ c n.succ) (fun n ↦ A n.succ),
        smul_mul_smul_comm, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons]

/-- **Families of subsets.** For nonnegative weights `a` on a finite set `T` and any collection
`𝒜` of subsets of `T`, `∑_{U ∈ 𝒜} ∏_{i ∈ U} a_i ≤ exp(∑_{i ∈ T} a_i)`. The empty family
contributes `1` and the nonempty ones at most `exp(∑_{i ∈ T} a_i) - 1`
(`sum_nonempty_powerset_prod_le_exp`). -/
theorem sum_prod_le_exp_of_subset_powerset {α : Type*} {T : Finset α}
    {𝒜 : Finset (Finset α)} (h𝒜 : 𝒜 ⊆ T.powerset) {a : α → ℝ} (ha : ∀ i ∈ T, 0 ≤ a i) :
    ∑ U ∈ 𝒜, ∏ i ∈ U, a i ≤ Real.exp (∑ i ∈ T, a i) := by
  classical
  calc ∑ U ∈ 𝒜, ∏ i ∈ U, a i ≤ ∑ U ∈ T.powerset, ∏ i ∈ U, a i :=
        sum_le_sum_of_subset_of_nonneg h𝒜 fun U hU _ ↦
          prod_nonneg fun i hi ↦ ha i (mem_powerset.1 hU hi)
    _ = 1 + ∑ U ∈ T.powerset.erase ∅, ∏ i ∈ U, a i := by
        rw [← add_sum_erase _ _ (empty_mem_powerset T), prod_empty]
    _ ≤ 1 + (Real.exp (∑ i ∈ T, a i) - 1) := by
        gcongr
        exact sum_nonempty_powerset_prod_le_exp ha
    _ = Real.exp (∑ i ∈ T, a i) := by ring

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (G : SimpleGraph κ) [DecidableRel G.Adj] (large : Finset κ → Prop)

/-- **The error at every temperature** (Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1334–1347). Let `H = ∑_k h_k` be Hermitian with Hermitian terms of norm at most `J`, let
`β ≥ 0` and `n > 0`, and let every large connected set `C` have `n_C + n_{∂C} ≤ S n_C`. Then the
product `ρ(β, l) = ρ(β/n, l)^n` of equation `mplt`, for any `n > 0` (the source takes the
smallest even `n` with `β/n ≤ β₀`), satisfies, for every `O`,
`|Tr (O (e^{-βH} - ρ(β/n, l)^n))| ≤ ‖O‖ (exp(n ∑_C y^{n_C}) - 1) Tr e^{-βH}`, the sum over the
large connected sets, with `y = (e^{Jβ/n} - 1) e^{SJβ/n}`.

The source sums the bound `(1/m!) (∑_C n y^{n_C})^m ‖O‖` on `Z⁻¹ Tr (O ρ_m)` (lines 1334–1341)
over `m ≥ 1`; here the words of `n` admissible families are summed directly, which gives the same
exponential. Counting large connected sets gives `exp(n N exp(-l/ξ)) - 1`
(`norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation`), with the integer number `n` of
factors in place of the source's `β/β₀` (lines 1342–1347). The correction is recorded in
`docs/paper-gaps/hastings05_temperature_factor_count.tex`. -/
theorem norm_trace_mul_exp_sub_truncatedExp_pow_le {H : Matrix ι ι ℂ} (hHerm : H.IsHermitian)
    {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k) (hh : ∀ k, (h k).IsHermitian) {J : ℝ}
    (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ} (hβ : 0 ≤ β) {S : ℝ}
    (hS : ∀ C ∈ largeConnected G large, ((#C : ℝ) + #(boundary G C)) ≤ S * #C)
    {n : ℕ} (hn : 0 < n) :
    ‖(O * (NormedSpace.exp (-(β • H)) - truncatedExp G large h (β / n) ^ n)).trace‖ ≤
      ‖O‖ * (Real.exp (n * ∑ C ∈ largeConnected G large,
          ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))) ^ #C) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  classical
  set T := largeConnected G large
  set 𝒜 : Finset (Finset (Finset κ)) := {U ∈ T.powerset | IsAdmissible G U} with h𝒜
  set y := (Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))
  set Z := (NormedSpace.exp (-(β • H))).trace.re
  set cp : Finset (Finset κ) → Matrix ι ι ℂ :=
    fun U ↦ clusterPart H h (U.biUnion (boundary G)) (U.biUnion id) (β / n)
  set f : Finset (Finset κ) → ℝ := fun U ↦ ∏ C ∈ U, y ^ #C with hf
  set term : (Fin n → Finset (Finset κ)) → Matrix ι ι ℂ :=
    fun w ↦ (List.ofFn fun j ↦ (-1 : ℂ) ^ #(w j) • cp (w j)).prod with hterm_def
  set W := Fintype.piFinset fun _ : Fin n ↦ 𝒜 with hW
  set w₀ : Fin n → Finset (Finset κ) := fun _ ↦ ∅ with hw₀_def
  have hZ : 0 ≤ Z := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  have hmem : ∀ U ∈ 𝒜, U ⊆ T ∧ IsAdmissible G U := fun U hU ↦ by
    simpa only [h𝒜, mem_filter, mem_powerset] using hU
  have hconn : ∀ U ∈ 𝒜, ∀ C ∈ U, (G.induce (C : Set κ)).Connected := fun U hU C hC ↦
    ((mem_largeConnected G).1 ((hmem U hU).1 hC)).1
  have hw₀ : w₀ ∈ W := Fintype.mem_piFinset.2 fun _ ↦ by
    change (∅ : Finset (Finset κ)) ∈ 𝒜
    exact mem_filter.2 ⟨empty_mem_powerset _, by simp [IsAdmissible]⟩
  -- The thermal factor `e^{-βH} = (e^{-βH/n})^n` is the word of empty families.
  have hexp : NormedSpace.exp (-(β • H)) = term w₀ := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hsmul : -(β • H) = n • -((β / n) • H) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_neg, smul_smul, mul_div_cancel₀ _ hn']
    rw [hsmul, Matrix.exp_nsmul, ← clusterPart_empty_empty H h]
    simp [term, hw₀_def, cp, List.ofFn_const, List.prod_replicate]
  -- The `n`-th power of the truncated factor as a sum over words of admissible families.
  have hpow : truncatedExp G large h (β / n) ^ n = ∑ w ∈ W, term w := by
    rw [truncatedExp_eq_sum G large hH, sum_pow_eq_sum_words]
    refine sum_congr ?_ fun _ _ ↦ rfl
    ext w
    simp [W, h𝒜, T, Fintype.mem_piFinset]
  have hdiff : NormedSpace.exp (-(β • H)) - truncatedExp G large h (β / n) ^ n =
      -∑ w ∈ W.erase w₀, term w := by
    rw [hpow, ← add_sum_erase W _ hw₀, hexp]
    abel
  -- The weights `y^{n_C}` are nonnegative: `J ≥ 0` as soon as `C` is nonempty.
  have hy0 : ∀ C : Finset κ, 0 ≤ y ^ #C := fun C ↦ by
    rcases C.eq_empty_or_nonempty with hC | ⟨k, -⟩
    · simp [hC]
    · have hJ0 : 0 ≤ J := (norm_nonneg _).trans (hJ k)
      have hβn : 0 ≤ β / n := div_nonneg hβ n.cast_nonneg
      exact pow_nonneg (mul_nonneg (sub_nonneg.2 (Real.one_le_exp (mul_nonneg hβn hJ0)))
        (Real.exp_pos _).le) _
  -- The bound of one word.
  have hterm : ∀ w ∈ W, ‖(O * term w).trace‖ ≤ ‖O‖ * (∏ j, f (w j)) * Z := by
    intro w hw
    have hwA : ∀ j, w j ∈ 𝒜 := Fintype.mem_piFinset.1 hw
    simp only [hterm_def]
    rw [prod_ofFn_smul, Matrix.mul_smul, trace_smul, norm_smul, norm_prod]
    simp only [norm_pow, norm_neg, norm_one, one_pow, prod_const_one, one_mul]
    refine (norm_trace_mul_list_prod_clusterPart_le_pow hHerm hn
      (B := fun j ↦ (w j).biUnion (boundary G)) (C := fun j ↦ (w j).biUnion id)
      (fun _ k _ ↦ hh k) (fun _ k _ ↦ hJ k) O hβ fun j ↦
        card_add_card_biUnion_boundary_le G (hmem _ (hwA j)).2 (hconn _ (hwA j))
          fun C hC ↦ hS C ((hmem _ (hwA j)).1 hC)).trans_eq ?_
    rw [sum_congr rfl fun j _ ↦ card_biUnion_of_admissible G (hmem _ (hwA j)).2 (hconn _ (hwA j))]
    simp only [hf, prod_pow_eq_pow_sum]
    rfl
  -- Summing over the words.
  have hf0 : 0 ≤ ∑ U ∈ 𝒜, f U := sum_nonneg fun U _ ↦ prod_nonneg fun C _ ↦ hy0 C
  have hsum : ∑ U ∈ 𝒜, f U ≤ Real.exp (∑ C ∈ T, y ^ #C) :=
    sum_prod_le_exp_of_subset_powerset (filter_subset _ _) fun C _ ↦ hy0 C
  have hwords : ∑ w ∈ W.erase w₀, ∏ j, f (w j) = (∑ U ∈ 𝒜, f U) ^ n - 1 := by
    have h1 : (∑ U ∈ 𝒜, f U) ^ n = ∑ w ∈ W, ∏ j, f (w j) := by
      rw [hW]
      exact sum_pow' 𝒜 f n
    rw [h1, ← add_sum_erase W _ hw₀]
    simp [hw₀_def, hf]
  rw [hdiff, Matrix.mul_neg, trace_neg, norm_neg, Finset.mul_sum, trace_sum]
  calc ‖∑ w ∈ W.erase w₀, (O * term w).trace‖
      ≤ ∑ w ∈ W.erase w₀, ‖O‖ * (∏ j, f (w j)) * Z :=
        (norm_sum_le _ _).trans (sum_le_sum fun w hw ↦ hterm w (mem_of_mem_erase hw))
    _ = ‖O‖ * ((∑ U ∈ 𝒜, f U) ^ n - 1) * Z := by
        rw [← sum_mul, ← mul_sum, hwords]
    _ ≤ ‖O‖ * (Real.exp (n * ∑ C ∈ T, y ^ #C) - 1) * Z := by
        gcongr
        rw [Real.exp_nat_mul]
        exact pow_le_pow_left₀ hf0 hsum n

/-- **The error at every temperature, percolation form** (Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1342–1347). Under the hypotheses of
`norm_trace_mul_exp_sub_truncatedExp_pow_le`, let every large connected set have at least `l + 1`
terms, let there be at most `N x^k` large connected sets of `k` terms, and let
`0 < x y ≤ 1/2` with `y = (e^{Jβ/n} - 1) e^{SJβ/n}`. Then
`|Tr (O (e^{-βH} - ρ(β/n, l)^n))| ≤ ‖O‖ (exp(n N e^{-l/ξ}) - 1) Tr e^{-βH}` with
`ξ = 1 / ln(1/(xy))`. After division by `Z = Tr e^{-βH}`, this is the source's
`{exp[(β/β₀) N exp(-l/ξ_perc)] - 1} ‖O‖` with the number `n` of factors in place of `β/β₀`
(see the module docstring). -/
theorem norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation {H : Matrix ι ι ℂ}
    (hHerm : H.IsHermitian) {h : κ → Matrix ι ι ℂ} (hH : H = ∑ k, h k)
    (hh : ∀ k, (h k).IsHermitian) {J : ℝ} (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β : ℝ}
    (hβ : 0 ≤ β) {S : ℝ}
    (hS : ∀ C ∈ largeConnected G large, ((#C : ℝ) + #(boundary G C)) ≤ S * #C)
    {n : ℕ} (hn : 0 < n) {l : ℕ} (hl : ∀ C ∈ largeConnected G large, l + 1 ≤ #C) {N x : ℝ}
    (hcount : ∀ k, (#{C ∈ largeConnected G large | #C = k} : ℝ) ≤ N * x ^ k) (hN : 0 ≤ N)
    (hx : 0 ≤ x) (hxy0 : 0 < x * ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))))
    (hxy : x * ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))) ≤ 1 / 2) :
    ‖(O * (NormedSpace.exp (-(β • H)) - truncatedExp G large h (β / n) ^ n)).trace‖ ≤
      ‖O‖ * (Real.exp (n * (N * Real.exp (-(l / (Real.log
          (x * ((Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))))⁻¹)⁻¹)))) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  refine (norm_trace_mul_exp_sub_truncatedExp_pow_le G large hHerm hH hh hJ O hβ hS hn).trans ?_
  set y := (Real.exp (β / n * J) - 1) * Real.exp (S * J * (β / n))
  have hZ := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  have hy : 0 ≤ y := (pos_of_mul_pos_right hxy0 hx).le
  gcongr
  calc ∑ C ∈ largeConnected G large, y ^ #C ≤ N * ((x * y) ^ (l + 1) / (1 - x * y)) :=
        sum_pow_le_of_card_le hl hcount hN hx hy (by linarith)
    _ ≤ N * (x * y) ^ l := by
        gcongr
        exact pow_succ_div_one_sub_le hxy0.le hxy l
    _ = N * Real.exp (-(l / (Real.log (x * y)⁻¹)⁻¹)) := by rw [pow_eq_exp_neg_div _ hxy0]

/-- For the least sufficient even factor count, the corrected percolation error has
`β/β₀ + 2` in its exponent. The strict factor-count inequality is established by
`evenTemperatureFactors_spec`, rather than assumed.
Hastings, arXiv:cond-mat/0508554v3, lines 1307–1312 and 1334–1347;
`docs/paper-gaps/hastings05_temperature_factor_count.tex`. -/
theorem norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation_add_two
    {H : Matrix ι ι ℂ} (hHerm : H.IsHermitian) {h : κ → Matrix ι ι ℂ}
    (hH : H = ∑ k, h k) (hh : ∀ k, (h k).IsHermitian) {J : ℝ}
    (hJ : ∀ k, ‖h k‖ ≤ J) (O : Matrix ι ι ℂ) {β β₀ : ℝ}
    (hβ : 0 < β) (hβ₀ : 0 < β₀) {S : ℝ}
    (hS : ∀ C ∈ largeConnected G large, ((#C : ℝ) + #(boundary G C)) ≤ S * #C)
    {l : ℕ} (hl : ∀ C ∈ largeConnected G large, l + 1 ≤ #C) {N x : ℝ}
    (hcount : ∀ k, (#{C ∈ largeConnected G large | #C = k} : ℝ) ≤ N * x ^ k)
    (hN : 0 ≤ N) (hx : 0 ≤ x)
    (hxy0 : 0 < x * ((Real.exp (β / evenTemperatureFactors β β₀ * J) - 1) *
      Real.exp (S * J * (β / evenTemperatureFactors β β₀))))
    (hxy : x * ((Real.exp (β / evenTemperatureFactors β β₀ * J) - 1) *
      Real.exp (S * J * (β / evenTemperatureFactors β β₀))) ≤ 1 / 2) :
    ‖(O * (NormedSpace.exp (-(β • H)) -
      truncatedExp G large h (β / (evenTemperatureFactors β β₀)) ^
        (evenTemperatureFactors β β₀))).trace‖ ≤
      ‖O‖ * (Real.exp ((β / β₀ + 2) * (N * Real.exp (-(l / (Real.log
          (x * ((Real.exp (β / (evenTemperatureFactors β β₀) * J) - 1) *
            Real.exp (S * J * (β / (evenTemperatureFactors β β₀)))))⁻¹)⁻¹)))) - 1) *
        (NormedSpace.exp (-(β • H))).trace.re := by
  have hn : 0 < evenTemperatureFactors β β₀ := by
    have := (evenTemperatureFactors_spec hβ hβ₀).2.1
    omega
  refine (norm_trace_mul_exp_sub_truncatedExp_pow_le_percolation G large hHerm hH hh hJ O
    hβ.le hS hn hl hcount hN hx hxy0 hxy).trans ?_
  have hZ := (hHerm.smul (IsSelfAdjoint.all β)).neg.re_trace_exp_nonneg
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (exp_evenTemperatureFactors_mul_sub_one_le hβ hβ₀
        (mul_nonneg hN (Real.exp_pos _).le)) (norm_nonneg O)) hZ

end ClusterExpansion

/-!
## The trace-norm form of the cluster-expansion bound

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1281–1301), turns the bound of eq. `perc2` on
expectation values, `Z⁻¹ |Tr O ρ(β) − Tr O ρ(β, l_proj)| ≤ ε ‖O‖` for every operator `O`, into
the trace-norm bound `|ρ(β) − ρ(β, l_proj)|₁ ≤ ε |ρ(β)|₁`. The source chooses `O` diagonal in an
eigenbasis of the difference, with entries the signs of its eigenvalues.

This file proves the step for an arbitrary square matrix, without assuming it Hermitian. The
trace norm of `D` is `Tr √(Dᴴ D)`. QICLean's trace-norm duality
(`Matrix.re_trace_sqrt_conjTranspose_mul_self_le_of_forall_norm_trace_mul_le`) bounds it by the
bound on expectation values at the single operator `O = Uᴴ`, where `D = U √(Dᴴ D)` is the polar
decomposition. For Hermitian `D` this `Uᴴ` may be taken to be the source's sign operator.

### Main results

* `ClusterExpansion.re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le`: the
  source's form, `|ρ − σ|₁ ≤ ε Tr ρ` from `|Tr O ρ − Tr O σ| ≤ ε ‖O‖ Tr ρ`, for `ε ≥ 0`.

### References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1281–1301.
-/

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace ClusterExpansion

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The trace-norm form of eq. `perc2`.** Let `ρ` and `σ` be square matrices and `ε ≥ 0`. If
`|Tr O ρ − Tr O σ| ≤ ε ‖O‖ Tr ρ` for every matrix `O`, then the trace norm of `ρ − σ` is at
most `ε Tr ρ`. For the thermal state `ρ = ρ(β) = e^{-βH}`, which is positive, `Tr ρ = Z` is its
trace norm `|ρ(β)|₁`, and this is Hastings' bound
`|ρ(β) − ρ(β, l_proj)|₁ ≤ ε |ρ(β)|₁` with
`ε = exp(N (xy)⁻¹ e^{-l_proj/ξ_perc}) − 1` after the size-threshold correction recorded in
`docs/paper-gaps/hastings05_percolation_cluster_size.tex`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1281–1301. -/
theorem re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le {ρ σ : Matrix n n ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ.trace.re)
    (h : ∀ O : Matrix n n ℂ, ‖(O * ρ).trace - (O * σ).trace‖ ≤ ε * ‖O‖ * ρ.trace.re) :
    (CFC.sqrt ((ρ - σ)ᴴ * (ρ - σ))).trace.re ≤ ε * ρ.trace.re := by
  refine re_trace_sqrt_conjTranspose_mul_self_le_of_forall_norm_trace_mul_le fun O hO ↦ ?_
  rw [Matrix.mul_sub, Matrix.trace_sub]
  calc ‖(O * ρ).trace - (O * σ).trace‖ ≤ ε * ‖O‖ * ρ.trace.re := h O
    _ ≤ ε * 1 * ρ.trace.re := by gcongr
    _ = ε * ρ.trace.re := by ring

end ClusterExpansion
