/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Integral
import QICLean.Analysis.PowerExponential
import QICLean.ManyBody.Dynamics.GraphGrowth
import QICLean.ManyBody.Dynamics.TruncatedEvolution
import QICLean.ManyBody.Hamiltonian.GaussianFilterLocality

/-!
# Gaussian-filtered terms under truncated dynamics

Hastings approximates the Gaussian-filtered term `H̃_i` by
`M_i = (ΔE / √(2πq)) ∫ e^{-(tΔE)²/(2q)} e^{iH_s t} H_i e^{-iH_s t} dt`, where the truncated
Hamiltonian `H_s = ∑_{k ∈ s} h_k` keeps only the terms of the interaction near `i`: `M_i` is the
filter of `H_i` under `H_s`. If the generator and `W` act on a region `K`, so does the filter.
The difference of the two evolutions is controlled by the commutators of the omitted terms
with the truncated evolution, which the Lieb–Robinson bound makes small for omitted terms far
from the support of `W` (eq. `apb`); this is first stated with separate commutator bounds for
the omitted terms, then summed with a weight decaying in the distance of their anchors. On a
graph of degree at most `D`, a rate `μ > log (D + 1)` makes the weighted tail beyond distance `m`
decay at rate `(μ - log (D + 1))/2`, with no growth hypothesis. Combined with the gap estimate
of the filter, `M_i` nearly preserves the ground space (eq. `facld`), and with the choices of
the source the error is a single exponential in the truncation radius.

**Local fix (the truncated approximation `M_i`, eqs. `mid`, `apb`, `truncb`):** the truncation
is stated for any subfamily `s` of the terms acting inside a region `K` containing the support
of `W`, with the shell given by the omitted terms meeting `K`; the time integral of the
Lieb–Robinson function is bounded by `T` times its value at `T`; the constants are explicit; the
Gaussian weight printed in eq. `mid` as `exp[-(tΔE)²/2]` is read as `exp[-(tΔE)²/(2q)]` of eq.
`thd`. Documented in `docs/paper-gaps/hastings05_truncated_dynamics.tex`.

## Main results

* `ManyBody.gaussianFilteredTerm_mem_supportedOperators` — the support of `M_i`.
* `ManyBody.norm_commutator_heisenbergEvolution_le_graphDistance_finset` — the Lieb–Robinson
  bound against an operator on a finite region, with prefactor `2 |Y| C |S|`.
* `ManyBody.norm_gaussianFilteredTerm_sub_truncated_le`,
  `ManyBody.truncated_approx_gaussianFilteredTerm` — eq. `apb`.
* `ManyBody.norm_gaussianFilteredTerm_sub_truncated_le_degree_tail` — the weighted tail.
* `ManyBody.norm_sub_starProjection_truncated_apply_le` — eq. `facld`.

## References

Hastings, *Solving Gapped Hamiltonians Locally*, arXiv:cond-mat/0508554v3, `proj3new.tex`:
eqs. `mid`, `odef`, `hpdef` and `apb` (lines 285–320), eq. `facld` (lines 322–348), proved at
lines 1458–1533 with the comparison of the two evolutions (lines 1469–1505), eqs. `thib` and
`truncb` (lines 1507–1533).

Moved from TNLean, `TNLean/Lattice/GaussianFilteredTruncation.lean`,
`GaussianFilteredTruncationWeighted.lean`, `GaussianFilteredTruncationGround.lean`,
at commit `e113e005`.
Changes: an interaction `Φ : Interaction X T` on any system of sites in place of a
family of terms with supports on `ι → Fin d`, with `[∀ v, Nonempty (X v)]` in place of
`[NeZero d]`; the time cutoff is written `τ`; the comparison `norm_conj_sub_conj_le` of two
Heisenberg evolutions is replaced by `ManyBody.norm_heisenbergEvolution_sub_le_of_commutator_bound`.
-/

open GaussianFilter Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator InnerProductSpace NNReal Nat

namespace ManyBody

section Truncation

section Abstract

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Filtering two evolutions.** For Hermitian `H` and `H'`, if the evolutions of `W` under `H`
and `H'` differ by at most `ε` for `|t| ≤ T`, then the two filtered operators differ by at most
`ε + 2 ‖W‖ e^{-(TΔE)²/(2q)}`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `dmi`
(lines 1458–1467) and the split of the time integral at lines 1524–1533. -/
theorem norm_gaussianFilteredTerm_sub_le {q ΔE : ℝ} (hq : 0 ≤ q) {H H' : Matrix n n ℂ}
    (hH : H.IsHermitian) (hH' : H'.IsHermitian) (W : Matrix n n ℂ) {T ε : ℝ} (hT : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hloc : ∀ t ∈ Set.Icc (-T) T,
      ‖hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) -
          hermitianUnitaryPath H' t * W * hermitianUnitaryPath H' (-t)‖ ≤ ε) :
    ‖gaussianFilteredTerm q ΔE H W - gaussianFilteredTerm q ΔE H' W‖ ≤
      ε + 2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  set μ := gaussianReal 0 (q / ΔE ^ 2).toNNReal
  set g : ℝ → Matrix n n ℂ := fun t =>
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) -
      hermitianUnitaryPath H' t * W * hermitianUnitaryPath H' (-t)
  have hI := integrable_intertwinerIntegrand (q / ΔE ^ 2).toNNReal hH hH W
  have hI' := integrable_intertwinerIntegrand (q / ΔE ^ 2).toNNReal hH' hH' W
  have heq : gaussianFilteredTerm q ΔE H W - gaussianFilteredTerm q ΔE H' W = ∫ t, g t ∂μ := by
    simp only [gaussianFilteredTerm, gaussianIntertwiner]
    rw [integral_sub hI hI']
  have hglob (t : ℝ) : ‖g t‖ ≤ 2 * ‖W‖ := by
    refine (norm_sub_le _ _).trans_eq ?_
    rw [norm_intertwinerIntegrand hH hH W t, norm_intertwinerIntegrand hH' hH' W t]
    ring
  have hg : Integrable g μ := hI.sub hI'
  rw [heq, ← integral_add_compl (s := Set.Icc (-T) T) measurableSet_Icc hg]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add (norm_setIntegral_le_of_norm_le_const (μ := μ) (by finiteness) hloc)
    (norm_setIntegral_le_of_norm_le_const (μ := μ) (by finiteness) (fun t _ => hglob t))).trans ?_
  exact add_le_add (mul_le_of_le_one_right hε measureReal_le_one)
    (mul_le_mul_of_nonneg_left (measure_compl_Icc_le_div_sq hq hT) (by positivity))

end Abstract

section Support

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)]

/-- If the generator `H` and the operator `W` act on `K`, so does the evolution
`e^{iHt} W e^{-iHt}`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 302–304:
`H_i^trunc(t)` acts only on sites within distance `l_proj` of `i`. -/
theorem hermitianUnitaryPath_conj_mem_supportedOperators {K : Finset V}
    {H W : Matrix (Config X) (Config X) ℂ}
    (hH : H ∈ supportedOperators X K)
    (hW : W ∈ supportedOperators X K) (t : ℝ) :
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t) ∈ supportedOperators X K := by
  have hU (s : ℝ) : hermitianUnitaryPath H s ∈ supportedOperators X K :=
    hermitianUnitaryPath_mem_supportedOperators hH s
  exact mul_mem (mul_mem (hU t) hW) (hU (-t))

/-- If the generator `H` and the operator `W` act on `K`, so does the filtered operator. With
`H = H_loc` and `W = H_i`, this is the support of `M_i` in Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eqs. `mid`, `odef`, `hpdef` (lines 285–303). -/
theorem gaussianFilteredTerm_mem_supportedOperators (q ΔE : ℝ) {K : Finset V}
    {H W : Matrix (Config X) (Config X) ℂ}
    (hH : H ∈ supportedOperators X K)
    (hW : W ∈ supportedOperators X K) :
    gaussianFilteredTerm q ΔE H W ∈ supportedOperators X K := by
  set μ := gaussianReal 0 (q / ΔE ^ 2).toNNReal
  set f : ℝ → Matrix (Config X) (Config X) ℂ := fun t =>
    hermitianUnitaryPath H t * W * hermitianUnitaryPath H (-t)
  have hf : gaussianFilteredTerm q ΔE H W = ∫ t, f t ∂μ := rfl
  rw [hf]
  by_cases hint : Integrable f μ
  · let V := Subalgebra.toSubmodule (supportedOperators X K).toSubalgebra
    exact (V.restrictScalars ℝ).convex.integral_mem (Submodule.closed_of_finiteDimensional V)
      (Filter.Eventually.of_forall fun t => hermitianUnitaryPath_conj_mem_supportedOperators
        hH hW t) hint
  · rw [integral_undef hint]
    exact zero_mem _

end Support

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]
  (G : SimpleGraph V) {T : κ → Finset V}
  (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)

include hHerm hDiam hCard hBudget

/-- **Lieb–Robinson bound against an operator on several sites.** Let `A` act on `S` and `B` on
a finite set `Y` with every site of `Y` at graph distance at least `m` from every site of `S`.
Then `‖[B, τ_t(A)]‖ ≤ 2 |Y| C |S| ‖A‖ ‖B‖ e^{v|t| - μm}`, with `C = 2 + 4 |b₀| e^{2μR}` and
`v = 2 v_R |b₀| e^{2μR} + 1`: the partial trace of `τ_t(A)` over `Y` commutes with `B`, and
it differs from `τ_t(A)` by at most the sum of the single-site commutator bounds over `Y`.
This is the input `‖[H_j, H_i(t')]‖` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1484–1505. The two-set bound
`ManyBody.norm_heisenberg_commutator_le_graphDistance_finsets_numeric` has no factor `|Y|`
and prefactor `4 |S|`, at the larger rate `4 v_R |b₀| e^{2μR}`; neither implies the other. -/
theorem norm_commutator_heisenbergEvolution_le_graphDistance_finset [∀ v, Nonempty (X v)]
    (S : Finset V)
    {A B : Matrix (Config X) (Config X) ℂ}
    (hA : A ∈ supportedOperators X S)
    (Y : Finset V) (hB : B ∈ supportedOperators X Y) (μ : ℝ)
    (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ x ∈ S, ∀ y ∈ Y, (m : ℕ∞) ≤ G.edist x y) (t : ℝ) :
    ‖B * heisenbergEvolution Φ.hamiltonian t A - heisenbergEvolution Φ.hamiltonian t A
        * B‖ ≤
      2 * (Y.card : ℝ) * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖A‖ * ‖B‖ *
        Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |t| - μ * m) := by
  set τA := heisenbergEvolution Φ.hamiltonian t A
  set c : ℝ := (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖A‖ *
    Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |t| - μ * m)
  have hloc : ‖τA - regionExpectation Yᶜ τA‖ ≤ ∑ _y ∈ Yᶜᶜ, c :=
    norm_sub_regionExpectation_le Yᶜ τA (fun _ => c) fun y hy U hU hUu => by
      have hyY : y ∈ Y := by simpa using hy
      have hLR := norm_heisenberg_commutator_le_graphDistance_finset G Φ hHerm
        R hDiam vR hCard b₀ hBudget S hA y
        hU
        μ hμ m (fun x hx => hm x hx y hyY) t
      rw [CStarRing.norm_of_mem_unitary hUu, mul_one] at hLR
      exact hLR
  rw [compl_compl, Finset.sum_const, nsmul_eq_mul] at hloc
  have hcomm : Commute B (regionExpectation Yᶜ τA) :=
    commute_of_mem_supportedOperators_of_disjoint hB
        (regionExpectation_mem_supportedOperators _ _) disjoint_compl_right
  have hsplit : B * τA - τA * B =
      B * (τA - regionExpectation Yᶜ τA) -
        (τA - regionExpectation Yᶜ τA) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hcomm.eq]
    abel
  rw [hsplit]
  calc _ ≤ 2 * ‖τA - regionExpectation Yᶜ τA‖ * ‖B‖ := norm_commutator_le B _
    _ ≤ 2 * ((Y.card : ℝ) * c) * ‖B‖ := by gcongr
    _ = _ := by ring

/-- **The commutator with the omitted terms.** Let `W` act on `S ⊆ K`, let `s` be a family of
terms acting inside `K`, and let `m` bound from below the graph distance from `S` to every
omitted term meeting `K`. Then the commutator of the omitted part `H - H_s` with the truncated
evolution `e^{iH_s u} W e^{-iH_s u}` has norm at most
`2 v_R C |S| ‖W‖ (∑ ‖hₖ‖) e^{v|u| - μm}`, the sum running over the omitted terms meeting `K`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1469–1505: the omitted terms far
from `i` commute with the truncated evolution, and the remaining ones are bounded by the
Lieb–Robinson bound. -/
theorem norm_commutator_sub_truncated_le [∀ v, Nonempty (X v)] [DecidableEq κ] (s : Finset κ)
    (K : Finset V) (hsK : ∀ k ∈ s, T k ⊆ K) (S : Finset V) (hSK : S ⊆ K)
    {W : Matrix (Config X) (Config X) ℂ} (hW : W ∈ supportedOperators X S)
    (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (T k) K → ∀ x ∈ S, ∀ y ∈ T k, (m : ℕ∞) ≤ G.edist x y) (u : ℝ) :
    ‖(Φ.hamiltonian - ∑ k ∈ s, Φ.term k) *
          (hermitianUnitaryPath (∑ k ∈ s, Φ.term k) u * W *
            hermitianUnitaryPath (∑ k ∈ s, Φ.term k) (-u)) -
        hermitianUnitaryPath (∑ k ∈ s, Φ.term k) u * W *
            hermitianUnitaryPath (∑ k ∈ s, Φ.term k) (-u) * (Φ.hamiltonian - ∑ k ∈ s, Φ.term k)‖ ≤
      2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ *
        (∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (T k) K), ‖Φ.term k‖) *
        Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |u| - μ * m) := by
  let Φ' : Interaction X T := ⟨fun k => if k ∈ s then Φ.term k else 0, fun k => by
    split_ifs
    exacts [Φ.mem k, zero_mem _]⟩
  have hsum : Φ'.hamiltonian = ∑ k ∈ s, Φ.term k := by
    simp only [Interaction.hamiltonian, Φ']
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hHerm' (k : κ) : (Φ'.term k).IsHermitian := by
    simp only [Φ']
    split_ifs
    exacts [hHerm k, isHermitian_zero]
  have hBudget' (x : V) : ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ'.term j‖ ≤ b₀ := by
    refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hBudget x)
    simp only [Φ']
    split_ifs
    exacts [le_rfl, by simp]
  have hHsK : (∑ k ∈ s, Φ.term k) ∈ supportedOperators X K :=
    sum_mem fun k hk =>
      supportedOperators_mono (Finset.coe_subset.mpr (hsK k hk)) (Φ.mem k)
  have hAK := hermitianUnitaryPath_conj_mem_supportedOperators hHsK
    (supportedOperators_mono (Finset.coe_subset.mpr hSK) hW) u
  have hA : heisenbergEvolution Φ'.hamiltonian u W = hermitianUnitaryPath (∑ k ∈ s, Φ.term k) u *
      W *
      hermitianUnitaryPath (∑ k ∈ s, Φ.term k) (-u) := by
    rw [hsum]
    rfl
  generalize hAdef : hermitianUnitaryPath (∑ k ∈ s, Φ.term k) u * W *
      hermitianUnitaryPath (∑ k ∈ s, Φ.term k) (-u) = A at hAK hA ⊢
  generalize hF : 2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ *
    Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |u| - μ * m) = F
  have hterm (k : κ) (hk : k ∉ s) :
      ‖Φ.term k * A - A * Φ.term k‖ ≤ if ¬Disjoint (T k) K then F * ‖Φ.term k‖ else 0 := by
    split_ifs with hd
    · rw [(commute_of_mem_supportedOperators_of_disjoint (Φ.mem k) hAK hd).eq,
        sub_self, norm_zero]
    · have hLR := norm_commutator_heisenbergEvolution_le_graphDistance_finset G Φ'
        hHerm' R hDiam vR hCard b₀ hBudget' S hW (T k) (Φ.mem k) μ hμ m
        (hm k hk hd) u
      rw [hA] at hLR
      refine hLR.trans (le_of_le_of_eq ?_ (congrArg (· * ‖Φ.term k‖) hF))
      have hXk : ((T k).card : ℝ) ≤ vR := by exact_mod_cast hCard k
      have hrest : 0 ≤ (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * ‖Φ.term k‖ *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * |u| - μ * m) := by
        positivity
      nlinarith
  rw [Interaction.hamiltonian, ← Finset.sum_compl_add_sum s Φ.term, add_sub_cancel_right,
    Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ sᶜ, ‖Φ.term k * A - A * Φ.term k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ sᶜ, if ¬Disjoint (T k) K then F * ‖Φ.term k‖ else 0 :=
      Finset.sum_le_sum fun k hk => hterm k (Finset.mem_compl.mp hk)
    _ = F * ∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (T k) K), ‖Φ.term k‖ := by
      rw [← Finset.sum_filter, Finset.mul_sum]
    _ = _ := by rw [← hF]; ring

/-- **The truncated dynamics, with the norms of the omitted terms.** Let `W` act on `S ⊆ K`,
and let `s` be a family of terms acting inside `K`. Let `m` bound from below the graph distance
from `S` to every omitted term meeting `K`. Then for every `μ ≥ 0` and `τ ≥ 0` the filters of
`W` under `H = ∑ₖ hₖ` and under `H_s = ∑_{k ∈ s} hₖ` differ by at most
`2 v_R C |S| ‖W‖ (∑ ‖hₖ‖) τ e^{vT - μm} + 2 ‖W‖ e^{-(TΔE)²/(2q)}`, the sum running over the
omitted terms meeting `K`, with `C = 2 + 4 |b₀| e^{2μR}` and `v = 2 v_R |b₀| e^{2μR} + 1`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, eq. `apb` (lines 300–320), proved at
lines 1458–1533: the difference of the two evolutions is bounded for `|t| ≤ τ` by the
commutators with the omitted terms (eqs. `thib`, `truncb`), and the Gaussian tail bounds the
rest. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_sum [∀ v, Nonempty (X v)] [DecidableEq κ]
    {q ΔE : ℝ}
    (hq : 0 ≤ q) (s : Finset κ) (K : Finset V) (hsK : ∀ k ∈ s, T k ⊆ K) (S : Finset V)
    (hSK : S ⊆ K) {W : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (T k) K → ∀ x ∈ S, ∀ y ∈ T k, (m : ℕ∞) ≤ G.edist x y)
    {τ : ℝ} (hT : 0 ≤ τ) :
    ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W - gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W‖ ≤
      2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ *
          (∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (T k) K), ‖Φ.term k‖) * τ *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * τ - μ * m) +
        2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) := by
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hHs : (∑ k ∈ s, Φ.term k).IsHermitian :=
    (isSelfAdjoint_sum s fun k _ ↦ (hHerm k).isSelfAdjoint).isHermitian
  have hv : 0 ≤ 2 * vR * |b₀| * Real.exp (2 * μ * R) + 1 := by positivity
  generalize hF : 2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ *
    (∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (T k) K), ‖Φ.term k‖) = F
  have hF0 : 0 ≤ F := by rw [← hF]; positivity
  have hstep (u : ℝ) (hu : |u| ≤ τ) :
      ‖(Φ.hamiltonian - ∑ k ∈ s, Φ.term k) *
            (hermitianUnitaryPath (∑ k ∈ s, Φ.term k) u * W *
              hermitianUnitaryPath (∑ k ∈ s, Φ.term k) (-u)) -
          hermitianUnitaryPath (∑ k ∈ s, Φ.term k) u * W *
              hermitianUnitaryPath (∑ k ∈ s, Φ.term k) (-u) * (Φ.hamiltonian - ∑ k ∈ s, Φ.term k)‖ ≤
        F * Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * τ - μ * m) := by
    refine (norm_commutator_sub_truncated_le G Φ hHerm R hDiam vR hCard b₀
      hBudget s K hsK S hSK hW μ hμ m hm u).trans ?_
    rw [hF]
    gcongr
  have h2 := norm_gaussianFilteredTerm_sub_le (ΔE := ΔE) hq hH hHs W hT
    (ε := F * Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * τ - μ * m) * τ)
    (by positivity) fun t ht => by
      have htT : |t| ≤ τ := abs_le.mpr ht
      refine (le_of_eq (norm_sub_rev _ _)).trans
        ((norm_heisenbergEvolution_sub_le_of_commutator_bound hH W t
          (F * Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * τ - μ * m))
          fun u hu ↦ ?_).trans ?_)
      · rw [← norm_neg]
        convert hstep u ?_ using 2
        · simp only [heisenbergEvolution]
          noncomm_ring
        · exact (by simpa using Set.abs_sub_left_of_mem_uIcc hu : |u| ≤ |t|).trans htT
      · gcongr
  refine h2.trans (le_of_eq ?_)
  ring

/-- **Hastings' truncated approximation, eq. `apb`.** If moreover every term has norm at most
`J`, the filters of `W` under `H` and under the truncated Hamiltonian `H_s` differ by at most
`2 v_R C |S| ‖W‖ J N τ e^{vT - μm} + 2 ‖W‖ e^{-(TΔE)²/(2q)}`, where `N` is the number of
omitted terms meeting `K`. With `W = H_i`, `K` the sites within distance `l_proj` of `i` and `s`
the terms within distance `l_proj - R` of `i`, this is Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eq. `apb` (lines 300–320), proved at lines 1458–1533, with `N` in place of
`N(l_proj)` and `q`, `τ` free. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le [∀ v, Nonempty (X v)] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (s : Finset κ) (K : Finset V) (hsK : ∀ k ∈ s, T k ⊆ K) (S : Finset V)
    (hSK : S ⊆ K) {W : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (J : ℝ) (hJ : ∀ k, ‖Φ.term k‖ ≤ J) (μ : ℝ)
    (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (T k) K → ∀ x ∈ S, ∀ y ∈ T k, (m : ℕ∞) ≤ G.edist x y)
    {τ : ℝ} (hT : 0 ≤ τ) :
    ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W - gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W‖ ≤
      2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
          ((sᶜ.filter (fun k => ¬Disjoint (T k) K)).card : ℝ) * τ *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * τ - μ * m) +
        2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) := by
  refine (norm_gaussianFilteredTerm_sub_truncated_le_sum G Φ hHerm R hDiam vR
    hCard b₀ hBudget hq s K hsK S hSK hW μ hμ m hm hT).trans ?_
  have hsum : ∑ k ∈ sᶜ.filter (fun k => ¬Disjoint (T k) K), ‖Φ.term k‖ ≤
      J * ((sᶜ.filter (fun k => ¬Disjoint (T k) K)).card : ℝ) := by
    rw [mul_comm, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun k _ => hJ k
  have hrest : 0 ≤ 2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * τ *
      Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * τ - μ * m) := by positivity
  nlinarith

/-- **Hastings' approximation `M_i`.** The filter `M = W_tilde_s` of `W` under the truncated
Hamiltonian `H_s = ∑_{k ∈ s} hₖ` acts on `K`, has norm at most `‖W‖`, is Hermitian when `W` is,
and approximates the filter of `W` under `H` as in
`norm_gaussianFilteredTerm_sub_truncated_le`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eqs. `mid`, `odef`, `hpdef`, `apb` and `‖M_i‖ ≤ J` (lines 285–320). -/
theorem truncated_approx_gaussianFilteredTerm [∀ v, Nonempty (X v)] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (s : Finset κ) (K : Finset V) (hsK : ∀ k ∈ s, T k ⊆ K) (S : Finset V)
    (hSK : S ⊆ K) {W : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (J : ℝ) (hJ : ∀ k, ‖Φ.term k‖ ≤ J) (μ : ℝ)
    (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (T k) K → ∀ x ∈ S, ∀ y ∈ T k, (m : ℕ∞) ≤ G.edist x y)
    {τ : ℝ} (hT : 0 ≤ τ) :
    gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W ∈ supportedOperators X K ∧
      ‖gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W‖ ≤ ‖W‖ ∧
      (W.IsHermitian → (gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W).IsHermitian) ∧
      ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W -
          gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W‖ ≤
        2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
            ((sᶜ.filter (fun k => ¬Disjoint (T k) K)).card : ℝ) * τ *
            Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * τ - μ * m) +
          2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) := by
  have hHs : (∑ k ∈ s, Φ.term k).IsHermitian :=
    (isSelfAdjoint_sum s fun k _ ↦ (hHerm k).isSelfAdjoint).isHermitian
  have hHsK : (∑ k ∈ s, Φ.term k) ∈ supportedOperators X K :=
    sum_mem fun k hk =>
      supportedOperators_mono (Finset.coe_subset.mpr (hsK k hk)) (Φ.mem k)
  exact ⟨gaussianFilteredTerm_mem_supportedOperators q ΔE hHsK
    (supportedOperators_mono (Finset.coe_subset.mpr hSK) hW),
    norm_gaussianFilteredTerm_le q ΔE hHs W, isHermitian_gaussianFilteredTerm q ΔE hHs,
    norm_gaussianFilteredTerm_sub_truncated_le G Φ hHerm R hDiam vR hCard b₀
      hBudget hq s K hsK S hSK hW J hJ μ hμ m hm hT⟩

end Graph

end Truncation

section TruncationWeighted

section Abstract

variable {ν κ : Type*} [Fintype ν] [DecidableEq ν] [Fintype κ] [DecidableEq κ]

/-- Termwise commutator estimates give a truncation bound without a shell-size factor.
Hastings, arXiv:cond-mat/0508554v3, lines 1469–1505 and 1524–1533. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_of_commutator_bounds
    (h : κ → Matrix ν ν ℂ) (hHerm : ∀ k, (h k).IsHermitian) (s : Finset κ)
    (W : Matrix ν ν ℂ) {q ΔE T : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T)
    (C : κ → ℝ) (hC : ∀ k, 0 ≤ C k)
    (hcomm : ∀ k ∉ s, ∀ u ∈ Set.Icc (-T) T,
      ‖h k * (hermitianUnitaryPath (∑ j ∈ s, h j) u * W *
          hermitianUnitaryPath (∑ j ∈ s, h j) (-u)) -
        (hermitianUnitaryPath (∑ j ∈ s, h j) u * W *
          hermitianUnitaryPath (∑ j ∈ s, h j) (-u)) * h k‖ ≤ C k) :
    ‖gaussianFilteredTerm q ΔE (∑ k, h k) W -
        gaussianFilteredTerm q ΔE (∑ k ∈ s, h k) W‖ ≤
      T * (∑ k ∈ sᶜ, C k) + 2 * ‖W‖ * Real.exp (-(T * ΔE) ^ 2 / (2 * q)) := by
  have hH : (∑ k, h k).IsHermitian :=
    (isSelfAdjoint_sum _ fun k _ ↦ (hHerm k).isSelfAdjoint).isHermitian
  have hHs : (∑ k ∈ s, h k).IsHermitian :=
    (isSelfAdjoint_sum s fun k _ ↦ (hHerm k).isSelfAdjoint).isHermitian
  have hsum0 : 0 ≤ ∑ k ∈ sᶜ, C k := Finset.sum_nonneg fun k _ ↦ hC k
  have hstep (u : ℝ) (hu : u ∈ Set.Icc (-T) T) :
      ‖((∑ k, h k) - ∑ k ∈ s, h k) *
          (hermitianUnitaryPath (∑ j ∈ s, h j) u * W *
            hermitianUnitaryPath (∑ j ∈ s, h j) (-u)) -
        (hermitianUnitaryPath (∑ j ∈ s, h j) u * W *
          hermitianUnitaryPath (∑ j ∈ s, h j) (-u)) *
          ((∑ k, h k) - ∑ k ∈ s, h k)‖ ≤ ∑ k ∈ sᶜ, C k := by
    rw [← Finset.sum_compl_add_sum s h, add_sub_cancel_right,
      Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk ↦
      hcomm k (Finset.mem_compl.mp hk) u hu)
  have hf := norm_gaussianFilteredTerm_sub_le (ΔE := ΔE) hq hH hHs W hT
    (ε := (∑ k ∈ sᶜ, C k) * T) (mul_nonneg hsum0 hT) (fun t ht ↦ by
      have htT : |t| ≤ T := abs_le.mpr ht
      refine (le_of_eq (norm_sub_rev _ _)).trans
        ((norm_heisenbergEvolution_sub_le_of_commutator_bound hH W t (∑ k ∈ sᶜ, C k)
          fun u hu ↦ ?_).trans ?_)
      · rw [← norm_neg]
        convert hstep u ?_ using 2
        · simp only [heisenbergEvolution]
          noncomm_ring
        · exact abs_le.mp ((by simpa using Set.abs_sub_left_of_mem_uIcc hu : |u| ≤ |t|).trans htT)
      · exact mul_le_mul_of_nonneg_left htT hsum0)
  simpa only [mul_comm T] using hf

end Abstract

section Graph

open GaussianFilter

variable {V κ : Type*} [Fintype V] [DecidableEq V] [Fintype κ] {X : V → Type*}
  [∀ v, Fintype (X v)] [∀ v, DecidableEq (X v)]

/-- Finite-support propagation in the distance between two anchors, with zero kernel
between components. Hastings, arXiv:cond-mat/0508554v3, lines 1469–1505. -/
theorem norm_commutator_heisenbergEvolution_le_anchor_kernel
    (G : SimpleGraph V) {T : κ → Finset V}
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, G.edist x y ≤ R)
    (vR : ℕ) (hvR : 1 ≤ vR) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (z : V) (S : Finset V) (hSrad : ∀ x ∈ S, G.edist z x ≤ R)
    {W : Matrix (Config X) (Config X) ℂ} (hW : W ∈ supportedOperators X S)
    (b : V) (Y : Finset V) (hYrad : ∀ y ∈ Y, G.edist y b ≤ R)
    {B : Matrix (Config X) (Config X) ℂ} (hB : B ∈ supportedOperators X Y)
    {μ : ℝ} (hμ : 0 < μ) (t : ℝ) :
    ‖B * heisenbergEvolution Φ.hamiltonian t W -
        heisenbergEvolution Φ.hamiltonian t W * B‖ ≤
      4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * ‖B‖ *
        Real.exp ((4 * vR * |b₀| * Real.exp (2 * μ * R)) * |t|) *
        (if G.edist z b = ⊤ then 0 else Real.exp (-(μ * ((G.edist z b).toNat : ℝ)))) := by
  let v : ℝ := 4 * vR * |b₀| * Real.exp (2 * μ * R)
  let C : ℝ := 4 * ((S.card : ℝ) + 1) * Real.exp (v * |t|)
  have hC : 2 ≤ C := by
    have he : 1 ≤ Real.exp (v * |t|) := Real.one_le_exp (by dsimp [v]; positivity)
    calc 2 ≤ 4 * ((S.card : ℝ) + 1) := by have := Nat.cast_nonneg (α := ℝ) S.card; linarith
      _ ≤ C := le_mul_of_one_le_right (by positivity) he
  have hH : Φ.hamiltonian.IsHermitian := Interaction.isHermitian_hamiltonian hHerm
  have hnorm : ‖heisenbergEvolution Φ.hamiltonian t W‖ = ‖W‖ :=
    norm_intertwinerIntegrand hH hH W t
  have htriv : ‖B * heisenbergEvolution Φ.hamiltonian t W -
      heisenbergEvolution Φ.hamiltonian t W * B‖ ≤ 2 * ‖W‖ * ‖B‖ := by
    simpa only [hnorm] using norm_commutator_le B
      (heisenbergEvolution Φ.hamiltonian t W)
  have hsep (l : ℕ) (hl : ((2 * R + l : ℕ) : ℕ∞) < G.edist z b) :
      ‖B * heisenbergEvolution Φ.hamiltonian t W -
          heisenbergEvolution Φ.hamiltonian t W * B‖ ≤
        C * ‖W‖ * ‖B‖ * Real.exp (-(μ * l)) := by
    have hd (x : V) (hx : x ∈ S) (y : V) (hy : y ∈ Y) :
        (l : ℕ∞) ≤ G.edist x y := by
      by_contra hn
      have hxy : G.edist x y ≤ l := (lt_of_not_ge hn).le
      have hz : G.edist z b ≤ ((2 * R + l : ℕ) : ℕ∞) := by
        calc G.edist z b ≤ G.edist z x + G.edist x y + G.edist y b :=
            (G.edist_triangle (u := z) (v := y) (w := b)).trans
              (add_le_add (G.edist_triangle (u := z) (v := x) (w := y))
                (le_refl (G.edist y b)))
          _ ≤ R + l + R := add_le_add (add_le_add (hSrad x hx) hxy) (hYrad y hy)
          _ = ((2 * R + l : ℕ) : ℕ∞) := by push_cast; ring
      exact (not_le_of_gt hl) hz
    have hLR := norm_heisenberg_commutator_le_graphDistance_finsets_numeric G Φ
      hHerm R hDiam vR hCard b₀ hBudget S hW Y
      hB μ hμ.le l hd t
    calc _ = ‖heisenbergEvolution Φ.hamiltonian t W * B -
          B * heisenbergEvolution Φ.hamiltonian t W‖ := norm_sub_rev _ _
      _ ≤ 4 * (S.card : ℝ) * ‖W‖ * ‖B‖ *
          Real.exp (v * |t| - μ * l) := hLR
      _ = 4 * (S.card : ℝ) * Real.exp (v * |t|) * ‖W‖ * ‖B‖ *
          Real.exp (-(μ * l)) := by rw [sub_eq_add_neg, Real.exp_add]; ring
      _ ≤ C * ‖W‖ * ‖B‖ * Real.exp (-(μ * l)) := by dsimp [C]; gcongr; linarith
  have hbound := le_anchorDecay_of_separated_exp hμ hC (norm_nonneg W) (norm_nonneg B)
    R (G.edist z b) htriv hsep
  exact hbound.trans_eq (by dsimp [C, v]; ring)

/-- The omitted interactions are summed with their individual exponential anchor weights.
The retained family is arbitrary; no bound on its containing region is assumed.
Hastings, arXiv:cond-mat/0508554v3, lines 1469–1505 and 1524–1533. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_anchor_sum [DecidableEq κ]
    (G : SimpleGraph V) {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, G.edist x y ≤ R)
    (vR : ℕ) (hvR : 1 ≤ vR) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (s : Finset κ) (z : V) (S : Finset V) (hSrad : ∀ x ∈ S, G.edist z x ≤ R)
    {W : Matrix (Config X) (Config X) ℂ} (hW : W ∈ supportedOperators X S)
    {q ΔE μ τ : ℝ} (hq : 0 ≤ q) (hμ : 0 < μ) (hT : 0 ≤ τ) :
    ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W -
        gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W‖ ≤
      4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * τ *
          Real.exp ((4 * vR * |b₀| * Real.exp (2 * μ * R)) * τ) *
          (∑ k ∈ sᶜ, ‖Φ.term k‖ * (if G.edist z (a k) = ⊤ then 0 else
            Real.exp (-(μ * ((G.edist z (a k)).toNat : ℝ))))) +
        2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) := by
  classical
  let v : ℝ := 4 * vR * |b₀| * Real.exp (2 * μ * R)
  let A : ℝ := 4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * Real.exp (v * τ)
  let w : κ → ℝ := fun k ↦ ‖Φ.term k‖ * (if G.edist z (a k) = ⊤ then 0 else
    Real.exp (-(μ * ((G.edist z (a k)).toNat : ℝ))))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw (k : κ) : 0 ≤ w k := by dsimp [w]; split_ifs <;> positivity
  have hBudget' (x : V) :
      ∑ j ∈ Finset.univ.filter (fun j : s ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀ := by
    rw [Finset.sum_filter, Finset.sum_coe_sort s (fun k : κ ↦ if x ∈ T k then ‖Φ.term k‖ else 0)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun j _ _ ↦ ?_)) ?_
    · split_ifs <;> simp
    · simpa only [Finset.sum_filter] using hBudget x
  have hpoint (k : κ) (_hk : k ∉ s) (t : ℝ) (ht : t ∈ Set.Icc (-τ) τ) :
      ‖Φ.term k * (hermitianUnitaryPath (∑ j ∈ s, Φ.term j) t * W *
          hermitianUnitaryPath (∑ j ∈ s, Φ.term j) (-t)) -
        (hermitianUnitaryPath (∑ j ∈ s, Φ.term j) t * W *
          hermitianUnitaryPath (∑ j ∈ s, Φ.term j) (-t)) * Φ.term k‖ ≤ A * w k := by
    have hb := norm_commutator_heisenbergEvolution_le_anchor_kernel G
      (⟨fun j : s ↦ Φ.term j, fun j ↦ Φ.mem j⟩ : Interaction X fun j : s ↦ T j)
      (fun j ↦ hHerm j) R (fun j ↦ hDiam j) vR hvR (fun j ↦ hCard j) b₀ hBudget'
      z S hSrad hW (a k) (T k) (fun y hy ↦ hDiam k y hy (a k) (ha k)) (Φ.mem k) hμ t
    simp only [Interaction.hamiltonian] at hb
    rw [Finset.sum_coe_sort] at hb
    have he : Real.exp (v * |t|) ≤ Real.exp (v * τ) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mpr ht) (by dsimp [v]; positivity))
    refine hb.trans ?_
    change _ ≤ A * w k
    change 4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * ‖Φ.term k‖ *
      Real.exp (v * |t|) * _ ≤ _
    calc _ = (4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * w k) *
          Real.exp (v * |t|) := by dsimp [w]; ring
      _ ≤ (4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * w k) *
          Real.exp (v * τ) := mul_le_mul_of_nonneg_left he (by positivity)
      _ = A * w k := by dsimp [A]; ring
  have hf := norm_gaussianFilteredTerm_sub_truncated_le_of_commutator_bounds (ΔE := ΔE)
    Φ.term hHerm s W hq hT
    (fun k ↦ A * w k) (fun k ↦ mul_nonneg hA (hw k)) hpoint
  rw [← Finset.mul_sum] at hf
  exact hf.trans_eq (by dsimp [A, w, v]; ring)

/-- A bounded-degree weighted tail controls an arbitrary truncation whose omitted
anchors are far away. There is no assumption on the size of the retained region.
Hastings, arXiv:cond-mat/0508554v3, lines 1469–1505 and 1524–1533. -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_degree_tail
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (hD : ∀ x, G.degree x ≤ D)
    {T : κ → Finset V} (a : κ → V) (ha : ∀ k, a k ∈ T k)
    (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
    (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ y ∈ T k, G.edist x y ≤ R)
    (vR : ℕ) (hvR : 1 ≤ vR) (hCard : ∀ k, (T k).card ≤ vR) (b₀ : ℝ)
    (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ x ∈ T j), ‖Φ.term j‖ ≤ b₀)
    (B : ℝ) (hB : 0 ≤ B)
    (hAnchorBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j ↦ a j = x), ‖Φ.term j‖ ≤ B)
    (s : Finset κ) (z : V) (S : Finset V) (hSrad : ∀ x ∈ S, G.edist z x ≤ R)
    {W : Matrix (Config X) (Config X) ℂ} (hW : W ∈ supportedOperators X S)
    (m : ℕ) (hsep : ∀ k ∉ s, (m : ℕ∞) ≤ G.edist z (a k))
    {q ΔE μ τ : ℝ} (hq : 0 ≤ q) (hμ : Real.log (D + 1) < μ) (hT : 0 ≤ τ) :
    let β := (μ - Real.log (D + 1)) / 2
    ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W -
        gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W‖ ≤
      4 * ((S.card : ℝ) + 1) * Real.exp (μ * (2 * R + 1)) * ‖W‖ * τ *
          Real.exp ((4 * vR * |b₀| * Real.exp (2 * μ * R)) * τ) *
          (B * Real.exp (-(β * m)) / (1 - Real.exp (-β))) +
        2 * ‖W‖ * Real.exp (-(τ * ΔE) ^ 2 / (2 * q)) := by
  classical
  intro β
  have hμ0 : 0 < μ := lt_of_le_of_lt (Real.log_nonneg (by
    have := Nat.cast_nonneg (α := ℝ) D
    linarith : (1 : ℝ) ≤ (D : ℝ) + 1)) hμ
  have hf := norm_gaussianFilteredTerm_sub_truncated_le_anchor_sum (ΔE := ΔE) G a ha Φ hHerm
    R hDiam vR hvR hCard b₀ hBudget s z S hSrad hW hq hμ0 hT
  have ht := sum_weight_exp_neg_edist_tail_le_degree G D hD a (fun k ↦ ‖Φ.term k‖)
    (fun k ↦ norm_nonneg _) B hB hAnchorBudget z sᶜ m
    (fun k hk ↦ hsep k (Finset.mem_compl.mp hk)) hμ
  refine hf.trans (add_le_add ?_ le_rfl)
  exact mul_le_mul_of_nonneg_left ht (by positivity)

end Graph

end TruncationWeighted

section TruncationGround

/-- At the time window `τ = q / ΔE`, the Gaussian tail `e^{-(TΔE)²/(2q)}` is `e^{-q/2}`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, the choice `q = c₁ l_proj ΔE` at
lines 337–341, where `τ = c₁ l_proj`. -/
theorem exp_neg_sq_div_eq_of_time_eq {q ΔE : ℝ} (hΔE : ΔE ≠ 0) :
    Real.exp (-(q / ΔE * ΔE) ^ 2 / (2 * q)) = Real.exp (-q / 2) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · congr 1
    rw [div_mul_cancel₀ q hΔE]
    field_simp

section Graph

variable {V : Type*} [Fintype V] [DecidableEq V] {X : V → Type*} [∀ v, Fintype (X v)]
  [∀ v, DecidableEq (X v)] {κ : Type*} [Fintype κ]
  (G : SimpleGraph V) {T : κ → Finset V}
  (Φ : Interaction X T) (hHerm : ∀ k, (Φ.term k).IsHermitian)
  (R : ℕ) (hDiam : ∀ k, ∀ x ∈ T k, ∀ z ∈ T k, G.edist x z ≤ R)
  (vR : ℕ) (hCard : ∀ k, (T k).card ≤ vR)
  (b₀ : ℝ) (hBudget : ∀ x, ∑ j ∈ Finset.univ.filter (fun j => x ∈ T j), ‖Φ.term j‖ ≤ b₀)

include hHerm hDiam hCard hBudget

/-- **The truncation error at the time window `τ = q / ΔE`.** The bound of
`norm_gaussianFilteredTerm_sub_truncated_le` at `τ = q / ΔE`, where the Gaussian tail is
`2 ‖W‖ e^{-q/2}`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, the bound on
`‖H_tilde_i⁰ - M_i‖` after the choice of `q` (lines 343–349). -/
theorem norm_gaussianFilteredTerm_sub_truncated_le_of_time [∀ v, Nonempty (X v)] [DecidableEq κ]
    {q ΔE : ℝ} (hq : 0 ≤ q) (hΔE : 0 < ΔE) (s : Finset κ) (K : Finset V)
    (hsK : ∀ k ∈ s, T k ⊆ K) (S : Finset V) (hSK : S ⊆ K)
    {W : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (J : ℝ)
    (hJ : ∀ k, ‖Φ.term k‖ ≤ J) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (T k) K → ∀ x ∈ S, ∀ y ∈ T k, (m : ℕ∞) ≤ G.edist x y) :
    ‖gaussianFilteredTerm q ΔE Φ.hamiltonian W - gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W‖ ≤
      2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
          ((sᶜ.filter (fun k => ¬Disjoint (T k) K)).card : ℝ) * (q / ΔE) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * (q / ΔE) - μ * m) +
        2 * ‖W‖ * Real.exp (-q / 2) := by
  have hb := norm_gaussianFilteredTerm_sub_truncated_le G Φ hHerm R hDiam vR hCard
    b₀ hBudget (ΔE := ΔE) hq s K hsK S hSK hW J hJ μ hμ m hm (div_nonneg hq hΔE.le)
  rwa [exp_neg_sq_div_eq_of_time_eq hΔE.ne'] at hb

/-- **Eq. `facld` for the truncated approximation.** Let every eigenvalue of `H = ∑ₖ hₖ` equal
`E₀` or be at least `E₀ + ΔE`, and let `ψ` be a ground vector. For the truncated filter
`M = W_tilde_s` of `W` under `H_s = ∑_{k ∈ s} hₖ`, the component of `M ψ` orthogonal to the
ground eigenspace has norm at most `(3 ‖W‖ e^{-q/2} + C (q/ΔE) e^{v q/ΔE - μ m}) ‖ψ‖`, with the
constants of `norm_gaussianFilteredTerm_sub_truncated_le`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, eq. `facld` (lines 322–348), with `q` free and `τ = q / ΔE`. -/
theorem norm_sub_starProjection_truncated_apply_le [∀ v, Nonempty (X v)] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (hΔE : 0 < ΔE) (hH : Φ.hamiltonian.IsHermitian) {E₀ : ℝ}
    (hgap : ∀ j, hH.eigenvalues j = E₀ ∨ E₀ + ΔE ≤ hH.eigenvalues j) (s : Finset κ)
    (K : Finset V) (hsK : ∀ k ∈ s, T k ⊆ K) (S : Finset V) (hSK : S ⊆ K)
    {W : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (J : ℝ)
    (hJ : ∀ k, ‖Φ.term k‖ ≤ J) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (T k) K → ∀ x ∈ S, ∀ y ∈ T k, (m : ℕ∞) ≤ G.edist x y)
    {ψ : EuclideanSpace ℂ (Config X)} (hψ : ψ ∈ groundSpace Φ.hamiltonian E₀) :
    ‖toEuclideanLin (gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W) ψ -
        (groundSpace Φ.hamiltonian E₀).starProjection
          (toEuclideanLin (gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W) ψ)‖ ≤
      (3 * ‖W‖ * Real.exp (-q / 2) +
        2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
          ((sᶜ.filter (fun k => ¬Disjoint (T k) K)).card : ℝ) * (q / ΔE) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * (q / ΔE) - μ * m)) * ‖ψ‖ := by
  refine (norm_sub_starProjection_apply_le_of_gaussianFilteredTerm hq hΔE hH hgap W _ hψ).trans
    (mul_le_mul_of_nonneg_right ?_ (norm_nonneg ψ))
  have hb := norm_gaussianFilteredTerm_sub_truncated_le_of_time G Φ hHerm R hDiam
    vR hCard b₀ hBudget hq hΔE s K hsK S hSK hW J hJ μ hμ m hm
  linarith

/-- **A unique gapped ground state is nearly an eigenvector of `M_i`.** If `H = ∑ₖ hₖ` is gapped
at `E₀` with gap `ΔE > 0` and its ground space is the line through the unit vector `Ω`, then the
truncated filter `M = W_tilde_s` satisfies
`‖M Ω - ⟨Ω, M Ω⟩ Ω‖ ≤ 3 ‖W‖ e^{-q/2} + C (q/ΔE) e^{v q/ΔE - μ m}`, with the constants of
`norm_gaussianFilteredTerm_sub_truncated_le`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, the case of one ground state (lines 375–387), with `q` free and `τ = q / ΔE`. -/
theorem norm_truncated_apply_sub_inner_smul_le [∀ v, Nonempty (X v)] [DecidableEq κ] {q ΔE : ℝ}
    (hq : 0 ≤ q) (hΔE : 0 < ΔE) {E₀ : ℝ} {Ω : EuclideanSpace ℂ (Config X)}
    (hΩ : ‖Ω‖ = 1) (hgap : IsGapped Φ.hamiltonian E₀ ΔE)
    (hspan : groundSpace Φ.hamiltonian E₀ = Submodule.span ℂ {Ω}) (s : Finset κ) (K : Finset V)
    (hsK : ∀ k ∈ s, T k ⊆ K) (S : Finset V) (hSK : S ⊆ K)
    {W : Matrix (Config X) (Config X) ℂ}
    (hW : W ∈ supportedOperators X S) (J : ℝ)
    (hJ : ∀ k, ‖Φ.term k‖ ≤ J) (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ k ∉ s, ¬Disjoint (T k) K → ∀ x ∈ S, ∀ y ∈ T k, (m : ℕ∞) ≤ G.edist x y) :
    ‖toEuclideanLin (gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W) Ω -
        ⟪Ω, toEuclideanLin (gaussianFilteredTerm q ΔE (∑ k ∈ s, Φ.term k) W) Ω⟫_ℂ • Ω‖ ≤
      3 * ‖W‖ * Real.exp (-q / 2) +
        2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (S.card : ℝ) * ‖W‖ * J *
          ((sᶜ.filter (fun k => ¬Disjoint (T k) K)).card : ℝ) * (q / ΔE) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * (q / ΔE) - μ * m) := by
  refine (norm_apply_sub_inner_smul_le_of_gaussianFilteredTerm hq hΔE
    (Interaction.isHermitian_hamiltonian hHerm) hΩ hgap hspan W _).trans ?_
  have hb := norm_gaussianFilteredTerm_sub_truncated_le_of_time G Φ hHerm R hDiam
    vR hCard b₀ hBudget hq hΔE s K hsK S hSK hW J hJ μ hμ m hm
  linarith

/-- **The sum of the truncated approximations.** For each term `hᵢ` let `Mᵢ = H_tilde_{s i}` be
its filter under the truncated Hamiltonian `∑_{k ∈ s i} hₖ`, where the terms of `s i` act on a
set `K i ⊇ Xᵢ` and the omitted terms meeting `K i` are at distance at least `m` from `Xᵢ`. Then
`‖∑ᵢ Mᵢ - H‖ ≤ ∑ᵢ ‖H_tilde_i - Mᵢ‖`, and each summand has the bound of
`norm_gaussianFilteredTerm_sub_truncated_le_of_time`. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 359–374: the difference between `H` and `M = ∑ᵢ Mᵢ` is at most the sum
of the errors of eq. `apb`, with `q` free and `τ = q / ΔE`. -/
theorem norm_sum_truncated_sub_le [∀ v, Nonempty (X v)] [DecidableEq κ] {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) (hH : Φ.hamiltonian.IsHermitian) (s : κ → Finset κ) (K : κ → Finset V)
    (hsK : ∀ i, ∀ k ∈ s i, T k ⊆ K i) (hXK : ∀ i, T i ⊆ K i) (J : ℝ) (hJ : ∀ k, ‖Φ.term k‖ ≤ J)
    (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ i, ∀ k ∉ s i, ¬Disjoint (T k) (K i) → ∀ x ∈ T i, ∀ y ∈ T k,
      (m : ℕ∞) ≤ G.edist x y) :
    ‖∑ i, gaussianFilteredTerm q ΔE (∑ k ∈ s i, Φ.term k) (Φ.term i) - Φ.hamiltonian‖ ≤
      ∑ i, (2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * ((T i).card : ℝ) * ‖Φ.term i‖ * J *
          (((s i)ᶜ.filter (fun k => ¬Disjoint (T k) (K i))).card : ℝ) * (q / ΔE) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * (q / ΔE) - μ * m) +
        2 * ‖Φ.term i‖ * Real.exp (-q / 2)) :=
  (norm_sum_sub_le_of_sum_eq Finset.univ q ΔE hH (W := Φ.term) rfl).trans <|
    Finset.sum_le_sum fun i _ ↦ norm_gaussianFilteredTerm_sub_truncated_le_of_time G Φ
      hHerm R hDiam vR hCard b₀ hBudget hq hΔE (s i) (K i) (hsK i) (T i) (hXK i)
      (Φ.mem i) J hJ μ hμ m (hm i)

/-- **The sum of the truncated approximations, uniform form.** Under the hypotheses of
`norm_sum_truncated_sub_le`, if at most `N₀` omitted terms meet each `K i`, then
`‖∑ᵢ Mᵢ - H‖` is at most the number of terms times
`2 v_R C v_R J² N₀ (q/ΔE) e^{v q/ΔE - μ m} + 2 J e^{-q/2}`. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 343–374: the number of terms times the bound
on `‖H_tilde_i⁰ - M_i‖`, with `q` free and `τ = q / ΔE`. -/
theorem norm_sum_truncated_sub_le_card [∀ v, Nonempty (X v)] [DecidableEq κ] {q ΔE : ℝ} (hq : 0 ≤ q)
    (hΔE : 0 < ΔE) (hH : Φ.hamiltonian.IsHermitian) (s : κ → Finset κ) (K : κ → Finset V)
    (hsK : ∀ i, ∀ k ∈ s i, T k ⊆ K i) (hXK : ∀ i, T i ⊆ K i) (J : ℝ) (hJ : ∀ k, ‖Φ.term k‖ ≤ J)
    (μ : ℝ) (hμ : 0 ≤ μ) (m : ℕ)
    (hm : ∀ i, ∀ k ∉ s i, ¬Disjoint (T k) (K i) → ∀ x ∈ T i, ∀ y ∈ T k,
      (m : ℕ∞) ≤ G.edist x y)
    (N₀ : ℕ) (hN₀ : ∀ i, ((s i)ᶜ.filter (fun k => ¬Disjoint (T k) (K i))).card ≤ N₀) :
    ‖∑ i, gaussianFilteredTerm q ΔE (∑ k ∈ s i, Φ.term k) (Φ.term i) - Φ.hamiltonian‖ ≤
      Fintype.card κ * (2 * vR * (2 + 4 * |b₀| * Real.exp (2 * μ * R)) * (vR : ℝ) * J * J *
          (N₀ : ℝ) * (q / ΔE) *
          Real.exp ((2 * vR * |b₀| * Real.exp (2 * μ * R) + 1) * (q / ΔE) - μ * m) +
        2 * J * Real.exp (-q / 2)) := by
  refine (norm_sum_truncated_sub_le G Φ hHerm R hDiam vR hCard b₀ hBudget hq hΔE
    hH s K hsK hXK J hJ μ hμ m hm).trans ?_
  rw [← nsmul_eq_mul, ← Finset.card_univ]
  refine Finset.sum_le_card_nsmul _ _ _ fun i _ ↦ ?_
  have hJ0 : 0 ≤ J := (norm_nonneg _).trans (hJ i)
  have hqΔE : 0 ≤ q / ΔE := div_nonneg hq hΔE.le
  gcongr
  · exact_mod_cast hCard i
  · exact hJ i
  · exact_mod_cast hN₀ i
  · exact hJ i

end Graph

end TruncationGround

end ManyBody
