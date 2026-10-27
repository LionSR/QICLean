/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The detectability lemma and its converse

Let `h_0, …, h_{m-1}` be orthogonal projections on an inner product space, and write
`Q_j = 1 - h_j`. For a vector `ψ`, put `ψ_k = Q_{k-1} ⋯ Q_0 ψ` and `φ = ψ_m`.

The detectability lemma (Arad, Landau, Vazirani and Vidick, arXiv:1602.08828v2,
`local_alg_arxiv_v2.tex`, Lemma `lem:dl`, lines 1508–1519; proved in Anshu, Arad and Vidick,
*Simple proof of the detectability lemma and spectral gap amplification*, Phys. Rev. B 93,
205142 (2016)) says: if each `h_i` fails to commute with at most `g` of the others, then
`⟨φ|H|φ⟩ ≤ g² (‖ψ‖² - ‖φ‖²)` for `H = ∑ h_i`. Equivalently, `‖φ‖² ≤ 1 / (ε_φ / g² + 1)` for a
unit vector `ψ`, where `ε_φ = ⟨φ|H|φ⟩ / ‖φ‖²`.

The proof bounds `‖h_i ψ_n‖` for `n > i` by induction on `n`. The step through a factor `Q_n`
that commutes with `h_i` does not increase it, and the step through a factor that does not
commute with `h_i` increases it by at most `‖h_n ψ_n‖`. Since
`‖h_n ψ_n‖² = ‖ψ_n‖² - ‖ψ_{n+1}‖²`, the Cauchy–Schwarz inequality and a double count of the
non-commuting pairs give the bound.

The converse (Lemma `lem:dl-converse`, lines 1528–1537) is stated in the source for an
eigenvector `ψ` of a nearest-neighbour Hamiltonian on a chain and for the product
`DL(H) = P P'` of the even and the odd factors, with the bound `1 - 4 ⟨ψ|H|ψ⟩`. Here it is
proved for every vector, with the constant `3`: if `P` and `P'` are products of two families of
commuting projections whose terms sum to `H`, then `‖P P' ψ‖² ≥ 1 - 3 ⟨ψ|H|ψ⟩` for every unit
vector `ψ`. The proof of Theorem `thm:FF-tH` (line 1565) applies the converse to a vector that
need not be an eigenvector, which this form covers.

## Main statements

* `ContinuousLinearMap.complementProd`: the product `Q_{k-1} ⋯ Q_0`.
* `ContinuousLinearMap.re_inner_sum_complementProd_le`: the detectability lemma,
  `⟨φ|H|φ⟩ ≤ g² (‖ψ‖² - ‖φ‖²)`.
* `ContinuousLinearMap.norm_sq_complementProd_le`: the form of the source.
* `ContinuousLinearMap.norm_sq_sub_norm_sq_complementProd_le`: the union bound
  `‖ψ‖² - ‖φ‖² ≤ ⟨ψ|H|ψ⟩` for commuting projections.
* `ContinuousLinearMap.one_sub_three_mul_le_norm_sq_complementProd_mul`: the converse.
-/

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The product `(1 - h_{k-1}) ⋯ (1 - h_0)`, in which `1 - h_0` acts first. -/
noncomputable def complementProd (h : ℕ → E →L[𝕜] E) : ℕ → E →L[𝕜] E
  | 0 => 1
  | k + 1 => (1 - h k) * complementProd h k

@[simp]
theorem complementProd_zero (h : ℕ → E →L[𝕜] E) : complementProd h 0 = 1 := rfl

theorem complementProd_succ (h : ℕ → E →L[𝕜] E) (k : ℕ) :
    complementProd h (k + 1) = (1 - h k) * complementProd h k := rfl

theorem complementProd_succ_apply (h : ℕ → E →L[𝕜] E) (k : ℕ) (x : E) :
    complementProd h (k + 1) x = complementProd h k x - h k (complementProd h k x) := rfl

variable [CompleteSpace E]

section StarProjection

variable {p : E →L[𝕜] E}

theorem _root_.IsStarProjection.apply_apply_self (hp : IsStarProjection p) (x : E) :
    p (p x) = p x :=
  congr($(hp.isIdempotentElem.eq) x)

theorem _root_.IsStarProjection.inner_apply_left (hp : IsStarProjection p) (x y : E) :
    ⟪p x, y⟫_𝕜 = ⟪x, p y⟫_𝕜 := by
  rw [← adjoint_inner_right, ← star_eq_adjoint, hp.isSelfAdjoint.star_eq]

theorem _root_.IsStarProjection.inner_apply_self (hp : IsStarProjection p) (x : E) :
    ⟪x, p x⟫_𝕜 = ((‖p x‖ ^ 2 : ℝ) : 𝕜) := by
  rw [← hp.apply_apply_self x, ← hp.inner_apply_left, hp.apply_apply_self,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_pow]

theorem _root_.IsStarProjection.re_inner_apply_self (hp : IsStarProjection p) (x : E) :
    RCLike.re ⟪x, p x⟫_𝕜 = ‖p x‖ ^ 2 := by
  rw [hp.inner_apply_self, RCLike.ofReal_re]

/-- Pythagoras for a projection: `‖x‖² = ‖p x‖² + ‖x - p x‖²`. -/
theorem _root_.IsStarProjection.norm_sq_eq (hp : IsStarProjection p) (x : E) :
    ‖x‖ ^ 2 = ‖p x‖ ^ 2 + ‖x - p x‖ ^ 2 := by
  have h0 : ⟪p x, x - p x⟫_𝕜 = 0 := by
    rw [hp.inner_apply_left, map_sub, hp.apply_apply_self, sub_self, inner_zero_right]
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (p x) (x - p x) h0
  simpa only [add_sub_cancel, sq] using this

theorem _root_.IsStarProjection.norm_apply_le (hp : IsStarProjection p) (x : E) :
    ‖p x‖ ≤ ‖x‖ := by
  have h := hp.norm_sq_eq x
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg x) (by nlinarith [sq_nonneg ‖x - p x‖])

end StarProjection

variable {h : ℕ → E →L[𝕜] E}

/-- One factor removes the mass `‖h_k ψ_k‖²`. -/
theorem norm_sq_complementProd_succ (hh : ∀ k, IsStarProjection (h k)) (x : E) (k : ℕ) :
    ‖complementProd h (k + 1) x‖ ^ 2 =
      ‖complementProd h k x‖ ^ 2 - ‖h k (complementProd h k x)‖ ^ 2 := by
  rw [complementProd_succ_apply, (hh k).norm_sq_eq (complementProd h k x)]
  ring

/-- For projections, `⟨y|∑ h_i|y⟩ = ∑ ‖h_i y‖²`. -/
theorem re_inner_sum_apply_eq (hh : ∀ k, IsStarProjection (h k)) (s : Finset ℕ) (y : E) :
    RCLike.re ⟪y, (∑ i ∈ s, h i) y⟫_𝕜 = ∑ i ∈ s, ‖h i y‖ ^ 2 := by
  rw [sum_apply, inner_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ (hh i).re_inner_apply_self y

/-- The masses removed by the factors add up to `‖ψ‖² - ‖ψ_n‖²`. -/
theorem sum_norm_sq_apply_complementProd (hh : ∀ k, IsStarProjection (h k)) (x : E) (n : ℕ) :
    ∑ k ∈ Finset.range n, ‖h k (complementProd h k x)‖ ^ 2 =
      ‖x‖ ^ 2 - ‖complementProd h n x‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, norm_sq_complementProd_succ hh]
    ring

open scoped Classical in
/-- The key step of the detectability lemma: `‖h_i ψ_n‖` is at most the sum of `‖h_k ψ_k‖` over
the factors `i < k < n` that do not commute with `h_i`. -/
theorem norm_apply_complementProd_le (hh : ∀ k, IsStarProjection (h k)) (x : E) {i n : ℕ}
    (hin : i < n) :
    ‖h i (complementProd h n x)‖ ≤
      ∑ k ∈ (Finset.range n).filter (fun k ↦ i < k ∧ ¬Commute (h i) (h k)),
        ‖h k (complementProd h k x)‖ := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hin with hin | rfl
    · rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hc : Commute (h i) (h n)
      · simp only [hc, not_true_eq_false, and_false, ↓reduceIte]
        have hQ : h i (complementProd h (n + 1) x) =
            (1 - h n) (h i (complementProd h n x)) := by
          rw [complementProd_succ]
          exact congr($(((Commute.one_right _).sub_right hc).eq) (complementProd h n x))
        rw [hQ]
        exact ((hh n).one_sub.norm_apply_le _).trans (ih hin)
      · simp only [hin, hc, not_false_eq_true, and_self, ↓reduceIte]
        rw [Finset.sum_insert (by simp), complementProd_succ_apply, map_sub, add_comm]
        exact (norm_sub_le _ _).trans (add_le_add (ih hin) ((hh i).norm_apply_le _))
    · have h0 : h i (complementProd h (i + 1) x) = 0 := by
        rw [complementProd_succ_apply, map_sub, (hh i).apply_apply_self, sub_self]
      rw [h0, norm_zero]
      exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

open scoped Classical in
/-- **Detectability lemma** (arXiv:1602.08828v2, Lemma `lem:dl`). If each of the projections
`h_0, …, h_{m-1}` fails to commute with at most `g` of the others, and `φ = Q_{m-1} ⋯ Q_0 ψ`
with `Q_j = 1 - h_j`, then `⟨φ|H|φ⟩ ≤ g² (‖ψ‖² - ‖φ‖²)` for `H = ∑ h_j`. -/
theorem re_inner_sum_complementProd_le (hh : ∀ k, IsStarProjection (h k)) {m g : ℕ}
    (hg : ∀ i < m,
      ((Finset.range m).filter (fun j ↦ j ≠ i ∧ ¬Commute (h i) (h j))).card ≤ g)
    (x : E) :
    RCLike.re ⟪complementProd h m x, (∑ i ∈ Finset.range m, h i) (complementProd h m x)⟫_𝕜 ≤
      (g : ℝ) ^ 2 * (‖x‖ ^ 2 - ‖complementProd h m x‖ ^ 2) := by
  set φ := complementProd h m x
  set a : ℕ → ℝ := fun k ↦ ‖h k (complementProd h k x)‖
  set A : ℕ → Finset ℕ := fun i ↦
    (Finset.range m).filter (fun k ↦ i < k ∧ ¬Commute (h i) (h k))
  have hA : ∀ i < m, (A i).card ≤ g := fun i hi ↦
    (Finset.card_le_card fun k hk ↦ by
      obtain ⟨hk, hik, hc⟩ := Finset.mem_filter.mp hk
      exact Finset.mem_filter.mpr ⟨hk, hik.ne', hc⟩).trans (hg i hi)
  have hA' : ∀ k < m, ((Finset.range m).filter (fun i ↦ k ∈ A i)).card ≤ g := fun k hk ↦
    (Finset.card_le_card fun i hi ↦ by
      obtain ⟨hi, hki⟩ := Finset.mem_filter.mp hi
      obtain ⟨-, hik, hc⟩ := Finset.mem_filter.mp hki
      exact Finset.mem_filter.mpr ⟨hi, hik.ne, fun hc' ↦ hc hc'.symm⟩).trans (hg k hk)
  have hH := re_inner_sum_apply_eq hh (Finset.range m) φ
  have hi : ∀ i ∈ Finset.range m, ‖h i φ‖ ^ 2 ≤ g * ∑ k ∈ A i, a k ^ 2 := by
    intro i him
    have him := Finset.mem_range.mp him
    calc ‖h i φ‖ ^ 2 ≤ (∑ k ∈ A i, a k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_apply_complementProd_le hh x him) 2
      _ ≤ (A i).card * ∑ k ∈ A i, a k ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ g * ∑ k ∈ A i, a k ^ 2 := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hA i him)
            (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hswap : ∑ i ∈ Finset.range m, ∑ k ∈ A i, a k ^ 2 =
      ∑ k ∈ Finset.range m, ((Finset.range m).filter (fun i ↦ k ∈ A i)).card * a k ^ 2 := by
    have hAi : ∀ i, ∑ k ∈ A i, a k ^ 2 =
        ∑ k ∈ Finset.range m, if k ∈ A i then a k ^ 2 else 0 := fun i ↦ by
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (Finset.filter_subset _ _)]
    simp_rw [hAi]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc RCLike.re ⟪φ, (∑ i ∈ Finset.range m, h i) φ⟫_𝕜
      = ∑ i ∈ Finset.range m, ‖h i φ‖ ^ 2 := hH
    _ ≤ ∑ i ∈ Finset.range m, g * ∑ k ∈ A i, a k ^ 2 := Finset.sum_le_sum hi
    _ = g * ∑ k ∈ Finset.range m,
          ((Finset.range m).filter (fun i ↦ k ∈ A i)).card * a k ^ 2 := by
        rw [← Finset.mul_sum, hswap]
    _ ≤ g * ∑ k ∈ Finset.range m, g * a k ^ 2 := by
        gcongr with k hk
        exact_mod_cast hA' k (Finset.mem_range.mp hk)
    _ = (g : ℝ) ^ 2 * (‖x‖ ^ 2 - ‖φ‖ ^ 2) := by
        rw [← Finset.mul_sum, ← mul_assoc, ← sq, sum_norm_sq_apply_complementProd hh]

open scoped Classical in
/-- **Detectability lemma** in the form of arXiv:1602.08828v2, Lemma `lem:dl`: for a unit
vector `ψ`, `‖φ‖² ≤ 1 / (ε_φ / g² + 1)` with `ε_φ = ⟨φ|H|φ⟩ / ‖φ‖²`. -/
theorem norm_sq_complementProd_le (hh : ∀ k, IsStarProjection (h k)) {m g : ℕ}
    (hg : ∀ i < m,
      ((Finset.range m).filter (fun j ↦ j ≠ i ∧ ¬Commute (h i) (h j))).card ≤ g)
    {x : E} (hx : ‖x‖ = 1) :
    ‖complementProd h m x‖ ^ 2 ≤
      1 / (RCLike.re ⟪complementProd h m x,
          (∑ i ∈ Finset.range m, h i) (complementProd h m x)⟫_𝕜 /
            ‖complementProd h m x‖ ^ 2 / (g : ℝ) ^ 2 + 1) := by
  set φ := complementProd h m x
  set e := RCLike.re ⟪φ, (∑ i ∈ Finset.range m, h i) φ⟫_𝕜
  have hDL := re_inner_sum_complementProd_le hh hg x
  rw [hx, one_pow] at hDL
  have he : 0 ≤ e := by
    rw [show e = ∑ i ∈ Finset.range m, ‖h i φ‖ ^ 2 from re_inner_sum_apply_eq hh _ φ]
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hφ1 : ‖φ‖ ^ 2 ≤ 1 := by
    have := sum_norm_sq_apply_complementProd hh x m
    rw [hx, one_pow] at this
    have : 0 ≤ ∑ k ∈ Finset.range m, ‖h k (complementProd h k x)‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith
  have hpos : 0 < e / ‖φ‖ ^ 2 / (g : ℝ) ^ 2 + 1 := by positivity
  rw [le_div_iff₀ hpos]
  rcases eq_or_lt_of_le (sq_nonneg ‖φ‖) with h0 | h0
  · rw [← h0, zero_mul]; exact zero_le_one
  rcases Nat.eq_zero_or_pos g with rfl | hg0
  · simpa using hφ1
  have hg2 : (0 : ℝ) < (g : ℝ) ^ 2 := by positivity
  calc ‖φ‖ ^ 2 * (e / ‖φ‖ ^ 2 / (g : ℝ) ^ 2 + 1) = e / (g : ℝ) ^ 2 + ‖φ‖ ^ 2 := by
        have hφ0 : ‖φ‖ ≠ 0 := fun h' ↦ by simp [h'] at h0
        field_simp
    _ ≤ (‖x‖ ^ 2 - ‖φ‖ ^ 2) + ‖φ‖ ^ 2 := by
        rw [hx, one_pow]
        gcongr
        rw [div_le_iff₀ hg2]
        linarith
    _ = 1 := by rw [hx, one_pow]; ring

omit [CompleteSpace E] in
/-- An operator commuting with `h_0, …, h_{k-1}` commutes with `Q_{k-1} ⋯ Q_0`. -/
theorem commute_complementProd {A : E →L[𝕜] E} {k : ℕ} (hA : ∀ j < k, Commute A (h j)) :
    Commute A (complementProd h k) := by
  induction k with
  | zero => exact Commute.one_right A
  | succ k ih =>
    exact ((Commute.one_right _).sub_right (hA k k.lt_succ_self)).mul_right
      (ih fun j hj ↦ hA j (hj.trans k.lt_succ_self))

/-- For pairwise commuting projections, the product `Q_{n-1} ⋯ Q_0` is a projection. -/
theorem isStarProjection_complementProd (hh : ∀ k, IsStarProjection (h k))
    (hc : ∀ i j, Commute (h i) (h j)) (n : ℕ) : IsStarProjection (complementProd h n) := by
  induction n with
  | zero => exact IsStarProjection.one _
  | succ n ih =>
    exact (hh n).one_sub.mul ih
      (commute_complementProd fun j _ ↦ (Commute.one_left _).sub_left (hc n j))

/-- **Union bound** for commuting projections: `‖ψ‖² - ‖Q_{n-1} ⋯ Q_0 ψ‖² ≤ ⟨ψ|H|ψ⟩` with
`H = ∑ h_k`. -/
theorem norm_sq_sub_norm_sq_complementProd_le (hh : ∀ k, IsStarProjection (h k))
    (hc : ∀ i j, Commute (h i) (h j)) (x : E) (n : ℕ) :
    ‖x‖ ^ 2 - ‖complementProd h n x‖ ^ 2 ≤
      RCLike.re ⟪x, (∑ k ∈ Finset.range n, h k) x⟫_𝕜 := by
  rw [← sum_norm_sq_apply_complementProd hh, re_inner_sum_apply_eq hh]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hcomm : h k (complementProd h k x) = complementProd h k (h k x) := by
    exact congr($((commute_complementProd fun j _ ↦ hc k j).eq) x)
  rw [hcomm]
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((isStarProjection_complementProd hh hc k).norm_apply_le _) 2

/-- Two projections with small complementary masses at a unit vector `x`: their product keeps
`‖P P' x‖² ≥ 1 - 3 (‖x - P x‖² + ‖x - P' x‖²)`. -/
theorem _root_.IsStarProjection.one_sub_three_mul_le_norm_sq_mul_apply {P P' : E →L[𝕜] E}
    (hP : IsStarProjection P) (hP' : IsStarProjection P') {x : E} (hx : ‖x‖ = 1) :
    1 - 3 * (‖x - P x‖ ^ 2 + ‖x - P' x‖ ^ 2) ≤ ‖P (P' x)‖ ^ 2 := by
  have hinner : ⟪x, P (P' x)⟫_𝕜 = ⟪x - (x - P x), x - (x - P' x)⟫_𝕜 := by
    rw [sub_sub_cancel, sub_sub_cancel, hP.inner_apply_left]
  have hw : RCLike.re ⟪x, x - P' x⟫_𝕜 = ‖x - P' x‖ ^ 2 := hP'.one_sub.re_inner_apply_self x
  have hu : RCLike.re ⟪x - P x, x⟫_𝕜 = ‖x - P x‖ ^ 2 := by
    rw [← inner_conj_symm, RCLike.conj_re]
    exact hP.one_sub.re_inner_apply_self x
  set u := x - P x
  set w := x - P' x
  clear_value u w
  have hx2 : RCLike.re ⟪x, x⟫_𝕜 = 1 := by
    rw [inner_self_eq_norm_sq, hx, one_pow]
  have huw : -(‖u‖ * ‖w‖) ≤ RCLike.re ⟪u, w⟫_𝕜 :=
    neg_le_of_abs_le ((RCLike.abs_re_le_norm _).trans (norm_inner_le_norm u w))
  have hre : 1 - ‖u‖ ^ 2 - ‖w‖ ^ 2 - ‖u‖ * ‖w‖ ≤ RCLike.re ⟪x, P (P' x)⟫_𝕜 := by
    rw [hinner, inner_sub_left, inner_sub_right, inner_sub_right, map_sub, map_sub, map_sub,
      hx2, hw, hu]
    linarith
  have hle : RCLike.re ⟪x, P (P' x)⟫_𝕜 ≤ ‖P (P' x)‖ := by
    refine (RCLike.re_le_norm _).trans ((norm_inner_le_norm _ _).trans ?_)
    rw [hx, one_mul]
  have hsq : ‖u‖ * ‖w‖ ≤ (‖u‖ ^ 2 + ‖w‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖u‖ - ‖w‖)]
  have h1 : 1 - 3 / 2 * (‖u‖ ^ 2 + ‖w‖ ^ 2) ≤ ‖P (P' x)‖ := by linarith
  nlinarith [norm_nonneg (P (P' x)), sq_nonneg (‖u‖ ^ 2 + ‖w‖ ^ 2), sq_nonneg ‖u‖,
    sq_nonneg ‖w‖]

/-- **Converse of the detectability lemma** (arXiv:1602.08828v2, Lemma `lem:dl-converse`, for
every unit vector and with the constant `3`). Let `h` and `h'` be two families of pairwise
commuting projections, such as the even and the odd terms of a nearest-neighbour chain, and let
`P` and `P'` be the products of the complements of their first `n` and `n'` terms. Then
`‖P P' ψ‖² ≥ 1 - 3 ⟨ψ|H|ψ⟩` with `H` the sum of these terms. -/
theorem one_sub_three_mul_le_norm_sq_complementProd_mul {h' : ℕ → E →L[𝕜] E}
    (hh : ∀ k, IsStarProjection (h k)) (hc : ∀ i j, Commute (h i) (h j))
    (hh' : ∀ k, IsStarProjection (h' k)) (hc' : ∀ i j, Commute (h' i) (h' j)) (n n' : ℕ)
    {x : E} (hx : ‖x‖ = 1) :
    1 - 3 * RCLike.re ⟪x, (∑ k ∈ Finset.range n, h k + ∑ k ∈ Finset.range n', h' k) x⟫_𝕜 ≤
      ‖complementProd h n (complementProd h' n' x)‖ ^ 2 := by
  have hP := isStarProjection_complementProd hh hc n
  have hP' := isStarProjection_complementProd hh' hc' n'
  have ha : ‖x - complementProd h n x‖ ^ 2 ≤ RCLike.re ⟪x, (∑ k ∈ Finset.range n, h k) x⟫_𝕜 := by
    have := hP.norm_sq_eq x
    linarith [norm_sq_sub_norm_sq_complementProd_le hh hc x n]
  have hb : ‖x - complementProd h' n' x‖ ^ 2 ≤
      RCLike.re ⟪x, (∑ k ∈ Finset.range n', h' k) x⟫_𝕜 := by
    have := hP'.norm_sq_eq x
    linarith [norm_sq_sub_norm_sq_complementProd_le hh' hc' x n']
  rw [add_apply, inner_add_right, map_add]
  linarith [hP.one_sub_three_mul_le_norm_sq_mul_apply hP' hx]

end ContinuousLinearMap
