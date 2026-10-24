/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import QICLean.Analysis.TraceExponentialPerturbation
import QICLean.Analysis.TraceHolderMulti

/-!
# Alternating sums of shifted exponentials

Let `Y` and `h_i`, `i ∈ S`, be Hermitian matrices, and write `h_E = ∑_{i ∈ E} h_i` for
`E ⊆ S`. The alternating sum

`Δ = ∑_{E ⊆ S} (-1)^{|S| - |E|} e^{-(Y + h_E)}`

is the mixed finite difference of `t ↦ e^{-(Y + ∑_i t_i h_i)}` over the unit cube. For every
matrix `O`,

`|Tr (O Δ)| ≤ ‖O‖ ∏_{i ∈ S} (e^{‖h_i‖} - 1) Tr e^{-Y}`,

with operator norms. If `‖h_i‖ ≤ J` for all `i`, the right side is at most
`‖O‖ (e^J - 1)^{|S|} Tr e^{-Y}`.

Let `H = ∑_i H_i`, let `C` be a cluster with boundary `B(C)`, and take
`Y = β (H - H_C - H_{B(C)})` and `h_i = β H_i` for `i ∈ C`. Then `Y + h_E = β (H - H_{B(C)} - H_D)`
with `D = C \ E`, and by inclusion-exclusion the alternating sum is the operator `ρ(β, C)` of
Hastings, *Solving gapped Hamiltonians locally*: the sum of the terms of the power series of
`e^{-βH}` that contain every `H_i` with `i ∈ C` and no `H_j` with `j ∈ B(C)`. If `‖H_i‖ ≤ J`, the
bound reads `‖O‖ (e^{βJ} - 1)^{n_C} Tr e^{-β(H - H_C - H_{B(C)})}`. Together with
`Matrix.IsHermitian.re_trace_exp_add_le`, which bounds the last trace by
`e^{β ‖H_C + H_{B(C)}‖} Tr e^{-βH}`, this gives the inequality before equation `percb2` (lines
1179–1184) with `‖O‖ Tr e^{-βH}` in place of the printed `Tr(O e^{-βH})`, which is the form that
`percb2` uses. The printed form fails: applied to `±O` it would force `ρ(β, C)` to be a multiple
of `e^{-βH}`. This is recorded in the TNLean paper-gap note
`https://sirui-lu.com/TNLean/paper-gaps/hastings05_cluster_part_trace_pairing.pdf`.

More generally, let `X` be Hermitian and let `p, q, r ≥ 0` with `p + q + r = 1`. Inserting the
alternating sum of the `e^{-q (Y + h_E)}` between `e^{-p X}` and `e^{-r X}` gives

`|Tr (O e^{-p X} (∑_{E ⊆ S} (-1)^{|S| - |E|} e^{-q (Y + h_E)}) e^{-r X})|
  ≤ ‖O‖ ∏_{i ∈ S} (e^{q ‖h_i‖} - 1) (Tr e^{-X})^{p + r} (Tr e^{-Y})^q`.

With `X = β H`, `q = 1/n`, `p = k/n` and `r = (n - k - 1)/n`, this is the bound on a cluster part
`ρ(β/n, C)` placed between the thermal factors `ρ(kβ/n)` and `ρ((n - k - 1)β/n)` that Hastings
uses for the matrix product approximation at arbitrary temperature (lines 1322–1333).

## Proof

The source argues by a power series expansion. Here the bound is proved by induction on `S`,
for ordered products `B_0 e^{-a_0 (Y_0 + c_0 s)} B_1 e^{-a_1 (Y_1 + c_1 s)} ⋯` with Hermitian base
generators `Y_j`, weights `a_j ≥ 0` summing to one, a common shift `s = h_E`, and flags
`c_j ∈ {0, 1}` that record which factors carry the shift. Let `w` be the total weight of the
factors with `c_j = 1`. For `S = ∅` the bound is the multi-factor Hölder inequality
`Matrix.norm_trace_list_prod_mul_exp_smul_le`. Adding an index `a` replaces the summand by its
difference in the direction `V = h_a`. The difference telescopes over the factors that carry the
shift: factor `j` changes from `Y_j` to `Y_j + V` while the earlier such factors carry `Y_k + V`.
By Duhamel's formula,

`d/du [e^{-(a_j - u)(Z + V)} e^{-u Z}] = e^{-(a_j - u)(Z + V)} V e^{-u Z}`,

which is an ordered product with one factor more, of the same total shifted weight, so the
inductive hypothesis bounds the derivative. The estimate `Tr e^{-(Y + V)} ≤ e^{‖V‖} Tr e^{-Y}` on
the shifted factors bounds the derivative at `u` by `‖V‖ e^{‖V‖ (A_j - u)}` times the previous
bound, with `A_j` the shifted weight of the first `j + 1` factors, and the mean value inequality
integrates this to `e^{‖V‖ A_j} - e^{‖V‖ A_{j-1}}`. The sum over `j` telescopes to
`e^{‖V‖ w} - 1`. The bound on `Tr (O Δ)` is the case of one factor, with `w = 1`; the bound
between the factors `e^{-p X}` and `e^{-r X}` is the case of three factors, of which only the
middle one carries the shift, with `w = q`.

## Main results

* `Matrix.norm_trace_mul_sum_powerset_exp_le`: the bound with the factors `e^{‖h_i‖} - 1`.
* `Matrix.norm_trace_mul_sum_powerset_exp_le_pow`: the bound with a uniform `‖h_i‖ ≤ J`.
* `Matrix.norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le`: the bound with the alternating sum
  between two thermal factors.
* `Matrix.norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le_pow`: the same bound with a uniform
  `‖h_i‖ ≤ J`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73, 085115 (2006),
  arXiv:cond-mat/0508554v3, source file `proj3new.tex`, lines 1162–1195: the definition of
  `ρ(β, C)`, the bound
  `Tr (O ρ(β, C)) ≤ [exp(Jβ) - 1]^{n_C} exp(β ‖H_C + H_{B(C)}‖) Tr e^{-βH}`
  and equation `percb2`; lines 1322–1333: the bound
  `Z^{-1} Tr (O ρ(kβ/n) ρ(β/n, C) ρ((n - k - 1)β/n)) ≤ ‖O‖ y^{n_C}`.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}

section AlternatingSum

/-- The alternating sum `∑_{E ⊆ S} (-1)^{|S| - |E|} F(h_E)`, with `h_E = ∑_{i ∈ E} h_i`. -/
private noncomputable def altSum (S : Finset κ) (h : κ → Matrix ι ι ℂ)
    (F : Matrix ι ι ℂ → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ E ∈ S.powerset, (-1 : ℂ) ^ (S.card - E.card) • F (∑ i ∈ E, h i)

omit [Fintype ι] [DecidableEq ι] in
private theorem altSum_empty (h : κ → Matrix ι ι ℂ)
    (F : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    altSum ∅ h F = F 0 := by
  simp [altSum]

omit [Fintype ι] [DecidableEq ι] in
/-- Adding an index to `S` replaces `F` by its difference in the direction `h_a`. -/
private theorem altSum_insert [DecidableEq κ] {a : κ} {S : Finset κ} (ha : a ∉ S)
    (h : κ → Matrix ι ι ℂ) (F : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    altSum (insert a S) h F = altSum S h fun s ↦ F (h a + s) - F s := by
  rw [altSum, Finset.sum_powerset_insert ha, altSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun E hE ↦ ?_
  have hES := Finset.mem_powerset.1 hE
  have haE : a ∉ E := fun h' ↦ ha (hES h')
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haE, Finset.sum_insert haE,
    Nat.add_sub_add_right, Nat.sub_add_comm (Finset.card_le_card hES), pow_succ, smul_sub]
  simp only [mul_neg, mul_one, neg_smul]
  abel

omit [Fintype ι] [DecidableEq ι] in
private theorem altSum_add (S : Finset κ) (h : κ → Matrix ι ι ℂ)
    (F G : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    altSum S h (fun s ↦ F s + G s) = altSum S h F + altSum S h G := by
  simp [altSum, smul_add, Finset.sum_add_distrib]

omit [Fintype ι] [DecidableEq ι] in
private theorem altSum_sub (S : Finset κ) (h : κ → Matrix ι ι ℂ)
    (F G : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    altSum S h (fun s ↦ F s - G s) = altSum S h F - altSum S h G := by
  simp [altSum, smul_sub, Finset.sum_sub_distrib]

end AlternatingSum

section Factors

/-- A factor of an ordered product: `B e^{-a (Y + s)}` with the common shift `s` when the flag
`sh` holds, and `B e^{-a Y}` otherwise. -/
private structure ShiftFactor (ι : Type*) where
  /-- The arbitrary matrix of the factor. -/
  B : Matrix ι ι ℂ
  /-- The base generator, Hermitian in all uses. -/
  Y : Matrix ι ι ℂ
  /-- The weight. -/
  a : ℝ
  /-- Whether the factor carries the common shift. -/
  sh : Bool

/-- The matrix `B e^{-a (Y + s)}`, or `B e^{-a Y}` for an unshifted factor, at shift `s`. -/
private noncomputable def ShiftFactor.mat (s : Matrix ι ι ℂ) (x : ShiftFactor ι) :
    Matrix ι ι ℂ :=
  x.B * NormedSpace.exp (x.a • -(x.Y + if x.sh then s else 0))

/-- The factor `‖B‖ (Tr e^{-Y})^a` of the bound. -/
private noncomputable def ShiftFactor.bd (x : ShiftFactor ι) : ℝ :=
  ‖x.B‖ * (NormedSpace.exp (-x.Y)).trace.re ^ x.a

omit [Fintype ι] [DecidableEq ι] in
/-- The factor with base generator `Y + V` if it carries the shift, and the factor itself
otherwise. -/
private def ShiftFactor.shift (V : Matrix ι ι ℂ) (x : ShiftFactor ι) : ShiftFactor ι :=
  ⟨x.B, if x.sh then x.Y + V else x.Y, x.a, x.sh⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The weight of a factor that carries the shift, and zero for any other factor. -/
private def ShiftFactor.sa (x : ShiftFactor ι) : ℝ :=
  if x.sh then x.a else 0

/-- The ordered product of a list of factors at shift `s`. -/
private noncomputable def prodAt (L : List (ShiftFactor ι)) (s : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (L.map (ShiftFactor.mat s)).prod

/-- The bound `∏ ‖B_j‖ (Tr e^{-Y_j})^{a_j}` of a list of factors. -/
private noncomputable def listBound (L : List (ShiftFactor ι)) : ℝ :=
  (L.map ShiftFactor.bd).prod

omit [Fintype ι] [DecidableEq ι] in
/-- The total weight of a list of factors. -/
private def listWeight (L : List (ShiftFactor ι)) : ℝ :=
  (L.map ShiftFactor.a).sum

omit [Fintype ι] [DecidableEq ι] in
/-- The total weight of the factors that carry the shift. -/
private def shiftWeight (L : List (ShiftFactor ι)) : ℝ :=
  (L.map ShiftFactor.sa).sum

omit [Fintype ι] [DecidableEq ι] in
/-- Hermitian base generators and nonnegative weights. -/
private def Admissible (L : List (ShiftFactor ι)) : Prop :=
  ∀ x ∈ L, x.Y.IsHermitian ∧ 0 ≤ x.a

private theorem prodAt_append (L₁ L₂ : List (ShiftFactor ι)) (s : Matrix ι ι ℂ) :
    prodAt (L₁ ++ L₂) s = prodAt L₁ s * prodAt L₂ s := by
  simp [prodAt]

private theorem prodAt_cons (x : ShiftFactor ι) (L : List (ShiftFactor ι))
    (s : Matrix ι ι ℂ) :
    prodAt (x :: L) s = x.mat s * prodAt L s := by
  simp [prodAt]

private theorem listBound_append (L₁ L₂ : List (ShiftFactor ι)) :
    listBound (L₁ ++ L₂) = listBound L₁ * listBound L₂ := by
  simp [listBound]

private theorem listBound_cons (x : ShiftFactor ι) (L : List (ShiftFactor ι)) :
    listBound (x :: L) = x.bd * listBound L := by
  simp [listBound]

omit [Fintype ι] [DecidableEq ι] in
private theorem listWeight_append (L₁ L₂ : List (ShiftFactor ι)) :
    listWeight (L₁ ++ L₂) = listWeight L₁ + listWeight L₂ := by
  simp [listWeight]

omit [Fintype ι] [DecidableEq ι] in
private theorem listWeight_cons (x : ShiftFactor ι) (L : List (ShiftFactor ι)) :
    listWeight (x :: L) = x.a + listWeight L := by
  simp [listWeight]

omit [Fintype ι] [DecidableEq ι] in
private theorem listWeight_map_shift (V : Matrix ι ι ℂ) (L : List (ShiftFactor ι)) :
    listWeight (L.map (ShiftFactor.shift V)) = listWeight L := by
  simp [listWeight, Function.comp_def, ShiftFactor.shift]

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftWeight_append (L₁ L₂ : List (ShiftFactor ι)) :
    shiftWeight (L₁ ++ L₂) = shiftWeight L₁ + shiftWeight L₂ := by
  simp [shiftWeight]

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftWeight_cons (x : ShiftFactor ι) (L : List (ShiftFactor ι)) :
    shiftWeight (x :: L) = x.sa + shiftWeight L := by
  simp [shiftWeight]

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftWeight_map_shift (V : Matrix ι ι ℂ) (L : List (ShiftFactor ι)) :
    shiftWeight (L.map (ShiftFactor.shift V)) = shiftWeight L := by
  simp only [shiftWeight, List.map_map]
  rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftWeight_nonneg {L : List (ShiftFactor ι)} (hL : Admissible L) :
    0 ≤ shiftWeight L :=
  List.sum_nonneg fun b hb ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    unfold ShiftFactor.sa
    split_ifs
    exacts [(hL y hy).2, le_rfl]

omit [Fintype ι] [DecidableEq ι] in
private theorem Admissible.map_shift {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    {L : List (ShiftFactor ι)} (hL : Admissible L) :
    Admissible (L.map (ShiftFactor.shift V)) := fun y hy ↦ by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  refine ⟨?_, (hL z hz).2⟩
  unfold ShiftFactor.shift
  split_ifs
  exacts [(hL z hz).1.add hV, (hL z hz).1]

/-- Adding `V` to the common shift is the same as shifting the base generators of the factors
that carry the shift. -/
private theorem prodAt_add (L : List (ShiftFactor ι)) (V s : Matrix ι ι ℂ) :
    prodAt L (V + s) = prodAt (L.map (ShiftFactor.shift V)) s := by
  simp only [prodAt, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ ↦ by
    cases x with
    | mk B Y a sh => cases sh <;> simp [ShiftFactor.mat, ShiftFactor.shift, add_assoc]

private theorem ShiftFactor.bd_nonneg {x : ShiftFactor ι} (hx : x.Y.IsHermitian) : 0 ≤ x.bd :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.neg.re_trace_exp_nonneg _)

private theorem listBound_nonneg {L : List (ShiftFactor ι)} (hL : Admissible L) : 0 ≤ listBound L :=
  List.prod_nonneg fun b hb ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact ShiftFactor.bd_nonneg (hL y hy).1

/-- Shifting the base generator by a Hermitian `V` raises the bound of a factor by at most
`e^{a ‖V‖}`. -/
private theorem ShiftFactor.bd_add_le {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    (B : Matrix ι ι ℂ) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) {a : ℝ} (ha : 0 ≤ a) (b : Bool) :
    (⟨B, Y + V, a, b⟩ : ShiftFactor ι).bd ≤
      Real.exp (‖V‖ * a) * (⟨B, Y, a, b⟩ : ShiftFactor ι).bd := by
  have htr := hY.neg.re_trace_exp_add_le hV.neg
  rw [norm_neg, ← neg_add] at htr
  have h0 : 0 ≤ (NormedSpace.exp (-(Y + V))).trace.re := (hY.add hV).neg.re_trace_exp_nonneg
  have h1 : 0 ≤ (NormedSpace.exp (-Y)).trace.re := hY.neg.re_trace_exp_nonneg
  calc ‖B‖ * (NormedSpace.exp (-(Y + V))).trace.re ^ a
      ≤ ‖B‖ * (Real.exp ‖V‖ * (NormedSpace.exp (-Y)).trace.re) ^ a :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 htr ha) (norm_nonneg _)
    _ = Real.exp (‖V‖ * a) * (⟨B, Y, a, b⟩ : ShiftFactor ι).bd := by
        rw [Real.mul_rpow (Real.exp_pos _).le h1, ← Real.exp_mul, ShiftFactor.bd]
        ring

/-- Shifting by a Hermitian `V` raises the bound of a factor by at most `e^{a ‖V‖}` if the factor
carries the shift, and leaves it unchanged otherwise. -/
private theorem ShiftFactor.bd_shift_le {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    {x : ShiftFactor ι} (hx : x.Y.IsHermitian) (ha : 0 ≤ x.a) :
    (x.shift V).bd ≤ Real.exp (‖V‖ * x.sa) * x.bd := by
  cases x with
  | mk B Y a sh =>
    cases sh
    · simp [ShiftFactor.shift, ShiftFactor.sa]
    · simpa [ShiftFactor.shift, ShiftFactor.sa] using ShiftFactor.bd_add_le hV B hx ha true

private theorem listBound_map_shift_le {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    {L : List (ShiftFactor ι)} (hL : Admissible L) :
    listBound (L.map (ShiftFactor.shift V)) ≤ Real.exp (‖V‖ * shiftWeight L) * listBound L := by
  induction L with
  | nil => simp [listBound, shiftWeight]
  | cons x L ih =>
    have hx := hL x (by simp)
    have hL' : Admissible L := fun y hy ↦ hL y (by simp [hy])
    rw [List.map_cons, listBound_cons, listBound_cons, shiftWeight_cons, mul_add, Real.exp_add]
    calc (x.shift V).bd * listBound (L.map (ShiftFactor.shift V))
        ≤ (Real.exp (‖V‖ * x.sa) * x.bd) * (Real.exp (‖V‖ * shiftWeight L) * listBound L) :=
          mul_le_mul (x.bd_shift_le hV hx.1 hx.2) (ih hL') (listBound_nonneg (hL'.map_shift hV))
            (mul_nonneg (Real.exp_pos _).le (ShiftFactor.bd_nonneg hx.1))
      _ = _ := by ring

/-- **Base case.** With no shift, the bound is the multi-factor Hölder inequality. -/
private theorem norm_trace_prodAt_zero_le {L : List (ShiftFactor ι)} (hL : Admissible L)
    (hw : listWeight L = 1) : ‖(prodAt L 0).trace‖ ≤ listBound L := by
  have h := norm_trace_list_prod_mul_exp_smul_le (fun j : Fin L.length ↦ (L.get j).B)
    (fun j ↦ -(L.get j).Y) (fun j ↦ (hL _ (List.get_mem L j)).1.neg) (fun j ↦ (L.get j).a)
    (fun j ↦ (hL _ (List.get_mem L j)).2) (by
      rw [← hw, listWeight]
      conv_rhs => rw [← List.ofFn_get L, List.map_ofFn, List.sum_ofFn]
      rfl)
  have e1 : prodAt L 0 = (List.ofFn fun j : Fin L.length ↦
      (L.get j).B * NormedSpace.exp ((L.get j).a • -(L.get j).Y)).prod := by
    rw [prodAt]
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn]
    simp [ShiftFactor.mat, Function.comp_def]
  have e2 : listBound L = (∏ j : Fin L.length, ‖(L.get j).B‖) *
      ∏ j : Fin L.length, (NormedSpace.exp (-(L.get j).Y)).trace.re ^ (L.get j).a := by
    rw [listBound]
    conv_lhs => rw [← List.ofFn_get L, List.map_ofFn, List.prod_ofFn]
    simp [ShiftFactor.bd, Finset.prod_mul_distrib]
  rw [e1, e2]
  exact h

end Factors

section Duhamel

/-- **Duhamel's formula.** The derivative of `v ↦ M e^{(a - v) K'} e^{v K} N` is
`M e^{(a - v) K'} (K - K') e^{v K} N`. -/
private theorem hasDerivAt_mul_exp_mul_exp (M N K K' : Matrix ι ι ℂ) (a u : ℝ) :
    HasDerivAt
      (fun v : ℝ ↦ M * NormedSpace.exp ((a - v) • K') * NormedSpace.exp (v • K) * N)
      (M * NormedSpace.exp ((a - u) • K') * (K - K') * NormedSpace.exp (u • K) * N) u := by
  have h1 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) K u
  have h2 : HasDerivAt (fun v : ℝ ↦ NormedSpace.exp ((a - v) • K'))
      (-(NormedSpace.exp ((a - u) • K') * K')) u := by
    have := HasDerivAt.scomp u (h := fun v : ℝ ↦ a - v)
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) K' (a - u)) ((hasDerivAt_id u).const_sub a)
    simpa [Function.comp_def] using this
  convert ((h2.const_mul M).mul h1).mul_const N using 1
  noncomm_ring

/-- The trace as a continuous real-linear map. -/
private noncomputable def traceCLM : Matrix ι ι ℂ →L[ℝ] ℂ :=
  ((traceLinearMap ι ℂ ℂ).restrictScalars ℝ).toContinuousLinearMap

omit [DecidableEq ι] in
private theorem traceCLM_apply (A : Matrix ι ι ℂ) : traceCLM A = A.trace := rfl

variable {S : Finset κ} {h : κ → Matrix ι ι ℂ}

/-- The bound for all lists of factors, at the level of the index set `S`; the exponents carry
the total weight of the factors that carry the shift. -/
private def Claim (S : Finset κ) (h : κ → Matrix ι ι ℂ) : Prop :=
  ∀ L : List (ShiftFactor ι), Admissible L → listWeight L = 1 →
    ‖(altSum S h (prodAt L)).trace‖ ≤
      (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight L) - 1)) * listBound L

/-- **One Duhamel step.** Replacing the base generator `Y` of one factor that carries the shift
by `Y + V` changes the alternating trace by at most
`∏_{i ∈ S} (e^{‖h_i‖ w} - 1) (e^{‖V‖ (W + a)} - e^{‖V‖ W})` times the bound, where `w` is the
weight of all factors that carry the shift and `W` the weight of the earlier ones, which already
carry the shift `V`. -/
private theorem norm_trace_altSum_step_le (hS : Claim S h) {V : Matrix ι ι ℂ}
    (hV : V.IsHermitian) (P : List (ShiftFactor ι)) (x : ShiftFactor ι)
    (R : List (ShiftFactor ι)) (hxs : x.sh = true) (hL : Admissible (P ++ x :: R))
    (hw : listWeight (P ++ x :: R) = 1) :
    ‖(altSum S h fun s ↦ prodAt (P.map (ShiftFactor.shift V) ++ x.shift V :: R) s -
        prodAt (P.map (ShiftFactor.shift V) ++ x :: R) s).trace‖ ≤
      (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (P ++ x :: R)) - 1)) *
        listBound (P ++ x :: R) *
          (Real.exp (‖V‖ * (shiftWeight P + x.a)) - Real.exp (‖V‖ * shiftWeight P)) := by
  set C := (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (P ++ x :: R)) - 1)) *
    listBound (P ++ x :: R) with hC
  set P' := P.map (ShiftFactor.shift V)
  have hx := hL x (by simp)
  have hP : Admissible P := fun y hy ↦ hL y (by simp [hy])
  have hR : Admissible R := fun y hy ↦ hL y (by simp [hy])
  have hP' : Admissible P' := hP.map_shift hV
  -- The interpolating list of factors.
  let Lu : ℝ → List (ShiftFactor ι) := fun u ↦
    P' ++ (⟨x.B, x.Y + V, x.a - u, true⟩ : ShiftFactor ι) ::
      (⟨V, x.Y, u, true⟩ : ShiftFactor ι) :: R
  -- The interpolating function and its derivative.
  let f : Matrix ι ι ℂ → ℝ → Matrix ι ι ℂ := fun s v ↦
    prodAt P' s * x.B * NormedSpace.exp ((x.a - v) • -(x.Y + V + s)) *
      NormedSpace.exp (v • -(x.Y + s)) * prodAt R s
  let G : ℝ → ℂ := fun v ↦ (altSum S h fun s ↦ f s v).trace
  let G' : ℝ → ℂ := fun v ↦ (altSum S h (prodAt (Lu v))).trace
  have hG : ∀ v, HasDerivAt G (G' v) v := by
    intro v
    have hsum : HasDerivAt (fun v ↦ altSum S h fun s ↦ f s v)
        (altSum S h (prodAt (Lu v))) v := by
      simp only [altSum]
      refine HasDerivAt.fun_sum fun E _ ↦ HasDerivAt.fun_const_smul _ ?_
      convert hasDerivAt_mul_exp_mul_exp (prodAt P' (∑ i ∈ E, h i) * x.B)
        (prodAt R (∑ i ∈ E, h i)) (-(x.Y + ∑ i ∈ E, h i)) (-(x.Y + V + ∑ i ∈ E, h i))
        x.a v
        using 1
      simp only [Lu, prodAt_append, prodAt_cons, ShiftFactor.mat, ite_true]
      rw [show -(x.Y + ∑ i ∈ E, h i) - -(x.Y + V + ∑ i ∈ E, h i) = V by abel]
      simp only [Matrix.mul_assoc]
    exact traceCLM.hasFDerivAt.comp_hasDerivAt v hsum
  -- Endpoint values.
  have hG0 : G 0 = (altSum S h (prodAt (P' ++ x.shift V :: R))).trace := by
    simp only [G]
    congr 2
    funext s
    simp only [f, prodAt_append, prodAt_cons, ShiftFactor.mat, ShiftFactor.shift, hxs, ite_true,
      sub_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_assoc]
  have hGa : G x.a = (altSum S h (prodAt (P' ++ x :: R))).trace := by
    simp only [G]
    congr 2
    funext s
    simp only [f, prodAt_append, prodAt_cons, ShiftFactor.mat, hxs, ite_true, sub_self,
      zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_assoc]
  -- The bound on the derivative.
  have hderiv : ∀ v ∈ Set.Ico 0 x.a,
      ‖G' v‖ ≤ C * (‖V‖ * Real.exp (‖V‖ * (shiftWeight P + x.a - v))) := by
    rintro v ⟨hv0, hva⟩
    have hadm : Admissible (Lu v) := by
      intro y hy
      simp only [Lu, List.mem_append, List.mem_cons] at hy
      rcases hy with hy | rfl | rfl | hy
      · exact hP' y hy
      · exact ⟨hx.1.add hV, by simp only; linarith⟩
      · exact ⟨hx.1, hv0⟩
      · exact hR y hy
    have hwu : listWeight (Lu v) = 1 := by
      rw [← hw]
      simp only [Lu, P', listWeight_append, listWeight_cons, listWeight_map_shift]
      ring
    have hsw : shiftWeight (Lu v) = shiftWeight (P ++ x :: R) := by
      simp only [Lu, P', shiftWeight_append, shiftWeight_cons, shiftWeight_map_shift,
        ShiftFactor.sa, hxs, ite_true]
      ring
    have ht : 0 ≤ (NormedSpace.exp (-x.Y)).trace.re := hx.1.neg.re_trace_exp_nonneg
    have hb : listBound (Lu v) ≤
        ‖V‖ * Real.exp (‖V‖ * (shiftWeight P + x.a - v)) * listBound (P ++ x :: R) := by
      have h1 := listBound_map_shift_le hV hP
      have h2 := ShiftFactor.bd_add_le hV x.B hx.1 (a := x.a - v) (by linarith) true
      have hRn := listBound_nonneg hR
      simp only [Lu, P', listBound_append, listBound_cons]
      calc listBound (P.map (ShiftFactor.shift V)) *
            ((⟨x.B, x.Y + V, x.a - v, true⟩ : ShiftFactor ι).bd *
              ((⟨V, x.Y, v, true⟩ : ShiftFactor ι).bd * listBound R))
          ≤ (Real.exp (‖V‖ * shiftWeight P) * listBound P) *
            ((Real.exp (‖V‖ * (x.a - v)) * (⟨x.B, x.Y, x.a - v, true⟩ : ShiftFactor ι).bd) *
              ((⟨V, x.Y, v, true⟩ : ShiftFactor ι).bd * listBound R)) := by
            have e3 : 0 ≤ (⟨V, x.Y, v, true⟩ : ShiftFactor ι).bd * listBound R :=
              mul_nonneg (ShiftFactor.bd_nonneg (x := ⟨V, x.Y, v, true⟩) hx.1) hRn
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 e3)
              (mul_nonneg
                (ShiftFactor.bd_nonneg (x := ⟨x.B, x.Y + V, x.a - v, true⟩) (hx.1.add hV)) e3)
              (mul_nonneg (Real.exp_pos _).le (listBound_nonneg hP))
        _ = ‖V‖ * Real.exp (‖V‖ * (shiftWeight P + x.a - v)) *
              (listBound P * (x.bd * listBound R)) := by
            have hpow : (NormedSpace.exp (-x.Y)).trace.re ^ (x.a - v) *
                (NormedSpace.exp (-x.Y)).trace.re ^ v =
                  (NormedSpace.exp (-x.Y)).trace.re ^ x.a := by
              rw [← Real.rpow_add_of_nonneg ht (by linarith) hv0, sub_add_cancel]
            simp only [ShiftFactor.bd]
            rw [← hpow, show ‖V‖ * (shiftWeight P + x.a - v) =
              ‖V‖ * shiftWeight P + ‖V‖ * (x.a - v) by ring, Real.exp_add]
            ring
    calc ‖G' v‖ ≤ (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (Lu v)) - 1)) * listBound (Lu v) :=
          hS _ hadm hwu
      _ ≤ (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (P ++ x :: R)) - 1)) *
          (‖V‖ * Real.exp (‖V‖ * (shiftWeight P + x.a - v)) * listBound (P ++ x :: R)) := by
          rw [hsw]
          gcongr
          exact Finset.prod_nonneg fun i _ ↦ sub_nonneg.2
            (Real.one_le_exp (mul_nonneg (norm_nonneg _) (shiftWeight_nonneg hL)))
      _ = C * (‖V‖ * Real.exp (‖V‖ * (shiftWeight P + x.a - v))) := by rw [hC]; ring
  -- The comparison function.
  have hB : ∀ v, HasDerivAt
      (fun v ↦ C *
        (Real.exp (‖V‖ * (shiftWeight P + x.a)) - Real.exp (‖V‖ * (shiftWeight P + x.a - v))))
      (C * (‖V‖ * Real.exp (‖V‖ * (shiftWeight P + x.a - v)))) v := by
    intro v
    have := ((((hasDerivAt_id' v).const_sub (shiftWeight P + x.a)).const_mul ‖V‖).exp.const_sub
      (Real.exp (‖V‖ * (shiftWeight P + x.a)))).const_mul C
    convert this using 1
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := x.a)
    (f := fun v ↦ G v - G 0) (f' := G')
    (fun v _ ↦ ((hG v).sub_const (G 0)).continuousAt.continuousWithinAt)
    (fun v _ ↦ ((hG v).sub_const (G 0)).hasDerivWithinAt) (by simp) hB hderiv
    (Set.right_mem_Icc.2 hx.2)
  rw [altSum_sub, trace_sub, ← hG0, ← hGa, norm_sub_rev]
  refine key.trans_eq ?_
  rw [add_sub_cancel_right]

/-- **One step, for any factor.** A factor that does not carry the shift is unchanged by the
shift and contributes nothing. -/
private theorem norm_trace_altSum_step_le' (hS : Claim S h) {V : Matrix ι ι ℂ}
    (hV : V.IsHermitian) (P : List (ShiftFactor ι)) (x : ShiftFactor ι)
    (R : List (ShiftFactor ι)) (hL : Admissible (P ++ x :: R))
    (hw : listWeight (P ++ x :: R) = 1) :
    ‖(altSum S h fun s ↦ prodAt (P.map (ShiftFactor.shift V) ++ x.shift V :: R) s -
        prodAt (P.map (ShiftFactor.shift V) ++ x :: R) s).trace‖ ≤
      (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (P ++ x :: R)) - 1)) *
        listBound (P ++ x :: R) *
          (Real.exp (‖V‖ * (shiftWeight P + x.sa)) - Real.exp (‖V‖ * shiftWeight P)) := by
  cases hxs : x.sh
  · have hx : x.shift V = x := by
      cases x
      simp_all [ShiftFactor.shift]
    have hsa : x.sa = 0 := by simp [ShiftFactor.sa, hxs]
    simp [hx, hsa, altSum]
  · have hsa : x.sa = x.a := by simp [ShiftFactor.sa, hxs]
    rw [hsa]
    exact norm_trace_altSum_step_le hS hV P x R hxs hL hw

/-- **Telescoping over the factors.** Shifting the base generators of the factors in `R` one at a
time, after the factors in `P` have already been shifted. -/
private theorem norm_trace_altSum_shift_sub_le (hS : Claim S h) {V : Matrix ι ι ℂ}
    (hV : V.IsHermitian) (R : List (ShiftFactor ι)) :
    ∀ P : List (ShiftFactor ι), Admissible (P ++ R) → listWeight (P ++ R) = 1 →
      ‖(altSum S h fun s ↦
          prodAt (P.map (ShiftFactor.shift V) ++ R.map (ShiftFactor.shift V)) s -
            prodAt (P.map (ShiftFactor.shift V) ++ R) s).trace‖ ≤
        (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (P ++ R)) - 1)) * listBound (P ++ R) *
          (Real.exp (‖V‖ * (shiftWeight P + shiftWeight R)) -
            Real.exp (‖V‖ * shiftWeight P)) := by
  induction R with
  | nil => intro P _ _; simp [altSum, shiftWeight]
  | cons x R ih =>
    intro P hL hw
    have happ : P ++ [x] ++ R = P ++ x :: R := by simp
    have h1 := ih (P ++ [x]) (happ ▸ hL) (happ ▸ hw)
    have h2 := norm_trace_altSum_step_le' hS hV P x R hL hw
    have hwP : shiftWeight (P ++ [x]) = shiftWeight P + x.sa := by simp [shiftWeight]
    rw [happ, hwP] at h1
    have hsplit : (fun s ↦
        prodAt (P.map (ShiftFactor.shift V) ++ (x :: R).map (ShiftFactor.shift V)) s -
          prodAt (P.map (ShiftFactor.shift V) ++ x :: R) s) = fun s ↦
        (prodAt ((P ++ [x]).map (ShiftFactor.shift V) ++ R.map (ShiftFactor.shift V)) s -
          prodAt ((P ++ [x]).map (ShiftFactor.shift V) ++ R) s) +
        (prodAt (P.map (ShiftFactor.shift V) ++ x.shift V :: R) s -
          prodAt (P.map (ShiftFactor.shift V) ++ x :: R) s) := by
      funext s
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append]
      abel
    rw [hsplit, altSum_add, trace_add, shiftWeight_cons]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add h1 h2).trans_eq ?_
    rw [← add_assoc]
    ring

end Duhamel

section Induction

variable {h : κ → Matrix ι ι ℂ}

private theorem claim_empty : Claim (∅ : Finset κ) h := by
  intro L hL hw
  rw [altSum_empty, Finset.prod_empty, one_mul]
  exact norm_trace_prodAt_zero_le hL hw

/-- **Induction step.** Adding an index `a` to `S` multiplies the bound by `e^{‖h_a‖ w} - 1`,
with `w` the weight of the factors that carry the shift. -/
private theorem claim_insert [DecidableEq κ] {S : Finset κ} {a : κ} (ha : a ∉ S)
    (hS : Claim S h) (hV : (h a).IsHermitian) : Claim (insert a S) h := by
  intro L hL hw
  have key := norm_trace_altSum_shift_sub_le hS hV L [] (by simpa using hL) (by simpa using hw)
  have h0 : shiftWeight ([] : List (ShiftFactor ι)) = 0 := by simp [shiftWeight]
  simp only [List.map_nil, List.nil_append] at key
  rw [h0, zero_add, mul_zero, Real.exp_zero] at key
  have hfun : (fun s ↦ prodAt L (h a + s) - prodAt L s) =
      fun s ↦ prodAt (L.map (ShiftFactor.shift (h a))) s - prodAt L s := by
    funext s
    rw [prodAt_add]
  rw [altSum_insert ha, hfun, Finset.prod_insert ha]
  exact key.trans_eq (by ring)

private theorem claim_of_isHermitian (S : Finset κ)
    (hh : ∀ i ∈ S, (h i).IsHermitian) : Claim S h := by
  classical
  induction S using Finset.induction_on with
  | empty => exact claim_empty
  | insert a S ha ih =>
    exact claim_insert ha (ih fun i hi ↦ hh i (Finset.mem_insert_of_mem hi))
      (hh a (Finset.mem_insert_self a S))

end Induction

/-- **Alternating sums of shifted exponentials.** For Hermitian `Y` and Hermitian `h_i`, `i ∈ S`,
write `h_E = ∑_{i ∈ E} h_i`. Then for every matrix `O`,
`|Tr (O ∑_{E ⊆ S} (-1)^{|S| - |E|} e^{-(Y + h_E)})|
  ≤ ‖O‖ ∏_{i ∈ S} (e^{‖h_i‖} - 1) Tr e^{-Y}`,
with operator norms. With `Y = β (H - H_C - H_{B(C)})` and `h_i = β H_i`, the alternating sum is
the operator `ρ(β, C)` of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1162–1195,
and this bound gives the inequality before equation `percb2` with `‖O‖ Tr e^{-βH}` in place of the
printed `Tr(O e^{-βH})`, which fails (TNLean paper-gap note
`https://sirui-lu.com/TNLean/paper-gaps/hastings05_cluster_part_trace_pairing.pdf`). -/
theorem norm_trace_mul_sum_powerset_exp_le (S : Finset κ)
    {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (h : κ → Matrix ι ι ℂ)
    (hh : ∀ i ∈ S, (h i).IsHermitian) (O : Matrix ι ι ℂ) :
    ‖(O * ∑ E ∈ S.powerset,
        (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (-(Y + ∑ i ∈ E, h i))).trace‖ ≤
      ‖O‖ * (∏ i ∈ S, (Real.exp ‖h i‖ - 1)) * (NormedSpace.exp (-Y)).trace.re := by
  have key := claim_of_isHermitian S hh [⟨O, Y, 1, true⟩]
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hY, zero_le_one⟩)
    (by simp [listWeight])
  have e1 : altSum S h (prodAt [⟨O, Y, 1, true⟩]) = O * ∑ E ∈ S.powerset,
      (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (-(Y + ∑ i ∈ E, h i)) := by
    simp [altSum, prodAt, ShiftFactor.mat, Finset.mul_sum]
  have e2 : listBound [(⟨O, Y, 1, true⟩ : ShiftFactor ι)] =
      ‖O‖ * (NormedSpace.exp (-Y)).trace.re := by
    simp [listBound, ShiftFactor.bd]
  have e3 : shiftWeight [(⟨O, Y, 1, true⟩ : ShiftFactor ι)] = 1 := by
    simp [shiftWeight, ShiftFactor.sa]
  rw [e1, e2, e3] at key
  simp only [mul_one] at key
  exact key.trans_eq (by ring)

/-- **Uniform form.** If moreover `‖h_i‖ ≤ J` for all `i ∈ S`, then
`|Tr (O ∑_{E ⊆ S} (-1)^{|S| - |E|} e^{-(Y + h_E)})| ≤ ‖O‖ (e^J - 1)^{|S|} Tr e^{-Y}`. -/
theorem norm_trace_mul_sum_powerset_exp_le_pow (S : Finset κ)
    {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (h : κ → Matrix ι ι ℂ)
    (hh : ∀ i ∈ S, (h i).IsHermitian) {J : ℝ} (hJ : ∀ i ∈ S, ‖h i‖ ≤ J)
    (O : Matrix ι ι ℂ) :
    ‖(O * ∑ E ∈ S.powerset,
        (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (-(Y + ∑ i ∈ E, h i))).trace‖ ≤
      ‖O‖ * (Real.exp J - 1) ^ S.card * (NormedSpace.exp (-Y)).trace.re := by
  refine (norm_trace_mul_sum_powerset_exp_le S hY h hh O).trans ?_
  have hprod : ∏ i ∈ S, (Real.exp ‖h i‖ - 1) ≤ (Real.exp J - 1) ^ S.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ ↦ sub_nonneg.2 (Real.one_le_exp (norm_nonneg _)))
      fun i hi ↦ by gcongr; exact hJ i hi
  gcongr
  exact hY.neg.re_trace_exp_nonneg

/-- **An alternating sum between thermal factors.** For Hermitian `X`, `Y` and `h_i`, `i ∈ S`,
weights `p, q, r ≥ 0` with `p + q + r = 1`, and every matrix `O`,
`|Tr (O e^{-p X} (∑_{E ⊆ S} (-1)^{|S| - |E|} e^{-q (Y + h_E)}) e^{-r X})|
  ≤ ‖O‖ ∏_{i ∈ S} (e^{q ‖h_i‖} - 1) (Tr e^{-X})^{p + r} (Tr e^{-Y})^q`,
with operator norms. With `X = β H`, `Y = β (H - H_C - H_{B(C)})`, `h_i = β H_i`, `q = 1/n`,
`p = k/n` and `r = (n - k - 1)/n`, the middle factor is the operator `ρ(β/n, C)` of Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1322–1333, inserted between `ρ(kβ/n)` and
`ρ((n - k - 1)β/n)`; together with `Matrix.IsHermitian.re_trace_exp_add_le`, which bounds
`Tr e^{-Y}` by `e^{β ‖H_C + H_{B(C)}‖} Tr e^{-βH}`, this gives the bound by `‖O‖ y^{n_C}` stated
there. -/
theorem norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le (S : Finset κ)
    {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (h : κ → Matrix ι ι ℂ)
    (hh : ∀ i ∈ S, (h i).IsHermitian) {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hpqr : p + q + r = 1) (O : Matrix ι ι ℂ) :
    ‖(O * NormedSpace.exp (p • -X) * (∑ E ∈ S.powerset,
        (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (q • -(Y + ∑ i ∈ E, h i))) *
          NormedSpace.exp (r • -X)).trace‖ ≤
      ‖O‖ * (∏ i ∈ S, (Real.exp (q * ‖h i‖) - 1)) *
        (NormedSpace.exp (-X)).trace.re ^ (p + r) * (NormedSpace.exp (-Y)).trace.re ^ q := by
  have key := claim_of_isHermitian S hh
    [⟨O, X, p, false⟩, ⟨1, Y, q, true⟩, ⟨1, X, r, false⟩]
    (fun x hx ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      exacts [⟨hX, hp⟩, ⟨hY, hq⟩, ⟨hX, hr⟩])
    (by simp only [listWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]; linarith)
  have e1 : altSum S h (prodAt [⟨O, X, p, false⟩, ⟨1, Y, q, true⟩, ⟨1, X, r, false⟩]) =
      O * NormedSpace.exp (p • -X) * (∑ E ∈ S.powerset,
        (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (q • -(Y + ∑ i ∈ E, h i))) *
          NormedSpace.exp (r • -X) := by
    simp [altSum, prodAt, ShiftFactor.mat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]
  have e2 : shiftWeight [(⟨O, X, p, false⟩ : ShiftFactor ι), ⟨1, Y, q, true⟩,
      ⟨1, X, r, false⟩] = q := by
    simp [shiftWeight, ShiftFactor.sa]
  have htX := hX.neg.re_trace_exp_nonneg
  have htY := hY.neg.re_trace_exp_nonneg
  have e3 : listBound [(⟨O, X, p, false⟩ : ShiftFactor ι), ⟨1, Y, q, true⟩,
      ⟨1, X, r, false⟩] ≤
      ‖O‖ * (NormedSpace.exp (-X)).trace.re ^ (p + r) *
        (NormedSpace.exp (-Y)).trace.re ^ q := by
    have h1 : ‖(1 : Matrix ι ι ℂ)‖ ≤ 1 := l2_opNorm_one_le
    have a1 := Real.rpow_nonneg htY q
    have a2 := Real.rpow_nonneg htX r
    simp only [listBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      ShiftFactor.bd, mul_one]
    rw [Real.rpow_add_of_nonneg htX hp hr]
    calc ‖O‖ * (NormedSpace.exp (-X)).trace.re ^ p *
          (‖(1 : Matrix ι ι ℂ)‖ * (NormedSpace.exp (-Y)).trace.re ^ q *
            (‖(1 : Matrix ι ι ℂ)‖ * (NormedSpace.exp (-X)).trace.re ^ r))
        ≤ ‖O‖ * (NormedSpace.exp (-X)).trace.re ^ p *
          (1 * (NormedSpace.exp (-Y)).trace.re ^ q *
            (1 * (NormedSpace.exp (-X)).trace.re ^ r)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (mul_le_mul_of_nonneg_right h1 a1) (mul_le_mul_of_nonneg_right h1 a2)
              (mul_nonneg (norm_nonneg _) a2) (by rw [one_mul]; exact a1))
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg htX p))
      _ = _ := by ring
  rw [e1, e2] at key
  refine key.trans ?_
  have hprod : ∏ i ∈ S, (Real.exp (‖h i‖ * q) - 1) = ∏ i ∈ S, (Real.exp (q * ‖h i‖) - 1) :=
    Finset.prod_congr rfl fun i _ ↦ by rw [mul_comm]
  rw [hprod]
  calc (∏ i ∈ S, (Real.exp (q * ‖h i‖) - 1)) *
        listBound [(⟨O, X, p, false⟩ : ShiftFactor ι), ⟨1, Y, q, true⟩, ⟨1, X, r, false⟩]
      ≤ (∏ i ∈ S, (Real.exp (q * ‖h i‖) - 1)) * (‖O‖ * (NormedSpace.exp (-X)).trace.re ^ (p + r) *
          (NormedSpace.exp (-Y)).trace.re ^ q) :=
        mul_le_mul_of_nonneg_left e3 (Finset.prod_nonneg fun i _ ↦ sub_nonneg.2
          (Real.one_le_exp (mul_nonneg hq (norm_nonneg _))))
    _ = _ := by ring

/-- **Uniform form between thermal factors.** If moreover `‖h_i‖ ≤ J` for all `i ∈ S`, then
`|Tr (O e^{-p X} (∑_{E ⊆ S} (-1)^{|S| - |E|} e^{-q (Y + h_E)}) e^{-r X})|
  ≤ ‖O‖ (e^{q J} - 1)^{|S|} (Tr e^{-X})^{p + r} (Tr e^{-Y})^q`. This is the factor
`[exp(Jβ/n) - 1]^{n_C}` of the bound of Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1322–1333. -/
theorem norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le_pow (S : Finset κ)
    {X Y : Matrix ι ι ℂ} (hX : X.IsHermitian) (hY : Y.IsHermitian) (h : κ → Matrix ι ι ℂ)
    (hh : ∀ i ∈ S, (h i).IsHermitian) {J : ℝ} (hJ : ∀ i ∈ S, ‖h i‖ ≤ J)
    {p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hpqr : p + q + r = 1)
    (O : Matrix ι ι ℂ) :
    ‖(O * NormedSpace.exp (p • -X) * (∑ E ∈ S.powerset,
        (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (q • -(Y + ∑ i ∈ E, h i))) *
          NormedSpace.exp (r • -X)).trace‖ ≤
      ‖O‖ * (Real.exp (q * J) - 1) ^ S.card *
        (NormedSpace.exp (-X)).trace.re ^ (p + r) * (NormedSpace.exp (-Y)).trace.re ^ q := by
  refine (norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le S hX hY h hh hp hq hr hpqr O).trans
    ?_
  have hprod : ∏ i ∈ S, (Real.exp (q * ‖h i‖) - 1) ≤ (Real.exp (q * J) - 1) ^ S.card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀
      (fun i _ ↦ sub_nonneg.2 (Real.one_le_exp (mul_nonneg hq (norm_nonneg _))))
      fun i hi ↦ by gcongr; exact hJ i hi
  have h1 := Real.rpow_nonneg hX.neg.re_trace_exp_nonneg (p + r)
  have h2 := Real.rpow_nonneg hY.neg.re_trace_exp_nonneg q
  gcongr

end Matrix
