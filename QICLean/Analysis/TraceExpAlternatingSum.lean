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
`percb2` uses.

## Proof

The source argues by a power series expansion. Here the bound is proved by induction on `S`,
for ordered products `B_0 e^{-a_0 (Y_0 + s)} B_1 e^{-a_1 (Y_1 + s)} ⋯` with Hermitian base
generators `Y_j`, weights `a_j ≥ 0` summing to one, and a common shift `s = h_E`. For `S = ∅`
this is the multi-factor Hölder inequality `Matrix.norm_trace_list_prod_mul_exp_smul_le`.
Adding an index `a` replaces the summand by its difference in the direction `V = h_a`. The
difference telescopes over the factors: factor `j` changes from `Y_j` to `Y_j + V` while the
earlier factors carry `Y_k + V`. By Duhamel's formula,

`d/du [e^{-(a_j - u)(Z + V)} e^{-u Z}] = e^{-(a_j - u)(Z + V)} V e^{-u Z}`,

which is an ordered product with one factor more, so the inductive hypothesis bounds the
derivative. The estimate `Tr e^{-(Y + V)} ≤ e^{‖V‖} Tr e^{-Y}` on the shifted factors bounds
the derivative at `u` by `‖V‖ e^{‖V‖ (A_j - u)}` times the previous bound, with `A_j` the weight
of the first `j + 1` factors, and the mean value inequality integrates this to
`e^{‖V‖ A_j} - e^{‖V‖ A_{j-1}}`. The sum over `j` telescopes to `e^{‖V‖} - 1`.

## Main results

* `Matrix.norm_trace_mul_sum_powerset_exp_le`: the bound with the factors `e^{‖h_i‖} - 1`.
* `Matrix.norm_trace_mul_sum_powerset_exp_le_pow`: the bound with a uniform `‖h_i‖ ≤ J`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73, 085115 (2006),
  arXiv:cond-mat/0508554v3, source file `proj3new.tex`, lines 1162–1195: the definition of
  `ρ(β, C)`, the bound
  `Tr (O ρ(β, C)) ≤ [exp(Jβ) - 1]^{n_C} exp(β ‖H_C + H_{B(C)}‖) Tr e^{-βH}`
  and equation `percb2`.
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

/-- A factor `B e^{-a (Y + s)}` of an ordered product, with a common shift `s`. -/
private structure ShiftFactor (ι : Type*) where
  /-- The arbitrary matrix of the factor. -/
  B : Matrix ι ι ℂ
  /-- The base generator, Hermitian in all uses. -/
  Y : Matrix ι ι ℂ
  /-- The weight. -/
  a : ℝ

/-- The matrix `B e^{-a (Y + s)}` of a factor at shift `s`. -/
private noncomputable def ShiftFactor.mat (s : Matrix ι ι ℂ) (x : ShiftFactor ι) :
    Matrix ι ι ℂ :=
  x.B * NormedSpace.exp (x.a • -(x.Y + s))

/-- The factor `‖B‖ (Tr e^{-Y})^a` of the bound. -/
private noncomputable def ShiftFactor.bd (x : ShiftFactor ι) : ℝ :=
  ‖x.B‖ * (NormedSpace.exp (-x.Y)).trace.re ^ x.a

omit [Fintype ι] [DecidableEq ι] in
/-- The factor with base generator `Y + V`. -/
private def ShiftFactor.shift (V : Matrix ι ι ℂ) (x : ShiftFactor ι) : ShiftFactor ι :=
  ⟨x.B, x.Y + V, x.a⟩

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

/-- Shifting every base generator by `V` is the same as adding `V` to the common shift. -/
private theorem prodAt_add (L : List (ShiftFactor ι)) (V s : Matrix ι ι ℂ) :
    prodAt L (V + s) = prodAt (L.map (ShiftFactor.shift V)) s := by
  simp only [prodAt, List.map_map]
  congr 1
  exact List.map_congr_left fun x _ ↦ by
    simp only [Function.comp_apply, ShiftFactor.mat, ShiftFactor.shift, add_assoc]

/-- The trace of the exponential of a Hermitian matrix has nonnegative real part. -/
private theorem re_trace_exp_nonneg {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    0 ≤ (NormedSpace.exp A).trace.re := by
  rw [hA.re_trace_exp_eq_sum]
  exact Finset.sum_nonneg fun i _ ↦ (Real.exp_pos _).le

private theorem ShiftFactor.bd_nonneg {x : ShiftFactor ι} (hx : x.Y.IsHermitian) : 0 ≤ x.bd :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (re_trace_exp_nonneg hx.neg) _)

private theorem listBound_nonneg {L : List (ShiftFactor ι)} (hL : Admissible L) : 0 ≤ listBound L :=
  List.prod_nonneg fun b hb ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact ShiftFactor.bd_nonneg (hL y hy).1

/-- Shifting the base generator by a Hermitian `V` raises the bound of a factor by at most
`e^{a ‖V‖}`. -/
private theorem ShiftFactor.bd_shift_le {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    {x : ShiftFactor ι} (hx : x.Y.IsHermitian) (ha : 0 ≤ x.a) :
    (x.shift V).bd ≤ Real.exp (‖V‖ * x.a) * x.bd := by
  have htr := hx.neg.re_trace_exp_add_le hV.neg
  rw [norm_neg, ← neg_add] at htr
  have h0 : 0 ≤ (NormedSpace.exp (-(x.Y + V))).trace.re := re_trace_exp_nonneg (hx.add hV).neg
  have h1 : 0 ≤ (NormedSpace.exp (-x.Y)).trace.re := re_trace_exp_nonneg hx.neg
  calc ‖x.B‖ * (NormedSpace.exp (-(x.Y + V))).trace.re ^ x.a
      ≤ ‖x.B‖ * (Real.exp ‖V‖ * (NormedSpace.exp (-x.Y)).trace.re) ^ x.a :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 htr ha) (norm_nonneg _)
    _ = Real.exp (‖V‖ * x.a) * x.bd := by
        rw [Real.mul_rpow (Real.exp_pos _).le h1, ← Real.exp_mul, ShiftFactor.bd]
        ring

private theorem listBound_map_shift_le {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    {L : List (ShiftFactor ι)} (hL : Admissible L) :
    listBound (L.map (ShiftFactor.shift V)) ≤ Real.exp (‖V‖ * listWeight L) * listBound L := by
  induction L with
  | nil => simp [listBound, listWeight]
  | cons x L ih =>
    have hx := hL x (by simp)
    have hL' : Admissible L := fun y hy ↦ hL y (by simp [hy])
    rw [List.map_cons, listBound_cons, listBound_cons, listWeight_cons, mul_add, Real.exp_add]
    calc (x.shift V).bd * listBound (L.map (ShiftFactor.shift V))
        ≤ (Real.exp (‖V‖ * x.a) * x.bd) * (Real.exp (‖V‖ * listWeight L) * listBound L) :=
          mul_le_mul (x.bd_shift_le hV hx.1 hx.2) (ih hL')
            (listBound_nonneg fun y hy ↦ by
              obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
              exact ⟨(hL' z hz).1.add hV, (hL' z hz).2⟩)
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

/-- The bound for all lists of factors, at the level of the index set `S`. -/
private def Claim (S : Finset κ) (h : κ → Matrix ι ι ℂ) : Prop :=
  ∀ L : List (ShiftFactor ι), Admissible L → listWeight L = 1 →
    ‖(altSum S h (prodAt L)).trace‖ ≤ (∏ i ∈ S, (Real.exp ‖h i‖ - 1)) * listBound L

/-- **One Duhamel step.** Replacing the base generator `Y` of one factor by `Y + V` changes the
alternating trace by at most `∏_{i ∈ S} (e^{‖h_i‖} - 1) (e^{‖V‖ (W + a)} - e^{‖V‖ W})` times the
bound, where `W` is the weight of the earlier factors, which already carry the shift `V`. -/
private theorem norm_trace_altSum_step_le (hS : Claim S h) {V : Matrix ι ι ℂ}
    (hV : V.IsHermitian) (P : List (ShiftFactor ι)) (x : ShiftFactor ι)
    (R : List (ShiftFactor ι)) (hL : Admissible (P ++ x :: R)) (hw : listWeight (P ++ x :: R) = 1) :
    ‖(altSum S h fun s ↦ prodAt (P.map (ShiftFactor.shift V) ++ x.shift V :: R) s -
        prodAt (P.map (ShiftFactor.shift V) ++ x :: R) s).trace‖ ≤
      (∏ i ∈ S, (Real.exp ‖h i‖ - 1)) * listBound (P ++ x :: R) *
        (Real.exp (‖V‖ * (listWeight P + x.a)) - Real.exp (‖V‖ * listWeight P)) := by
  set C := (∏ i ∈ S, (Real.exp ‖h i‖ - 1)) * listBound (P ++ x :: R) with hC
  set P' := P.map (ShiftFactor.shift V)
  have hx := hL x (by simp)
  have hP : Admissible P := fun y hy ↦ hL y (by simp [hy])
  have hR : Admissible R := fun y hy ↦ hL y (by simp [hy])
  have hP' : Admissible P' := fun y hy ↦ by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact ⟨(hP z hz).1.add hV, (hP z hz).2⟩
  -- The interpolating list of factors.
  let Lu : ℝ → List (ShiftFactor ι) := fun u ↦
    P' ++ (⟨x.B, x.Y + V, x.a - u⟩ : ShiftFactor ι) :: (⟨V, x.Y, u⟩ : ShiftFactor ι) :: R
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
      simp only [Lu, prodAt_append, prodAt_cons, ShiftFactor.mat]
      rw [show -(x.Y + ∑ i ∈ E, h i) - -(x.Y + V + ∑ i ∈ E, h i) = V by abel]
      simp only [Matrix.mul_assoc]
    exact traceCLM.hasFDerivAt.comp_hasDerivAt v hsum
  -- Endpoint values.
  have hG0 : G 0 = (altSum S h (prodAt (P' ++ x.shift V :: R))).trace := by
    simp only [G]
    congr 2
    funext s
    simp only [f, prodAt_append, prodAt_cons, ShiftFactor.mat, ShiftFactor.shift, sub_zero,
      zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_assoc]
  have hGa : G x.a = (altSum S h (prodAt (P' ++ x :: R))).trace := by
    simp only [G]
    congr 2
    funext s
    simp only [f, prodAt_append, prodAt_cons, ShiftFactor.mat, sub_self, zero_smul,
      NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_assoc]
  -- The bound on the derivative.
  have hderiv : ∀ v ∈ Set.Ico 0 x.a,
      ‖G' v‖ ≤ C * (‖V‖ * Real.exp (‖V‖ * (listWeight P + x.a - v))) := by
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
    have ht : 0 ≤ (NormedSpace.exp (-x.Y)).trace.re := re_trace_exp_nonneg hx.1.neg
    have hb : listBound (Lu v) ≤
        ‖V‖ * Real.exp (‖V‖ * (listWeight P + x.a - v)) * listBound (P ++ x :: R) := by
      have h1 := listBound_map_shift_le hV hP
      have h2 := ShiftFactor.bd_shift_le (x := ⟨x.B, x.Y, x.a - v⟩) hV hx.1
        (by simp only; linarith)
      have hRn := listBound_nonneg hR
      simp only [Lu, P', listBound_append, listBound_cons]
      calc listBound (P.map (ShiftFactor.shift V)) *
            ((ShiftFactor.shift V ⟨x.B, x.Y, x.a - v⟩).bd *
              ((⟨V, x.Y, v⟩ : ShiftFactor ι).bd * listBound R))
          ≤ (Real.exp (‖V‖ * listWeight P) * listBound P) *
            ((Real.exp (‖V‖ * (x.a - v)) * (⟨x.B, x.Y, x.a - v⟩ : ShiftFactor ι).bd) *
              ((⟨V, x.Y, v⟩ : ShiftFactor ι).bd * listBound R)) := by
            have e3 : 0 ≤ (⟨V, x.Y, v⟩ : ShiftFactor ι).bd * listBound R :=
              mul_nonneg (ShiftFactor.bd_nonneg (x := ⟨V, x.Y, v⟩) hx.1) hRn
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 e3)
              (mul_nonneg
                (ShiftFactor.bd_nonneg (x := ⟨x.B, x.Y + V, x.a - v⟩) (hx.1.add hV)) e3)
              (mul_nonneg (Real.exp_pos _).le (listBound_nonneg hP))
        _ = ‖V‖ * Real.exp (‖V‖ * (listWeight P + x.a - v)) *
              (listBound P * (x.bd * listBound R)) := by
            have hpow : (NormedSpace.exp (-x.Y)).trace.re ^ (x.a - v) *
                (NormedSpace.exp (-x.Y)).trace.re ^ v =
                  (NormedSpace.exp (-x.Y)).trace.re ^ x.a := by
              rw [← Real.rpow_add_of_nonneg ht (by linarith) hv0, sub_add_cancel]
            simp only [ShiftFactor.bd]
            rw [← hpow, show ‖V‖ * (listWeight P + x.a - v) =
              ‖V‖ * listWeight P + ‖V‖ * (x.a - v) by ring, Real.exp_add]
            ring
    calc ‖G' v‖ ≤ (∏ i ∈ S, (Real.exp ‖h i‖ - 1)) * listBound (Lu v) := hS _ hadm hwu
      _ ≤ (∏ i ∈ S, (Real.exp ‖h i‖ - 1)) *
          (‖V‖ * Real.exp (‖V‖ * (listWeight P + x.a - v)) * listBound (P ++ x :: R)) := by
          gcongr
          exact Finset.prod_nonneg fun i _ ↦ sub_nonneg.2 (Real.one_le_exp (norm_nonneg _))
      _ = C * (‖V‖ * Real.exp (‖V‖ * (listWeight P + x.a - v))) := by rw [hC]; ring
  -- The comparison function.
  have hB : ∀ v, HasDerivAt
      (fun v ↦ C *
        (Real.exp (‖V‖ * (listWeight P + x.a)) - Real.exp (‖V‖ * (listWeight P + x.a - v))))
      (C * (‖V‖ * Real.exp (‖V‖ * (listWeight P + x.a - v)))) v := by
    intro v
    have := ((((hasDerivAt_id' v).const_sub (listWeight P + x.a)).const_mul ‖V‖).exp.const_sub
      (Real.exp (‖V‖ * (listWeight P + x.a)))).const_mul C
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

/-- **Telescoping over the factors.** Shifting the base generators of the factors in `R` one at a
time, after the factors in `P` have already been shifted. -/
private theorem norm_trace_altSum_shift_sub_le (hS : Claim S h) {V : Matrix ι ι ℂ}
    (hV : V.IsHermitian) (R : List (ShiftFactor ι)) :
    ∀ P : List (ShiftFactor ι), Admissible (P ++ R) → listWeight (P ++ R) = 1 →
      ‖(altSum S h fun s ↦
          prodAt (P.map (ShiftFactor.shift V) ++ R.map (ShiftFactor.shift V)) s -
            prodAt (P.map (ShiftFactor.shift V) ++ R) s).trace‖ ≤
        (∏ i ∈ S, (Real.exp ‖h i‖ - 1)) * listBound (P ++ R) *
          (Real.exp (‖V‖ * (listWeight P + listWeight R)) - Real.exp (‖V‖ * listWeight P)) := by
  induction R with
  | nil => intro P _ _; simp [altSum, listWeight]
  | cons x R ih =>
    intro P hL hw
    have happ : P ++ [x] ++ R = P ++ x :: R := by simp
    have h1 := ih (P ++ [x]) (happ ▸ hL) (happ ▸ hw)
    have h2 := norm_trace_altSum_step_le hS hV P x R hL hw
    have hwP : listWeight (P ++ [x]) = listWeight P + x.a := by simp [listWeight]
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
    rw [hsplit, altSum_add, trace_add, listWeight_cons]
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

/-- **Induction step.** Adding an index `a` to `S` multiplies the bound by `e^{‖h_a‖} - 1`. -/
private theorem claim_insert [DecidableEq κ] {S : Finset κ} {a : κ} (ha : a ∉ S)
    (hS : Claim S h) (hV : (h a).IsHermitian) : Claim (insert a S) h := by
  intro L hL hw
  have key := norm_trace_altSum_shift_sub_le hS hV L [] (by simpa using hL) (by simpa using hw)
  have h0 : listWeight ([] : List (ShiftFactor ι)) = 0 := by simp [listWeight]
  simp only [List.map_nil, List.nil_append] at key
  rw [h0, hw, zero_add, mul_one, mul_zero, Real.exp_zero] at key
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
printed `Tr(O e^{-βH})`. -/
theorem norm_trace_mul_sum_powerset_exp_le (S : Finset κ)
    {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) (h : κ → Matrix ι ι ℂ)
    (hh : ∀ i ∈ S, (h i).IsHermitian) (O : Matrix ι ι ℂ) :
    ‖(O * ∑ E ∈ S.powerset,
        (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (-(Y + ∑ i ∈ E, h i))).trace‖ ≤
      ‖O‖ * (∏ i ∈ S, (Real.exp ‖h i‖ - 1)) * (NormedSpace.exp (-Y)).trace.re := by
  have key := claim_of_isHermitian S hh [⟨O, Y, 1⟩]
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hY, zero_le_one⟩)
    (by simp [listWeight])
  have e1 : altSum S h (prodAt [⟨O, Y, 1⟩]) = O * ∑ E ∈ S.powerset,
      (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (-(Y + ∑ i ∈ E, h i)) := by
    simp [altSum, prodAt, ShiftFactor.mat, Finset.mul_sum]
  have e2 : listBound [(⟨O, Y, 1⟩ : ShiftFactor ι)] =
      ‖O‖ * (NormedSpace.exp (-Y)).trace.re := by
    simp [listBound, ShiftFactor.bd]
  rw [e1, e2] at key
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
  exact re_trace_exp_nonneg hY.neg

end Matrix
