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

The same bound holds for ordered products of several alternating sums. For matrices `B_j`,
Hermitian `Y_j`, weights `q_j ≥ 0` with `∑_j q_j = 1` and Hermitian `h_{j,i}`, `i ∈ S_j`, write
`ρ_j = ∑_{E ⊆ S_j} (-1)^{|S_j| - |E|} e^{-q_j (Y_j + h_{j,E})}`. Then

`|Tr (B_0 ρ_0 ⋯ B_{n-1} ρ_{n-1})|
  ≤ ∏_j ‖B_j‖ ∏_{i ∈ S_j} (e^{q_j ‖h_{j,i}‖} - 1) (Tr e^{-Y_j})^{q_j}`.

A factor with `S_j = ∅` is a thermal factor `e^{-q_j Y_j}`, so this bounds every product of
thermal factors and cluster parts that occurs in the operator `ρ_m` of lines 1334–1341.

## Proof

The source argues by a power series expansion. Here the bound is proved by induction on `S`,
for ordered products `B_0 e^{-a_0 (Y_0 + c_0 s)} B_1 e^{-a_1 (Y_1 + c_1 s)} ⋯` with Hermitian base
generators `Y_j`, weights `a_j ≥ 0` summing to one, and tags `t_j`; the factor `j` carries the
shift `s_{t_j}`, where `s_t = ∑_{i ∈ E, t(i) = t} h_i` sums the indices `i` whose tag `t(i)` is `t`.
Let `w_t` be the total weight of the factors with the tag `t`. For `S = ∅` the bound is the
multi-factor Hölder inequality `Matrix.norm_trace_list_prod_mul_exp_smul_le`. Adding an index `a`
replaces the summand by its difference in the direction `V = h_a` at the tag `t(a)`. The
difference telescopes over the factors with that tag: factor `j` changes from `Y_j` to `Y_j + V`
while the earlier such factors carry `Y_k + V`.
By Duhamel's formula,

`d/du [e^{-(a_j - u)(Z + V)} e^{-u Z}] = e^{-(a_j - u)(Z + V)} V e^{-u Z}`,

which is an ordered product with one factor more and the same weight at every tag, since both
new factors keep the tag of factor `j`, so the inductive hypothesis bounds the derivative. The
estimate `Tr e^{-(Y + V)} ≤ e^{‖V‖} Tr e^{-Y}` on the shifted factors bounds the derivative at
`u` by `‖V‖ e^{‖V‖ (A_j - u)}` times the previous bound, with `A_j` the shifted weight of the
first `j + 1` factors with the tag `t(a)`, and the mean value inequality integrates this to
`e^{‖V‖ A_j} - e^{‖V‖ A_{j-1}}`. The sum over `j` telescopes to `e^{‖V‖ w_{t(a)}} - 1`. The
bound on `Tr (O Δ)` is the case of one factor, with `w = 1`; the bound between the factors
`e^{-p X}` and `e^{-r X}` is the case of three factors, of which only the middle one carries the
shift, with `w = q`. For the product of several alternating sums, the factor `j` has its own tag
`j`, so `w_j = q_j`, and by multilinearity of the ordered product the tagged alternating sum over
the disjoint union of the `S_j` equals the ordered product of the alternating sums `ρ_j`.

## Main results

* `Matrix.norm_trace_mul_sum_powerset_exp_le`: the bound with the factors `e^{‖h_i‖} - 1`.
* `Matrix.norm_trace_mul_sum_powerset_exp_le_pow`: the bound with a uniform `‖h_i‖ ≤ J`.
* `Matrix.norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le`: the bound with the alternating sum
  between two thermal factors.
* `Matrix.norm_trace_mul_exp_mul_sum_powerset_exp_mul_exp_le_pow`: the same bound with a uniform
  `‖h_i‖ ≤ J`.
* `Matrix.norm_trace_list_prod_mul_sum_powerset_exp_le`: the bound for an ordered product of
  several alternating sums.
* `Matrix.norm_trace_list_prod_mul_sum_powerset_exp_le_pow`: the same bound with a uniform
  `‖h_{j,i}‖ ≤ J`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73, 085115 (2006),
  arXiv:cond-mat/0508554v3, source file `proj3new.tex`, lines 1162–1195: the definition of
  `ρ(β, C)`, the bound
  `Tr (O ρ(β, C)) ≤ [exp(Jβ) - 1]^{n_C} exp(β ‖H_C + H_{B(C)}‖) Tr e^{-βH}`
  and equation `percb2`; lines 1322–1333: the bound
  `Z^{-1} Tr (O ρ(kβ/n) ρ(β/n, C) ρ((n - k - 1)β/n)) ≤ ‖O‖ y^{n_C}`; lines 1334–1341: the
  operator `ρ_m`, a sum of products of thermal factors and cluster parts.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} {τ : Type*} [DecidableEq τ]

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
private theorem altSum_map {κ' : Type*} (S : Finset κ) (e : κ ↪ κ') (h : κ' → Matrix ι ι ℂ)
    (F : Matrix ι ι ℂ → Matrix ι ι ℂ) :
    altSum (S.map e) h F = altSum S (fun i ↦ h (e i)) F := by
  classical
  induction S using Finset.induction_on generalizing F with
  | empty => simp [altSum_empty]
  | insert a S ha ih =>
    rw [Finset.map_insert, altSum_insert (by simpa using ha), ih, altSum_insert ha]

/-- The alternating sum with tagged shifts: the index `i` shifts the tag `home i`, so that the
shift at the tag `t` is `∑_{i ∈ E, home i = t} h_i`. -/
private noncomputable def altSumT (S : Finset κ) (h : κ → Matrix ι ι ℂ) (home : κ → τ)
    (F : (τ → Matrix ι ι ℂ) → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  ∑ E ∈ S.powerset, (-1 : ℂ) ^ (S.card - E.card) • F (∑ i ∈ E, Pi.single (home i) (h i))

omit [Fintype ι] [DecidableEq ι] in
private theorem altSumT_empty (h : κ → Matrix ι ι ℂ) (home : κ → τ)
    (F : (τ → Matrix ι ι ℂ) → Matrix ι ι ℂ) :
    altSumT ∅ h home F = F 0 := by
  simp [altSumT]

omit [Fintype ι] [DecidableEq ι] in
/-- Adding an index `a` to `S` replaces `F` by its difference in the direction `h_a` at the tag
`home a`. -/
private theorem altSumT_insert [DecidableEq κ] {a : κ} {S : Finset κ} (ha : a ∉ S)
    (h : κ → Matrix ι ι ℂ) (home : κ → τ) (F : (τ → Matrix ι ι ℂ) → Matrix ι ι ℂ) :
    altSumT (insert a S) h home F =
      altSumT S h home fun σ ↦ F (Pi.single (home a) (h a) + σ) - F σ := by
  rw [altSumT, Finset.sum_powerset_insert ha, altSumT, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun E hE ↦ ?_
  have hES := Finset.mem_powerset.1 hE
  have haE : a ∉ E := fun h' ↦ ha (hES h')
  rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem haE, Finset.sum_insert haE,
    Nat.add_sub_add_right, Nat.sub_add_comm (Finset.card_le_card hES), pow_succ, smul_sub]
  simp only [mul_neg, mul_one, neg_smul]
  abel

omit [Fintype ι] [DecidableEq ι] in
private theorem altSumT_add (S : Finset κ) (h : κ → Matrix ι ι ℂ) (home : κ → τ)
    (F G : (τ → Matrix ι ι ℂ) → Matrix ι ι ℂ) :
    altSumT S h home (fun σ ↦ F σ + G σ) = altSumT S h home F + altSumT S h home G := by
  simp [altSumT, smul_add, Finset.sum_add_distrib]

omit [Fintype ι] [DecidableEq ι] in
private theorem altSumT_sub (S : Finset κ) (h : κ → Matrix ι ι ℂ) (home : κ → τ)
    (F G : (τ → Matrix ι ι ℂ) → Matrix ι ι ℂ) :
    altSumT S h home (fun σ ↦ F σ - G σ) = altSumT S h home F - altSumT S h home G := by
  simp [altSumT, smul_sub, Finset.sum_sub_distrib]

/-- **Products of alternating sums.** For an ordered product of `n` slots, where slot `j` sees
only the shift at the tag `j`, the tagged alternating sum is the ordered product of the
alternating sums of the slots, each over the indices whose tag is `j`. -/
private theorem altSumT_ofFn_prod {n : ℕ} (h : κ → Matrix ι ι ℂ)
    (home : κ → Fin n) (S : Finset κ) :
    ∀ F : Fin n → Matrix ι ι ℂ → Matrix ι ι ℂ,
      altSumT S h home (fun σ ↦ (List.ofFn fun j ↦ F j (σ j)).prod) =
        (List.ofFn fun j ↦ altSum (S.filter (home · = j)) h (F j)).prod := by
  classical
  induction S using Finset.induction_on with
  | empty => intro F; simp [altSumT_empty, altSum_empty]
  | insert a S ha ih =>
    intro F
    set G : Fin n → Matrix ι ι ℂ → Matrix ι ι ℂ :=
      Function.update F (home a) fun s ↦ F (home a) (h a + s) - F (home a) s with hG
    rw [altSumT_insert ha]
    trans altSumT S h home (fun σ ↦ (List.ofFn fun j ↦ G j (σ j)).prod)
    · congr 1
      funext σ
      have key := MultilinearMap.map_update_sub (MultilinearMap.mkPiAlgebraFin ℂ n (Matrix ι ι ℂ))
        (fun j ↦ F j (σ j)) (home a) (F (home a) (h a + σ (home a))) (F (home a) (σ (home a)))
      simp only [MultilinearMap.mkPiAlgebraFin_apply, Function.update_eq_self] at key
      have e1 : (fun j ↦ F j ((Pi.single (home a) (h a) + σ : Fin n → Matrix ι ι ℂ) j)) =
          Function.update (fun j ↦ F j (σ j)) (home a) (F (home a) (h a + σ (home a))) := by
        funext j
        by_cases hj : j = home a
        · subst hj; simp
        · simp [hj]
      have e3 : (fun j ↦ G j (σ j)) = Function.update (fun j ↦ F j (σ j)) (home a)
          (F (home a) (h a + σ (home a)) - F (home a) (σ (home a))) := by
        funext j
        by_cases hj : j = home a
        · subst hj; simp [hG]
        · simp [hG, hj]
      rw [e1, e3, key]
    · rw [ih G]
      congr 1
      congr 1
      funext j
      by_cases hj : j = home a
      · subst hj
        simp only [Finset.filter_insert, ↓reduceIte]
        rw [altSum_insert (by simp only [Finset.mem_filter, not_and]; exact fun h' ↦ (ha h').elim)]
        simp [hG]
      · simp only [Finset.filter_insert, show home a ≠ j from fun h' ↦ hj h'.symm, ↓reduceIte]
        simp [hG, hj]

end AlternatingSum

section Factors

/-- A factor of an ordered product: `B e^{-a (Y + σ_t)}`, where `σ_t` is the shift at the tag `t`
of the factor. -/
private structure ShiftFactor (τ ι : Type*) where
  /-- The arbitrary matrix of the factor. -/
  B : Matrix ι ι ℂ
  /-- The base generator, Hermitian in all uses. -/
  Y : Matrix ι ι ℂ
  /-- The weight. -/
  a : ℝ
  /-- The tag of the shift that the factor carries. -/
  tag : τ

/-- The matrix `B e^{-a (Y + σ_t)}` at the family of shifts `σ`. -/
private noncomputable def ShiftFactor.mat (σ : τ → Matrix ι ι ℂ) (x : ShiftFactor τ ι) :
    Matrix ι ι ℂ :=
  x.B * NormedSpace.exp (x.a • -(x.Y + σ x.tag))

/-- The factor `‖B‖ (Tr e^{-Y})^a` of the bound. -/
private noncomputable def ShiftFactor.bd (x : ShiftFactor τ ι) : ℝ :=
  ‖x.B‖ * (NormedSpace.exp (-x.Y)).trace.re ^ x.a

omit [Fintype ι] [DecidableEq ι] in
/-- The factor with base generator `Y + V` if it carries the tag `t`, and the factor itself
otherwise. -/
private def ShiftFactor.shift (t : τ) (V : Matrix ι ι ℂ) (x : ShiftFactor τ ι) : ShiftFactor τ ι :=
  ⟨x.B, if x.tag = t then x.Y + V else x.Y, x.a, x.tag⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The weight of a factor that carries the tag `t`, and zero for any other factor. -/
private def ShiftFactor.sa (t : τ) (x : ShiftFactor τ ι) : ℝ :=
  if x.tag = t then x.a else 0

/-- The ordered product of a list of factors at the family of shifts `σ`. -/
private noncomputable def prodAt (L : List (ShiftFactor τ ι)) (σ : τ → Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (L.map (ShiftFactor.mat σ)).prod

/-- The bound `∏ ‖B_j‖ (Tr e^{-Y_j})^{a_j}` of a list of factors. -/
private noncomputable def listBound (L : List (ShiftFactor τ ι)) : ℝ :=
  (L.map ShiftFactor.bd).prod

omit [Fintype ι] [DecidableEq ι] [DecidableEq τ] in
/-- The total weight of a list of factors. -/
private def listWeight (L : List (ShiftFactor τ ι)) : ℝ :=
  (L.map ShiftFactor.a).sum

omit [Fintype ι] [DecidableEq ι] in
/-- The total weight of the factors that carry the tag `t`. -/
private def shiftWeight (t : τ) (L : List (ShiftFactor τ ι)) : ℝ :=
  (L.map (ShiftFactor.sa t)).sum

omit [Fintype ι] [DecidableEq ι] [DecidableEq τ] in
/-- Hermitian base generators and nonnegative weights. -/
private def Admissible (L : List (ShiftFactor τ ι)) : Prop :=
  ∀ x ∈ L, x.Y.IsHermitian ∧ 0 ≤ x.a

omit [DecidableEq τ] in
private theorem prodAt_append (L₁ L₂ : List (ShiftFactor τ ι)) (σ : τ → Matrix ι ι ℂ) :
    prodAt (L₁ ++ L₂) σ = prodAt L₁ σ * prodAt L₂ σ := by
  simp [prodAt]

omit [DecidableEq τ] in
private theorem prodAt_cons (x : ShiftFactor τ ι) (L : List (ShiftFactor τ ι))
    (σ : τ → Matrix ι ι ℂ) :
    prodAt (x :: L) σ = x.mat σ * prodAt L σ := by
  simp [prodAt]

omit [DecidableEq τ] in
private theorem listBound_append (L₁ L₂ : List (ShiftFactor τ ι)) :
    listBound (L₁ ++ L₂) = listBound L₁ * listBound L₂ := by
  simp [listBound]

omit [DecidableEq τ] in
private theorem listBound_cons (x : ShiftFactor τ ι) (L : List (ShiftFactor τ ι)) :
    listBound (x :: L) = x.bd * listBound L := by
  simp [listBound]

omit [Fintype ι] [DecidableEq ι] [DecidableEq τ] in
private theorem listWeight_append (L₁ L₂ : List (ShiftFactor τ ι)) :
    listWeight (L₁ ++ L₂) = listWeight L₁ + listWeight L₂ := by
  simp [listWeight]

omit [Fintype ι] [DecidableEq ι] [DecidableEq τ] in
private theorem listWeight_cons (x : ShiftFactor τ ι) (L : List (ShiftFactor τ ι)) :
    listWeight (x :: L) = x.a + listWeight L := by
  simp [listWeight]

omit [Fintype ι] [DecidableEq ι] in
private theorem listWeight_map_shift (t : τ) (V : Matrix ι ι ℂ) (L : List (ShiftFactor τ ι)) :
    listWeight (L.map (ShiftFactor.shift t V)) = listWeight L := by
  simp [listWeight, Function.comp_def, ShiftFactor.shift]

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftWeight_append (t : τ) (L₁ L₂ : List (ShiftFactor τ ι)) :
    shiftWeight t (L₁ ++ L₂) = shiftWeight t L₁ + shiftWeight t L₂ := by
  simp [shiftWeight]

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftWeight_cons (t : τ) (x : ShiftFactor τ ι) (L : List (ShiftFactor τ ι)) :
    shiftWeight t (x :: L) = x.sa t + shiftWeight t L := by
  simp [shiftWeight]

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftWeight_map_shift (t t' : τ) (V : Matrix ι ι ℂ)
    (L : List (ShiftFactor τ ι)) :
    shiftWeight t' (L.map (ShiftFactor.shift t V)) = shiftWeight t' L := by
  simp only [shiftWeight, List.map_map]
  rfl

omit [Fintype ι] [DecidableEq ι] in
private theorem shiftWeight_nonneg (t : τ) {L : List (ShiftFactor τ ι)} (hL : Admissible L) :
    0 ≤ shiftWeight t L :=
  List.sum_nonneg fun b hb ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    unfold ShiftFactor.sa
    split_ifs
    exacts [(hL y hy).2, le_rfl]

omit [Fintype ι] [DecidableEq ι] in
private theorem Admissible.map_shift (t : τ) {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    {L : List (ShiftFactor τ ι)} (hL : Admissible L) :
    Admissible (L.map (ShiftFactor.shift t V)) := fun y hy ↦ by
  obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
  refine ⟨?_, (hL z hz).2⟩
  unfold ShiftFactor.shift
  split_ifs
  exacts [(hL z hz).1.add hV, (hL z hz).1]

/-- Adding `V` to the shift at the tag `t` is the same as shifting the base generators of the
factors that carry the tag `t`. -/
private theorem prodAt_add (L : List (ShiftFactor τ ι)) (t : τ) (V : Matrix ι ι ℂ)
    (σ : τ → Matrix ι ι ℂ) :
    prodAt L (Pi.single t V + σ) = prodAt (L.map (ShiftFactor.shift t V)) σ := by
  simp only [prodAt, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ ↦ ?_
  by_cases hx : x.tag = t
  · simp [ShiftFactor.mat, ShiftFactor.shift, hx, add_assoc]
  · simp [ShiftFactor.mat, ShiftFactor.shift, hx]

omit [DecidableEq τ] in
private theorem ShiftFactor.bd_nonneg {x : ShiftFactor τ ι} (hx : x.Y.IsHermitian) : 0 ≤ x.bd :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hx.neg.re_trace_exp_nonneg _)

omit [DecidableEq τ] in
private theorem listBound_nonneg {L : List (ShiftFactor τ ι)} (hL : Admissible L) :
    0 ≤ listBound L :=
  List.prod_nonneg fun b hb ↦ by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hb
    exact ShiftFactor.bd_nonneg (hL y hy).1

omit [DecidableEq τ] in
/-- Shifting the base generator by a Hermitian `V` raises the bound of a factor by at most
`e^{a ‖V‖}`. -/
private theorem ShiftFactor.bd_add_le {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    (B : Matrix ι ι ℂ) {Y : Matrix ι ι ℂ} (hY : Y.IsHermitian) {a : ℝ} (ha : 0 ≤ a) (t : τ) :
    (⟨B, Y + V, a, t⟩ : ShiftFactor τ ι).bd ≤
      Real.exp (‖V‖ * a) * (⟨B, Y, a, t⟩ : ShiftFactor τ ι).bd := by
  have htr := hY.neg.re_trace_exp_add_le hV.neg
  rw [norm_neg, ← neg_add] at htr
  have h0 : 0 ≤ (NormedSpace.exp (-(Y + V))).trace.re := (hY.add hV).neg.re_trace_exp_nonneg
  have h1 : 0 ≤ (NormedSpace.exp (-Y)).trace.re := hY.neg.re_trace_exp_nonneg
  calc ‖B‖ * (NormedSpace.exp (-(Y + V))).trace.re ^ a
      ≤ ‖B‖ * (Real.exp ‖V‖ * (NormedSpace.exp (-Y)).trace.re) ^ a :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h0 htr ha) (norm_nonneg _)
    _ = Real.exp (‖V‖ * a) * (⟨B, Y, a, t⟩ : ShiftFactor τ ι).bd := by
        rw [Real.mul_rpow (Real.exp_pos _).le h1, ← Real.exp_mul, ShiftFactor.bd]
        ring

/-- Shifting by a Hermitian `V` at the tag `t` raises the bound of a factor by at most
`e^{a ‖V‖}` if the factor carries the tag `t`, and leaves it unchanged otherwise. -/
private theorem ShiftFactor.bd_shift_le (t : τ) {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    {x : ShiftFactor τ ι} (hx : x.Y.IsHermitian) (ha : 0 ≤ x.a) :
    (x.shift t V).bd ≤ Real.exp (‖V‖ * x.sa t) * x.bd := by
  cases x with
  | mk B Y a tg =>
    by_cases htg : tg = t
    · simpa [ShiftFactor.shift, ShiftFactor.sa, htg] using ShiftFactor.bd_add_le hV B hx ha t
    · simp [ShiftFactor.shift, ShiftFactor.sa, htg]

private theorem listBound_map_shift_le (t : τ) {V : Matrix ι ι ℂ} (hV : V.IsHermitian)
    {L : List (ShiftFactor τ ι)} (hL : Admissible L) :
    listBound (L.map (ShiftFactor.shift t V)) ≤
      Real.exp (‖V‖ * shiftWeight t L) * listBound L := by
  induction L with
  | nil => simp [listBound, shiftWeight]
  | cons x L ih =>
    have hx := hL x (by simp)
    have hL' : Admissible L := fun y hy ↦ hL y (by simp [hy])
    rw [List.map_cons, listBound_cons, listBound_cons, shiftWeight_cons, mul_add, Real.exp_add]
    calc (x.shift t V).bd * listBound (L.map (ShiftFactor.shift t V))
        ≤ (Real.exp (‖V‖ * x.sa t) * x.bd) *
            (Real.exp (‖V‖ * shiftWeight t L) * listBound L) :=
          mul_le_mul (x.bd_shift_le t hV hx.1 hx.2) (ih hL')
            (listBound_nonneg (hL'.map_shift t hV))
            (mul_nonneg (Real.exp_pos _).le (ShiftFactor.bd_nonneg hx.1))
      _ = _ := by ring

omit [DecidableEq τ] in
/-- **Base case.** With no shift, the bound is the multi-factor Hölder inequality. -/
private theorem norm_trace_prodAt_zero_le {L : List (ShiftFactor τ ι)} (hL : Admissible L)
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

variable {S : Finset κ} {h : κ → Matrix ι ι ℂ} {home : κ → τ}

/-- The bound for all lists of factors, at the level of the index set `S`; the exponent of the
index `i` carries the total weight of the factors with the tag `home i`. -/
private def Claim (S : Finset κ) (h : κ → Matrix ι ι ℂ) (home : κ → τ) : Prop :=
  ∀ L : List (ShiftFactor τ ι), Admissible L → listWeight L = 1 →
    ‖(altSumT S h home (prodAt L)).trace‖ ≤
      (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (home i) L) - 1)) * listBound L

/-- **One Duhamel step.** Replacing the base generator `Y` of one factor with the tag `t` by
`Y + V` changes the alternating trace by at most
`∏_{i ∈ S} (e^{‖h_i‖ w_i} - 1) (e^{‖V‖ (W + a)} - e^{‖V‖ W})` times the bound, where `w_i` is the
weight of the factors with the tag `home i` and `W` the weight of the earlier factors with the
tag `t`, which already carry the shift `V`. -/
private theorem norm_trace_altSum_step_le (hS : Claim S h home) (t : τ) {V : Matrix ι ι ℂ}
    (hV : V.IsHermitian) (P : List (ShiftFactor τ ι)) (x : ShiftFactor τ ι)
    (R : List (ShiftFactor τ ι)) (hxs : x.tag = t) (hL : Admissible (P ++ x :: R))
    (hw : listWeight (P ++ x :: R) = 1) :
    ‖(altSumT S h home fun σ ↦ prodAt (P.map (ShiftFactor.shift t V) ++ x.shift t V :: R) σ -
        prodAt (P.map (ShiftFactor.shift t V) ++ x :: R) σ).trace‖ ≤
      (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (home i) (P ++ x :: R)) - 1)) *
        listBound (P ++ x :: R) *
          (Real.exp (‖V‖ * (shiftWeight t P + x.a)) - Real.exp (‖V‖ * shiftWeight t P)) := by
  set C := (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (home i) (P ++ x :: R)) - 1)) *
    listBound (P ++ x :: R) with hC
  set P' := P.map (ShiftFactor.shift t V)
  have hx := hL x (by simp)
  have hP : Admissible P := fun y hy ↦ hL y (by simp [hy])
  have hR : Admissible R := fun y hy ↦ hL y (by simp [hy])
  have hP' : Admissible P' := hP.map_shift t hV
  -- The interpolating list of factors.
  let Lu : ℝ → List (ShiftFactor τ ι) := fun u ↦
    P' ++ (⟨x.B, x.Y + V, x.a - u, t⟩ : ShiftFactor τ ι) ::
      (⟨V, x.Y, u, t⟩ : ShiftFactor τ ι) :: R
  -- The interpolating function and its derivative.
  let f : (τ → Matrix ι ι ℂ) → ℝ → Matrix ι ι ℂ := fun σ v ↦
    prodAt P' σ * x.B * NormedSpace.exp ((x.a - v) • -(x.Y + V + σ t)) *
      NormedSpace.exp (v • -(x.Y + σ t)) * prodAt R σ
  let G : ℝ → ℂ := fun v ↦ (altSumT S h home fun σ ↦ f σ v).trace
  let G' : ℝ → ℂ := fun v ↦ (altSumT S h home (prodAt (Lu v))).trace
  have hG : ∀ v, HasDerivAt G (G' v) v := by
    intro v
    have hsum : HasDerivAt (fun v ↦ altSumT S h home fun σ ↦ f σ v)
        (altSumT S h home (prodAt (Lu v))) v := by
      simp only [altSumT]
      refine HasDerivAt.fun_sum fun E _ ↦ HasDerivAt.fun_const_smul _ ?_
      set σ : τ → Matrix ι ι ℂ := ∑ i ∈ E, Pi.single (home i) (h i)
      convert hasDerivAt_mul_exp_mul_exp (prodAt P' σ * x.B) (prodAt R σ) (-(x.Y + σ t))
        (-(x.Y + V + σ t)) x.a v using 1
      simp only [Lu, prodAt_append, prodAt_cons, ShiftFactor.mat]
      rw [show -(x.Y + σ t) - -(x.Y + V + σ t) = V by abel]
      simp only [Matrix.mul_assoc]
    exact traceCLM.hasFDerivAt.comp_hasDerivAt v hsum
  -- Endpoint values.
  have hG0 : G 0 = (altSumT S h home (prodAt (P' ++ x.shift t V :: R))).trace := by
    simp only [G]
    congr 2
    funext σ
    simp only [f, prodAt_append, prodAt_cons, ShiftFactor.mat, ShiftFactor.shift, hxs,
      ite_true, sub_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_assoc]
  have hGa : G x.a = (altSumT S h home (prodAt (P' ++ x :: R))).trace := by
    simp only [G]
    congr 2
    funext σ
    simp only [f, prodAt_append, prodAt_cons, ShiftFactor.mat, hxs, sub_self,
      zero_smul, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_assoc]
  -- The bound on the derivative.
  have hderiv : ∀ v ∈ Set.Ico 0 x.a,
      ‖G' v‖ ≤ C * (‖V‖ * Real.exp (‖V‖ * (shiftWeight t P + x.a - v))) := by
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
    have hsw : ∀ t', shiftWeight t' (Lu v) = shiftWeight t' (P ++ x :: R) := by
      intro t'
      simp only [Lu, P', shiftWeight_append, shiftWeight_cons, shiftWeight_map_shift,
        ShiftFactor.sa, hxs]
      split_ifs <;> ring
    have ht : 0 ≤ (NormedSpace.exp (-x.Y)).trace.re := hx.1.neg.re_trace_exp_nonneg
    have hb : listBound (Lu v) ≤
        ‖V‖ * Real.exp (‖V‖ * (shiftWeight t P + x.a - v)) * listBound (P ++ x :: R) := by
      have h1 := listBound_map_shift_le t hV hP
      have h2 := ShiftFactor.bd_add_le hV x.B hx.1 (a := x.a - v) (by linarith) t
      have hRn := listBound_nonneg hR
      simp only [Lu, P', listBound_append, listBound_cons]
      calc listBound (P.map (ShiftFactor.shift t V)) *
            ((⟨x.B, x.Y + V, x.a - v, t⟩ : ShiftFactor τ ι).bd *
              ((⟨V, x.Y, v, t⟩ : ShiftFactor τ ι).bd * listBound R))
          ≤ (Real.exp (‖V‖ * shiftWeight t P) * listBound P) *
            ((Real.exp (‖V‖ * (x.a - v)) * (⟨x.B, x.Y, x.a - v, t⟩ : ShiftFactor τ ι).bd) *
              ((⟨V, x.Y, v, t⟩ : ShiftFactor τ ι).bd * listBound R)) := by
            have e3 : 0 ≤ (⟨V, x.Y, v, t⟩ : ShiftFactor τ ι).bd * listBound R :=
              mul_nonneg (ShiftFactor.bd_nonneg (x := ⟨V, x.Y, v, t⟩) hx.1) hRn
            exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 e3)
              (mul_nonneg
                (ShiftFactor.bd_nonneg (x := ⟨x.B, x.Y + V, x.a - v, t⟩) (hx.1.add hV)) e3)
              (mul_nonneg (Real.exp_pos _).le (listBound_nonneg hP))
        _ = ‖V‖ * Real.exp (‖V‖ * (shiftWeight t P + x.a - v)) *
              (listBound P * (x.bd * listBound R)) := by
            have hpow : (NormedSpace.exp (-x.Y)).trace.re ^ (x.a - v) *
                (NormedSpace.exp (-x.Y)).trace.re ^ v =
                  (NormedSpace.exp (-x.Y)).trace.re ^ x.a := by
              rw [← Real.rpow_add_of_nonneg ht (by linarith) hv0, sub_add_cancel]
            simp only [ShiftFactor.bd]
            rw [← hpow, show ‖V‖ * (shiftWeight t P + x.a - v) =
              ‖V‖ * shiftWeight t P + ‖V‖ * (x.a - v) by ring, Real.exp_add]
            ring
    calc ‖G' v‖ ≤ (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (home i) (Lu v)) - 1)) *
          listBound (Lu v) :=
          hS _ hadm hwu
      _ ≤ (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (home i) (P ++ x :: R)) - 1)) *
          (‖V‖ * Real.exp (‖V‖ * (shiftWeight t P + x.a - v)) * listBound (P ++ x :: R)) := by
          simp only [hsw]
          gcongr
          exact Finset.prod_nonneg fun i _ ↦ sub_nonneg.2
            (Real.one_le_exp (mul_nonneg (norm_nonneg _) (shiftWeight_nonneg _ hL)))
      _ = C * (‖V‖ * Real.exp (‖V‖ * (shiftWeight t P + x.a - v))) := by rw [hC]; ring
  -- The comparison function.
  have hB : ∀ v, HasDerivAt
      (fun v ↦ C *
        (Real.exp (‖V‖ * (shiftWeight t P + x.a)) -
          Real.exp (‖V‖ * (shiftWeight t P + x.a - v))))
      (C * (‖V‖ * Real.exp (‖V‖ * (shiftWeight t P + x.a - v)))) v := by
    intro v
    have := ((((hasDerivAt_id' v).const_sub (shiftWeight t P + x.a)).const_mul ‖V‖).exp.const_sub
      (Real.exp (‖V‖ * (shiftWeight t P + x.a)))).const_mul C
    convert this using 1
    ring
  have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (a := 0) (b := x.a)
    (f := fun v ↦ G v - G 0) (f' := G')
    (fun v _ ↦ ((hG v).sub_const (G 0)).continuousAt.continuousWithinAt)
    (fun v _ ↦ ((hG v).sub_const (G 0)).hasDerivWithinAt) (by simp) hB hderiv
    (Set.right_mem_Icc.2 hx.2)
  rw [altSumT_sub, trace_sub, ← hG0, ← hGa, norm_sub_rev]
  refine key.trans_eq ?_
  rw [add_sub_cancel_right]

/-- **One step, for any factor.** A factor that does not carry the tag `t` is unchanged by the
shift and contributes nothing. -/
private theorem norm_trace_altSum_step_le' (hS : Claim S h home) (t : τ) {V : Matrix ι ι ℂ}
    (hV : V.IsHermitian) (P : List (ShiftFactor τ ι)) (x : ShiftFactor τ ι)
    (R : List (ShiftFactor τ ι)) (hL : Admissible (P ++ x :: R))
    (hw : listWeight (P ++ x :: R) = 1) :
    ‖(altSumT S h home fun σ ↦ prodAt (P.map (ShiftFactor.shift t V) ++ x.shift t V :: R) σ -
        prodAt (P.map (ShiftFactor.shift t V) ++ x :: R) σ).trace‖ ≤
      (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (home i) (P ++ x :: R)) - 1)) *
        listBound (P ++ x :: R) *
          (Real.exp (‖V‖ * (shiftWeight t P + x.sa t)) - Real.exp (‖V‖ * shiftWeight t P)) := by
  by_cases hxs : x.tag = t
  · have hsa : x.sa t = x.a := by simp [ShiftFactor.sa, hxs]
    rw [hsa]
    exact norm_trace_altSum_step_le hS t hV P x R hxs hL hw
  · have hx : x.shift t V = x := by
      cases x
      simp_all [ShiftFactor.shift]
    have hsa : x.sa t = 0 := by simp [ShiftFactor.sa, hxs]
    simp [hx, hsa, altSumT]

/-- **Telescoping over the factors.** Shifting the base generators of the factors in `R` with
the tag `t` one at a time, after the factors in `P` have already been shifted. -/
private theorem norm_trace_altSum_shift_sub_le (hS : Claim S h home) (t : τ)
    {V : Matrix ι ι ℂ} (hV : V.IsHermitian) (R : List (ShiftFactor τ ι)) :
    ∀ P : List (ShiftFactor τ ι), Admissible (P ++ R) → listWeight (P ++ R) = 1 →
      ‖(altSumT S h home fun σ ↦
          prodAt (P.map (ShiftFactor.shift t V) ++ R.map (ShiftFactor.shift t V)) σ -
            prodAt (P.map (ShiftFactor.shift t V) ++ R) σ).trace‖ ≤
        (∏ i ∈ S, (Real.exp (‖h i‖ * shiftWeight (home i) (P ++ R)) - 1)) * listBound (P ++ R) *
          (Real.exp (‖V‖ * (shiftWeight t P + shiftWeight t R)) -
            Real.exp (‖V‖ * shiftWeight t P)) := by
  induction R with
  | nil => intro P _ _; simp [altSumT, shiftWeight]
  | cons x R ih =>
    intro P hL hw
    have happ : P ++ [x] ++ R = P ++ x :: R := by simp
    have h1 := ih (P ++ [x]) (happ ▸ hL) (happ ▸ hw)
    have h2 := norm_trace_altSum_step_le' hS t hV P x R hL hw
    have hwP : shiftWeight t (P ++ [x]) = shiftWeight t P + x.sa t := by simp [shiftWeight]
    rw [happ, hwP] at h1
    have hsplit : (fun σ ↦
        prodAt (P.map (ShiftFactor.shift t V) ++ (x :: R).map (ShiftFactor.shift t V)) σ -
          prodAt (P.map (ShiftFactor.shift t V) ++ x :: R) σ) = fun σ ↦
        (prodAt ((P ++ [x]).map (ShiftFactor.shift t V) ++ R.map (ShiftFactor.shift t V)) σ -
          prodAt ((P ++ [x]).map (ShiftFactor.shift t V) ++ R) σ) +
        (prodAt (P.map (ShiftFactor.shift t V) ++ x.shift t V :: R) σ -
          prodAt (P.map (ShiftFactor.shift t V) ++ x :: R) σ) := by
      funext σ
      simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc,
        List.singleton_append]
      abel
    rw [hsplit, altSumT_add, trace_add, shiftWeight_cons]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add h1 h2).trans_eq ?_
    rw [← add_assoc]
    ring

end Duhamel

section Induction

variable {h : κ → Matrix ι ι ℂ} {home : κ → τ}

private theorem claim_empty : Claim (∅ : Finset κ) h home := by
  intro L hL hw
  rw [altSumT_empty, Finset.prod_empty, one_mul]
  exact norm_trace_prodAt_zero_le hL hw

/-- **Induction step.** Adding an index `a` to `S` multiplies the bound by `e^{‖h_a‖ w} - 1`,
with `w` the weight of the factors with the tag `home a`. -/
private theorem claim_insert [DecidableEq κ] {S : Finset κ} {a : κ} (ha : a ∉ S)
    (hS : Claim S h home) (hV : (h a).IsHermitian) : Claim (insert a S) h home := by
  intro L hL hw
  have key := norm_trace_altSum_shift_sub_le hS (home a) hV L [] (by simpa using hL)
    (by simpa using hw)
  have h0 : shiftWeight (home a) ([] : List (ShiftFactor τ ι)) = 0 := by simp [shiftWeight]
  simp only [List.map_nil, List.nil_append] at key
  rw [h0, zero_add, mul_zero, Real.exp_zero] at key
  have hfun : (fun σ ↦ prodAt L (Pi.single (home a) (h a) + σ) - prodAt L σ) =
      fun σ ↦ prodAt (L.map (ShiftFactor.shift (home a) (h a))) σ - prodAt L σ := by
    funext σ
    rw [prodAt_add]
  rw [altSumT_insert ha, hfun, Finset.prod_insert ha]
  exact key.trans_eq (by ring)

private theorem claim_of_isHermitian (S : Finset κ)
    (hh : ∀ i ∈ S, (h i).IsHermitian) : Claim S h home := by
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
  have key := claim_of_isHermitian (home := fun _ ↦ ()) S hh [⟨O, Y, 1, ()⟩]
    (fun x hx ↦ by
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨hY, zero_le_one⟩)
    (by simp [listWeight])
  have e1 : altSumT S h (fun _ ↦ ()) (prodAt [⟨O, Y, 1, ()⟩]) = O * ∑ E ∈ S.powerset,
      (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (-(Y + ∑ i ∈ E, h i)) := by
    simp [altSumT, prodAt, ShiftFactor.mat, Finset.mul_sum, Finset.sum_apply]
  have e2 : listBound [(⟨O, Y, 1, ()⟩ : ShiftFactor Unit ι)] =
      ‖O‖ * (NormedSpace.exp (-Y)).trace.re := by
    simp [listBound, ShiftFactor.bd]
  have e3 : shiftWeight () [(⟨O, Y, 1, ()⟩ : ShiftFactor Unit ι)] = 1 := by
    simp [shiftWeight, ShiftFactor.sa]
  simp only [e1, e2, e3, mul_one] at key
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
  have key := claim_of_isHermitian (home := fun _ ↦ true) S hh
    [⟨O, X, p, false⟩, ⟨1, Y, q, true⟩, ⟨1, X, r, false⟩]
    (fun x hx ↦ by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      exacts [⟨hX, hp⟩, ⟨hY, hq⟩, ⟨hX, hr⟩])
    (by
      simp only [listWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      linarith)
  have e1 : altSumT S h (fun _ ↦ true)
      (prodAt [⟨O, X, p, false⟩, ⟨1, Y, q, true⟩, ⟨1, X, r, false⟩]) =
      O * NormedSpace.exp (p • -X) * (∑ E ∈ S.powerset,
        (-1 : ℂ) ^ (S.card - E.card) • NormedSpace.exp (q • -(Y + ∑ i ∈ E, h i))) *
          NormedSpace.exp (r • -X) := by
    simp [altSumT, prodAt, ShiftFactor.mat, Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc,
      Finset.sum_apply]
  have e2 : shiftWeight true [(⟨O, X, p, false⟩ : ShiftFactor Bool ι), ⟨1, Y, q, true⟩,
      ⟨1, X, r, false⟩] = q := by
    simp [shiftWeight, ShiftFactor.sa]
  have htX := hX.neg.re_trace_exp_nonneg
  have htY := hY.neg.re_trace_exp_nonneg
  have e3 : listBound [(⟨O, X, p, false⟩ : ShiftFactor Bool ι), ⟨1, Y, q, true⟩,
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
  simp only [e1, e2] at key
  refine key.trans ?_
  have hprod : ∏ i ∈ S, (Real.exp (‖h i‖ * q) - 1) = ∏ i ∈ S, (Real.exp (q * ‖h i‖) - 1) :=
    Finset.prod_congr rfl fun i _ ↦ by rw [mul_comm]
  rw [hprod]
  calc (∏ i ∈ S, (Real.exp (q * ‖h i‖) - 1)) *
        listBound [(⟨O, X, p, false⟩ : ShiftFactor Bool ι), ⟨1, Y, q, true⟩, ⟨1, X, r, false⟩]
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

/-- **Products of alternating sums.** Let `B_j` be matrices, `Y_j` Hermitian matrices and
`q_j ≥ 0` weights with `∑_j q_j = 1`, for `j < n`, and let `h_{j,i}`, `i ∈ S_j`, be Hermitian
matrices. Write `ρ_j = ∑_{E ⊆ S_j} (-1)^{|S_j| - |E|} e^{-q_j (Y_j + h_{j,E})}`. Then
`|Tr (B_0 ρ_0 B_1 ρ_1 ⋯ B_{n-1} ρ_{n-1})|
  ≤ ∏_j ‖B_j‖ ∏_{i ∈ S_j} (e^{q_j ‖h_{j,i}‖} - 1) (Tr e^{-Y_j})^{q_j}`,
with operator norms. For `S_j = ∅` the factor `ρ_j` is the thermal factor `e^{-q_j Y_j}`. With
`q_j = 1/n`, `Y_j = β H` for a thermal factor and `Y_j = β (H - H_{C_j} - H_{B(C_j)})`,
`h_{j,i} = β H_i` for a cluster part `ρ(β/n, C_j)`, this bounds the products of thermal factors
and cluster parts that make up the operator `ρ_m` of Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 1334–1341. If moreover `‖H_i‖ ≤ J` and `n_{C_j} + n_{B(C_j)} ≤ S n_{C_j}`
for every cluster, `Matrix.IsHermitian.re_trace_exp_add_le` turns the bound into
`‖O‖ ∏_j y^{n_{C_j}} Tr e^{-βH}` with `y = [exp(Jβ/n) - 1] exp(SJβ/n)`, the product running over
the cluster parts. -/
theorem norm_trace_list_prod_mul_sum_powerset_exp_le {n : ℕ} (B Y : Fin n → Matrix ι ι ℂ)
    (hY : ∀ j, (Y j).IsHermitian) (q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    (S : Fin n → Finset κ) (h : Fin n → κ → Matrix ι ι ℂ)
    (hh : ∀ j, ∀ i ∈ S j, (h j i).IsHermitian) :
    ‖(List.ofFn fun j ↦ B j * ∑ E ∈ (S j).powerset, (-1 : ℂ) ^ ((S j).card - E.card) •
        NormedSpace.exp (q j • -(Y j + ∑ i ∈ E, h j i))).prod.trace‖ ≤
      ∏ j, ‖B j‖ * (∏ i ∈ S j, (Real.exp (q j * ‖h j i‖) - 1)) *
        (NormedSpace.exp (-Y j)).trace.re ^ q j := by
  classical
  let L : List (ShiftFactor (Fin n) ι) := List.ofFn fun j ↦ ⟨B j, Y j, q j, j⟩
  have hL : Admissible L := by
    intro x hx
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact ⟨hY j, hq j⟩
  have hw : listWeight L = 1 := by
    simpa [L, listWeight, List.map_ofFn, Function.comp_def, List.sum_ofFn] using hq1
  have key := claim_of_isHermitian (h := fun x : Σ _ : Fin n, κ ↦ h x.1 x.2) (home := Sigma.fst)
    (Finset.univ.sigma S) (fun x hx ↦ hh x.1 x.2 (Finset.mem_sigma.1 hx).2) L hL hw
  have hP : prodAt L = fun σ ↦
      (List.ofFn fun j ↦ B j * NormedSpace.exp (q j • -(Y j + σ j))).prod := by
    funext σ
    simp [L, prodAt, List.map_ofFn, ShiftFactor.mat, Function.comp_def]
  have hfilter : ∀ j, (Finset.univ.sigma S).filter (fun x ↦ x.1 = j) =
      (S j).map (Function.Embedding.sigmaMk j) := by
    intro j
    ext ⟨j', i⟩
    simp only [Finset.mem_filter, Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.sigmaMk_apply]
    constructor
    · rintro ⟨hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i', hi', he⟩
      cases he
      exact ⟨hi', rfl⟩
  have e1 : altSumT (Finset.univ.sigma S) (fun x ↦ h x.1 x.2) Sigma.fst (prodAt L) =
      (List.ofFn fun j ↦ B j * ∑ E ∈ (S j).powerset, (-1 : ℂ) ^ ((S j).card - E.card) •
        NormedSpace.exp (q j • -(Y j + ∑ i ∈ E, h j i))).prod := by
    rw [hP, altSumT_ofFn_prod (fun x : Σ _ : Fin n, κ ↦ h x.1 x.2) Sigma.fst _
      fun j s ↦ B j * NormedSpace.exp (q j • -(Y j + s))]
    congr 2
    funext j
    rw [hfilter j, altSum_map]
    simp [altSum, Finset.mul_sum]
  have hsw : ∀ j, shiftWeight j L = q j := by
    intro j
    simp [L, shiftWeight, List.map_ofFn, Function.comp_def, List.sum_ofFn, ShiftFactor.sa]
  have hlb : listBound L = ∏ j, ‖B j‖ * (NormedSpace.exp (-Y j)).trace.re ^ q j := by
    simp [L, listBound, List.map_ofFn, Function.comp_def, List.prod_ofFn, ShiftFactor.bd]
  rw [e1] at key
  refine key.trans_eq ?_
  simp only [hsw, hlb, Finset.prod_sigma, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [Finset.prod_congr rfl fun i _ ↦ by rw [mul_comm (‖h j i‖)]]
  ring

/-- **Uniform form of products.** If moreover `‖h_{j,i}‖ ≤ J` for all `j` and `i ∈ S_j`, then
`|Tr (B_0 ρ_0 B_1 ρ_1 ⋯ B_{n-1} ρ_{n-1})|
  ≤ ∏_j ‖B_j‖ (e^{q_j J} - 1)^{|S_j|} (Tr e^{-Y_j})^{q_j}`. -/
theorem norm_trace_list_prod_mul_sum_powerset_exp_le_pow {n : ℕ} (B Y : Fin n → Matrix ι ι ℂ)
    (hY : ∀ j, (Y j).IsHermitian) (q : Fin n → ℝ) (hq : ∀ j, 0 ≤ q j) (hq1 : ∑ j, q j = 1)
    (S : Fin n → Finset κ) (h : Fin n → κ → Matrix ι ι ℂ)
    (hh : ∀ j, ∀ i ∈ S j, (h j i).IsHermitian) {J : ℝ} (hJ : ∀ j, ∀ i ∈ S j, ‖h j i‖ ≤ J) :
    ‖(List.ofFn fun j ↦ B j * ∑ E ∈ (S j).powerset, (-1 : ℂ) ^ ((S j).card - E.card) •
        NormedSpace.exp (q j • -(Y j + ∑ i ∈ E, h j i))).prod.trace‖ ≤
      ∏ j, ‖B j‖ * (Real.exp (q j * J) - 1) ^ (S j).card *
        (NormedSpace.exp (-Y j)).trace.re ^ q j := by
  refine (norm_trace_list_prod_mul_sum_powerset_exp_le B Y hY q hq hq1 S h hh).trans ?_
  refine Finset.prod_le_prod₀ (fun j _ ↦ ?_) fun j _ ↦ ?_
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ ↦ sub_nonneg.2
      (Real.one_le_exp (mul_nonneg (hq j) (norm_nonneg _)))))
      (Real.rpow_nonneg (hY j).neg.re_trace_exp_nonneg _)
  · have hprod : ∏ i ∈ S j, (Real.exp (q j * ‖h j i‖) - 1) ≤
        (Real.exp (q j * J) - 1) ^ (S j).card := by
      rw [← Finset.prod_const]
      exact Finset.prod_le_prod₀
        (fun i _ ↦ sub_nonneg.2 (Real.one_le_exp (mul_nonneg (hq j) (norm_nonneg _))))
        fun i hi ↦ by gcongr; exacts [hq j, hJ j i hi]
    have := Real.rpow_nonneg (hY j).neg.re_trace_exp_nonneg (q j)
    gcongr

end Matrix
