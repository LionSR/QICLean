/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ExteriorPieri
import QICLean.Representation.WeylDimension

/-!
# The Weyl character formula for the multiplicity spaces

For a label `λ` of `S_k` with at most `q` rows, let `χ_λ(y) = Tr(E^λ_{00} diag(y)^{⊗k})` be the
character of the multiplicity space `V_λ ⊆ (ℂ^q)^{⊗k}`, so that
`Tr(π^λ diag(y)^{⊗k}) = d_λ χ_λ(y)`. The area-law paper (*A two-dimensional area law from a
global spectral gap*, `05-replicas.tex`, proof of Lemma 6.2, lines 336–364) uses the Weyl
character formula

`Δ(y) χ_λ(y) = det [y_i ^ {l_j}]`, `l_j = λ_j + q - 1 - j`,

with `Δ(y) = det [y_i ^ {q - 1 - j}]` the Vandermonde determinant ("the Weyl denominator cancels
`Δ(s^t)` in the density").

## Method

The idempotent `e^μ_{00} ⊗ A_r` of `ℂ[S_{m+r}]` has trace `χ_μ(y) e_r(y)` against
`diag(y)^{⊗(m+r)}`, and decomposes over the labels `λ` of `S_{m+r}` with multiplicities at
most one, supported on vertical strips `λ = μ + 1_S` (`ExteriorPieri.lean`). Comparing
dimensions with the Weyl dimension formula and the dimension form of the alternant Pieri rule
shows that every vertical strip occurs: `χ_μ e_r = ∑_{λ/μ vertical r-strip} χ_λ`. The
alternants satisfy the same rule, with the summands outside the vertical strips vanishing.
Removing the first column of `λ` and inducting on `k`, then downward on the number of rows,
gives the formula.

The proofs are written from the standard theory; no Lean source was adapted.

## Main declarations

* `TensorPower.glChar q λ y` — the character `χ_λ(y)`.
* `TensorPower.trace_mul_tensorPow_eq_sum` — `Tr(ρ(a) diag(y)^{⊗k}) = ∑_λ tr(W_λ(a)) χ_λ(y)`.
* `TensorPower.glChar_mul_elemSymm` — **the vertical-strip Pieri rule for the characters**.
* `TensorPower.alternant_mul_glChar` — **the Weyl character formula**.
* `TensorPower.trace_labelProj_mul_tensorPow` — `Tr(π^λ diag(y)^{⊗k}) = d_λ χ_λ(y)`.
-/

open Finset Matrix PermutationRepresentation MonoidAlgebra

namespace TensorPower

variable {q m r k : ℕ}

/-- The character `χ_λ(y) = Tr(E^λ_{00} diag(y)^{⊗k})` of the multiplicity space `V_λ`. -/
noncomputable def glChar (q : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) (y : Fin q → ℂ) : ℂ :=
  (unitOp q l * tensorPow (diagonal y)).trace

/-- A label has at most `q` rows. -/
def HasRows (q : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) : Prop :=
  ∀ a, q ≤ a → labelPart l a = 0

theorem multSpace_ne_bot_iff_hasRows (l : IrrepLabel (Equiv.Perm (Fin k))) :
    multSpace q l ≠ ⊥ ↔ HasRows q l := by
  rw [multSpace_ne_bot_iff]
  constructor
  · intro h a ha
    simp only [labelPart]
    split_ifs with hak
    · exact h ⟨a, hak⟩ ha
    · rfl
  · intro h i hi
    have := h i hi
    simpa [labelPart, i.2] using this

theorem unitOp_eq_zero_of_not_hasRows {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : ¬HasRows q l) : unitOp q l = 0 := by
  rw [← multSpace_ne_bot_iff_hasRows, not_not, multSpace, LinearMap.range_eq_bot] at hl
  exact toLin'.injective (by rw [hl, map_zero])

theorem glChar_eq_zero_of_not_hasRows {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : ¬HasRows q l) (y : Fin q → ℂ) : glChar q l y = 0 := by
  rw [glChar, unitOp_eq_zero_of_not_hasRows hl, Matrix.zero_mul, trace_zero]

theorem glChar_one (l : IrrepLabel (Equiv.Perm (Fin k))) :
    glChar q l 1 = multiplicity (copyPerm (Fin q) k) l := by
  rw [glChar, show diagonal (1 : Fin q → ℂ) = 1 from diagonal_one, tensorPow_one,
    Matrix.mul_one]
  exact trace_eq_finrank_range_of_mul_self (matrixUnitOp_mul_matrixUnitOp_self _ l _ _ _)

theorem multiplicity_pos {l : IrrepLabel (Equiv.Perm (Fin k))} (hl : HasRows q l) :
    0 < multiplicity (copyPerm (Fin q) k) l := by
  rw [← multSpace_ne_bot_iff_hasRows] at hl
  exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hl)

theorem multiplicity_eq_zero_of_not_hasRows {l : IrrepLabel (Equiv.Perm (Fin k))}
    (hl : ¬HasRows q l) : multiplicity (copyPerm (Fin q) k) l = 0 := by
  have h := glChar_one (q := q) l
  rw [glChar_eq_zero_of_not_hasRows hl] at h
  exact_mod_cast h.symm

/-! ### Traces against diagonal tensor powers -/

/-- `Tr(π^λ M) = d_λ Tr(E^λ_{00} M)` for `M` commuting with the copy permutations. -/
theorem trace_mul_labelProj_eq {M : Matrix (Fin k → Fin q) (Fin k → Fin q) ℂ}
    (hM : ∀ g, Commute (permOp (copyPerm (Fin q) k) g) M) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (M * labelProj (copyPerm (Fin q) k) l).trace = l.dim * (M * unitOp q l).trace := by
  rw [← sum_matrixUnitOp_diag, mul_sum, trace_sum,
    sum_congr rfl fun i _ => by rw [trace_mul_matrixUnitOp _ hM, ite_eq_left rfl]]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem commute_permOp_tensorPow (y : Fin q → ℂ) (g : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (Fin q) k) g) (tensorPow (diagonal y)) :=
  commute_permOp_copyPerm_tensorPow _ g

/-- `Tr(π^λ diag(y)^{⊗k}) = d_λ χ_λ(y)`. -/
theorem trace_labelProj_mul_tensorPow (l : IrrepLabel (Equiv.Perm (Fin k))) (y : Fin q → ℂ) :
    (labelProj (copyPerm (Fin q) k) l * tensorPow (diagonal y)).trace = l.dim * glChar q l y := by
  rw [trace_mul_comm, trace_mul_labelProj_eq (commute_permOp_tensorPow y), glChar,
    trace_mul_comm]

/-- **Label decomposition of a trace**: `Tr(ρ(a) diag(y)^{⊗k}) = ∑_λ tr(W_λ(a)) χ_λ(y)`. -/
theorem trace_mul_tensorPow_eq_sum (a : MonoidAlgebra ℂ (Equiv.Perm (Fin k)))
    (y : Fin q → ℂ) :
    (groupAlgebraRep (copyPerm (Fin q) k) a * tensorPow (diagonal y)).trace =
      ∑ l, (IrrepLabel.block l a).trace * glChar q l y := by
  set M := tensorPow (k := k) (diagonal y)
  have hM := commute_permOp_tensorPow (k := k) y
  have hsum : (groupAlgebraRep (copyPerm (Fin q) k) a * M).trace =
      ∑ l, (M * (groupAlgebraRep (copyPerm (Fin q) k) a *
        labelProj (copyPerm (Fin q) k) l)).trace := by
    rw [trace_mul_comm, ← trace_sum, ← mul_sum, ← mul_sum, sum_labelProj, Matrix.mul_one]
  rw [hsum]
  refine sum_congr rfl fun l _ => ?_
  have h := trace_mul_groupAlgebraRep_mul_labelProj (copyPerm (Fin q) k) hM a l
  rw [trace_mul_labelProj_eq hM] at h
  have hd : (l.dim : ℂ) ≠ 0 := by exact_mod_cast l.dim_pos.ne'
  rw [glChar, trace_mul_comm (unitOp q l)]
  apply mul_left_cancel₀ hd
  rw [h]
  ring

/-- The trace of `e^μ_{00} ⊗ A_r` against `diag(y)^{⊗(m + r)}` is `χ_μ(y) e_r(y)`. -/
theorem trace_pieriElem_mul_tensorPow (μ : IrrepLabel (Equiv.Perm (Fin m))) (y : Fin q → ℂ) :
    (groupAlgebraRep (copyPerm (Fin q) (m + r)) (pieriElem μ r) *
        tensorPow (diagonal y)).trace = glChar q μ y * Partition.elemSymm r y := by
  rw [groupAlgebraRep_pieriElem, tensorPow_eq_splitOp, splitOp_mul, trace_splitOp,
    trace_antisym_mul_tensorPow]
  rfl

/-! ### Partitions with at most `q` rows -/

theorem hasRows_iff_part {l l' : IrrepLabel (Equiv.Perm (Fin k))} (hl : HasRows q l)
    (hl' : HasRows q l') (h : part q l = part q l') : l = l' := by
  refine labelPart_injective (funext fun a => ?_)
  by_cases ha : a < q
  · exact congrFun h ⟨a, ha⟩
  · rw [hl a (not_lt.mp ha), hl' a (not_lt.mp ha)]

theorem antitone_part (l : IrrepLabel (Equiv.Perm (Fin k))) : Antitone (part q l) :=
  fun _ _ hab => labelPart_antitone l hab

theorem sum_part {l : IrrepLabel (Equiv.Perm (Fin k))} (hl : HasRows q l) :
    ∑ a, part q l a = k :=
  sum_labelPart_of_rows l hl

/-- Every partition of `k` with at most `q` rows is the partition of a label. -/
theorem exists_part_eq {p : Fin q → ℕ} (hp : Antitone p) (hsum : ∑ a, p a = k) :
    ∃ l : IrrepLabel (Equiv.Perm (Fin k)), HasRows q l ∧ part q l = p := by
  classical
  -- rows beyond `k` vanish
  have hzero : ∀ a : Fin q, k ≤ (a : ℕ) → p a = 0 := by
    intro a ha
    by_contra hne
    have hle : ∀ b : Fin q, b ≤ a → 1 ≤ p b := fun b hb => (Nat.one_le_iff_ne_zero.mpr hne).trans
      (hp hb)
    have : (a : ℕ) + 1 ≤ ∑ b, p b := by
      calc (a : ℕ) + 1 = ∑ b ∈ univ.filter (fun b : Fin q => b ≤ a), 1 := by
            rw [sum_const, smul_eq_mul, mul_one]
            rw [show univ.filter (fun b : Fin q => b ≤ a) = Iic a by ext; simp]
            simp
        _ ≤ ∑ b ∈ univ.filter (fun b : Fin q => b ≤ a), p b :=
            sum_le_sum fun b hb => hle b (mem_filter.mp hb).2
        _ ≤ ∑ b, p b := sum_le_sum_of_subset (filter_subset _ _)
    omega
  set μ : Fin k → ℕ := fun i => if h : (i : ℕ) < q then p ⟨i, h⟩ else 0
  have hμ : μ ∈ Partition.padded k k := by
    rw [Partition.mem_padded]
    refine ⟨fun i j hij => ?_, ?_⟩
    · simp only [μ]
      split_ifs with hj hi hi
      · exact hp (Fin.mk_le_mk.mpr hij)
      · omega
      · exact Nat.zero_le _
      · exact le_rfl
    · refine Eq.trans ?_ hsum
      calc ∑ i : Fin k, μ i = ∑ i ∈ range k, (if h : i < q then p ⟨i, h⟩ else 0) :=
            Fin.sum_univ_eq_sum_range (fun i => if h : i < q then p ⟨i, h⟩ else 0) k
        _ = ∑ i ∈ range q, (if h : i < q then p ⟨i, h⟩ else 0) := by
            rcases le_total k q with hkq | hqk
            · refine sum_subset (range_subset_range.mpr hkq) fun i hi hik => ?_
              simp only [mem_range, not_lt] at hi hik
              rw [dite_eq_left hi]
              exact hzero ⟨i, hi⟩ hik
            · exact (sum_subset (range_subset_range.mpr hqk) fun i _ hiq => by
                simp only [mem_range, not_lt] at hiq
                rw [dite_eq_right (not_lt.mpr hiq)]).symm
        _ = ∑ a : Fin q, p a :=
            (Fin.sum_univ_eq_sum_range (fun i => if h : i < q then p ⟨i, h⟩ else 0) q).symm.trans
              (sum_congr rfl fun a _ => by simp)
  obtain ⟨l, hl⟩ := exists_labelShape_eq hμ
  have hpart : ∀ a : ℕ, labelPart l a = if h : a < q then p ⟨a, h⟩ else 0 := by
    intro a
    simp only [labelPart, hl, μ]
    split_ifs with hak haq haq
    · rfl
    · rfl
    · exact (hzero ⟨a, haq⟩ (not_lt.mp hak)).symm
    · rfl
  refine ⟨l, fun a ha => by rw [hpart, dite_eq_right (not_lt.mpr ha)], funext fun a => ?_⟩
  simp only [part, hpart, a.2, dite_eq_left]

/-! ### Vertical strips -/

/-- Adding a set of boxes to distinct rows of a partition either gives a partition or makes two
shifted parts coincide. -/
theorem exists_shiftedPart_eq_of_not_antitone {p : Fin q → ℕ} (hp : Antitone p)
    {S : Finset (Fin q)} (h : ¬Antitone (p + Partition.indic S)) :
    ∃ a b, a ≠ b ∧ Partition.shiftedPart (p + Partition.indic S) a =
      Partition.shiftedPart (p + Partition.indic S) b := by
  cases q with
  | zero => exact absurd (fun a => a.elim0) h
  | succ n =>
    rw [Fin.antitone_iff_succ_le] at h
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hle := hp (Fin.castSucc_le_succ i)
    simp only [Pi.add_apply, Partition.indic] at hi
    refine ⟨Fin.castSucc i, i.succ, Fin.castSucc_lt_succ.ne, ?_⟩
    simp only [Partition.shiftedPart, Pi.add_apply, Partition.indic, Fin.val_castSucc,
      Fin.val_succ]
    split_ifs at hi ⊢ with h1 h2 h2 <;> omega

theorem weylFormula_eq_zero_of_shiftedPart_eq {p : Fin q → ℕ} {a b : Fin q} (hab : a ≠ b)
    (h : Partition.shiftedPart p a = Partition.shiftedPart p b) : Partition.weylFormula p = 0 := by
  rw [Partition.weylFormula]
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact prod_eq_zero (i := (a, b)) (by simp [Partition.rowPairs, hlt]) (by simp [h])
  · exact prod_eq_zero (i := (b, a)) (by simp [Partition.rowPairs, hlt]) (by simp [h])

open scoped Classical in
/-- The labels `λ = μ + 1_S` of `S_{m + r}` with at most `q` rows, `|S| = r`. -/
noncomputable def pieriSet (q : ℕ) (μ : IrrepLabel (Equiv.Perm (Fin m))) (r : ℕ) :
    Finset (IrrepLabel (Equiv.Perm (Fin (m + r)))) :=
  univ.filter fun l => HasRows q l ∧
    ∃ S ∈ powersetCard r (univ : Finset (Fin q)), part q l = part q μ + Partition.indic S

theorem mem_pieriSet {μ : IrrepLabel (Equiv.Perm (Fin m))}
    {l : IrrepLabel (Equiv.Perm (Fin (m + r)))} :
    l ∈ pieriSet q μ r ↔ HasRows q l ∧
      ∃ S ∈ powersetCard r (univ : Finset (Fin q)), part q l = part q μ + Partition.indic S := by
  classical
  simp [pieriSet]

/-- Sums over the vertical strips are sums over the sets of added rows, when the summand
vanishes at non-partitions. -/
theorem sum_pieriSet {M : Type*} [AddCommMonoid M] {μ : IrrepLabel (Equiv.Perm (Fin m))}
    (hμ : HasRows q μ) (F : (Fin q → ℕ) → M)
    (hF : ∀ S : Finset (Fin q), ¬Antitone (part q μ + Partition.indic S) →
      F (part q μ + Partition.indic S) = 0) :
    ∑ l ∈ pieriSet q μ r, F (part q l) =
      ∑ S ∈ powersetCard r (univ : Finset (Fin q)), F (part q μ + Partition.indic S) := by
  classical
  rw [← sum_filter_of_ne (s := powersetCard r univ)
    (p := fun S => Antitone (part q μ + Partition.indic S))
    (fun S _ hne => by by_contra h; exact hne (hF S h))]
  refine sum_bij (fun l hl => ((mem_pieriSet.mp hl).2).choose) ?_ ?_ ?_ ?_
  · intro l hl
    obtain ⟨hS, hpart⟩ := ((mem_pieriSet.mp hl).2).choose_spec
    refine mem_filter.mpr ⟨hS, ?_⟩
    rw [← hpart]
    exact antitone_part l
  · intro l hl l' hl' heq
    obtain ⟨-, hpart⟩ := ((mem_pieriSet.mp hl).2).choose_spec
    obtain ⟨-, hpart'⟩ := ((mem_pieriSet.mp hl').2).choose_spec
    refine hasRows_iff_part (mem_pieriSet.mp hl).1 (mem_pieriSet.mp hl').1 ?_
    rw [hpart, hpart', heq]
  · intro S hS
    obtain ⟨hS1, hanti⟩ := mem_filter.mp hS
    have hsum : ∑ a, (part q μ + Partition.indic S) a = m + r := by
      simp only [Pi.add_apply]
      rw [sum_add_distrib, sum_part hμ]
      simp [Partition.indic, (mem_powersetCard.mp hS1).2]
    obtain ⟨l, hl, hpart⟩ := exists_part_eq hanti hsum
    have hmem : l ∈ pieriSet q μ r := mem_pieriSet.mpr ⟨hl, S, hS1, hpart⟩
    refine ⟨l, hmem, ?_⟩
    obtain ⟨-, hpart'⟩ := ((mem_pieriSet.mp hmem).2).choose_spec
    have h2 : Partition.indic S = Partition.indic ((mem_pieriSet.mp hmem).2).choose :=
      funext fun a => by
        have h1 := congrFun hpart a
        have h3 := congrFun hpart' a
        simp only [Pi.add_apply] at h1 h3
        omega
    exact (Partition.indic_injective h2).symm
  · intro l hl
    obtain ⟨-, hpart⟩ := ((mem_pieriSet.mp hl).2).choose_spec
    exact congrArg F hpart

/-! ### The vertical-strip Pieri rule for the characters -/

theorem pieriRank_hasRows_eq_zero_or_mem {μ : IrrepLabel (Equiv.Perm (Fin m))}
    (hμ : HasRows q μ) {l : IrrepLabel (Equiv.Perm (Fin (m + r)))} (hl : HasRows q l) :
    pieriRank μ l ≤ 1 ∧ (pieriRank μ l ≠ 0 → l ∈ pieriSet q μ r) := by
  classical
  have hμ' := (multSpace_ne_bot_iff_hasRows (q := q) μ).mpr hμ
  have hl' := (multSpace_ne_bot_iff_hasRows (q := q) l).mpr hl
  obtain ⟨hle, hex⟩ := pieriRank_le_one_and μ l hμ' hl'
  refine ⟨hle, fun hne => ?_⟩
  obtain ⟨z, hz, hsh⟩ := hex hne
  refine mem_pieriSet.mpr ⟨hl, univ.image z, ?_, ?_⟩
  · exact mem_powersetCard.mpr ⟨subset_univ _, by rw [card_image_of_injective _ hz]; simp⟩
  · funext a
    have h := congrFun hsh a
    rw [shape_eq_labelPart, shape_eq_labelPart] at h
    simp only [Pi.add_apply] at h ⊢
    have hw : weight z a = ((Partition.indic (univ.image z) a : ℕ) : ℤ) := by
      simp only [Partition.indic]
      simp only [weight, mem_image, mem_univ, true_and]
      split_ifs with ha
      · obtain ⟨j, hj⟩ := ha
        rw [sum_eq_single j]
        · simp [hj]
        · intro i _ hi
          rw [ite_eq_right]
          intro h'
          exact hi (hz (h'.trans hj.symm))
        · simp
      · push Not at ha
        exact sum_eq_zero fun i _ => by simp [ha i]
    rw [hw] at h
    exact_mod_cast h

/-- The total multiplicity of `V_μ ⊗ Λ^r` equals the sum over the vertical strips. -/
theorem sum_pieriSet_multiplicity {μ : IrrepLabel (Equiv.Perm (Fin m))} (hμ : HasRows q μ) :
    (∑ l ∈ pieriSet q μ r, (multiplicity (copyPerm (Fin q) (m + r)) l : ℝ)) =
      (q.choose r : ℝ) * multiplicity (copyPerm (Fin q) m) μ := by
  rw [sum_congr rfl fun l hl => multiplicity_eq_weylFormula l (mem_pieriSet.mp hl).1,
    multiplicity_eq_weylFormula μ hμ]
  rw [sum_pieriSet hμ Partition.weylFormula fun S hS => by
    obtain ⟨a, b, hab, h⟩ := exists_shiftedPart_eq_of_not_antitone (antitone_part μ) hS
    exact weylFormula_eq_zero_of_shiftedPart_eq hab h]
  exact Partition.sum_weylFormula_add_indic _ r

/-- Every vertical strip occurs in `V_μ ⊗ Λ^r` exactly once. -/
theorem pieriRank_eq_one {μ : IrrepLabel (Equiv.Perm (Fin m))} (hμ : HasRows q μ)
    {l : IrrepLabel (Equiv.Perm (Fin (m + r)))} (hl : l ∈ pieriSet q μ r) : pieriRank μ l = 1 := by
  classical
  -- the total multiplicity, from the trace at `y = 1`
  have htot : (∑ l', (pieriRank μ l' : ℝ) * multiplicity (copyPerm (Fin q) (m + r)) l') =
      (q.choose r : ℝ) * multiplicity (copyPerm (Fin q) m) μ := by
    have h1 := trace_pieriElem_mul_tensorPow (q := q) (r := r) μ 1
    rw [trace_mul_tensorPow_eq_sum] at h1
    simp only [trace_block_pieriElem, glChar_one] at h1
    have h2 : Partition.elemSymm r (1 : Fin q → ℂ) = q.choose r := by
      simp [Partition.elemSymm, card_powersetCard]
    rw [h2] at h1
    have := congrArg Complex.re h1
    simp only [Complex.re_sum] at this
    convert this using 1
    · refine sum_congr rfl fun l' _ => ?_
      norm_cast
    · norm_cast
      rw [mul_comm]
  -- terms outside the vertical strips vanish, and those inside are at most `m_λ`
  have hout : ∀ l' ∉ pieriSet q μ r,
      (pieriRank μ l' : ℝ) * multiplicity (copyPerm (Fin q) (m + r)) l' = 0 := by
    intro l' hl'
    by_cases hr : HasRows q l'
    · have := pieriRank_hasRows_eq_zero_or_mem hμ hr
      have h0 : pieriRank μ l' = 0 := by
        by_contra hne; exact hl' (this.2 hne)
      simp [h0]
    · simp [multiplicity_eq_zero_of_not_hasRows hr]
  have hsplit := sum_add_sum_compl (pieriSet q μ r)
    (fun l' => (pieriRank μ l' : ℝ) * multiplicity (copyPerm (Fin q) (m + r)) l')
  rw [sum_eq_zero fun l' hl' => hout l' (mem_compl.mp hl'), add_zero, htot,
    ← sum_pieriSet_multiplicity hμ] at hsplit
  have hle : ∀ l' ∈ pieriSet q μ r, (pieriRank μ l' : ℝ) *
      multiplicity (copyPerm (Fin q) (m + r)) l' ≤ multiplicity (copyPerm (Fin q) (m + r)) l' := by
    intro l' hl'
    have h1 := (pieriRank_hasRows_eq_zero_or_mem hμ (mem_pieriSet.mp hl').1).1
    have h1' : (pieriRank μ l' : ℝ) ≤ 1 := by exact_mod_cast h1
    nlinarith [(multiplicity (copyPerm (Fin q) (m + r)) l').cast_nonneg (α := ℝ)]
  have heq := (sum_eq_sum_iff_of_le hle).mp hsplit l hl
  have hpos : (0 : ℝ) < multiplicity (copyPerm (Fin q) (m + r)) l := by
    exact_mod_cast multiplicity_pos (mem_pieriSet.mp hl).1
  have : (pieriRank μ l : ℝ) = 1 := by
    have := mul_right_cancel₀ hpos.ne' (heq.trans (one_mul _).symm)
    exact this
  exact_mod_cast this

/-- **The vertical-strip Pieri rule for the characters**: `χ_μ e_r = ∑_{λ/μ vertical} χ_λ`. -/
theorem glChar_mul_elemSymm {μ : IrrepLabel (Equiv.Perm (Fin m))} (hμ : HasRows q μ)
    (y : Fin q → ℂ) :
    glChar q μ y * Partition.elemSymm r y = ∑ l ∈ pieriSet q μ r, glChar q l y := by
  classical
  rw [← trace_pieriElem_mul_tensorPow, trace_mul_tensorPow_eq_sum]
  simp only [trace_block_pieriElem]
  rw [← sum_add_sum_compl (pieriSet q μ r)]
  rw [sum_eq_zero (s := (pieriSet q μ r)ᶜ), add_zero]
  · exact sum_congr rfl fun l hl => by rw [pieriRank_eq_one hμ hl]; simp
  · intro l hl
    by_cases hr : HasRows q l
    · have h0 : pieriRank μ l = 0 := by
        by_contra hne
        exact (mem_compl.mp hl) ((pieriRank_hasRows_eq_zero_or_mem hμ hr).2 hne)
      simp [h0]
    · simp [glChar_eq_zero_of_not_hasRows hr]


/-! ### The Weyl character formula -/

/-- The rows of a label that are not empty, among the first `q`. -/
noncomputable def rowSet (q : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) : Finset (Fin q) :=
  univ.filter fun a => part q l a ≠ 0

theorem mem_rowSet {l : IrrepLabel (Equiv.Perm (Fin k))} {a : Fin q} :
    a ∈ rowSet q l ↔ part q l a ≠ 0 := by
  simp [rowSet]

theorem mem_rowSet_of_le {l : IrrepLabel (Equiv.Perm (Fin k))} {a b : Fin q} (hab : b ≤ a)
    (ha : a ∈ rowSet q l) : b ∈ rowSet q l := by
  rw [mem_rowSet] at ha ⊢
  have := antitone_part (q := q) l hab
  omega

/-- A vertical strip over the label with its first column removed, other than the label itself,
has more rows. -/
theorem card_rowSet_lt {l l' : IrrepLabel (Equiv.Perm (Fin (m + r)))} {p : Fin q → ℕ}
    (hl : part q l = p + Partition.indic (rowSet q l)) {S : Finset (Fin q)}
    (hS : S.card = (rowSet q l).card) (hl' : part q l' = p + Partition.indic S)
    (hne : S ≠ rowSet q l) : (rowSet q l).card < (rowSet q l').card := by
  classical
  obtain ⟨a, haS, ha⟩ : ∃ a ∈ S, a ∉ rowSet q l := by
    by_contra h
    push Not at h
    exact hne (eq_of_subset_of_card_le h hS.ge)
  have hpa : p a = 0 := by
    have := congrFun hl a
    simp only [Pi.add_apply, Partition.indic, ha, ite_false, add_zero] at this
    rw [← this]
    simpa [mem_rowSet] using ha
  have hal' : a ∈ rowSet q l' := by
    rw [mem_rowSet, hl']
    simp [Partition.indic, haS, hpa]
  have hsub : rowSet q l ⊆ rowSet q l' := by
    intro b hb
    refine mem_rowSet_of_le ?_ hal'
    by_contra hlt
    exact ha (mem_rowSet_of_le (not_le.mp hlt).le hb)
  exact card_lt_card ⟨hsub, fun h => ha (h hal')⟩

theorem glChar_of_part_eq_zero {l : IrrepLabel (Equiv.Perm (Fin k))} (hl : HasRows q l)
    (h0 : part q l = 0) (y : Fin q → ℂ) : glChar q l y = 1 := by
  have hk : k = 0 := by rw [← sum_part hl, h0]; simp
  subst hk
  have hT : tensorPow (k := 0) (diagonal y) = 1 := by
    ext x x'
    rw [tensorPow_apply, Subsingleton.elim x x']
    simp
  have hm := multiplicity_eq_weylFormula l hl
  rw [show part q l = 0 from h0, Partition.weylFormula_zero] at hm
  rw [glChar, hT, Matrix.mul_one,
    trace_eq_finrank_range_of_mul_self (matrixUnitOp_mul_matrixUnitOp_self _ l _ _ _)]
  exact_mod_cast hm

/-- **The Weyl character formula** (`05-replicas.tex`, proof of Lemma 6.2, lines 336–364): for
a label `λ` with at most `q` rows, `Δ(y) χ_λ(y) = det [y_i ^ {l_j}]` with `l_j = λ_j + q - 1 - j`
and `Δ(y) = det [y_i ^ {q - 1 - j}]`. -/
theorem alternant_mul_glChar : ∀ {k : ℕ} {l : IrrepLabel (Equiv.Perm (Fin k))},
    HasRows q l → ∀ y : Fin q → ℂ,
      Partition.alternant (Partition.shiftedPart (0 : Fin q → ℕ)) y * glChar q l y =
        Partition.alternant (Partition.shiftedPart (part q l)) y := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IHk =>
  suffices H : ∀ n, ∀ l : IrrepLabel (Equiv.Perm (Fin k)), HasRows q l →
      q - (rowSet q l).card = n → ∀ y : Fin q → ℂ,
        Partition.alternant (Partition.shiftedPart (0 : Fin q → ℕ)) y * glChar q l y =
          Partition.alternant (Partition.shiftedPart (part q l)) y from
    fun {l} hl => H _ l hl rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IHn =>
  intro l hl hn y
  -- the empty partition
  by_cases h0 : rowSet q l = ∅
  · have hp : part q l = 0 := funext fun a => by
      by_contra h
      have : a ∈ rowSet q l := mem_rowSet.mpr h
      rw [h0] at this
      exact absurd this (Finset.notMem_empty a)
    rw [glChar_of_part_eq_zero hl hp, mul_one, hp]
  -- remove the first column
  set S0 := rowSet q l with hS0
  set p : Fin q → ℕ := fun a => part q l a - Partition.indic S0 a with hpdef
  have hlp : part q l = p + Partition.indic S0 := by
    funext a
    simp only [Pi.add_apply, p, Partition.indic]
    split_ifs with ha
    · have := mem_rowSet.mp ha; omega
    · omega
  have hpanti : Antitone p := by
    intro a b hab
    have h1 := antitone_part (q := q) l hab
    by_cases hb : b ∈ S0
    · have ha : a ∈ S0 := mem_rowSet_of_le hab hb
      simp only [p, Partition.indic, ha, hb, ite_true]
      omega
    · have : part q l b = 0 := by
        by_contra h; exact hb (mem_rowSet.mpr h)
      simp only [p, Partition.indic, hb, ite_false]
      omega
  generalize hℓ : S0.card = ℓ
  have hℓpos : 1 ≤ ℓ := by
    rw [← hℓ, Nat.one_le_iff_ne_zero]
    exact fun h => h0 (card_eq_zero.mp h)
  have hpsum : ∑ a, p a + ℓ = k := by
    rw [← hℓ, ← sum_part hl, hlp]
    simp [sum_add_distrib, Partition.indic]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + ℓ := ⟨∑ a, p a, hpsum.symm⟩
  obtain ⟨μ, hμ, hμp⟩ := exists_part_eq (k := m) hpanti (by omega)
  have hIHμ := IHk m (by omega) hμ y
  have hcard : (rowSet q l).card = ℓ := hℓ
  -- the Pieri rules
  have hP := glChar_mul_elemSymm (r := ℓ) hμ y
  have hA := Partition.alternant_mul_elemSymm (Partition.shiftedPart (part q μ)) ℓ y
  simp only [← Partition.shiftedPart_add_indic] at hA
  have hsumA := sum_pieriSet (r := ℓ) hμ
    (fun p' => Partition.alternant (Partition.shiftedPart p') y) fun S hS => by
      obtain ⟨a, b, hab, h⟩ := exists_shiftedPart_eq_of_not_antitone (antitone_part μ) hS
      exact Partition.alternant_eq_zero_of_eq y hab h
  have hfinal : ∑ l' ∈ pieriSet q μ ℓ,
      Partition.alternant (Partition.shiftedPart (0 : Fin q → ℕ)) y * glChar q l' y =
      ∑ l' ∈ pieriSet q μ ℓ, Partition.alternant (Partition.shiftedPart (part q l')) y := by
    rw [← mul_sum, ← hP, ← mul_assoc, hIHμ, hA]
    exact hsumA.symm
  -- `λ` is one of the vertical strips
  have hlmem : l ∈ pieriSet q μ ℓ :=
    mem_pieriSet.mpr ⟨hl, S0, mem_powersetCard.mpr ⟨subset_univ _, hℓ⟩, by rw [hμp]; exact hlp⟩
  have hothers : ∀ l' ∈ (pieriSet q μ ℓ).erase l,
      Partition.alternant (Partition.shiftedPart (0 : Fin q → ℕ)) y * glChar q l' y =
        Partition.alternant (Partition.shiftedPart (part q l')) y := by
    intro l' hl'
    obtain ⟨hne, hl'm⟩ := mem_erase.mp hl'
    obtain ⟨hl'r, S, hS, hl'p⟩ := mem_pieriSet.mp hl'm
    have hSne : S ≠ S0 := by
      rintro rfl
      exact hne (hasRows_iff_part hl'r hl (by rw [hl'p, hμp, hlp]))
    have hlt := card_rowSet_lt (p := p) hlp (by rw [(mem_powersetCard.mp hS).2, hℓ])
      (by rw [hl'p, hμp]) hSne
    rw [hcard] at hlt
    have hle : (rowSet q l').card ≤ q := by
      simpa using card_le_univ (rowSet q l')
    exact IHn _ (by omega) l' hl'r rfl y
  have hsplit := add_sum_erase (pieriSet q μ ℓ)
    (fun l' => Partition.alternant (Partition.shiftedPart (0 : Fin q → ℕ)) y * glChar q l' y)
    hlmem
  have hsplit' := add_sum_erase (pieriSet q μ ℓ)
    (fun l' => Partition.alternant (Partition.shiftedPart (part q l')) y) hlmem
  rw [sum_congr rfl hothers] at hsplit
  rw [← hsplit, ← hsplit'] at hfinal
  exact add_right_cancel hfinal

end TensorPower
