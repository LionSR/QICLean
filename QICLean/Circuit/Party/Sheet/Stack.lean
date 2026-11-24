/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Original.Frame
import QICLean.Circuit.Party.Original.Sequence
import QICLean.Circuit.Party.Sheet.Defs

/-!
# The memory of several sheets

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory holds several
sheets: the main sheet, the active auxiliary sheet of the current repainting, the frozen
auxiliary sheets of earlier repaintings, and the auxiliary copies of `Ω` not yet in use, each
held privately by the party that will initialize it. The reference vector at each stage is the
tensor product of the reference vectors of the sheets and of the idle copies, every factor of
norm at most one (`06-geometry.tex`, lines 39–41 and 658–667).

None of this depends on what a sheet is. This file works with an arbitrary type `κ` of sheets,
each sheet `F` carrying a system `sys F` and, where a reference vector is needed, a vector
`ref F` of that system. The sheets of a chain are one instance (`Sheet.system`).

The system of a list of sheets followed by an idle system `W` has at every party the basis of
every sheet followed by that of `W` (`stackSystem`), and the reference vector is the product of
the reference vectors of the sheets with a vector of the idle system (`stackVec`).

A bounded change acts on one sheet (a birth or a death) or on two adjacent sheets (an exchange).
Lifting the change to the whole stack, with the other sheets as spectators (`liftOne`,
`liftTwo`: the change framed by the other sheets, `OriginalCircuit.frame`, between relabellings),
changes neither its gates nor its participants, and its reference error on the stack is at most
its reference error on the sheets it acts on, when every reference vector has norm at most one
(`norm_op_liftOne_stackVec_sub_le`, `norm_op_liftTwo_stackVec_sub_le`). A permutation of the
sheets is a relabelling of the stack system (`exists_relabel_stackVec_of_perm`).

## Main definitions

* `QuantumCircuit.Party.stackSystem`, `QuantumCircuit.Party.stackVec`.
* `QuantumCircuit.Party.liftOne`, `QuantumCircuit.Party.liftTwo`.

## Main results

* `QuantumCircuit.Party.norm_stackVec`, `QuantumCircuit.Party.norm_stackVec_le`.
* `QuantumCircuit.Party.norm_op_liftOne_stackVec_sub_le`,
  `QuantumCircuit.Party.norm_op_liftTwo_stackVec_sub_le`.
* `QuantumCircuit.Party.exists_relabel_stackVec_of_perm`.
* `QuantumCircuit.Party.perm_map_cons`, `QuantumCircuit.Party.perm_map_update_cons`: moving the
  sheet of one index of a family to the front of the list of sheets.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 39–41 (the reference vectors as products of frame vectors) and
  658–667 (initialization and the reference vectors); encoded frames, `05-frames.tex`,
  lines 71–96.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit.Party

variable {κ : Type*} {P : Type} [DecidableEq P]

/-! ### The system of several sheets -/

section System

variable (sys : κ → P → Type)

/-- The system of a list of sheets, in order, followed by the idle system `W`: at every party
the product of the bases of the sheets and of `W`. -/
@[reducible] def stackSystem : List κ → (P → Type) → P → Type
  | [], W => W
  | F :: Fs, W => fun p ↦ sys F p × stackSystem Fs W p

/-- The bases of the system of several sheets are finite. -/
instance instFintypeStackSystem [∀ F p, Fintype (sys F p)] :
    (Fs : List κ) → (W : P → Type) → [∀ p, Fintype (W p)] → (p : P) →
      Fintype (stackSystem sys Fs W p)
  | [], _, i, _ => i _
  | F :: Fs, W, _, p =>
    letI := instFintypeStackSystem Fs W p
    inferInstanceAs (Fintype (sys F p × stackSystem sys Fs W p))

/-- The bases of the system of several sheets have decidable equality. -/
instance instDecidableEqStackSystem [∀ F p, DecidableEq (sys F p)] :
    (Fs : List κ) → (W : P → Type) → [∀ p, DecidableEq (W p)] → (p : P) →
      DecidableEq (stackSystem sys Fs W p)
  | [], _, i, _ => i _
  | F :: Fs, W, _, p =>
    letI := instDecidableEqStackSystem Fs W p
    inferInstanceAs (DecidableEq (sys F p × stackSystem sys Fs W p))

end System

/-! ### Changes of one sheet and of two adjacent sheets -/

section Lift

variable (sys : κ → P → Type) [∀ F p, Fintype (sys F p)] [∀ F p, DecidableEq (sys F p)]
  (W : P → Type) [∀ p, Fintype (W p)] [∀ p, DecidableEq (W p)]

/-- A change of the sheet `F` into `F'` on the whole stack `pre ++ F :: post`, with the other
sheets and the idle system `W` as spectators: on the empty prefix the change framed by the rest
of the stack, between two relabellings exchanging the factors; behind a sheet `G` the lift
framed by `G`. -/
def liftOne {F F' : κ} (post : List κ) (c : OriginalCircuit (sys F) (sys F')) :
    (pre : List κ) →
      OriginalCircuit (stackSystem sys (pre ++ F :: post) W)
        (stackSystem sys (pre ++ F' :: post) W)
  | [] =>
    (OriginalCircuit.relabel (X := fun p ↦ sys F p × stackSystem sys post W p)
        fun p ↦ Equiv.prodComm (stackSystem sys post W p) (sys F p)).comp
      ((c.frame (stackSystem sys post W)).comp
        (OriginalCircuit.relabel (Y := fun p ↦ sys F' p × stackSystem sys post W p)
          fun p ↦ Equiv.prodComm (sys F' p) (stackSystem sys post W p)))
  | G :: pre => (liftOne post c pre).frame (sys G)

/-- Lifting keeps the number of nonprivate gates. -/
@[simp] theorem nonprivateCount_liftOne {F F' : κ} (post : List κ)
    (c : OriginalCircuit (sys F) (sys F')) :
    (pre : List κ) → (liftOne sys W post c pre).nonprivateCount = c.nonprivateCount
  | [] => by
    change 0 + ((c.frame _).nonprivateCount + 0) = _
    rw [zero_add, add_zero, OriginalCircuit.nonprivateCount_frame]
  | G :: pre => (OriginalCircuit.nonprivateCount_frame (sys G) _).trans
    (nonprivateCount_liftOne post c pre)

/-- Lifting keeps every condition on the participants of the gates, such as the condition that
they lie in a set `S`. -/
theorem forall_participants_liftOne {Q : Finset P → Prop} {F F' : κ} (post : List κ)
    (c : OriginalCircuit (sys F) (sys F')) (hc : ∀ g, Q (c.participants g)) :
    (pre : List κ) → ∀ g, Q ((liftOne sys W post c pre).participants g)
  | [], g => by
    rcases g with g | g | g
    · exact g.elim
    · exact OriginalCircuit.forall_participants_frame _ c hc g
    · exact g.elim
  | G :: pre, g =>
    OriginalCircuit.forall_participants_frame (sys G) _
      (forall_participants_liftOne post c hc pre) g

/-- Lifting keeps the expansion bounds. -/
theorem isExpansionBounded_liftOne {F F' : κ} (post : List κ)
    (c : OriginalCircuit (sys F) (sys F')) {r : ℕ} {s : ℝ} (hc : c.IsExpansionBounded r s) :
    (pre : List κ) → (liftOne sys W post c pre).IsExpansionBounded r s
  | [] => ⟨OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero rfl r s,
      c.isExpansionBounded_frame _ hc,
      OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero rfl r s⟩
  | G :: pre => (liftOne sys W post c pre).isExpansionBounded_frame (sys G)
      (isExpansionBounded_liftOne post c hc pre)

/-- Lifting keeps the monomial bounds. -/
theorem isMonomialBounded_liftOne {F F' : κ} (post : List κ)
    (c : OriginalCircuit (sys F) (sys F')) {K : ℕ} (hc : c.IsMonomialBounded K) :
    (pre : List κ) → (liftOne sys W post c pre).IsMonomialBounded K
  | [] => ⟨OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero rfl K,
      c.isMonomialBounded_frame _ hc,
      OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero rfl K⟩
  | G :: pre => (liftOne sys W post c pre).isMonomialBounded_frame (sys G)
      (isMonomialBounded_liftOne post c hc pre)

/-- Lifting keeps the pair-source bounds. -/
theorem isSourceBounded_liftOne {F F' : κ} (post : List κ)
    (c : OriginalCircuit (sys F) (sys F')) {rs : ℕ} (hc : c.IsSourceBounded rs) :
    (pre : List κ) → (liftOne sys W post c pre).IsSourceBounded rs
  | [] => ⟨OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero rfl rs,
      c.isSourceBounded_frame _ hc,
      OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero rfl rs⟩
  | G :: pre => (liftOne sys W post c pre).isSourceBounded_frame (sys G)
      (isSourceBounded_liftOne post c hc pre)

/-- A change of the adjacent sheets `F₁, F₂` into `F₁', F₂'` on the whole stack
`pre ++ F₁ :: F₂ :: post`, with the other sheets and the idle system `W` as spectators. The
change acts on the product system of the two sheets. -/
def liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ)
    (c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p)) :
    (pre : List κ) →
      OriginalCircuit (stackSystem sys (pre ++ F₁ :: F₂ :: post) W)
        (stackSystem sys (pre ++ F₁' :: F₂' :: post) W)
  | [] =>
    (OriginalCircuit.relabel (X := fun p ↦ sys F₁ p × (sys F₂ p × stackSystem sys post W p))
        fun _ ↦ (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)).comp
      ((c.frame (stackSystem sys post W)).comp
        (OriginalCircuit.relabel
          (Y := fun p ↦ sys F₁' p × (sys F₂' p × stackSystem sys post W p))
          fun _ ↦ (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)))
  | G :: pre => (liftTwo post c pre).frame (sys G)

/-- Lifting keeps the number of nonprivate gates. -/
@[simp] theorem nonprivateCount_liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ)
    (c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p)) :
    (pre : List κ) → (liftTwo sys W post c pre).nonprivateCount = c.nonprivateCount
  | [] => by
    change 0 + ((c.frame _).nonprivateCount + 0) = _
    rw [zero_add, add_zero, OriginalCircuit.nonprivateCount_frame]
  | G :: pre => (OriginalCircuit.nonprivateCount_frame (sys G) _).trans
    (nonprivateCount_liftTwo post c pre)

/-- Lifting keeps every condition on the participants of the gates. -/
theorem forall_participants_liftTwo {Q : Finset P → Prop} {F₁ F₂ F₁' F₂' : κ} (post : List κ)
    (c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p))
    (hc : ∀ g, Q (c.participants g)) :
    (pre : List κ) → ∀ g, Q ((liftTwo sys W post c pre).participants g)
  | [], g => by
    rcases g with g | g | g
    · exact g.elim
    · exact OriginalCircuit.forall_participants_frame _ c hc g
    · exact g.elim
  | G :: pre, g =>
    OriginalCircuit.forall_participants_frame (sys G) _
      (forall_participants_liftTwo post c hc pre) g

/-- Lifting keeps the expansion bounds. -/
theorem isExpansionBounded_liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ)
    (c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p))
    {r : ℕ} {s : ℝ} (hc : c.IsExpansionBounded r s) :
    (pre : List κ) → (liftTwo sys W post c pre).IsExpansionBounded r s
  | [] => ⟨OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero rfl r s,
      c.isExpansionBounded_frame _ hc,
      OriginalCircuit.isExpansionBounded_of_nonprivateCount_eq_zero rfl r s⟩
  | G :: pre => (liftTwo sys W post c pre).isExpansionBounded_frame (sys G)
      (isExpansionBounded_liftTwo post c hc pre)

/-- Lifting keeps the monomial bounds. -/
theorem isMonomialBounded_liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ)
    (c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p))
    {K : ℕ} (hc : c.IsMonomialBounded K) :
    (pre : List κ) → (liftTwo sys W post c pre).IsMonomialBounded K
  | [] => ⟨OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero rfl K,
      c.isMonomialBounded_frame _ hc,
      OriginalCircuit.isMonomialBounded_of_nonprivateCount_eq_zero rfl K⟩
  | G :: pre => (liftTwo sys W post c pre).isMonomialBounded_frame (sys G)
      (isMonomialBounded_liftTwo post c hc pre)

/-- Lifting keeps the pair-source bounds. -/
theorem isSourceBounded_liftTwo {F₁ F₂ F₁' F₂' : κ} (post : List κ)
    (c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p))
    {rs : ℕ} (hc : c.IsSourceBounded rs) :
    (pre : List κ) → (liftTwo sys W post c pre).IsSourceBounded rs
  | [] => ⟨OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero rfl rs,
      c.isSourceBounded_frame _ hc,
      OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero rfl rs⟩
  | G :: pre => (liftTwo sys W post c pre).isSourceBounded_frame (sys G)
      (isSourceBounded_liftTwo post c hc pre)

end Lift

/-! ### Reference vectors -/

section Reference

variable [Fintype P] {sys : κ → P → Type} [∀ F p, Fintype (sys F p)]
  (ref : ∀ F, EuclideanSpace ℂ (Config (sys F)))

/-- The product of the reference vectors `ref F` of a list of sheets with a vector `ξ` of the
idle system. Source: `06-geometry.tex`, lines 39–41. -/
noncomputable def stackVec : (Fs : List κ) → {W : P → Type} → [∀ p, Fintype (W p)] →
    EuclideanSpace ℂ (Config W) → EuclideanSpace ℂ (Config (stackSystem sys Fs W))
  | [], _, _, ξ => ξ
  | F :: Fs, _, _, ξ => prodVec (ref F) (stackVec Fs ξ)

/-- The norm of the reference vector of several sheets is the product of the norms of the
reference vectors of the sheets and of the idle vector. -/
theorem norm_stackVec {W : P → Type} [∀ p, Fintype (W p)] (ξ : EuclideanSpace ℂ (Config W)) :
    (Fs : List κ) → ‖stackVec ref Fs ξ‖ = (Fs.map fun F ↦ ‖ref F‖).prod * ‖ξ‖
  | [] => (one_mul _).symm
  | F :: Fs => (norm_prodVec (ref F) (stackVec ref Fs ξ)).trans (by
    rw [norm_stackVec ξ Fs, List.map_cons, List.prod_cons, mul_assoc])

variable {ref}

/-- If every reference vector has norm at most one, the reference vector of several sheets has
norm at most that of the idle vector. -/
theorem norm_stackVec_le (href : ∀ F, ‖ref F‖ ≤ 1) {W : P → Type} [∀ p, Fintype (W p)]
    (ξ : EuclideanSpace ℂ (Config W)) : (Fs : List κ) → ‖stackVec ref Fs ξ‖ ≤ ‖ξ‖
  | [] => le_rfl
  | F :: Fs => (norm_prodVec (ref F) (stackVec ref Fs ξ)).trans_le
    ((mul_le_of_le_one_left (norm_nonneg _) (href F)).trans (norm_stackVec_le href ξ Fs))

variable [∀ F p, DecidableEq (sys F p)] (W : P → Type) [∀ p, Fintype (W p)]
  [∀ p, DecidableEq (W p)]

omit [∀ F p, Fintype (sys F p)] [∀ F p, DecidableEq (sys F p)] in
/-- The change of the first factor of a product system, framed by the second between two
relabellings, moves `x ⊗ ζ` by at most what the change moves `x`, when `‖ζ‖ ≤ 1`. -/
private theorem norm_op_frameRight_prodVec_sub_le {X Y : P → Type} [∀ p, Fintype (X p)]
    [∀ p, DecidableEq (X p)] [∀ p, Fintype (Y p)] [∀ p, DecidableEq (Y p)]
    (c : OriginalCircuit X Y) {ζ : EuclideanSpace ℂ (Config W)} (hζ : ‖ζ‖ ≤ 1)
    (x : EuclideanSpace ℂ (Config X)) (y : EuclideanSpace ℂ (Config Y)) :
    ‖toEuclideanLin ((OriginalCircuit.relabel (X := fun p ↦ X p × W p)
        fun p ↦ Equiv.prodComm (W p) (X p)).comp ((c.frame W).comp
          (OriginalCircuit.relabel (Y := fun p ↦ Y p × W p)
            fun p ↦ Equiv.prodComm (Y p) (W p)))).op (prodVec x ζ) - prodVec y ζ‖ ≤
      ‖toEuclideanLin c.op x - y‖ := by
  simp only [OriginalCircuit.op_comp, Matrix.toLpLin_mul_same, LinearMap.comp_apply,
    OriginalCircuit.toEuclideanLin_op_relabel_prodComm_prodVec,
    OriginalCircuit.toEuclideanLin_op_frame_prodVec, prodVec_sub_left, norm_prodVec]
  exact mul_le_of_le_one_right (norm_nonneg _) hζ

/-- **The reference error of a change of one sheet.** On the whole stack, the change takes the
reference vector within the error it makes on its own sheet.
Source: `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem norm_op_liftOne_stackVec_sub_le {F F' : κ} (post : List κ)
    (c : OriginalCircuit (sys F) (sys F')) (href : ∀ F, ‖ref F‖ ≤ 1)
    {ξ : EuclideanSpace ℂ (Config W)} (hξ : ‖ξ‖ ≤ 1) :
    (pre : List κ) →
      ‖toEuclideanLin (liftOne sys W post c pre).op (stackVec ref (pre ++ F :: post) ξ) -
          stackVec ref (pre ++ F' :: post) ξ‖ ≤ ‖toEuclideanLin c.op (ref F) - ref F'‖
  | [] => norm_op_frameRight_prodVec_sub_le _ c ((norm_stackVec_le href ξ post).trans hξ) _ _
  | G :: pre => (OriginalCircuit.norm_op_frame_prodVec_sub_le (sys G) _ (href G) _ _).trans
      (norm_op_liftOne_stackVec_sub_le post c href hξ pre)

omit [∀ F p, Fintype (sys F p)] [∀ F p, DecidableEq (sys F p)] in
/-- The change of two adjacent factors of a product system, framed by the third between two
relabellings, moves `x ⊗ (y ⊗ ζ)` by at most what the change moves `x ⊗ y`, when
`‖ζ‖ ≤ 1`. -/
private theorem norm_op_frameRight₂_prodVec_sub_le {X₁ X₂ Y₁ Y₂ : P → Type}
    [∀ p, Fintype (X₁ p)] [∀ p, DecidableEq (X₁ p)] [∀ p, Fintype (X₂ p)]
    [∀ p, DecidableEq (X₂ p)] [∀ p, Fintype (Y₁ p)] [∀ p, DecidableEq (Y₁ p)]
    [∀ p, Fintype (Y₂ p)] [∀ p, DecidableEq (Y₂ p)]
    (c : OriginalCircuit (fun p ↦ X₁ p × X₂ p) (fun p ↦ Y₁ p × Y₂ p))
    {ζ : EuclideanSpace ℂ (Config W)} (hζ : ‖ζ‖ ≤ 1) (x₁ : EuclideanSpace ℂ (Config X₁))
    (x₂ : EuclideanSpace ℂ (Config X₂)) (y₁ : EuclideanSpace ℂ (Config Y₁))
    (y₂ : EuclideanSpace ℂ (Config Y₂)) :
    ‖toEuclideanLin ((OriginalCircuit.relabel (X := fun p ↦ X₁ p × (X₂ p × W p))
        fun _ ↦ (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)).comp ((c.frame W).comp
          (OriginalCircuit.relabel (Y := fun p ↦ Y₁ p × (Y₂ p × W p))
            fun _ ↦ (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)))).op
        (prodVec x₁ (prodVec x₂ ζ)) - prodVec y₁ (prodVec y₂ ζ)‖ ≤
      ‖toEuclideanLin c.op (prodVec x₁ x₂) - prodVec y₁ y₂‖ := by
  have hin : toEuclideanLin (OriginalCircuit.relabel (X := fun p ↦ X₁ p × (X₂ p × W p))
      fun _ ↦ (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)).op
        (prodVec x₁ (prodVec x₂ ζ)) = prodVec ζ (prodVec x₁ x₂) := by
    ext z
    rw [OriginalCircuit.toEuclideanLin_op_relabel]
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
    ring
  have hout : ∀ v : EuclideanSpace ℂ (Config fun p ↦ Y₁ p × Y₂ p),
      toEuclideanLin (OriginalCircuit.relabel (Y := fun p ↦ Y₁ p × (Y₂ p × W p))
        fun _ ↦ (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)).op (prodVec ζ v) =
        LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (Equiv.piCongrRight fun p ↦ (Equiv.prodAssoc (Y₁ p) (Y₂ p) (W p))) (prodVec v ζ) := by
    intro v
    ext z
    rw [OriginalCircuit.toEuclideanLin_op_relabel]
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, mul_comm]
  have hy : prodVec y₁ (prodVec y₂ ζ) = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (Equiv.piCongrRight fun p ↦ (Equiv.prodAssoc (Y₁ p) (Y₂ p) (W p)))
        (prodVec (prodVec y₁ y₂) ζ) := by
    ext z
    simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, mul_assoc]
  simp only [OriginalCircuit.op_comp, Matrix.toLpLin_mul_same, LinearMap.comp_apply]
  rw [hin, OriginalCircuit.toEuclideanLin_op_frame_prodVec, hout, hy, ← map_sub,
    LinearIsometryEquiv.norm_map, prodVec_sub_left, norm_prodVec]
  exact mul_le_of_le_one_right (norm_nonneg _) hζ

/-- **The reference error of a change of two adjacent sheets.** On the whole stack, the change
takes the reference vector within the error it makes on its two sheets.
Source: `06-geometry.tex`, lines 39–41 and 574–583. -/
theorem norm_op_liftTwo_stackVec_sub_le {F₁ F₂ F₁' F₂' : κ} (post : List κ)
    (c : OriginalCircuit (fun p ↦ sys F₁ p × sys F₂ p) (fun p ↦ sys F₁' p × sys F₂' p))
    (href : ∀ F, ‖ref F‖ ≤ 1) {ξ : EuclideanSpace ℂ (Config W)} (hξ : ‖ξ‖ ≤ 1) :
    (pre : List κ) →
      ‖toEuclideanLin (liftTwo sys W post c pre).op
          (stackVec ref (pre ++ F₁ :: F₂ :: post) ξ) -
          stackVec ref (pre ++ F₁' :: F₂' :: post) ξ‖ ≤
        ‖toEuclideanLin c.op (prodVec (ref F₁) (ref F₂)) - prodVec (ref F₁') (ref F₂')‖
  | [] => norm_op_frameRight₂_prodVec_sub_le _ c ((norm_stackVec_le href ξ post).trans hξ) _ _
      _ _
  | G :: pre => (OriginalCircuit.norm_op_frame_prodVec_sub_le (sys G) _ (href G) _ _).trans
      (norm_op_liftTwo_stackVec_sub_le post c href hξ pre)

/-! ### Reordering the sheets -/

/-- **Reordering the sheets is a relabelling.** A permutation of a list of sheets is implemented
on the stack system, followed by an idle system, by one relabelling of the bases of every party,
which carries the reference vector of the sheets in the first order to the reference vector in
the second. Source: `06-geometry.tex`, lines 662–667, and allowed monomials,
`04-compression.tex`, lines 32–35. -/
theorem exists_relabel_stackVec_of_perm (ref : ∀ F, EuclideanSpace ℂ (Config (sys F)))
    {Fs Fs' : List κ} (h : Fs.Perm Fs') :
    ∃ e : ∀ p, stackSystem sys Fs' W p ≃ stackSystem sys Fs W p, ∀ ξ,
      toEuclideanLin (OriginalCircuit.relabel e).op (stackVec ref Fs ξ) = stackVec ref Fs' ξ := by
  induction h with
  | nil => exact ⟨fun _ ↦ Equiv.refl _, fun ξ ↦ by
      ext z
      rw [OriginalCircuit.toEuclideanLin_op_relabel]
      simp [LinearIsometryEquiv.piLpCongrLeft_apply]⟩
  | cons F _ ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨fun p ↦ (Equiv.refl _).prodCongr (e p), fun ξ ↦ ?_⟩
    have h := congrArg (fun v ↦ prodVec (ref F) v) (he ξ)
    refine Eq.trans ?_ h
    ext z
    simp only [OriginalCircuit.toEuclideanLin_op_relabel, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply]
    simp only [stackVec, prodVec_apply, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply]
    rfl
  | swap F G Fs =>
    refine ⟨fun p ↦ (Equiv.prodAssoc _ _ _).symm.trans
      (((Equiv.prodComm _ _).prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)),
      fun ξ ↦ ?_⟩
    ext z
    rw [OriginalCircuit.toEuclideanLin_op_relabel]
    simp [stackVec, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]
    ring
  | trans _ _ ih ih' =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨e', he'⟩ := ih'
    refine ⟨fun p ↦ (e' p).trans (e p), fun ξ ↦ ?_⟩
    rw [← he', ← he]
    ext z
    simp only [OriginalCircuit.toEuclideanLin_op_relabel, LinearIsometryEquiv.piLpCongrLeft_apply,
      Equiv.piCongrLeft'_apply]
    rfl

end Reference

/-! ### Moving one sheet of an indexed family to the front -/

section Reordering

variable {X : Type*} [DecidableEq X]

/-- Updating the auxiliary value at a selected index in a duplicate-free list lets that value
move before the main value, leaving the other auxiliary values in their original order. -/
theorem perm_map_update_cons {Y : Type*} (M : Y) {l : List X} (hl : l.Nodup) {x : X} (hx : x ∈ l)
    (A : X → Y) (F : Y) :
    (M :: l.map (Function.update A x F)).Perm (F :: M :: (l.erase x).map A) := by
  have hp := (List.perm_cons_erase hx).map (Function.update A x F)
  rw [List.map_cons, Function.update_self] at hp
  have he : (l.erase x).map (Function.update A x F) = (l.erase x).map A :=
    List.map_congr_left fun y hy ↦ Function.update_of_ne
      (fun h ↦ (hl.mem_erase_iff.1 (h ▸ hy)).1 rfl) _ _
  rw [he] at hp
  exact (hp.cons M).trans (List.Perm.swap _ _ _)

/-- A selected auxiliary value may move before the main value, leaving the values of the index
list with the selected index erased once. -/
theorem perm_map_cons {Y : Type*} (M : Y) {l : List X} {x : X} (hx : x ∈ l) (A : X → Y) :
    (M :: l.map A).Perm (A x :: M :: (l.erase x).map A) := by
  have hp := (List.perm_cons_erase hx).map A
  rw [List.map_cons] at hp
  exact (hp.cons M).trans (List.Perm.swap _ _ _)

end Reordering

end QuantumCircuit.Party
