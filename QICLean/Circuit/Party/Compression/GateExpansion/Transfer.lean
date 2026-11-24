/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Party.Monomial.WeightedGate

/-!
# A transferred register as a sum of local operations

A register with basis `α` is transferred from the sender `p` to the receiver `q`: the input
system `X` has the basis `α × Z p` at `p` (read through `eX`), the output system `Y` has the
basis `α × Z q` at `q` (read through `eY`), and both agree with the system `Z` elsewhere. The
transfer is the identity on the register and on `Z`, a permutation matrix (`transferMatrix`). In
every orthonormal basis `b` of `ℂ^α` it is the sum `∑ i, |b i⟩_q ⟨b i|_p` of a local bra at the
sender followed by a local ket at the receiver (`Word.sum_op_transferTerm`; the manuscript
writes it in the standard basis, `∑ a |a⟩⟨a|`). Every term is an allowed word without pair
sources, and the expansion as a weighted list of monomials (`WeightedGate.transferTerms`) has
one term of coefficient one for each basis vector, so a message of dimension `|α|` multiplies
the number of monomials and the coefficient sum by `|α|` and adds no pair effect.

The configurations of a system with a factor `α` split off at one party are pairs of a
configuration of `α` and one of the remaining system (`ManyBody.factorConfigEquiv`); the local
preparation and the local bra (`Word.localPrepare`, `Word.localDiscard`) are the preparation and
the effect along this equivalence.

## Main definitions

* `QuantumCircuit.Party.transferMatrix`.
* `QuantumCircuit.Party.Word.transferTerm`.
* `QuantumCircuit.Party.WeightedGate.transferTerms`.

## Main results

* `QuantumCircuit.Party.Word.op_transferTerm`.
* `QuantumCircuit.Party.Word.sum_op_transferTerm`.
* `QuantumCircuit.Party.WeightedGate.gate_toGate_transferTerms`, `length_transferTerms`,
  `sum_norm_coeff_transferTerms`, `isAllowed_effectCount_transferTerms`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, `04-compression.tex`,
  lines 32–45 and 143–147.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

variable {P : Type} [DecidableEq P]

/-! ### The transfer -/

/-- **The identity transfer** of a register with basis `α` from the sender `p` to the receiver
`q`: the permutation matrix that keeps the configuration of the register and of the remaining
system `Z`. Source: `04-compression.tex`, lines 35–41. -/
def transferMatrix [Fintype P] {X Y Z : P → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (p q : P) {α : Type} (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p)
    (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q) : Matrix (Config Y) (Config X) ℂ :=
  ((factorConfigEquiv q hY eY).trans
    (factorConfigEquiv p (fun s hs ↦ (hZ s hs).symm) eX).symm).toPEquiv.toMatrix

/-- The transfer is a contraction. -/
theorem norm_transferMatrix_le [Fintype P] {X Y Z : P → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)] (p q : P) {α : Type} (hZ : ∀ s ≠ p, Z s = X s)
    (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q) :
    ‖transferMatrix p q hZ eX hY eY‖ ≤ 1 :=
  l2_opNorm_toMatrix_toPEquiv_le _

namespace Word

variable {X Y Z : P → Type}

variable [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)]
  [∀ s, DecidableEq (Z s)] [Fintype P]

/-- One term of a transfer in the orthonormal basis `b` of the register: the bra `⟨b i|` at the
sender `p`, then the ket `|b i⟩` at the receiver `q`. Source: `04-compression.tex`,
lines 35–41. -/
def transferTerm (p q : P) {α : Type} [Fintype α] (hZ : ∀ s ≠ p, Z s = X s)
    (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) (i : ι) : Word X Y :=
  PartyCircuit.comp (localDiscard p hZ (b i) eX) (localPrepare q hY (b i) eY)

omit [Fintype P] in
/-- Every term of a transfer is composed of allowed local operations. Source:
`04-compression.tex`, lines 39–42. -/
theorem isAllowed_transferTerm [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (p q : P)
    {α : Type} [Fintype α] (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p)
    (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) (i : ι) :
    (transferTerm p q hZ eX hY eY b i).IsAllowed :=
  ⟨isAllowed_localDiscard p hZ _ eX (b.norm_eq_one i),
    isAllowed_localPrepare q hY _ eY (b.norm_eq_one i)⟩

omit [Fintype P] in
/-- A transfer has no pair source. -/
@[simp] theorem sources_transferTerm (p q : P) {α : Type} [Fintype α] (hZ : ∀ s ≠ p, Z s = X s)
    (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q) {ι : Type}
    [Fintype ι] (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) (i : ι) :
    (transferTerm p q hZ eX hY eY b i).sources = [] :=
  rfl

/-- The operator of one term: the bra `⟨b i|` on the factor of the sender, then the ket `|b i⟩`
on the factor of the receiver, the configuration of `Z` kept. Source:
`04-compression.tex`, lines 35–41. -/
theorem op_transferTerm [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (p q : P) {α : Type}
    [Fintype α] (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
    (eY : Y q ≃ α × Z q) {ι : Type} [Fintype ι] (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α))
    (i : ι) :
    (transferTerm p q hZ eX hY eY b i).op =
      prepMatrix (factorConfigEquiv q hY eY) (b i) *
        (effectMatrix (b i) (Config Z)).submatrix id
          (factorConfigEquiv p (fun s hs ↦ (hZ s hs).symm) eX) := by
  rw [transferTerm, Word.op_comp, op_localPrepare_eq_prepMatrix, op_localDiscard]

/-- The coordinates of an orthonormal basis of `ℂ^α` satisfy `∑ i, b i a * conj (b i a') = δ`. -/
private theorem sum_apply_mul_star_apply {α ι : Type} [Fintype α] [DecidableEq α] [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) (a a' : α) :
    ∑ i, b i a * star (b i a') = if a = a' then 1 else 0 := by
  have h := b.sum_inner_mul_inner (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single a' 1)
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one,
    one_mul] at h
  rw [show (EuclideanSpace.single a (1 : ℂ)).ofLp = Pi.single a 1 from rfl, Pi.single_apply,
    apply_ite (starRingEnd ℂ), map_one, map_zero] at h
  exact h.trans (if_congr eq_comm rfl rfl)

/-- **The terms of a transfer add up to the identity transfer**, in every orthonormal basis of the
register and on every input, a register of dimension zero included. Source:
`04-compression.tex`, lines 35–41. -/
theorem sum_op_transferTerm [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (p q : P) {α : Type}
    [Fintype α] (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p)
    (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q) {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) :
    ∑ i, (transferTerm p q hZ eX hY eY b i).op = transferMatrix p q hZ eX hY eY := by
  classical
  ext y x
  rw [Matrix.sum_apply]
  simp only [op_transferTerm, prepMatrix_mul_apply, submatrix_apply, effectMatrix_apply, id]
  simp only [transferMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Equiv.trans_apply]
  set FY := factorConfigEquiv q hY eY
  set FX := factorConfigEquiv p (fun s hs ↦ (hZ s hs).symm) eX
  rw [if_congr (Equiv.symm_apply_eq FX) rfl rfl]
  by_cases h2 : (FY y).2 = (FX x).2
  · simp only [h2, ite_true]
    rw [sum_apply_mul_star_apply b (FY y).1 (FX x).1]
    exact if_congr ⟨fun h ↦ Prod.ext h h2, fun h ↦ congrArg Prod.fst h⟩ rfl rfl
  · simp only [h2, ite_false, mul_zero, Finset.sum_const_zero]
    exact (ite_eq_right fun h ↦ h2 (congrArg Prod.snd h)).symm

end Word

/-! ### The weighted list of a transfer -/

namespace WeightedGate

variable {D : Finset P} {X Y Z : ↥D → Type} [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]
  [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] {α : Type} [Fintype α] {ι : Type} [Fintype ι]

/-- The expansion of a transfer in the orthonormal basis `b` of the register as a weighted list of
monomials: one monomial of coefficient one for each basis vector. Source:
`04-compression.tex`, lines 35–43. -/
def transferTerms (p q : ↥D) (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p)
    (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) : List (ℂ × Monomial D X Y) :=
  (Finset.univ : Finset ι).toList.map fun i ↦
    (1, (Word.transferTerm p q hZ eX hY eY b i).toChain)

/-- The expansion of a transfer has as many terms as the dimension of the register; a register of
dimension zero gives the empty expansion. Source: `04-compression.tex`,
lines 35–43. -/
theorem length_transferTerms (p q : ↥D) (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p)
    (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) :
    (transferTerms p q hZ eX hY eY b).length = Fintype.card ι := by
  simp only [transferTerms, List.length_map, Finset.length_toList, Finset.card_univ]

/-- Every monomial of a transfer is allowed and has no pair effect. Source:
`04-compression.tex`, lines 39–42. -/
theorem isAllowed_effectCount_transferTerms [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
    (p q : ↥D) (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
    (eY : Y q ≃ α × Z q) (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α))
    {t : ℂ × Monomial D X Y} (ht : t ∈ transferTerms p q hZ eX hY eY b) :
    t.2.IsAllowed chainEv ChainGate.IsAllowed ∧ t.2.effectCount = 0 := by
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ht
  refine ⟨(Word.isAllowed_transferTerm p q hZ eX hY eY b i).toChain, ?_⟩
  rw [Monomial.effectCount, Monomial.effects_toChain, List.length_nil]

/-- The coefficient sum of a transfer is the dimension of the register. Source:
`04-compression.tex`, lines 35–43. -/
theorem sum_norm_coeff_transferTerms (p q : ↥D) (hZ : ∀ s ≠ p, Z s = X s)
    (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s) (eY : Y q ≃ α × Z q)
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) :
    ((transferTerms p q hZ eX hY eY b).map fun t ↦ ‖t.1‖).sum = (Fintype.card ι : ℝ) := by
  simp [transferTerms, List.map_map, Function.comp_def]

/-- **The expansion of a transfer is the identity transfer.** Source:
`04-compression.tex`, lines 35–43. -/
theorem gate_toGate_transferTerms [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] (p q : ↥D)
    (hZ : ∀ s ≠ p, Z s = X s) (eX : X p ≃ α × Z p) (hY : ∀ s ≠ q, Y s = Z s)
    (eY : Y q ≃ α × Z q) (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ α)) :
    GateExpansion.gate (toGate (transferTerms p q hZ eX hY eY b)) =
      transferMatrix p q hZ eX hY eY := by
  rw [gate_toGate, transferTerms, List.map_map, ← Word.sum_op_transferTerm p q hZ eX hY eY b]
  simp only [Function.comp_def, one_smul, Word.op_toChain, Finset.sum_map_toList]

end WeightedGate

end QuantumCircuit.Party
