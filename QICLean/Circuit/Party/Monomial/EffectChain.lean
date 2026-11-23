/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.TensorProduct.CyclicInsertionMatrix
import QICLean.Analysis.Norm.MatrixKroneckerContraction

/-!
# Pair effects and the replaced monomial

A monomial of a gate expansion is a composition of contractions, preparations of normalized
pair vectors, and contractions by normalized pair bras (pair effects).  Grouping the steps
between consecutive effects, a monomial with `n` effects is a chain
`F_n E_n F_{n-1} ⋯ E_1 F_0`, where each `F_i` is a contraction and each `E_i = ⟨η_i| ⊗ 1`
contracts a pair register with a normalized pair vector `η_i` and leaves a spectator register
untouched.  We formalize such chains as `EffectChain`.

Registers are finite basis types and operators are matrices: a piece `F_i` from the register
`X` to the register `Z` is a complex matrix `Matrix Z X ℂ` (rows indexed by the output basis),
normed by the operator norm of `ℂ^X → ℂ^Z` (`Matrix.Norms.L2Operator`), and vectors are
elements of `EuclideanSpace ℂ X`.  An effect acts on a register `(α × β) × S`: the pair
register `α × β` is the first factor and the spectator register `S` the second.  This is the
convention for the operators of circuits, `Matrix (Config Y) (Config X) ℂ` with the operator
norm.

Each effect occurrence receives its own output stack of `m` pair registers, the basis type
`Fin m → α × β`.  In the replaced monomial the effect `⟨η|` is replaced by the cyclic
insertion `T_m`, and the stack stays idle afterwards.  The ideal replacement appends the fixed
vector `η^{⊗ m}`.  Telescoping the `n` replacements in one monomial gives the error `n / √m`.
The insertion maps enter through their matrices in the standard bases
(`QICLean.Analysis.TensorProduct.CyclicInsertionMatrix`).

The expansion of the replaced monomial into its terms and the gate expansions are treated in
`QICLean.Circuit.Party.Monomial.Elimination`.

## Main definitions

* `QuantumCircuit.Party.effectMatrix` : the pair effect `⟨η| ⊗ 1` as a matrix.
* `QuantumCircuit.Party.appendVector` : the matrix of `y ↦ y ⊗ v`.
* `QuantumCircuit.Party.EffectChain` : a monomial written as a chain of matrices and pair
  effects.
* `QuantumCircuit.Party.EffectChain.eval` : the matrix of a monomial.
* `QuantumCircuit.Party.EffectChain.stackIndex`, `stackVector` : the stack registers of a
  monomial and their ideal content.
* `QuantumCircuit.Party.EffectChain.replace` : the replaced monomial with occurrence-specific
  stacks.
* `QuantumCircuit.Party.EffectChain.replaceTerm` : one term of the expansion of the replaced
  monomial.

## Main results

* `QuantumCircuit.Party.EffectChain.norm_replace_sub_le` : telescoping bound `n / √m` for one
  monomial.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §5.1 and Lemma 5.1 `lem:effects`,
  `04-compression.tex`, lines 21–127.

Adapted from TNLean, `TNLean/Lattice/PartyCircuit/PairEffectChain.lean` at commit
`ded76a266d` (Apache-2.0).  Changes: the bundled inner product spaces are replaced by finite
basis types, continuous linear maps by matrices with the operator norm, tensor products of
spaces by products of basis types, and the maps appending a vector, exchanging two tensor
factors and tensoring with an identity by `appendVector`, `Matrix.reindex` and Kronecker
products with identity matrices.
-/

noncomputable section

open scoped InnerProductSpace Kronecker Matrix.Norms.L2Operator
open Matrix EuclideanSpace CyclicInsertion

namespace QuantumCircuit.Party

/-! ### Matrices of pair effects and appended vectors -/

section Matrices

variable {ι V X Y S : Type*}

/-- The exchange `(w, (y, t)) ↦ (y, (w, t))` of the first two factors of a triple product. -/
def prodLeftComm (W Y T : Type*) : W × (Y × T) ≃ Y × (W × T) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The exchange of the first two factors on a triple. -/
@[simp]
theorem prodLeftComm_apply (W Y T : Type*) (x : W × (Y × T)) :
    prodLeftComm W Y T x = (x.2.1, (x.1, x.2.2)) :=
  rfl

/-- The inverse exchange of the first two factors on a triple. -/
@[simp]
theorem prodLeftComm_symm_apply (W Y T : Type*) (x : Y × (W × T)) :
    (prodLeftComm W Y T).symm x = (x.2.1, (x.1, x.2.2)) :=
  rfl

/-- The pair effect `⟨η| ⊗ 1 : ℂ^{ι × S} → ℂ^S` as a matrix: its entry at `(s, (i, s'))` is
`conj (η i)` when `s = s'` and `0` otherwise. -/
def effectMatrix (η : EuclideanSpace ℂ ι) (S : Type*) [DecidableEq S] : Matrix S (ι × S) ℂ :=
  Matrix.of fun s x ↦ if s = x.2 then star (η x.1) else 0

/-- The entries of the pair effect. -/
@[simp]
theorem effectMatrix_apply (η : EuclideanSpace ℂ ι) (S : Type*) [DecidableEq S] (s : S)
    (x : ι × S) : effectMatrix η S s x = if s = x.2 then star (η x.1) else 0 :=
  rfl

/-- The pair effect sends a product vector `h ⊗ v` to `⟪η, h⟫ v`. -/
theorem toEuclideanLin_effectMatrix_vecKron [Fintype ι] [DecidableEq ι] [Fintype S]
    [DecidableEq S] (η h : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ S) :
    toEuclideanLin (effectMatrix η S) (vecKron h v) = ⟪η, h⟫_ℂ • v := by
  ext s
  simp only [vecKron, toLpLin_toLp, toLin'_apply, mulVec, dotProduct, effectMatrix_apply,
    RCLike.star_def, mul_comm, mul_ite, zero_mul, Fintype.sum_prod_type, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, PiLp.inner_apply, RCLike.inner_apply, PiLp.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Appending a fixed vector `v` behind the input: the matrix of `y ↦ y ⊗ v`, with entry
`v w` at `((y, w), y)` and `0` at `((y', w), y)` for `y' ≠ y`. -/
def appendVector (Y : Type*) [DecidableEq Y] (v : EuclideanSpace ℂ V) : Matrix (Y × V) Y ℂ :=
  Matrix.of fun x y ↦ if x.1 = y then v x.2 else 0

/-- The entries of the matrix appending a vector. -/
@[simp]
theorem appendVector_apply (Y : Type*) [DecidableEq Y] (v : EuclideanSpace ℂ V) (x : Y × V)
    (y : Y) : appendVector Y v x y = if x.1 = y then v x.2 else 0 :=
  rfl

/-- Appending `v` after the matrix `A`: the entry at `((y, w), z)` is `v w * A y z`. -/
theorem appendVector_mul_apply [Fintype Y] [DecidableEq Y] (v : EuclideanSpace ℂ V)
    (A : Matrix Y X ℂ) (x : Y × V) (z : X) :
    (appendVector Y v * A) x z = v x.2 * A x.1 z := by
  simp [Matrix.mul_apply, appendVector_apply, ite_mul, zero_mul, Finset.sum_ite_eq]

/-- Appending a vector multiplies norms by at most its norm. -/
theorem norm_appendVector_le [Fintype Y] [DecidableEq Y] [Fintype V]
    (v : EuclideanSpace ℂ V) : ‖appendVector Y v‖ ≤ ‖v‖ := by
  refine l2_opNorm_le_of_forall (norm_nonneg _) fun u => ?_
  have h : (EuclideanSpace.equiv (Y × V) ℂ).symm (appendVector Y v *ᵥ u) =
      vecKron ((EuclideanSpace.equiv Y ℂ).symm u) v := by
    ext ⟨y, w⟩
    simp [mulVec, dotProduct, appendVector_apply, vecKron, mul_comm]
  rw [h, norm_vecKron, mul_comm]

/-- The pair effect is the adjoint of appending `η`, with the two factors exchanged. -/
theorem effectMatrix_eq_conjTranspose [DecidableEq S] (η : EuclideanSpace ℂ ι) :
    effectMatrix η S = reindex (Equiv.refl S) (Equiv.prodComm S ι) (appendVector S η)ᴴ := by
  ext s ⟨i, s'⟩
  by_cases h : s = s'
  · subst h; simp
  · simp [h, Ne.symm h]

/-- A pair effect with a unit vector is a contraction. -/
theorem norm_effectMatrix_le [Fintype ι] [DecidableEq ι] [Fintype S] [DecidableEq S]
    {η : EuclideanSpace ℂ ι} (hη : ‖η‖ = 1) : ‖effectMatrix η S‖ ≤ 1 := by
  rw [effectMatrix_eq_conjTranspose]
  exact (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_conjTranspose _).trans_le
    ((norm_appendVector_le η).trans hη.le))

end Matrices

/-! ### Monomials as chains of matrices and pair effects -/

/-- A monomial of a gate expansion, written as a chain `F_n E_n ⋯ E_1 F_0` of effect-free
pieces `F_i` and pair effects `E_i = ⟨η_i| ⊗ 1`, on finite basis types.

* `final F` is the effect-free piece `F` with no further effect.
* `effect α β S F η rest` first applies the effect-free piece `F`, which ends with a pair
  register `α × β` in front of the spectator register `S`, then contracts the pair register
  with the bra `⟨η|`, and continues with the monomial `rest` on `S`.

Polynomial-PEPS manuscript (September 24, 2026), allowed monomials, `04-compression.tex`,
lines 32–35. -/
inductive EffectChain : Type → Type → Type 1
  | final {X Y : Type} (F : Matrix Y X ℂ) : EffectChain X Y
  | effect {X Y : Type} (α β S : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
      [Fintype S] [DecidableEq S] (F : Matrix ((α × β) × S) X ℂ)
      (η : EuclideanSpace ℂ (α × β)) (rest : EffectChain S Y) : EffectChain X Y

namespace EffectChain

/-- The matrix of a monomial. -/
def eval : {X Y : Type} → EffectChain X Y → Matrix Y X ℂ
  | _, _, final F => F
  | _, _, effect _ _ S F η rest => rest.eval * effectMatrix η S * F

/-- The number of pair effects of a monomial. -/
@[reducible] def effectCount : {X Y : Type} → EffectChain X Y → ℕ
  | _, _, final _ => 0
  | _, _, effect _ _ _ _ _ rest => rest.effectCount + 1

/-- The stack registers of a monomial: one stack `Fin m → α × β` of `m` pair registers for
each of its effect occurrences, in the order of the occurrences. -/
@[reducible] def stackIndex (m : ℕ) : {X Y : Type} → EffectChain X Y → Type
  | _, _, final _ => Unit
  | _, _, effect α β _ _ _ rest => (Fin m → α × β) × rest.stackIndex m

/-- The stack registers form a finite type. -/
instance instFintypeStackIndex (m : ℕ) :
    {X Y : Type} → (M : EffectChain X Y) → Fintype (M.stackIndex m)
  | _, _, final _ => inferInstanceAs (Fintype Unit)
  | _, _, effect α β _ _ _ rest =>
      haveI := instFintypeStackIndex m rest
      inferInstanceAs (Fintype ((Fin m → α × β) × rest.stackIndex m))

/-- The stack registers have decidable equality. -/
instance instDecidableEqStackIndex (m : ℕ) :
    {X Y : Type} → (M : EffectChain X Y) → DecidableEq (M.stackIndex m)
  | _, _, final _ => inferInstanceAs (DecidableEq Unit)
  | _, _, effect α β _ _ _ rest =>
      haveI := instDecidableEqStackIndex m rest
      inferInstanceAs (DecidableEq ((Fin m → α × β) × rest.stackIndex m))

/-- The ideal content of the stacks of a monomial: `η^{⊗ m}` in the stack of each effect
occurrence. -/
def stackVector (m : ℕ) : {X Y : Type} → (M : EffectChain X Y) →
    EuclideanSpace ℂ (M.stackIndex m)
  | _, _, final _ => EuclideanSpace.single () 1
  | _, _, effect _ _ _ _ η rest => vecKron (tensorPower (Fin m) η) (rest.stackVector m)

variable {Y : Type} [Fintype Y]

/-- A monomial is allowed when its effect-free pieces are contractions and its pair effects
are normalized.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35. -/
def IsAllowed : {X : Type} → [Fintype X] → [DecidableEq X] → EffectChain X Y → Prop
  | _, _, _, final F => ‖F‖ ≤ 1
  | _, _, _, effect _ _ _ F η rest => ‖F‖ ≤ 1 ∧ ‖η‖ = 1 ∧ rest.IsAllowed

/-- The matrix of an allowed monomial is a contraction. -/
theorem norm_eval_le_one : {X : Type} → [Fintype X] → [DecidableEq X] →
    (M : EffectChain X Y) → M.IsAllowed → ‖M.eval‖ ≤ 1
  | _, _, _, final _, h => h
  | _, _, _, effect _ _ S _ _ rest, h => by
      obtain ⟨hF, hη, hrest⟩ := h
      exact l2_opNorm_mul_le_one _ _ (l2_opNorm_mul_le_one _ _ (norm_eval_le_one rest hrest)
        (norm_effectMatrix_le hη)) hF

/-- The ideal stack content of an allowed monomial is a unit vector. -/
theorem norm_stackVector (m : ℕ) : {X : Type} → [Fintype X] → [DecidableEq X] →
    (M : EffectChain X Y) → M.IsAllowed → ‖M.stackVector m‖ = 1
  | _, _, _, final _, _ => by simp [stackVector]
  | _, _, _, effect _ _ _ _ η rest, h => by
      obtain ⟨_, hη, hrest⟩ := h
      simp only [stackVector]
      rw [norm_vecKron, norm_tensorPower hη, norm_stackVector m rest hrest, one_mul]

variable [DecidableEq Y]

/-- The replaced monomial: each effect `⟨η|` is replaced by the cyclic insertion `T_m` into
the stack of that occurrence, and the stack stays idle afterwards.  The output register is
`Y × stackIndex m M`.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 5.1, `04-compression.tex`,
lines 100–106. -/
def replace (m : ℕ) : {X : Type} → (M : EffectChain X Y) → Matrix (Y × M.stackIndex m) X ℂ
  | _, final F => appendVector Y (EuclideanSpace.single () 1) * F
  | _, effect α β S F η rest =>
      reindex (prodLeftComm _ _ _) (Equiv.refl _)
        (((1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ rest.replace m) *
          (cyclicInsertionMatrix η m ⊗ₖ (1 : Matrix S S ℂ)) * F)

/-- One term of the expansion of the replaced monomial: the effect occurrence number `i` is
replaced by the insertion at position `κ i`.  The definition applies no pair bra: it composes
the pieces `F_i` of the monomial with insertions, which are preparations of copies of the
normalized pair vector followed by register permutations (`CyclicInsertion.insertAt_zero`,
`CyclicInsertion.insertAt_perm`).  When the pieces `F_i` are local contractions on parties, each
term is therefore the operator of a word of local contractions and normalized pair sources.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 96–98 and
121–123. -/
def replaceTerm (m : ℕ) : {X : Type} → (M : EffectChain X Y) →
    (Fin M.effectCount → Fin m) → Matrix (Y × M.stackIndex m) X ℂ
  | _, final F, _ => appendVector Y (EuclideanSpace.single () 1) * F
  | _, effect α β S F η rest, κ =>
      reindex (prodLeftComm _ _ _) (Equiv.refl _)
        (((1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ
            rest.replaceTerm m (Fin.tail κ)) *
          (insertAtMatrix η (κ (0 : Fin (rest.effectCount + 1))) ⊗ₖ (1 : Matrix S S ℂ)) * F)

/-- The replaced monomial of an allowed monomial is a contraction. -/
theorem norm_replace_le_one (m : ℕ) : {X : Type} → [Fintype X] → [DecidableEq X] →
    (M : EffectChain X Y) → M.IsAllowed → ‖M.replace m‖ ≤ 1
  | _, _, _, final _, h =>
      l2_opNorm_mul_le_one _ _ ((norm_appendVector_le _).trans (by simp)) h
  | _, _, _, effect _ _ _ _ _ rest, h => by
      obtain ⟨hF, hη, hrest⟩ := h
      exact (l2_opNorm_reindex_le _ _ _).trans <| l2_opNorm_mul_le_one _ _
        (l2_opNorm_mul_le_one _ _
          ((l2_opNorm_one_kronecker_le _).trans (norm_replace_le_one m rest hrest))
          ((l2_opNorm_kronecker_one_le _).trans (norm_cyclicInsertionMatrix_le_one hη m))) hF

/-- Every term of the expansion of the replaced monomial of an allowed monomial is a
contraction. -/
theorem norm_replaceTerm_le_one (m : ℕ) : {X : Type} → [Fintype X] → [DecidableEq X] →
    (M : EffectChain X Y) → M.IsAllowed → ∀ κ, ‖M.replaceTerm m κ‖ ≤ 1
  | _, _, _, final _, h, _ =>
      l2_opNorm_mul_le_one _ _ ((norm_appendVector_le _).trans (by simp)) h
  | _, _, _, effect _ _ _ _ _ rest, h, _ => by
      obtain ⟨hF, hη, hrest⟩ := h
      exact (l2_opNorm_reindex_le _ _ _).trans <| l2_opNorm_mul_le_one _ _
        (l2_opNorm_mul_le_one _ _
          ((l2_opNorm_one_kronecker_le _).trans (norm_replaceTerm_le_one m rest hrest _))
          ((l2_opNorm_kronecker_one_le _).trans (norm_insertAtMatrix_le_one hη _))) hF

/-- The ideal replacement of the first effect occurrence: appending the stack vector after the
monomial equals replacing its first effect `⟨η|` by the ideal map `|η^{⊗ m}⟩⟨η|` and the
remaining monomial by its own ideal augmentation, followed by the exchange of the first two
output registers. -/
theorem appendVector_mul_eval_effect {X : Type} {α β S : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype S] [DecidableEq S]
    (m : ℕ) (F : Matrix ((α × β) × S) X ℂ) (η : EuclideanSpace ℂ (α × β))
    (rest : EffectChain S Y) :
    appendVector Y ((effect α β S F η rest).stackVector m) * (effect α β S F η rest).eval =
      reindex (prodLeftComm _ _ _) (Equiv.refl _)
        (((1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ
            (appendVector Y (rest.stackVector m) * rest.eval)) *
          (idealInsertionMatrix η m ⊗ₖ (1 : Matrix S S ℂ)) * F) := by
  rw [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  ext ⟨y, f, σ⟩ x
  rw [appendVector_mul_apply, reindex_apply, submatrix_apply]
  simp only [stackVector, eval, prodLeftComm_symm_apply, Equiv.refl_symm, Equiv.coe_refl,
    id_eq, Matrix.mul_apply, Finset.mul_sum, effectMatrix_apply, mul_ite, mul_zero]
  refine Finset.sum_congr rfl fun ⟨i, s'⟩ _ => ?_
  simp only [kronecker_apply, appendVector_mul_apply, idealInsertionMatrix_apply, vecKron,
    PiLp.toLp_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- **Telescoping bound for one monomial.** Replacing the `n` effects of an allowed monomial
by cyclic insertions changes it by at most `n / √m` from the ideal augmented monomial
`M ⊗ |η_1^{⊗ m} ⊗ ⋯ ⊗ η_n^{⊗ m}⟩`.

Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 5.1, `04-compression.tex`,
lines 117–121. -/
theorem norm_replace_sub_le {m : ℕ} (hm : m ≠ 0) : {X : Type} → [Fintype X] →
    [DecidableEq X] → (M : EffectChain X Y) → M.IsAllowed →
    ‖M.replace m - appendVector Y (M.stackVector m) * M.eval‖ ≤ M.effectCount / Real.sqrt m
  | _, _, _, final F, _ => by
      simp only [replace, stackVector, eval, sub_self, norm_zero, effectCount,
        CharP.cast_eq_zero, zero_div, le_refl]
  | _, _, _, effect α β S F η rest, h => by
      obtain ⟨hF, hη, hrest⟩ := h
      rw [appendVector_mul_eval_effect]
      set A := rest.replace m
      set I := appendVector Y (rest.stackVector m) * rest.eval
      set T := cyclicInsertionMatrix η m
      set P := idealInsertionMatrix η m
      have hsplit : replace m (effect α β S F η rest) -
          reindex (prodLeftComm _ _ _) (Equiv.refl _)
            (((1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ I) *
              (P ⊗ₖ (1 : Matrix S S ℂ)) * F) =
          reindex (prodLeftComm _ _ _) (Equiv.refl _)
            ((((1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ (A - I)) *
                (T ⊗ₖ (1 : Matrix S S ℂ)) +
              ((1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ I) *
                ((T - P) ⊗ₖ (1 : Matrix S S ℂ))) * F) := by
        rw [replace, ← coe_reindexLinearEquiv ℂ ℂ, ← map_sub, ← Matrix.sub_mul]
        congr 2
        simp only [← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
        ext ⟨a, b⟩ ⟨c, d⟩
        simp only [Matrix.sub_apply, Matrix.add_apply, kronecker_apply]
        ring
      have hI : ‖I‖ ≤ 1 := l2_opNorm_mul_le_one _ _
        ((norm_appendVector_le _).trans (norm_stackVector m rest hrest).le)
        (norm_eval_le_one rest hrest)
      have hA := norm_replace_sub_le hm rest hrest
      have hT : ‖T‖ ≤ 1 := norm_cyclicInsertionMatrix_le_one hη m
      have hTP : ‖T - P‖ ≤ 1 / Real.sqrt m := norm_cyclicInsertionMatrix_sub_ideal_le hη hm
      have h1 : ‖((1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ (A - I)) *
          (T ⊗ₖ (1 : Matrix S S ℂ))‖ ≤ rest.effectCount / Real.sqrt m :=
        (l2_opNorm_mul _ _).trans <| (mul_le_mul (l2_opNorm_one_kronecker_le _)
          ((l2_opNorm_kronecker_one_le _).trans hT) (norm_nonneg _) (norm_nonneg _)).trans
          ((mul_one _).trans_le hA)
      have h2 : ‖((1 : Matrix (Fin m → α × β) (Fin m → α × β) ℂ) ⊗ₖ I) *
          ((T - P) ⊗ₖ (1 : Matrix S S ℂ))‖ ≤ 1 / Real.sqrt m :=
        (l2_opNorm_mul _ _).trans <| (mul_le_mul ((l2_opNorm_one_kronecker_le _).trans hI)
          ((l2_opNorm_kronecker_one_le _).trans hTP) (norm_nonneg _) zero_le_one).trans_eq
          (one_mul _)
      rw [hsplit]
      refine (l2_opNorm_reindex_le _ _ _).trans <| (l2_opNorm_mul _ _).trans ?_
      calc _ ≤ ((rest.effectCount + 1 : ℕ) / Real.sqrt m) * 1 := by
            refine mul_le_mul ?_ hF (norm_nonneg _) (by positivity)
            refine (norm_add_le _ _).trans ?_
            calc _ ≤ rest.effectCount / Real.sqrt m + 1 / Real.sqrt m := add_le_add h1 h2
              _ = _ := by push_cast; ring
        _ = _ := by rw [mul_one]

end EffectChain

end QuantumCircuit.Party
