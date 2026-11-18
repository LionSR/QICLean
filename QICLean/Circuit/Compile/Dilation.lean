/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausFamilyDilation
import QICLean.Circuit.Compile.Encoding
import QICLean.Circuit.Core.LayerEntry
import QICLean.Circuit.Core.TensorRight

/-!
# Protocols as unitary circuits on enlarged sites

Every protocol is the preparation of a product of basis vectors on an environment at every
site, an unbranched circuit of unitary gates on the enlarged local systems of depth at most
that of the protocol, and the partial trace over the output environments
(`IsProtocol.exists_unitary_dilation`). The geometry, the cells and their costs are those of
the protocol; only the local bases grow.

The proof is by layers. A layer is dilated on its own cells (`Layer.isUnitaryDilation`): every
gate and onsite family is replaced by its unitary dilation
(`KrausFamily.IsTP.exists_unitary_dilation`, Wolf, Thm. 2.5), whose environment is a single
basis for the whole cell; it is placed at one designated site of the cell (`IsRep`), the other
sites of the cell carrying a one-element basis (`Distribute`). A gate on an empty cell acts on a
one-element basis, so by trace preservation its map is the identity and it is replaced by the
identity. The map of a layer is the tensor product of the maps of its gates and onsite families
(`Layer.map_single_apply`), so the dilated layer, traced and prepared, has the map of the
layer. Dilations compose (`IsUnitaryDilation.comp`): the environments of the later circuit are
prepared at the start and carried through the earlier one by `Circuit.tensorRight`, and those
of the earlier circuit are carried through the later one; the partial trace over an
environment commutes with a circuit tensored with the identity on it
(`map_traceCircuit_map_tensorRight`), and depth-zero layers of relabellings regroup the local
products in between.

## Main definitions

* `QuantumCircuit.prepareCircuit` — the preparation of the environments in basis vectors.
* `QuantumCircuit.traceCircuit` — the partial trace over the environments.
* `QuantumCircuit.relabelCircuit` — the relabelling of the local bases along equivalences.

* `QuantumCircuit.IsUnitaryDilation` — a map is the partial trace of an unbranched unitary
  circuit of bounded depth on prepared environments.

## Main results

* `QuantumCircuit.IsProtocol.exists_unitary_dilation` — the unitary dilation of a protocol.
* `QuantumCircuit.Circuit.isUnitaryDilation` — the same for an unbranched circuit of
  trace-preserving gates.
* `QuantumCircuit.Layer.isUnitaryDilation` — one layer, with the environment of every gate at
  a designated site of its cell (`QuantumCircuit.IsRep`).
* `QuantumCircuit.IsUnitaryDilation.comp` — dilations compose, with the sum of the depths.
* `QuantumCircuit.map_traceCircuit_map_tensorRight` — the partial trace over an environment
  commutes with a circuit tensored with the identity on it.
-/

open Matrix ManyBody
open scoped Kronecker

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] (Γ : Geometry S)

/-! ### Preparation, partial trace and relabelling -/

section Local

variable {X Y Z E F : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
  [∀ s, Fintype (E s)] [∀ s, DecidableEq (E s)] [∀ s, Fintype (F s)] [∀ s, DecidableEq (F s)]

/-- The preparation of the environment `E s` at every site in the basis vector `e₀ s`. -/
def prepareCircuit (e₀ : ∀ s, E s) : Circuit Γ KrausGate X (fun s ↦ X s × E s) :=
  encodeCircuit Γ fun s ↦ ⟨fun a ↦ (a, e₀ s), fun _ _ h ↦ congrArg Prod.fst h⟩

/-- The partial trace over the environment `F s` at every site. -/
def traceCircuit (Z F : S → Type) [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    [∀ s, Fintype (F s)] [∀ s, DecidableEq (F s)] :
    Circuit Γ KrausGate (fun s ↦ Z s × F s) Z :=
  Circuit.ofLayer (Layer.ofOnsite fun s ↦ KrausFamily.traceRight (Z s) (F s))

/-- The relabelling of the local bases along equivalences `σ s`. -/
def relabelCircuit (σ : ∀ s, X s ≃ Y s) : Circuit Γ KrausGate X Y :=
  encodeCircuit Γ fun s ↦ (σ s).toEmbedding

variable {Γ}

theorem map_prepareCircuit_apply (e₀ : ∀ s, E s) (ρ : Matrix (Config X) (Config X) ℂ)
    (w w' : Config fun s ↦ X s × E s) :
    (prepareCircuit Γ e₀).map KrausGate.ev ρ w w' =
      if (fun s ↦ (w s).2) = e₀ ∧ (fun s ↦ (w' s).2) = e₀ then
        ρ (fun s ↦ (w s).1) (fun s ↦ (w' s).1) else 0 := by
  rw [prepareCircuit, map_encodeCircuit]
  have key : ∀ (w : Config fun s ↦ X s × E s) (x : Config X),
      w = (Function.Embedding.piCongrRight fun s ↦
        (⟨fun a ↦ (a, e₀ s), fun _ _ h ↦ congrArg Prod.fst h⟩ : X s ↪ X s × E s)) x ↔
        (fun s ↦ (w s).2) = e₀ ∧ x = fun s ↦ (w s).1 := by
    intro w x
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h, rfl⟩
      funext s
      exact Prod.ext rfl (congrFun h s)
  simp only [mul_apply, conjTranspose_apply, initializedBasisMatrix, submatrix_apply, id,
    one_apply, key, ite_and]
  by_cases hw : (fun s ↦ (w s).2) = e₀ <;> by_cases hw' : (fun s ↦ (w' s).2) = e₀ <;>
    simp [hw, hw', Finset.sum_ite_eq']

theorem map_traceCircuit_apply (M : Matrix (Config fun s ↦ Z s × F s)
    (Config fun s ↦ Z s × F s) ℂ) (y y' : Config Z) :
    (traceCircuit Γ Z F).map KrausGate.ev M y y' =
      ∑ f : Config F, M (fun s ↦ (y s, f s)) (fun s ↦ (y' s, f s)) := by
  set L : Layer Γ KrausGate (fun s ↦ Z s × F s) Z :=
    Layer.ofOnsite fun s ↦ KrausFamily.traceRight (Z s) (F s)
  have hmem : ∀ s, s ∉ L.cells.biUnion Γ.cell := fun s ↦ by simp [L, Layer.ofOnsite]
  let e : L.Index ≃ Config F :=
    { toFun := fun i s ↦ i.2 ⟨s, hmem s⟩
      invFun := fun f ↦ (fun b ↦ absurd b.2 (Finset.notMem_empty _), fun t ↦ f t.1)
      left_inv := fun i ↦ Prod.ext (funext fun b ↦ absurd b.2 (Finset.notMem_empty _)) rfl
      right_inv := fun _ ↦ rfl }
  have hK : ∀ (i : L.Index) (w : Config fun s ↦ Z s × F s) (z : Config Z),
      L.kraus KrausGate.ev i z w =
        if w = (fun s ↦ ((z s, i.2 ⟨s, hmem s⟩) : Z s × F s)) then 1 else 0 := by
    intro i w z
    rw [Layer.kraus_ofOnsite, prodOp_apply]
    split_ifs with h
    · subst h
      refine Finset.prod_eq_one fun s _ ↦ ?_
      simp only [KrausFamily.traceRight, of_apply]
      exact ite_eq_left rfl
    · obtain ⟨s, hs⟩ := Function.ne_iff.mp h
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      simp only [KrausFamily.traceRight, of_apply]
      exact ite_eq_right hs
  rw [traceCircuit, Circuit.map_ofLayer, KrausFamily.map_apply, Matrix.sum_apply]
  refine Fintype.sum_equiv e _ _ fun i ↦ ?_
  change (L.kraus KrausGate.ev i * M * (L.kraus KrausGate.ev i)ᴴ) y y' = _
  simp only [mul_apply, conjTranspose_apply, hK]
  simp only [apply_ite star, star_one, star_zero, mul_ite, ite_mul, mul_one, one_mul,
    mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

theorem map_relabelCircuit_apply (σ : ∀ s, X s ≃ Y s) (ρ : Matrix (Config X) (Config X) ℂ)
    (w w' : Config Y) :
    (relabelCircuit Γ σ).map KrausGate.ev ρ w w' =
      ρ (fun s ↦ (σ s).symm (w s)) (fun s ↦ (σ s).symm (w' s)) := by
  have key : ∀ (w : Config Y) (x : Config X),
      w = (Function.Embedding.piCongrRight fun s ↦ (σ s).toEmbedding) x ↔
        x = fun s ↦ (σ s).symm (w s) := by
    intro w x
    constructor
    · rintro rfl
      funext s
      exact ((σ s).symm_apply_apply _).symm
    · rintro rfl
      funext s
      exact ((σ s).apply_symm_apply _).symm
  rw [relabelCircuit, map_encodeCircuit]
  simp only [mul_apply, conjTranspose_apply, initializedBasisMatrix, submatrix_apply, id,
    one_apply, key]
  simp [Finset.sum_ite_eq']

omit [Fintype S] [DecidableEq S] in
private theorem initializedBasisMatrix_mul_conjTranspose_equiv {α β : Type} [Fintype α]
    [DecidableEq β] (σ : α ≃ β) :
    initializedBasisMatrix σ.toEmbedding * (initializedBasisMatrix σ.toEmbedding)ᴴ = 1 := by
  ext y y'
  simp only [mul_apply, conjTranspose_apply, initializedBasisMatrix, submatrix_apply, id,
    one_apply, Equiv.coe_toEmbedding]
  rw [Finset.sum_eq_single (σ.symm y) (fun x _ hx ↦ by
    rw [ite_eq_right (fun h ↦ hx (by rw [h, Equiv.symm_apply_apply])), zero_mul]) (by simp)]
  simp [eq_comm]

omit [Fintype S] in
theorem forall_isUnitary_relabelCircuit (σ : ∀ s, X s ≃ Y s) :
    (relabelCircuit Γ σ).Forall KrausGate.ev KrausFamily.IsUnitary :=
  ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun s ↦
    ⟨⟨inferInstanceAs (Unique Unit)⟩, fun _ ↦ ⟨initializedBasisMatrix_isIsometry _,
      initializedBasisMatrix_mul_conjTranspose_equiv (σ s.1)⟩⟩⟩, fun _ ↦ trivial⟩

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
theorem isUnbranched_relabelCircuit (σ : ∀ s, X s ≃ Y s) : (relabelCircuit Γ σ).IsUnbranched :=
  Circuit.isUnbranched_ofLayer _

omit [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] in
theorem depth_relabelCircuit (σ : ∀ s, X s ≃ Y s) : (relabelCircuit Γ σ).depth = 0 := by
  rw [relabelCircuit, encodeCircuit, Circuit.depth_ofLayer, Layer.depth_ofOnsite]

/-- The partial trace of a product with `ω` is the trace of `ω` times the first factor. -/
theorem map_traceCircuit_kronecker (A : Matrix (Config Z) (Config Z) ℂ)
    (ω : Matrix (Config F) (Config F) ℂ) :
    (traceCircuit Γ Z F).map KrausGate.ev ((A ⊗ₖ ω).submatrix
      (Equiv.arrowProdEquivProdArrow S Z F) (Equiv.arrowProdEquivProdArrow S Z F)) =
      ω.trace • A := by
  ext y y'
  rw [map_traceCircuit_apply, Matrix.smul_apply, smul_eq_mul, trace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  rw [submatrix_apply, kronecker_apply, mul_comm]
  rfl

/-- The partial trace over `W` commutes with a circuit tensored with the identity on `W`. -/
theorem map_traceCircuit_map_tensorRight (c : Circuit Γ KrausGate X Z)
    (N : Matrix (Config fun s ↦ X s × F s) (Config fun s ↦ X s × F s) ℂ) :
    (traceCircuit Γ Z F).map KrausGate.ev ((c.tensorRight F).map KrausGate.ev N) =
      c.map KrausGate.ev ((traceCircuit Γ X F).map KrausGate.ev N) := by
  set e := Equiv.arrowProdEquivProdArrow S X F
  let r : Matrix (Config X × Config F) (Config X × Config F) ℂ ≃ₗ[ℂ]
      Matrix (Config fun s ↦ X s × F s) (Config fun s ↦ X s × F s) ℂ :=
    reindexLinearEquiv ℂ ℂ e.symm e.symm
  have key : (traceCircuit Γ Z F).map KrausGate.ev ∘ₗ (c.tensorRight F).map KrausGate.ev ∘ₗ
      r.toLinearMap = c.map KrausGate.ev ∘ₗ (traceCircuit Γ X F).map KrausGate.ev ∘ₗ
        r.toLinearMap := by
    refine linearMap_ext_kronecker fun ρ ω ↦ ?_
    have hr : r (ρ ⊗ₖ ω) = (ρ ⊗ₖ ω).submatrix e e := rfl
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hr]
    rw [Circuit.map_tensorRight, map_traceCircuit_kronecker, map_traceCircuit_kronecker, map_smul]
  have := LinearMap.congr_fun key (r.symm N)
  simpa using this

end Local

/-! ### Moving environments -/

section Reassoc

variable {X Y Z A B C : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
  [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Fintype (B s)] [∀ s, DecidableEq (B s)]
  [∀ s, Fintype (C s)] [∀ s, DecidableEq (C s)]

variable {Γ}

/-- Preparing two environments, then regrouping, is preparing the first and tensoring with the
basis vector of the second. -/
private theorem map_relabel_prepare (a₀ : ∀ s, A s) (b₀ : ∀ s, B s)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    (relabelCircuit Γ fun s ↦ (Equiv.prodAssoc (X s) (A s) (B s)).symm).map KrausGate.ev
        ((prepareCircuit Γ fun s ↦ (a₀ s, b₀ s)).map KrausGate.ev ρ) =
      ((prepareCircuit Γ a₀).map KrausGate.ev ρ ⊗ₖ Matrix.single b₀ b₀ (1 : ℂ)).submatrix
        (Equiv.arrowProdEquivProdArrow S (fun s ↦ X s × A s) B)
        (Equiv.arrowProdEquivProdArrow S (fun s ↦ X s × A s) B) := by
  ext w w'
  rw [map_relabelCircuit_apply, map_prepareCircuit_apply, submatrix_apply, kronecker_apply,
    map_prepareCircuit_apply]
  simp only [Equiv.arrowProdEquivProdArrow_apply, Matrix.single_apply, funext_iff, Prod.ext_iff]
  simp only [Equiv.symm_symm, Equiv.prodAssoc_apply, mul_ite, mul_one, mul_zero]
  split_ifs <;> grind

/-- The partial trace over two environments, after regrouping, is the partial trace over the
inner one after the partial trace over the outer one. -/
private theorem map_trace_relabel (Q : Matrix (Config fun s ↦ (Z s × B s) × C s)
    (Config fun s ↦ (Z s × B s) × C s) ℂ) :
    (traceCircuit Γ Z fun s ↦ B s × C s).map KrausGate.ev
        ((relabelCircuit Γ fun s ↦ Equiv.prodAssoc (Z s) (B s) (C s)).map KrausGate.ev Q) =
      (traceCircuit Γ Z B).map KrausGate.ev
        ((traceCircuit Γ (fun s ↦ Z s × B s) C).map KrausGate.ev Q) := by
  ext y y'
  simp only [map_traceCircuit_apply, map_relabelCircuit_apply]
  rw [← (Equiv.arrowProdEquivProdArrow S B C).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- Tracing out an environment after moving a prepared one past it is preparing after tracing. -/
private theorem map_trace_relabel_prepare (b₀ : ∀ s, B s)
    (M : Matrix (Config fun s ↦ Y s × C s) (Config fun s ↦ Y s × C s) ℂ) :
    (traceCircuit Γ (fun s ↦ Y s × B s) C).map KrausGate.ev
        ((relabelCircuit Γ fun s ↦ ((Equiv.prodAssoc (Y s) (C s) (B s)).trans
          ((Equiv.refl (Y s)).prodCongr (Equiv.prodComm (C s) (B s)))).trans
            (Equiv.prodAssoc (Y s) (B s) (C s)).symm).map KrausGate.ev
          ((M ⊗ₖ Matrix.single b₀ b₀ (1 : ℂ)).submatrix
            (Equiv.arrowProdEquivProdArrow S (fun s ↦ Y s × C s) B)
            (Equiv.arrowProdEquivProdArrow S (fun s ↦ Y s × C s) B))) =
      (prepareCircuit Γ b₀).map KrausGate.ev ((traceCircuit Γ Y C).map KrausGate.ev M) := by
  ext w w'
  simp only [map_traceCircuit_apply, map_relabelCircuit_apply, map_prepareCircuit_apply,
    submatrix_apply, Equiv.arrowProdEquivProdArrow_apply, kroneckerMap_apply, Matrix.single_apply,
    Equiv.symm_trans_apply, Equiv.prodAssoc_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.refl_symm, Equiv.prodComm_symm, Equiv.symm_symm, Prod.map, Equiv.refl_apply,
    Equiv.prodComm_apply, Prod.swap, Equiv.prodAssoc_symm_apply, funext_iff]
  by_cases h1 : ∀ s, (w s).2 = b₀ s <;> by_cases h2 : ∀ s, (w' s).2 = b₀ s <;>
    simp [h1, h2, eq_comm]

end Reassoc

/-! ### Environments of the cells of a layer -/

section Distribute

variable {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X Y : S → Type}
  (L : Layer Γ G X Y)

/-- The site `s` is the designated site of the cell `b`, a site chosen in the nonempty cell. -/
def IsRep (b : L.cells) (s : S) : Prop :=
  ∃ h : (Γ.cell b.1).Nonempty, h.choose = s

noncomputable instance (b : L.cells) : DecidablePred (IsRep Γ L b) :=
  Classical.decPred _

noncomputable instance (s : S) : DecidablePred fun b ↦ IsRep Γ L b s :=
  Classical.decPred _

variable {Γ} {L}

omit [Fintype S] [GateFamily G] in
theorem IsRep.mem {b : L.cells} {s : S} (h : IsRep Γ L b s) : s ∈ Γ.cell b.1 := by
  obtain ⟨h, rfl⟩ := h
  exact h.choose_spec

omit [Fintype S] [GateFamily G] in
/-- A site is the designated site of at most the one cell containing it. -/
theorem IsRep.eq {b c : L.cells} {s : S} (h : IsRep Γ L c s) (hb : s ∈ Γ.cell b.1) : c = b :=
  (L.cellOf_eq (L.mem_biUnion_of_mem_cell c h.mem) h.mem).symm.trans
    (L.cellOf_eq (L.mem_biUnion_of_mem_cell c h.mem) hb)

omit [Fintype S] [GateFamily G] in
theorem not_isRep_of_free {c : L.cells} (t : L.Free) : ¬ IsRep Γ L c t.1 :=
  fun h ↦ t.2 (L.mem_biUnion_of_mem_cell c h.mem)

variable (L) in
/-- Types `T b` on the cells and `T' t` at the free sites of a layer, as a system: the site `s`
carries `T b` for the cells `b` it is designated for, at most one, and `T' t` if it is the free
site `t`. -/
abbrev Distribute (T : L.cells → Type) (T' : L.Free → Type) (s : S) : Type :=
  ((c : {c : L.cells // IsRep Γ L c s}) → T c.1) × ((t : {t : L.Free // t.1 = s}) → T' t.1)

omit [Fintype S] [GateFamily G] in
/-- On a nonempty cell `b` the distributed system is `T b`. -/
noncomputable def distributeCellEquiv (T : L.cells → Type) (T' : L.Free → Type) (b : L.cells)
    (h : (Γ.cell b.1).Nonempty) : RegionConfig (Distribute L T T') (Γ.cell b) ≃ T b where
  toFun φ := (φ ⟨h.choose, h.choose_spec⟩).1 ⟨b, h, rfl⟩
  invFun t v := (fun c ↦ cast (congrArg T (c.2.eq v.2).symm) t,
    fun t' ↦ (t'.1.2 (by rw [t'.2]; exact L.mem_biUnion_of_mem_cell b v.2)).elim)
  left_inv φ := by
    funext ⟨v, hvb⟩
    refine Prod.ext (funext fun ⟨c, hcv⟩ ↦ ?_) (funext fun t' ↦ ?_)
    · obtain rfl : c = b := hcv.eq hvb
      have key : ∀ (w : S) (hw : w ∈ Γ.cell c.1) (_ : w = h.choose) (p : IsRep Γ L c w),
          cast (congrArg T (p.eq hw).symm) ((φ ⟨h.choose, h.choose_spec⟩).1 ⟨c, h, rfl⟩) =
            (φ ⟨w, hw⟩).1 ⟨c, p⟩ := by
        rintro w hw rfl p
        rfl
      exact key v hvb hcv.2.symm hcv
    · exact (t'.1.2 (by rw [t'.2]; exact L.mem_biUnion_of_mem_cell b hvb)).elim
  right_inv t := rfl

omit [Fintype S] [GateFamily G] in
/-- At a free site `t` the distributed system is `T' t`. -/
def distributeFreeEquiv (T : L.cells → Type) (T' : L.Free → Type) (t : L.Free) :
    Distribute L T T' t.1 ≃ T' t where
  toFun p := p.2 ⟨t, rfl⟩
  invFun x := (fun c ↦ (not_isRep_of_free t c.2).elim,
    fun t' ↦ cast (congrArg T' (Subtype.ext t'.2).symm) x)
  left_inv p := by
    refine Prod.ext (funext fun c ↦ (not_isRep_of_free t c.2).elim) (funext fun t' ↦ ?_)
    obtain ⟨t', ht'⟩ := t'
    obtain rfl : t' = t := Subtype.ext ht'
    rfl
  right_inv x := rfl

end Distribute

/-! ### Unitary dilations -/

section Dilation

variable {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]

/-- The map `Φ` is the partial trace over output environments `F s` of an unbranched circuit of
unitary gates of depth at most `T`, applied after the preparation of input environments `E s` in
basis vectors. -/
def IsUnitaryDilation (T : ℕ)
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ (E F : S → Type) (_ : ∀ s, Fintype (E s)) (_ : ∀ s, DecidableEq (E s))
    (_ : ∀ s, Fintype (F s)) (_ : ∀ s, DecidableEq (F s)) (e₀ : ∀ s, E s)
    (c : Circuit Γ KrausGate (fun s ↦ X s × E s) (fun s ↦ Z s × F s)),
    c.Forall KrausGate.ev KrausFamily.IsUnitary ∧ c.IsUnbranched ∧ c.depth ≤ T ∧
      Φ = (traceCircuit Γ Z F).map KrausGate.ev ∘ₗ c.map KrausGate.ev ∘ₗ
        (prepareCircuit Γ e₀).map KrausGate.ev

variable {Γ}

/-- A composition of dilated maps is dilated, with the sum of the depths: the environments of
the second map are prepared at the start and carried through the first circuit, and those of
the first are carried through the second. -/
theorem IsUnitaryDilation.comp {T₁ T₂ : ℕ}
    {Φ₁ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Y) (Config Y) ℂ}
    {Φ₂ : Matrix (Config Y) (Config Y) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h₁ : IsUnitaryDilation Γ T₁ Φ₁) (h₂ : IsUnitaryDilation Γ T₂ Φ₂) :
    IsUnitaryDilation Γ (T₁ + T₂) (Φ₂ ∘ₗ Φ₁) := by
  obtain ⟨E₁, F₁, _, _, _, _, e₁, c₁, hu₁, hb₁, hd₁, rfl⟩ := h₁
  obtain ⟨E₂, F₂, _, _, _, _, e₂, c₂, hu₂, hb₂, hd₂, rfl⟩ := h₂
  let R₁ := relabelCircuit Γ fun s ↦ (Equiv.prodAssoc (X s) (E₁ s) (E₂ s)).symm
  let R₂ := relabelCircuit Γ fun s ↦
    ((Equiv.prodAssoc (Y s) (F₁ s) (E₂ s)).trans ((Equiv.refl (Y s)).prodCongr
      (Equiv.prodComm (F₁ s) (E₂ s)))).trans (Equiv.prodAssoc (Y s) (E₂ s) (F₁ s)).symm
  let R₃ := relabelCircuit Γ fun s ↦ Equiv.prodAssoc (Z s) (F₂ s) (F₁ s)
  refine ⟨fun s ↦ E₁ s × E₂ s, fun s ↦ F₂ s × F₁ s, inferInstance, inferInstance, inferInstance,
    inferInstance, fun s ↦ (e₁ s, e₂ s),
    R₁.comp ((c₁.tensorRight E₂).comp (R₂.comp ((c₂.tensorRight F₁).comp R₃))), ?_, ?_, ?_, ?_⟩
  · exact (forall_isUnitary_relabelCircuit _).comp _ ((Circuit.forall_isUnitary_tensorRight _
      hu₁).comp _ ((forall_isUnitary_relabelCircuit _).comp _
        ((Circuit.forall_isUnitary_tensorRight _ hu₂).comp _ (forall_isUnitary_relabelCircuit _))))
  · exact (isUnbranched_relabelCircuit _).comp ((Circuit.isUnbranched_mapLayers _ hb₁).comp
      ((isUnbranched_relabelCircuit _).comp ((Circuit.isUnbranched_mapLayers _ hb₂).comp
        (isUnbranched_relabelCircuit _))))
  · refine (Circuit.depth_comp _ _).trans ?_
    rw [depth_relabelCircuit, zero_add]
    refine (Circuit.depth_comp _ _).trans (add_le_add ((Circuit.depth_tensorRight_le _ _).trans hd₁)
      ((Circuit.depth_comp _ _).trans ?_))
    rw [depth_relabelCircuit, zero_add]
    refine (Circuit.depth_comp _ _).trans ?_
    rw [depth_relabelCircuit, add_zero]
    exact (Circuit.depth_tensorRight_le _ _).trans hd₂
  · refine LinearMap.ext fun ρ ↦ ?_
    simp only [LinearMap.comp_apply, Circuit.map_comp, R₁, R₂, R₃]
    rw [map_relabel_prepare, Circuit.map_tensorRight, map_trace_relabel,
      map_traceCircuit_map_tensorRight, map_trace_relabel_prepare]

omit [Fintype S] [DecidableEq S] in
private theorem map_reindex_single_apply {α β α' β' : Type} [Fintype α] [DecidableEq α]
    [Fintype α'] [DecidableEq α'] (K : KrausFamily α β) (e : α' ≃ α)
    (f : β' ≃ β) (a a' : α') (b b' : β') :
    (K.reindex e f).map (Matrix.single a a' 1) b b' =
      K.map (Matrix.single (e a) (e a') 1) (f b) (f b') := by
  rw [KrausFamily.map_single_apply, KrausFamily.map_single_apply]
  rfl

omit [Fintype S] [DecidableEq S] in
/-- The local form of a unitary dilation: the partial trace over the environment of the
dilating family on a prepared matrix unit is the map of the family on the matrix unit. -/
private theorem sum_map_single_of_dilation {α β E F : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    {K : KrausFamily α β} {e₀ : E} {U : KrausFamily (α × E) (β × F)}
    (h : K.map = (KrausFamily.traceRight β F).map ∘ₗ U.map ∘ₗ
      (KrausFamily.embed ⟨fun a ↦ (a, e₀), fun _ _ h ↦ congrArg Prod.fst h⟩).map)
    (a a' : α) (b b' : β) :
    ∑ f : F, U.map (Matrix.single (a, e₀) (a', e₀) 1) (b, f) (b', f) =
      K.map (Matrix.single a a' 1) b b' := by
  have hJ : initializedBasisMatrix (⟨fun a ↦ (a, e₀), fun _ _ h ↦ congrArg Prod.fst h⟩ :
      α ↪ α × E) * Matrix.single a a' (1 : ℂ) * (initializedBasisMatrix
        (⟨fun a ↦ (a, e₀), fun _ _ h ↦ congrArg Prod.fst h⟩ : α ↪ α × E))ᴴ =
      Matrix.single (a, e₀) (a', e₀) (1 : ℂ) := by
    ext w w'
    have he : ∀ x : α, (⟨fun a ↦ (a, e₀), fun _ _ h ↦ congrArg Prod.fst h⟩ : α ↪ α × E) x =
        (x, e₀) := fun _ ↦ rfl
    simp only [mul_apply, conjTranspose_apply, initializedBasisMatrix, submatrix_apply, id,
      one_apply, Matrix.single_apply, he]
    simp only [ite_and, apply_ite star, star_one, star_zero, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.sum_eq_single a' (fun x _ hx ↦ by simp [Ne.symm hx]) (by simp)]
    by_cases h1 : w = (a, e₀) <;> by_cases h2 : w' = (a', e₀) <;>
      simp [h1, h2, eq_comm]
  rw [h, LinearMap.comp_apply, LinearMap.comp_apply, KrausFamily.map_traceRight,
    KrausFamily.map_embed_apply, hJ, partialTraceRight_apply]

/-- A layer of trace-preserving gates and onsite families on nonempty bases is dilated by one
layer of unitary gates on the same cells: every gate and onsite family is replaced by its
unitary dilation (`KrausFamily.IsTP.exists_unitary_dilation`), the environment of a gate placed
at the designated site of its cell. A gate on an empty cell acts on a one-element basis and is
replaced by the identity there. -/
theorem Layer.isUnitaryDilation [∀ s, Nonempty (X s)] (L : Layer Γ KrausGate X Y)
    (hL : L.Forall KrausGate.ev KrausFamily.IsTP) :
    IsUnitaryDilation Γ L.depth ((Circuit.ofLayer L).map KrausGate.ev) := by
  let : ∀ b : L.cells, DecidableEq (L.gateFamily KrausGate.ev b).Index :=
    fun _ ↦ Classical.decEq _
  let : ∀ t : L.Free, DecidableEq (L.onsite t).Index := fun _ ↦ Classical.decEq _
  have hTP : ∀ b, (L.gateFamily KrausGate.ev b).IsTP := hL.1
  choose eb Ub hUb hKb using fun b : L.cells ↦ (hTP b).exists_unitary_dilation
  choose es Us hUs hKs using fun t : L.Free ↦ (hL.2 t).exists_unitary_dilation
  let T : L.cells → Type := fun b ↦ RegionConfig Y (Γ.cell b) × (L.gateFamily KrausGate.ev b).Index
  let T₂ : L.cells → Type := fun b ↦
    RegionConfig X (Γ.cell b) × (L.gateFamily KrausGate.ev b).Index
  let T' : L.Free → Type := fun t ↦ Y t × (L.onsite t).Index
  let T₂' : L.Free → Type := fun t ↦ X t × (L.onsite t).Index
  let : ∀ s, DecidableEq (Distribute L T T' s) := fun _ ↦ Classical.decEq _
  let : ∀ s, DecidableEq (Distribute L T₂ T₂' s) := fun _ ↦ Classical.decEq _
  let e₀ : ∀ s, Distribute L T T' s := fun s ↦ (fun c ↦ eb c.1, fun t ↦ es t.1)
  let σX : ∀ (b : L.cells) (h : (Γ.cell b.1).Nonempty),
      RegionConfig (fun s ↦ X s × Distribute L T T' s) (Γ.cell b) ≃
        RegionConfig X (Γ.cell b) × T b := fun b h ↦
    (Equiv.arrowProdEquivProdArrow _ _ _).trans
      ((Equiv.refl _).prodCongr (distributeCellEquiv T T' b h))
  let σY : ∀ (b : L.cells) (h : (Γ.cell b.1).Nonempty),
      RegionConfig (fun s ↦ Y s × Distribute L T₂ T₂' s) (Γ.cell b) ≃
        RegionConfig Y (Γ.cell b) × T₂ b := fun b h ↦
    (Equiv.arrowProdEquivProdArrow _ _ _).trans
      ((Equiv.refl _).prodCongr (distributeCellEquiv T₂ T₂' b h))
  let U : Layer Γ KrausGate (fun s ↦ X s × Distribute L T T' s)
      (fun s ↦ Y s × Distribute L T₂ T₂' s) :=
    { cells := L.cells
      pairwiseDisjoint := L.pairwiseDisjoint
      gate := fun b ↦ if h : (Γ.cell b.1).Nonempty then (Ub b).reindex (σX b h) (σY b h)
        else KrausFamily.single (Matrix.of fun _ _ ↦ 1)
      onsite := fun t ↦ (Us t).reindex ((Equiv.refl _).prodCongr (distributeFreeEquiv T T' t))
        ((Equiv.refl _).prodCongr (distributeFreeEquiv T₂ T₂' t)) }
  refine ⟨Distribute L T T', Distribute L T₂ T₂', inferInstance, inferInstance, inferInstance,
    inferInstance, e₀, Circuit.ofLayer U, ?_, Circuit.isUnbranched_ofLayer _, ?_, ?_⟩
  · refine ⟨⟨fun b ↦ ?_, fun t ↦ (hUs t).reindex _ _⟩, fun _ ↦ trivial⟩
    change (if h : (Γ.cell b.1).Nonempty then (Ub b).reindex (σX b h) (σY b h)
      else KrausFamily.single (Matrix.of fun _ _ ↦ (1 : ℂ))).IsUnitary
    split_ifs with h
    · exact (hUb b).reindex _ _
    · have : IsEmpty {v // v ∈ Γ.cell b.1} := ⟨fun v ↦ h ⟨v.1, v.2⟩⟩
      refine ⟨⟨inferInstanceAs (Unique Unit)⟩, fun _ ↦ ⟨?_, ?_⟩⟩ <;> ext a a' <;>
        obtain rfl := Subsingleton.elim a a' <;> simp [mul_apply]
  · rw [Circuit.depth_ofLayer]
    rfl
  apply Matrix.ext_linearMap
  intro x x'
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Matrix.singleLinearMap_apply]
  have hP : (prepareCircuit Γ e₀).map KrausGate.ev (Matrix.single x x' 1) =
      Matrix.single (fun s ↦ (x s, e₀ s)) (fun s ↦ (x' s, e₀ s)) 1 := by
    have key : ∀ (z : Config X) (w : Config fun s ↦ X s × Distribute L T T' s),
        (fun s ↦ (z s, e₀ s)) = w ↔ (z = fun s ↦ (w s).1) ∧ (fun s ↦ (w s).2) = e₀ := by
      intro z w
      constructor
      · rintro rfl
        exact ⟨rfl, rfl⟩
      · rintro ⟨rfl, h⟩
        funext s
        exact Prod.ext rfl (congrFun h s).symm
    ext w w'
    rw [map_prepareCircuit_apply]
    simp only [Matrix.single_apply, key]
    by_cases h₁ : (fun s ↦ (w s).2) = e₀ <;> by_cases h₂ : (fun s ↦ (w' s).2) = e₀ <;>
      by_cases h₃ : x = (fun s ↦ (w s).1) <;> by_cases h₄ : x' = (fun s ↦ (w' s).1) <;>
      simp only [h₁, h₂, h₃, h₄, and_true, and_false, ite_true, ite_false]
  ext y y'
  rw [hP, Circuit.map_ofLayer, Layer.map_single_apply, map_traceCircuit_apply]
  simp only [Circuit.map_ofLayer, Layer.map_single_apply]
  refine Eq.trans ?_ (Fintype.sum_equiv (U.configEquiv (Distribute L T₂ T₂')) _
    (fun p ↦ (∏ b, (U.gateFamily KrausGate.ev b).map
      (Matrix.single (fun v ↦ (x v, e₀ v)) (fun v ↦ (x' v, e₀ v)) 1)
        (fun v ↦ (y v, p.1 b v)) (fun v ↦ (y' v, p.1 b v))) *
      ∏ t, (U.onsite t).map (Matrix.single (x t, e₀ t) (x' t, e₀ t) 1) (y t, p.2 t)
        (y' t, p.2 t)) fun f ↦ rfl).symm
  rw [Fintype.sum_prod_type]
  dsimp only
  rw [← Finset.sum_mul_sum]
  let Φ : (b : L.cells) → RegionConfig (Distribute L T₂ T₂') (Γ.cell b) → ℂ := fun b g ↦
    (U.gateFamily KrausGate.ev b).map
      (Matrix.single (fun v ↦ (x v, e₀ v)) (fun v ↦ (x' v, e₀ v)) 1)
        (fun v ↦ (y v, g v)) (fun v ↦ (y' v, g v))
  let Ψ : (t : L.Free) → Distribute L T₂ T₂' t → ℂ := fun t h ↦
    (U.onsite t).map (Matrix.single (x t, e₀ t) (x' t, e₀ t) 1) (y t, h) (y' t, h)
  change _ = (∑ i : (b : L.cells) → RegionConfig (Distribute L T₂ T₂') (Γ.cell b),
    ∏ b, Φ b (i b)) * ∑ j : (t : L.Free) → Distribute L T₂ T₂' t, ∏ t, Ψ t (j t)
  rw [← Fintype.prod_sum, ← Fintype.prod_sum]
  congr 1
  · refine Fintype.prod_congr _ _ fun b ↦ ?_
    by_cases h : (Γ.cell b.1).Nonempty
    · have hgate : U.gate b = (Ub b).reindex (σX b h) (σY b h) := by
        simp only [U, h, ↓reduceDIte]
      have hg : U.gateFamily KrausGate.ev b = (Ub b).reindex (σX b h) (σY b h) := by
        rw [Layer.gateFamily, hgate]
        rfl
      simp only [Φ, hg, map_reindex_single_apply]
      rw [← sum_map_single_of_dilation (hKb b)]
      exact (Fintype.sum_equiv (distributeCellEquiv T₂ T₂' b h) _ _ fun g ↦ rfl).symm
    · have : IsEmpty {v // v ∈ Γ.cell b.1} := ⟨fun v ↦ h ⟨v.1, v.2⟩⟩
      have hgate : U.gate b = KrausFamily.single (Matrix.of fun _ _ ↦ 1) := by
        simp only [U, h, ↓reduceDIte]
      have hg : U.gateFamily KrausGate.ev b = KrausFamily.single (Matrix.of fun _ _ ↦ 1) := by
        rw [Layer.gateFamily, hgate]
        rfl
      rw [Fintype.sum_unique]
      change _ = (U.gateFamily KrausGate.ev b).map _ _ _
      rw [hg, KrausFamily.map_single_apply, KrausFamily.map_single_apply]
      have hK := congrFun (congrFun (hTP b) (fun v ↦ x v)) (fun v ↦ x v)
      rw [KrausFamily.effect, Matrix.sum_apply, one_apply_eq] at hK
      have hx : (fun v : {v // v ∈ Γ.cell b.1} ↦ x' v) = fun v : {v // v ∈ Γ.cell b.1} ↦ x v :=
        Subsingleton.elim _ _
      have hy : (fun v : {v // v ∈ Γ.cell b.1} ↦ y' v) = fun v : {v // v ∈ Γ.cell b.1} ↦ y v :=
        Subsingleton.elim _ _
      rw [hx, hy]
      refine Eq.trans ?_ (Eq.trans hK ?_)
      · refine Fintype.sum_congr _ _ fun i ↦ ?_
        rw [mul_apply, Fintype.sum_unique, conjTranspose_apply, mul_comm]
        congr 3 <;> exact Subsingleton.elim _ _
      · simp only [KrausFamily.single]
        simp only [of_apply, star_one, Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast (rfl : (Finset.univ : Finset Unit).card = 1).symm
  · refine Fintype.prod_congr _ _ fun t ↦ ?_
    simp only [Ψ, U, map_reindex_single_apply]
    rw [← sum_map_single_of_dilation (hKs t)]
    exact (Fintype.sum_equiv (distributeFreeEquiv T₂ T₂' t) _ _ fun g ↦ rfl).symm

theorem IsUnitaryDilation.mono {T T' : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsUnitaryDilation Γ T Φ) (hT : T ≤ T') : IsUnitaryDilation Γ T' Φ := by
  obtain ⟨E, F, i₁, i₂, i₃, i₄, e₀, c, hu, hb, hd, hΦ⟩ := h
  exact ⟨E, F, i₁, i₂, i₃, i₄, e₀, c, hu, hb, hd.trans hT, hΦ⟩

/-- The identity is dilated by the empty circuit, with trivial environments. -/
theorem isUnitaryDilation_id : IsUnitaryDilation Γ 0
    (LinearMap.id : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config X) (Config X) ℂ) := by
  refine ⟨fun _ ↦ PUnit, fun _ ↦ PUnit, inferInstance, inferInstance, inferInstance,
    inferInstance, fun _ ↦ PUnit.unit, Circuit.done _, trivial, trivial, le_rfl, ?_⟩
  refine LinearMap.ext fun ρ ↦ ?_
  ext y y'
  simp only [LinearMap.comp_apply, Circuit.map_done, LinearMap.id_apply]
  rw [map_traceCircuit_apply, Fintype.sum_unique, map_prepareCircuit_apply,
    ite_eq_left_of_eq_true _ _ (eq_true ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩)]

/-- An unbranched circuit of trace-preserving gates and onsite families on nonempty input bases
is dilated by an unbranched circuit of unitary gates of no larger depth. -/
theorem Circuit.isUnitaryDilation : {X Z : S → Type} → [∀ s, Fintype (X s)] →
    [∀ s, DecidableEq (X s)] → [∀ s, Fintype (Z s)] → [∀ s, DecidableEq (Z s)] →
    [∀ s, Nonempty (X s)] → (c : Circuit Γ KrausGate X Z) →
    c.Forall KrausGate.ev KrausFamily.IsTP → c.IsUnbranched →
      IsUnitaryDilation Γ c.depth (c.map KrausGate.ev)
  | _, _, i₁, i₂, i₃, i₄, _, done _, _, _ => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    rw [Circuit.map_done]
    exact isUnitaryDilation_id
  | _, _, _, _, _, _, _, step L next, hc, hb => by
    have hc : L.Forall KrausGate.ev KrausFamily.IsTP ∧
        ∀ i, (next i).Forall KrausGate.ev KrausFamily.IsTP := hc
    have hb : (∀ i j, next i = next j) ∧ ∀ i, (next i).IsUnbranched := hb
    obtain ⟨i₀⟩ := L.nonempty_index_of_forall_isTP KrausGate.ev hc.1
    have := L.nonempty_output_of_forall_isTP KrausGate.ev hc.1
    rw [Circuit.step_eq_ofLayer_comp L hb.1 i₀, Circuit.map_comp]
    refine ((Layer.isUnitaryDilation L hc.1).comp
      (Circuit.isUnitaryDilation (next i₀) (hc.2 i₀) (hb.2 i₀))).mono ?_
    rw [← Circuit.step_eq_ofLayer_comp L hb.1 i₀, Circuit.depth_step]
    exact Nat.add_le_add_left (Finset.le_sup (f := fun i ↦ (next i).depth)
      (Finset.mem_univ i₀)) _

/-- Every protocol of depth at most `T` on nonempty input bases is the preparation of a product
of basis vectors on an environment at every site, an unbranched circuit of unitary gates of depth
at most `T` on the enlarged local systems, and the partial trace over the output environments.
The geometry, its cells and their costs are those of the protocol. -/
theorem IsProtocol.exists_unitary_dilation [∀ s, Nonempty (X s)] {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) :
    ∃ (E F : S → Type) (_ : ∀ s, Fintype (E s)) (_ : ∀ s, DecidableEq (E s))
      (_ : ∀ s, Fintype (F s)) (_ : ∀ s, DecidableEq (F s)) (e₀ : ∀ s, E s)
      (c : Circuit Γ KrausGate (fun s ↦ X s × E s) (fun s ↦ Z s × F s)),
      c.Forall KrausGate.ev KrausFamily.IsUnitary ∧ c.IsUnbranched ∧ c.depth ≤ T ∧
        Φ = (traceCircuit Γ Z F).map KrausGate.ev ∘ₗ c.map KrausGate.ev ∘ₗ
          (prepareCircuit Γ e₀).map KrausGate.ev := by
  obtain ⟨c, hc, hd, rfl, hb⟩ := h
  exact (Circuit.isUnitaryDilation c hc hb).mono hd

end Dilation

end QuantumCircuit
