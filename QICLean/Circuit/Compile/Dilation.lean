/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Data.Finset.Pairwise
import QICLean.Algebra.MatrixKroneckerExt
import QICLean.Channel.KrausFamilyDilation
import QICLean.Circuit.Compile.Encoding
import QICLean.Circuit.Core.LayerEntry
import QICLean.Circuit.Core.TensorRight

/-!
# Protocols as unitary circuits on enlarged sites

Every protocol is the preparation of a product of basis vectors on an environment at every
site, an unbranched circuit of unitary gates on the enlarged local systems of depth at most
that of the protocol, and the partial trace over the output environments
(`IsProtocol.isUnitaryDilation`). The geometry and its costs are those of the protocol; only the
local bases grow.

The proof is by layers (`Layer.isUnitaryDilation`). Every gate and onsite family is replaced by
its unitary dilation (`KrausFamily.IsTP.exists_unitary_dilation`, the construction in the proof
of Wolf, Thm. 2.5), whose environment is a single basis for the whole cell; it is placed at one
designated site of the cell (`Layer.IsRep`), the other sites of the cell carrying a one-element
basis (`Layer.Distribute`). A gate on an empty cell acts on a one-element basis, so by trace
preservation its map is the identity (`KrausFamily.IsTP.map_apply_of_subsingleton`) and it is
replaced by the identity. The map of a layer is the tensor product of the maps of its gates and
onsite families (`Layer.map_matrixUnit_apply`), and a sum over the environment configurations of
such a product factors (`Layer.sum_prod_mul_prod`), so the dilated layer, traced and prepared,
has the map of the layer. Dilations compose (`IsUnitaryDilation.comp`): the
environments of the later circuit are prepared at the start and carried through the earlier one
by `Circuit.tensorRight`, and those of the earlier circuit are carried through the later one;
the partial trace over an environment commutes with a circuit tensored with the identity on it
(`map_traceCircuit_map_tensorRight`), and depth-zero layers of relabellings regroup the local
products in between.

## Main definitions

* `QuantumCircuit.prepareCircuit` — the preparation of the environments in basis vectors.
* `QuantumCircuit.traceCircuit` — the partial trace over the environments.
* `QuantumCircuit.relabelCircuit` — the relabelling of the local bases along equivalences.
* `QuantumCircuit.Layer.IsRep`, `QuantumCircuit.Layer.Distribute` — the designated site of a
  cell and the environments of the cells placed at their designated sites.
* `QuantumCircuit.IsUnitaryDilation` — a map is the partial trace of an unbranched unitary
  circuit of bounded depth on prepared environments.

## Main results

* `QuantumCircuit.IsProtocol.isUnitaryDilation` — the unitary dilation of a protocol.
* `QuantumCircuit.Circuit.isUnitaryDilation` — the same for an unbranched circuit of
  trace-preserving gates.
* `QuantumCircuit.Layer.isUnitaryDilation` — one layer.
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
  encodeCircuit Γ fun s ↦ Function.Embedding.sectL (X s) (e₀ s)

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
        Function.Embedding.sectL (X s) (e₀ s)) x ↔
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
      simp only [initializedBasisMatrix, conjTranspose_apply, submatrix_apply, id, one_apply]
      exact (congrArg star (ite_eq_left rfl)).trans (star_one ℂ)
    · obtain ⟨s, hs⟩ := Function.ne_iff.mp h
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      simp only [initializedBasisMatrix, conjTranspose_apply, submatrix_apply, id, one_apply]
      exact (congrArg star (ite_eq_right hs)).trans (star_zero ℂ)
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
  rw [relabelCircuit, map_encodeCircuit,
    show Function.Embedding.piCongrRight (fun s ↦ (σ s).toEmbedding) =
      (Equiv.piCongrRight σ).toEmbedding from rfl,
    initializedBasisMatrix_equiv_mul_mul_conjTranspose]
  rfl

omit [Fintype S] in
theorem forall_isUnitary_relabelCircuit (σ : ∀ s, X s ≃ Y s) :
    (relabelCircuit Γ σ).Forall KrausGate.ev KrausFamily.IsUnitary :=
  ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun s ↦
    (KrausFamily.isUnitary_single (one_mem _)).reindex (σ s.1) (Equiv.refl _)⟩, fun _ ↦ trivial⟩

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

/-- The partial trace over `F` commutes with a circuit tensored with the identity on `F`. -/
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

namespace Layer

section Distribute

variable {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G] {X Y : S → Type}
  {Γ} (L : Layer Γ G X Y)

/-- The site `s` is the designated site of the cell `b`, a site chosen in the nonempty cell. -/
def IsRep (b : L.cells) (s : S) : Prop :=
  ∃ h : (Γ.cell b.1).Nonempty, h.choose = s

/-- The cells a site is designated for, decided classically. -/
@[instance_reducible] noncomputable def decIsRep (s : S) : DecidablePred fun b ↦ L.IsRep b s :=
  Classical.decPred _

attribute [local instance] decIsRep

variable {L}

omit [Fintype S] [GateFamily G] in
theorem IsRep.mem {b : L.cells} {s : S} (h : L.IsRep b s) : s ∈ Γ.cell b.1 := by
  obtain ⟨h, rfl⟩ := h
  exact h.choose_spec

omit [Fintype S] [GateFamily G] in
/-- A site is the designated site of at most the one cell containing it. -/
theorem IsRep.eq {b c : L.cells} {s : S} (h : L.IsRep c s) (hb : s ∈ Γ.cell b.1) : c = b :=
  Subtype.ext (Set.PairwiseDisjoint.elim_finset L.pairwiseDisjoint c.2 b.2 s h.mem hb)

omit [Fintype S] [GateFamily G] in
theorem not_isRep_of_free {c : L.cells} (t : L.Free) : ¬ L.IsRep c t.1 :=
  fun h ↦ t.2 (Finset.subset_biUnion_of_mem Γ.cell c.2 h.mem)

variable (L) in
/-- Types `T b` on the cells and `T' t` at the free sites of a layer, as a system: the site `s`
carries `T b` for the cells `b` it is designated for, at most one, and `T' t` if it is the free
site `t`. -/
abbrev Distribute (T : L.cells → Type) (T' : L.Free → Type) (s : S) : Type :=
  ((c : {c : L.cells // L.IsRep c s}) → T c.1) × ((t : {t : L.Free // t.1 = s}) → T' t.1)

omit [Fintype S] [GateFamily G] in
/-- On a nonempty cell `b` the distributed system is `T b`. -/
noncomputable def distributeCellEquiv (T : L.cells → Type) (T' : L.Free → Type) (b : L.cells)
    (h : (Γ.cell b.1).Nonempty) : RegionConfig (L.Distribute T T') (Γ.cell b) ≃ T b where
  toFun φ := (φ ⟨h.choose, h.choose_spec⟩).1 ⟨b, h, rfl⟩
  invFun t v := (fun c ↦ cast (congrArg T (c.2.eq v.2).symm) t,
    fun t' ↦ (t'.1.2 (by rw [t'.2]; exact Finset.subset_biUnion_of_mem Γ.cell b.2 v.2)).elim)
  left_inv φ := by
    funext ⟨v, hvb⟩
    refine Prod.ext (funext fun ⟨c, hcv⟩ ↦ ?_) (funext fun t' ↦ ?_)
    · obtain rfl : c = b := hcv.eq hvb
      have key : ∀ (w : S) (hw : w ∈ Γ.cell c.1) (_ : w = h.choose) (p : L.IsRep c w),
          cast (congrArg T (p.eq hw).symm) ((φ ⟨h.choose, h.choose_spec⟩).1 ⟨c, h, rfl⟩) =
            (φ ⟨w, hw⟩).1 ⟨c, p⟩ := by
        rintro w hw rfl p
        rfl
      exact key v hvb hcv.2.symm hcv
    · exact (t'.1.2 (by rw [t'.2]; exact Finset.subset_biUnion_of_mem Γ.cell b.2 hvb)).elim
  right_inv t := rfl

omit [Fintype S] [GateFamily G] in
/-- At a free site `t` the distributed system is `T' t`. -/
def distributeFreeEquiv (T : L.cells → Type) (T' : L.Free → Type) (t : L.Free) :
    L.Distribute T T' t.1 ≃ T' t where
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

end Layer

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
    refine (Circuit.depth_comp _ _).trans (add_le_add ((Circuit.depth_tensorRight _ _).trans_le hd₁)
      ((Circuit.depth_comp _ _).trans ?_))
    rw [depth_relabelCircuit, zero_add]
    refine (Circuit.depth_comp _ _).trans ?_
    rw [depth_relabelCircuit, add_zero]
    exact (Circuit.depth_tensorRight _ _).trans_le hd₂
  · refine LinearMap.ext fun ρ ↦ ?_
    simp only [LinearMap.comp_apply, Circuit.map_comp, R₁, R₂, R₃]
    rw [map_relabel_prepare, Circuit.map_tensorRight, map_trace_relabel,
      map_traceCircuit_map_tensorRight, map_trace_relabel_prepare]

omit [Fintype S] [DecidableEq S] in
/-- The local form of a unitary dilation: the partial trace over the environment of the
dilating family on a prepared matrix unit is the map of the family on the matrix unit. -/
private theorem sum_map_matrixUnit_of_dilation {α β E F : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]
    {K : KrausFamily α β} {e₀ : E} {U : KrausFamily (α × E) (β × F)}
    (h : K.map = (KrausFamily.traceRight β F).map ∘ₗ U.map ∘ₗ
      (KrausFamily.embed (Function.Embedding.sectL α e₀)).map)
    (a a' : α) (b b' : β) :
    ∑ f : F, U.map (Matrix.single (a, e₀) (a', e₀) 1) (b, f) (b', f) =
      K.map (Matrix.single a a' 1) b b' := by
  rw [h, LinearMap.comp_apply, LinearMap.comp_apply, KrausFamily.map_traceRight,
    KrausFamily.map_embed_apply, initializedBasisMatrix_mul_single_mul_conjTranspose,
    partialTraceRight_apply]
  rfl

omit [Fintype S] [DecidableEq S] in
/-- The one operator with all entries `1` between one-element bases is unitary. -/
private theorem isUnitary_single_ones {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Unique α] [Unique β] :
    (KrausFamily.single (Matrix.of fun (_ : β) (_ : α) ↦ (1 : ℂ))).IsUnitary :=
  ⟨⟨inferInstanceAs (Unique Unit)⟩, fun _ ↦
    ⟨by ext a a'; rw [Subsingleton.elim a' a]; simp [mul_apply],
      by ext a a'; rw [Subsingleton.elim a' a]; simp [mul_apply]⟩⟩

namespace Layer

attribute [local instance] decIsRep

variable (L : Layer Γ KrausGate X Y) {T T₂ : L.cells → Type} {T' T₂' : L.Free → Type}

/-- The enlarged configurations of a nonempty cell `b`: the configurations of the system and the
environment `T b` of its gate. -/
private noncomputable def cellEquiv {W : S → Type} (T : L.cells → Type) (T' : L.Free → Type)
    (b : L.cells) (h : (Γ.cell b.1).Nonempty) :
    RegionConfig (fun s ↦ W s × L.Distribute T T' s) (Γ.cell b) ≃
      RegionConfig W (Γ.cell b) × T b :=
  (Equiv.arrowProdEquivProdArrow _ _ _).trans ((Equiv.refl _).prodCongr
    (distributeCellEquiv T T' b h))

/-- The layer of the families `Ub b` on the nonempty cells and `Us t` at the free sites, each on
the system and its environment, and of the identity on the empty cells. -/
private noncomputable abbrev dilate
    (Ub : ∀ b : L.cells,
      KrausFamily (RegionConfig X (Γ.cell b) × T b) (RegionConfig Y (Γ.cell b) × T₂ b))
    (Us : ∀ t : L.Free, KrausFamily (X t × T' t) (Y t × T₂' t)) :
    Layer Γ KrausGate (fun s ↦ X s × L.Distribute T T' s)
      (fun s ↦ Y s × L.Distribute T₂ T₂' s) where
  cells := L.cells
  pairwiseDisjoint := L.pairwiseDisjoint
  gate b := if h : (Γ.cell b.1).Nonempty then
      (Ub b).reindex (L.cellEquiv T T' b h) (L.cellEquiv T₂ T₂' b h)
    else
      KrausFamily.single (Matrix.of fun _ _ ↦ 1)
  onsite t := (Us t).reindex ((Equiv.refl _).prodCongr (distributeFreeEquiv T T' t))
    ((Equiv.refl _).prodCongr (distributeFreeEquiv T₂ T₂' t))

variable {Ub : ∀ b : L.cells,
    KrausFamily (RegionConfig X (Γ.cell b) × T b) (RegionConfig Y (Γ.cell b) × T₂ b)}
  {Us : ∀ t : L.Free, KrausFamily (X t × T' t) (Y t × T₂' t)}

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
private theorem dilate_gate_of_nonempty {b : L.cells} (h : (Γ.cell b.1).Nonempty) :
    (L.dilate Ub Us).gate b =
      (Ub b).reindex (L.cellEquiv T T' b h) (L.cellEquiv T₂ T₂' b h) := by
  simp only [dilate, h, ↓reduceDIte]

omit [Fintype S] [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Y s)]
  [∀ s, DecidableEq (Y s)] in
private theorem dilate_gate_of_not_nonempty {b : L.cells} (h : ¬ (Γ.cell b.1).Nonempty) :
    (L.dilate Ub Us).gate b = KrausFamily.single (Matrix.of fun _ _ ↦ 1) := by
  simp only [dilate, h, ↓reduceDIte]

variable [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] [∀ b, Fintype (T₂ b)]
  [∀ b, DecidableEq (T₂ b)] [∀ t, Fintype (T' t)] [∀ t, DecidableEq (T' t)]
  [∀ t, Fintype (T₂' t)] [∀ t, DecidableEq (T₂' t)]
  [∀ s, DecidableEq (L.Distribute T T' s)] [∀ s, DecidableEq (L.Distribute T₂ T₂' s)]


private theorem forall_isUnitary_dilate (hb : ∀ b, (Ub b).IsUnitary)
    (ht : ∀ t, (Us t).IsUnitary) : (L.dilate Ub Us).Forall KrausGate.ev KrausFamily.IsUnitary := by
  refine ⟨fun b ↦ ?_, fun t ↦ (ht t).reindex _ _⟩
  rw [gateFamily_krausGate]
  by_cases h : (Γ.cell b.1).Nonempty
  · rw [L.dilate_gate_of_nonempty h]
    exact (hb b).reindex _ _
  · rw [L.dilate_gate_of_not_nonempty h]
    have : IsEmpty {v // v ∈ Γ.cell b.1} :=
      Finset.isEmpty_coe_sort.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    exact isUnitary_single_ones

/-- The dilated layer, prepared and traced, has the map of the layer when every family `Ub b` on
a nonempty cell and every `Us t` dilates the corresponding gate or onsite family of the layer. -/
private theorem map_dilate (hTP : ∀ b, (L.gate b).IsTP) (eb : ∀ b, T b) (es : ∀ t, T' t)
    (hKb : ∀ b, (Γ.cell b.1).Nonempty → (L.gate b).map =
      (KrausFamily.traceRight _ (T₂ b)).map ∘ₗ (Ub b).map ∘ₗ
        (KrausFamily.embed (Function.Embedding.sectL _ (eb b))).map)
    (hKs : ∀ t, (L.onsite t).map = (KrausFamily.traceRight _ (T₂' t)).map ∘ₗ (Us t).map ∘ₗ
      (KrausFamily.embed (Function.Embedding.sectL _ (es t))).map) :
    (Circuit.ofLayer L).map KrausGate.ev =
      (traceCircuit Γ Y (L.Distribute T₂ T₂')).map KrausGate.ev ∘ₗ
        (Circuit.ofLayer (L.dilate Ub Us)).map KrausGate.ev ∘ₗ
          (prepareCircuit Γ fun s ↦ ((fun c ↦ eb c.1, fun t ↦ es t.1) :
            L.Distribute T T' s)).map KrausGate.ev := by
  let e₀ : ∀ s, L.Distribute T T' s := fun s ↦ (fun c ↦ eb c.1, fun t ↦ es t.1)
  apply Matrix.ext_linearMap
  intro x x'
  apply LinearMap.ext_ring
  ext y y'
  simp only [LinearMap.comp_apply, Matrix.singleLinearMap_apply, prepareCircuit,
    map_encodeCircuit, initializedBasisMatrix_mul_single_mul_conjTranspose, map_traceCircuit_apply,
    Circuit.map_ofLayer, map_matrixUnit_apply, gateFamily_krausGate]
  refine Eq.trans ?_ ((L.dilate Ub Us).sum_prod_mul_prod (F := L.Distribute T₂ T₂')
    (fun b g ↦ ((L.dilate Ub Us).gate b).map
      (Matrix.single (fun v ↦ (x v, e₀ v)) (fun v ↦ (x' v, e₀ v)) 1)
      (fun v ↦ (y v, g v)) (fun v ↦ (y' v, g v)))
    (fun t g ↦ ((L.dilate Ub Us).onsite t).map (Matrix.single (x t, e₀ t) (x' t, e₀ t) 1)
      (y t, g) (y' t, g))).symm
  congr 1
  · refine Fintype.prod_congr _ _ fun b ↦ ?_
    by_cases h : (Γ.cell b.1).Nonempty
    · rw [L.dilate_gate_of_nonempty h, ← sum_map_matrixUnit_of_dilation (hKb b h)]
      refine (Fintype.sum_equiv (distributeCellEquiv T₂ T₂' b h) _ _ fun g ↦ ?_).symm
      rw [KrausFamily.map_matrixUnit_apply, KrausFamily.map_matrixUnit_apply]
      rfl
    · have : IsEmpty {v // v ∈ Γ.cell b.1} :=
        Finset.isEmpty_coe_sort.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
      rw [L.dilate_gate_of_not_nonempty h,
        (hTP b).map_apply_of_subsingleton _ (fun v : {v // v ∈ Γ.cell b.1} ↦ x v)
          (fun v : {v // v ∈ Γ.cell b.1} ↦ x' v), Fintype.sum_unique,
        isUnitary_single_ones.isTP.map_apply_of_subsingleton _
          (fun v : {v // v ∈ Γ.cell b.1} ↦ (x v, e₀ v))
          (fun v : {v // v ∈ Γ.cell b.1} ↦ (x' v, e₀ v)), single_apply_same, single_apply_same]
  · refine Fintype.prod_congr _ _ fun t ↦ ?_
    rw [← sum_map_matrixUnit_of_dilation (hKs t)]
    refine (Fintype.sum_equiv (distributeFreeEquiv T₂ T₂' t) _ _ fun g ↦ ?_).symm
    rw [KrausFamily.map_matrixUnit_apply, KrausFamily.map_matrixUnit_apply]
    rfl

end Layer

/-- A layer of trace-preserving gates and onsite families on nonempty bases has a unitary
dilation of its own depth. The dilating circuit is one layer on the same cells: every gate and
onsite family is replaced by its unitary dilation (`KrausFamily.IsTP.exists_unitary_dilation`),
the environment of a gate placed at the designated site of its cell, and a gate on an empty
cell, which acts on a one-element basis, by the identity. -/
theorem Layer.isUnitaryDilation [∀ s, Nonempty (X s)] (L : Layer Γ KrausGate X Y)
    (hL : L.Forall KrausGate.ev KrausFamily.IsTP) :
    IsUnitaryDilation Γ L.depth ((Circuit.ofLayer L).map KrausGate.ev) := by
  let : ∀ b : L.cells, DecidableEq (L.gate b).Index := fun _ ↦ Classical.decEq _
  let : ∀ t : L.Free, DecidableEq (L.onsite t).Index := fun _ ↦ Classical.decEq _
  let := Layer.decIsRep L
  have hTP : ∀ b, (L.gate b).IsTP := hL.1
  choose eb Ub hUb hKb using fun b : L.cells ↦ (hTP b).exists_unitary_dilation
  choose es Us hUs hKs using fun t : L.Free ↦ (hL.2 t).exists_unitary_dilation
  let T : L.cells → Type := fun b ↦ RegionConfig Y (Γ.cell b) × (L.gate b).Index
  let T₂ : L.cells → Type := fun b ↦ RegionConfig X (Γ.cell b) × (L.gate b).Index
  let T' : L.Free → Type := fun t ↦ Y t × (L.onsite t).Index
  let T₂' : L.Free → Type := fun t ↦ X t × (L.onsite t).Index
  let : ∀ s, DecidableEq (L.Distribute T T' s) := fun _ ↦ Classical.decEq _
  let : ∀ s, DecidableEq (L.Distribute T₂ T₂' s) := fun _ ↦ Classical.decEq _
  exact ⟨L.Distribute T T', L.Distribute T₂ T₂', inferInstance, inferInstance, inferInstance,
    inferInstance, fun s ↦ (fun c ↦ eb c.1, fun t ↦ es t.1), Circuit.ofLayer (L.dilate Ub Us),
    ⟨forall_isUnitary_dilate (L := L) hUb hUs, fun _ ↦ trivial⟩, Circuit.isUnbranched_ofLayer _,
    (Circuit.depth_ofLayer (L.dilate Ub Us)).trans_le le_rfl,
    map_dilate (L := L) hTP eb es (fun b _ ↦ hKb b) hKs⟩

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

/-- Every protocol of depth at most `T` on nonempty input bases has a unitary dilation of depth
`T`: there are bases `E s` and `F s` at every site, basis vectors `e₀ s ∈ E s` and an unbranched
circuit `c` of unitary gates and onsite families of depth at most `T` on the same geometry, from
`fun s ↦ X s × E s` to `fun s ↦ Z s × F s`, with `Φ ρ = tr_F (c (ρ ⊗ |e₀⟩⟨e₀|))`. -/
theorem IsProtocol.isUnitaryDilation [∀ s, Nonempty (X s)] {T : ℕ}
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsProtocol Γ T Φ) : IsUnitaryDilation Γ T Φ := by
  obtain ⟨c, hc, hd, rfl, hb⟩ := h
  exact (Circuit.isUnitaryDilation c hc hb).mono hd

end Dilation

end QuantumCircuit
