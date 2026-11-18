/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.KrausFamilyEncoding
import QICLean.Circuit.Model.Protocol

/-!
# Encoding circuits into larger bases

Sitewise embeddings `e s : X s ↪ Y s` of bases encode a system into a larger one: the circuit
`encodeCircuit Γ e` is the onsite layer of the isometries `|x⟩ ↦ |e s x⟩`. A layer of
trace-preserving plain gates and onsite families is carried along such embeddings of its input
and output systems to a layer on the same cells, again trace-preserving, which acts as the layer
on the code (`Layer.exists_encoded`). Layer by layer, a circuit whose bases all have at most
`B ≤ q` elements is carried to a circuit of the same depth on the alphabet `Fin q` at every
site (`Circuit.exists_encoded_of_isDimBounded`).
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] (Γ : Geometry S)
  {X Y X' Y' : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (X' s)] [∀ s, DecidableEq (X' s)]
  [∀ s, Fintype (Y' s)] [∀ s, DecidableEq (Y' s)]

/-- The sitewise encoding along embeddings `e s : X s ↪ Y s`, as a circuit of one onsite
layer. -/
def encodeCircuit (e : ∀ s, X s ↪ Y s) : Circuit Γ KrausGate X Y :=
  Circuit.ofLayer (Layer.ofOnsite fun s ↦ KrausFamily.embed (e s))

variable {Γ}

/-- The circuit of an onsite layer of single operators is conjugation by their product. -/
private theorem map_ofLayer_ofOnsite_single (V : ∀ s, Matrix (Y s) (X s) ℂ)
    (ρ : Matrix (Config X) (Config X) ℂ) :
    (Circuit.ofLayer (Layer.ofOnsite (Γ := Γ) (G := KrausGate) fun s ↦
      KrausFamily.single (V s))).map KrausGate.ev ρ = prodOp V * ρ * (prodOp V)ᴴ := by
  set L : Layer Γ KrausGate X Y := Layer.ofOnsite fun s ↦ KrausFamily.single (V s)
  have hJ : ∀ i, L.kraus KrausGate.ev i = prodOp V := fun i ↦ Layer.kraus_ofOnsite _ _ i
  have : Subsingleton L.Index := ⟨fun i j ↦ Prod.ext
    (funext fun b : L.cells ↦ absurd b.2 (Finset.notMem_empty _))
    (funext fun _ ↦ Subsingleton.elim (α := Unit) _ _)⟩
  let i₀ : L.Index := (fun b ↦ absurd b.2 (Finset.notMem_empty _), fun _ ↦ ())
  rw [Circuit.map_ofLayer, KrausFamily.map_apply]
  refine (Fintype.sum_subsingleton _ i₀).trans ?_
  change L.kraus _ i₀ * ρ * (L.kraus _ i₀)ᴴ = _
  rw [hJ]

/-- The encoding is conjugation by the isometry of the product embedding. -/
private theorem map_encodeCircuit (e : ∀ s, X s ↪ Y s) (ρ : Matrix (Config X) (Config X) ℂ) :
    (encodeCircuit Γ e).map KrausGate.ev ρ =
      initializedBasisMatrix (Function.Embedding.piCongrRight e) * ρ *
        (initializedBasisMatrix (Function.Embedding.piCongrRight e))ᴴ := by
  have hJ : prodOp (fun s ↦ initializedBasisMatrix (e s)) =
      initializedBasisMatrix (Function.Embedding.piCongrRight e) := by
    ext y x
    simp [prodOp_apply, initializedBasisMatrix, one_apply, funext_iff, Finset.prod_ite_zero]
  rw [encodeCircuit, ← hJ]
  exact map_ofLayer_ofOnsite_single _ ρ

namespace Layer

/-- The layer `L` carried along embeddings `e` of its input and `f` of its output system, with
the fallback outputs `y₀`: on every cell and every free site, the family carried along the
embeddings (`KrausFamily.encode`). -/
private def encode (L : Layer Γ KrausGate X Y) (e : ∀ s, X s ↪ X' s) (f : ∀ s, Y s ↪ Y' s)
    (y₀ : ∀ s, Y' s) : Layer Γ KrausGate X' Y' where
  cells := L.cells
  pairwiseDisjoint := L.pairwiseDisjoint
  gate b := (L.gate b).encode (Function.Embedding.piCongrRight fun v ↦ e v)
    (Function.Embedding.piCongrRight fun v ↦ f v) fun v ↦ y₀ v
  onsite s := (L.onsite s).encode (e s) (f s) (y₀ s)

/-- The branches of the encoded layer that follow the layer. -/
private def encodeIndex (L : Layer Γ KrausGate X Y) (e : ∀ s, X s ↪ X' s)
    (f : ∀ s, Y s ↪ Y' s) (y₀ : ∀ s, Y' s) (p : L.Index) : (L.encode e f y₀).Index :=
  (fun b ↦ Sum.inl (p.1 b), fun s ↦ Sum.inl (p.2 s))

omit [Fintype S] [∀ s, DecidableEq (X s)] [∀ s, DecidableEq (Y s)] [∀ s, Fintype (Y' s)] in
private theorem encodeIndex_injective (L : Layer Γ KrausGate X Y) (e : ∀ s, X s ↪ X' s)
    (f : ∀ s, Y s ↪ Y' s) (y₀ : ∀ s, Y' s) : Function.Injective (L.encodeIndex e f y₀) :=
  fun _ _ h ↦ Prod.ext (funext fun b ↦ Sum.inl_injective (congrFun (congrArg Prod.fst h) b))
    (funext fun s ↦ Sum.inl_injective (congrFun (congrArg Prod.snd h) s))

/-- On the code, the encoded layer acts as the layer along the branches that follow it. -/
private theorem kraus_encode_mul (L : Layer Γ KrausGate X Y) (e : ∀ s, X s ↪ X' s)
    (f : ∀ s, Y s ↪ Y' s) (y₀ : ∀ s, Y' s) (p : L.Index) :
    (L.encode e f y₀).kraus KrausGate.ev (L.encodeIndex e f y₀ p) *
        initializedBasisMatrix (Function.Embedding.piCongrRight e) =
      initializedBasisMatrix (Function.Embedding.piCongrRight f) * L.kraus KrausGate.ev p := by
  ext y' x
  rw [mul_initializedBasisMatrix_apply]
  have hgate : ∀ b : L.cells, KrausGate.ev ((L.encode e f y₀).gate b) (Sum.inl (p.1 b))
      (fun v ↦ y' v) (fun v ↦ (Function.Embedding.piCongrRight e) x v) =
      (initializedBasisMatrix (Function.Embedding.piCongrRight fun v : {v // v ∈ Γ.cell b} ↦ f v)
        * KrausGate.ev (L.gate b) (p.1 b)) (fun v ↦ y' v) (fun v ↦ x v) := fun b ↦
    (mul_initializedBasisMatrix_apply _ _ _ _).symm.trans
      (congrFun (congrFun (KrausFamily.encode_op_inl_mul (L.gate b) _ _ _ (p.1 b)) _) _)
  have honsite : ∀ s : L.Free, ((L.encode e f y₀).onsite s).op (Sum.inl (p.2 s)) (y' s)
      ((Function.Embedding.piCongrRight e) x s) =
      (initializedBasisMatrix (f s) * (L.onsite s).op (p.2 s)) (y' s) (x s) := fun s ↦
    (mul_initializedBasisMatrix_apply _ _ _ _).symm.trans
      (congrFun (congrFun (KrausFamily.encode_op_inl_mul (L.onsite s) _ _ _ (p.2 s)) _) _)
  change (∏ b : L.cells, _) * (∏ s : L.Free, _) = _
  simp only [encodeIndex]
  rw [Finset.prod_congr rfl fun b _ ↦ hgate b, Finset.prod_congr rfl fun s _ ↦ honsite s]
  by_cases hy : y' ∈ Set.range (Function.Embedding.piCongrRight f)
  · obtain ⟨y, rfl⟩ := hy
    rw [initializedBasisMatrix_mul_apply_self]
    change _ = (∏ b : L.cells, _) * ∏ s : L.Free, _
    congr 1
    · exact Finset.prod_congr rfl fun b _ ↦
        initializedBasisMatrix_mul_apply_self
          (Function.Embedding.piCongrRight fun v : {v // v ∈ Γ.cell b} ↦ f v) _
          (fun v : {v // v ∈ Γ.cell b} ↦ y v) _
    · exact Finset.prod_congr rfl fun s _ ↦ initializedBasisMatrix_mul_apply_self (f s) _ _ _
  · rw [initializedBasisMatrix_mul_apply_of_notMem _ _ hy]
    obtain ⟨v, hv⟩ : ∃ v, y' v ∉ Set.range (f v) := by
      by_contra h
      push Not at h
      exact hy ⟨fun v ↦ (h v).choose, funext fun v ↦ (h v).choose_spec⟩
    by_cases hc : v ∈ L.cells.biUnion Γ.cell
    · obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hc
      refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ ⟨b, hb⟩) ?_) _
      exact initializedBasisMatrix_mul_apply_of_notMem _ _
        (fun ⟨z, hz⟩ ↦ hv ⟨z ⟨v, hvb⟩, congrFun hz ⟨v, hvb⟩⟩) _
    · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨v, hc⟩)
        (initializedBasisMatrix_mul_apply_of_notMem _ _ hv _))

omit [∀ s, DecidableEq (X s)] [∀ s, DecidableEq (Y s)] in
/-- On the code, the branches of the encoded layer that do not follow the layer vanish. -/
private theorem kraus_encode_mul_eq_zero (L : Layer Γ KrausGate X Y) (e : ∀ s, X s ↪ X' s)
    (f : ∀ s, Y s ↪ Y' s) (y₀ : ∀ s, Y' s) {p : (L.encode e f y₀).Index}
    (hp : p ∉ Set.range (L.encodeIndex e f y₀)) :
    (L.encode e f y₀).kraus KrausGate.ev p *
      initializedBasisMatrix (Function.Embedding.piCongrRight e) = 0 := by
  ext y' x
  rw [mul_initializedBasisMatrix_apply, Matrix.zero_apply]
  change (∏ b : L.cells, _) * (∏ s : L.Free, _) = 0
  by_cases hg : ∀ b, ∃ i, p.1 b = Sum.inl i
  · have ho : ¬∀ s, ∃ i, p.2 s = Sum.inl i := fun ho ↦ hp
      ⟨(fun b ↦ (hg b).choose, fun s ↦ (ho s).choose), Prod.ext
        (funext fun b ↦ (hg b).choose_spec.symm) (funext fun s ↦ (ho s).choose_spec.symm)⟩
    push Not at ho
    obtain ⟨s, hs⟩ := ho
    obtain ⟨a, ha⟩ : ∃ a, p.2 s = Sum.inr a := by
      cases h : p.2 s with
      | inl i => exact absurd h (hs i)
      | inr a => exact ⟨a, rfl⟩
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ s) ?_)
    change ((L.onsite s).encode (e s) (f s) (y₀ s)).op (p.2 s) (y' s) (e s (x s)) = 0
    rw [ha]
    exact (mul_initializedBasisMatrix_apply (e s) _ _ _).symm.trans
      (congrFun (congrFun (KrausFamily.encode_op_inr_mul _ _ _ _ a) _) _)
  · push Not at hg
    obtain ⟨b, hb⟩ := hg
    obtain ⟨a, ha⟩ : ∃ a, p.1 b = Sum.inr a := by
      cases h : p.1 b with
      | inl i => exact absurd h (hb i)
      | inr a => exact ⟨a, rfl⟩
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ b) ?_) _
    change ((L.gate b).encode (Function.Embedding.piCongrRight fun v ↦ e v)
      (Function.Embedding.piCongrRight fun v ↦ f v) fun v ↦ y₀ v).op (p.1 b) (fun v ↦ y' v)
        ((Function.Embedding.piCongrRight fun v : {v // v ∈ Γ.cell b} ↦ e v) fun v ↦ x v) = 0
    rw [ha]
    exact (mul_initializedBasisMatrix_apply _ _ _ _).symm.trans
      (congrFun (congrFun (KrausFamily.encode_op_inr_mul _ _ _ _ a) _) _)

/-- A layer of trace-preserving plain gates and onsite families on nonempty bases is carried
along embeddings `e` of its input and `f` of its output system to a layer on the same cells,
again trace-preserving, which acts as the layer on the code. The nonemptiness supplies a basis
vector of every output basis, to which the encoded layer sends the part of its input outside
the code. -/
theorem exists_encoded [∀ s, Nonempty (X s)] (L : Layer Γ KrausGate X Y)
    (hL : L.Forall KrausGate.ev KrausFamily.IsTP) (e : ∀ s, X s ↪ X' s) (f : ∀ s, Y s ↪ Y' s) :
    ∃ L' : Layer Γ KrausGate X' Y', L'.cells = L.cells ∧
      L'.Forall KrausGate.ev KrausFamily.IsTP ∧
      (Circuit.ofLayer L').map KrausGate.ev ∘ₗ (encodeCircuit Γ e).map KrausGate.ev =
        (encodeCircuit Γ f).map KrausGate.ev ∘ₗ (Circuit.ofLayer L).map KrausGate.ev := by
  have := L.nonempty_output_of_forall_isTP KrausGate.ev hL
  let y₀ : ∀ s, Y' s := fun s ↦ f s (Classical.arbitrary _)
  refine ⟨L.encode e f y₀, rfl, ⟨fun b ↦ (hL.1 b).encode _ _ _, fun s ↦ (hL.2 s).encode _ _ _⟩,
    LinearMap.ext fun ρ ↦ ?_⟩
  simp only [LinearMap.comp_apply, map_encodeCircuit, Circuit.map_ofLayer, KrausFamily.map_apply,
    Matrix.mul_sum, Matrix.sum_mul]
  refine (Fintype.sum_of_injective (L.encodeIndex e f y₀) (L.encodeIndex_injective e f y₀) _ _
    (fun p hp ↦ ?_) fun p ↦ ?_).symm
  · change (L.encode e f y₀).kraus _ p *
        (initializedBasisMatrix (Function.Embedding.piCongrRight e) * ρ *
          (initializedBasisMatrix (Function.Embedding.piCongrRight e))ᴴ) *
        ((L.encode e f y₀).kraus _ p)ᴴ = 0
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, kraus_encode_mul_eq_zero L e f y₀ hp]
    simp
  · change initializedBasisMatrix (Function.Embedding.piCongrRight f) *
        (L.kraus _ p * ρ * (L.kraus _ p)ᴴ) *
          (initializedBasisMatrix (Function.Embedding.piCongrRight f))ᴴ =
      (L.encode e f y₀).kraus _ (L.encodeIndex e f y₀ p) *
        (initializedBasisMatrix (Function.Embedding.piCongrRight e) * ρ *
          (initializedBasisMatrix (Function.Embedding.piCongrRight e))ᴴ) *
        ((L.encode e f y₀).kraus _ (L.encodeIndex e f y₀ p))ᴴ
    have h := L.kraus_encode_mul e f y₀ p
    calc _ = initializedBasisMatrix (Function.Embedding.piCongrRight f) * L.kraus KrausGate.ev p *
          ρ * (initializedBasisMatrix (Function.Embedding.piCongrRight f) *
            L.kraus KrausGate.ev p)ᴴ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by
          rw [← h]
          simp only [conjTranspose_mul, Matrix.mul_assoc]

end Layer

end QuantumCircuit
