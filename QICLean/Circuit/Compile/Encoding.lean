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
`encodeCircuit Γ e` is the onsite layer of the isometries `|x⟩ ↦ |e s x⟩`, and the circuit
`decodeCircuit Γ e x₀` of the decodings with fallback basis vectors `x₀ s` is a left inverse of
it. A layer of trace-preserving plain gates and onsite families is carried along such
embeddings of its input and output systems to a layer on the same cells, again
trace-preserving, which acts as the layer on the code (`Layer.exists_encoded`). Layer by layer,
a circuit whose bases all have between `1` and `B ≤ q` elements is carried to a circuit of the
same depth on the alphabet `Fin q` at every site (`Circuit.exists_encoded_of_isDimBounded`).

This is not an instance of `Circuit.exists_substitute`: an embedding into `Fin q` exists only
for bases of at most `q` elements, so the encoding of a layer needs the dimension bound along
the circuit, and the encoded circuit keeps the branching of the circuit.

## Main definitions

* `QuantumCircuit.encodeCircuit` — the sitewise encoding along embeddings of bases.
* `QuantumCircuit.decodeCircuit` — the sitewise decoding, with fallback basis vectors.

## Main results

* `QuantumCircuit.map_encodeCircuit` — the encoding is conjugation by the product embedding.
* `QuantumCircuit.map_encodeCircuit_congr`, `QuantumCircuit.map_encodeCircuit_trans` — the
  encoding does not depend on the geometry, and composite embeddings encode in two steps.
* `QuantumCircuit.map_decodeCircuit_comp_map_encodeCircuit` — decoding after encoding is the
  identity.
* `QuantumCircuit.Layer.exists_encoded` — the encoding of a layer.
* `QuantumCircuit.Circuit.exists_encoded_of_isDimBounded` — the encoding of a circuit with
  bounded bases into a constant alphabet.
* `QuantumCircuit.IsBoundedProtocol.exists_encoded` — the same for bounded protocols.

The declarations restate the encodings of `TNLean/Circuit/Channel/OnsiteRegisterEncoding.lean`,
`TNLean/Circuit/Channel/EncodedChannelLayer.lean` and
`TNLean/Circuit/Channel/EncodedChannelProtocol.lean` at commit
`75fc22288234ef66239cb4c2fa0b22914cfa5c6b` (Apache-2.0). The changes: the encodings are
circuits of one onsite layer on any geometry instead of products of maps on a ring of registers;
a layer is encoded on its own cells with explicit Kraus operators instead of through a pair of
sites; the circuit theorem allows any codes of the input and output, keeps the depth and the
branching, and replaces the words of fixed-register operations by circuits.
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

/-- The encoding is conjugation by the isometry of the product embedding. -/
theorem map_encodeCircuit (e : ∀ s, X s ↪ Y s) (ρ : Matrix (Config X) (Config X) ℂ) :
    (encodeCircuit Γ e).map KrausGate.ev ρ =
      basisInclusion (Function.Embedding.piCongrRight e) * ρ *
        (basisInclusion (Function.Embedding.piCongrRight e))ᴴ := by
  rw [encodeCircuit, ← prodOp_basisInclusion]
  exact Circuit.map_ofLayer_ofOnsite_single _ _ ρ

/-- The map of an encoding does not depend on the geometry the circuit is written on. -/
theorem map_encodeCircuit_congr (Γ' : Geometry S) (e : ∀ s, X s ↪ Y s) :
    (encodeCircuit Γ e).map KrausGate.ev = (encodeCircuit Γ' e).map KrausGate.ev :=
  LinearMap.ext fun ρ ↦ by rw [map_encodeCircuit, map_encodeCircuit]

/-- Encoding along composite embeddings is the encoding along the first followed by the encoding
along the second. -/
theorem map_encodeCircuit_trans (e : ∀ s, X s ↪ Y s) (g : ∀ s, Y s ↪ Y' s) :
    (encodeCircuit Γ fun s ↦ (e s).trans (g s)).map KrausGate.ev =
      (encodeCircuit Γ g).map KrausGate.ev ∘ₗ (encodeCircuit Γ e).map KrausGate.ev := by
  refine LinearMap.ext fun ρ ↦ ?_
  have h : Function.Embedding.piCongrRight (fun s ↦ (e s).trans (g s)) =
      (Function.Embedding.piCongrRight e).trans (Function.Embedding.piCongrRight g) := rfl
  rw [LinearMap.comp_apply, map_encodeCircuit, map_encodeCircuit, map_encodeCircuit, h,
    ← initializedBasisMatrix_mul_initializedBasisMatrix]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

variable (Γ) in
/-- The sitewise decoding along embeddings `e s : X s ↪ Y s` with fallback basis vectors
`x₀ s`, as a circuit of one onsite layer. -/
def decodeCircuit (e : ∀ s, X s ↪ Y s) (x₀ : ∀ s, X s) : Circuit Γ KrausGate Y X :=
  Circuit.ofLayer (Layer.ofOnsite fun s ↦ KrausFamily.decode (e s) (x₀ s))

/-- Decoding after encoding is the identity. -/
theorem map_decodeCircuit_comp_map_encodeCircuit (e : ∀ s, X s ↪ Y s) (x₀ : ∀ s, X s) :
    (decodeCircuit Γ e x₀).map KrausGate.ev ∘ₗ (encodeCircuit Γ e).map KrausGate.ev =
      LinearMap.id := by
  refine LinearMap.ext fun ρ ↦ ?_
  set L : Layer Γ KrausGate Y X := Layer.ofOnsite fun s ↦ KrausFamily.decode (e s) (x₀ s)
  set P := prodOp fun s ↦ basisInclusion (e s)
  have hK : ∀ i, L.kraus KrausGate.ev i * P = prodOp fun s ↦
      (KrausFamily.decode (e s) (x₀ s)).op (i.2 ⟨s, by simp [L, Layer.ofOnsite]⟩) *
        basisInclusion (e s) := fun i ↦ by
    rw [Layer.kraus_ofOnsite, prodOp_mul]
  have hconj : ∀ i, L.kraus KrausGate.ev i * (P * ρ * Pᴴ) * (L.kraus KrausGate.ev i)ᴴ =
      (L.kraus KrausGate.ev i * P) * ρ * (L.kraus KrausGate.ev i * P)ᴴ := fun i ↦ by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  let i₁ : L.Index := (fun b ↦ absurd b.2 (Finset.notMem_empty _), fun _ ↦ Sum.inl ())
  rw [LinearMap.comp_apply, map_encodeCircuit, ← prodOp_basisInclusion, decodeCircuit,
    Circuit.ofLayer, Circuit.map_step, LinearMap.id_apply]
  simp only [Circuit.map_done, LinearMap.id_apply]
  rw [Finset.sum_eq_single i₁ (fun i _ hi ↦ ?_) fun h ↦ absurd (Finset.mem_univ _) h, hconj]
  · rw [hK]
    simp only [i₁, KrausFamily.decode_op_inl_mul, prodOp_one, Matrix.one_mul, conjTranspose_one,
      Matrix.mul_one]
  · obtain ⟨s, b, hb⟩ : ∃ s : S, ∃ b : {c // c ∉ Set.range (e s)},
        i.2 ⟨s, by simp [L, Layer.ofOnsite]⟩ = (Sum.inr b : Unit ⊕ {c // c ∉ Set.range (e s)}) := by
      by_contra h
      push Not at h
      refine hi (Prod.ext (funext fun b ↦ absurd b.2 (Finset.notMem_empty _)) (funext fun s ↦ ?_))
      cases h' : i.2 s with
      | inl u => rfl
      | inr b => exact absurd h' (h s.1 b)
    have h0 : L.kraus KrausGate.ev i * P = 0 := by
      rw [hK]
      ext y x
      rw [prodOp_apply, Matrix.zero_apply]
      refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
      rw [hb, KrausFamily.decode_op_inr_mul, Matrix.zero_apply]
    rw [hconj, h0]
    simp

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
        basisInclusion (Function.Embedding.piCongrRight e) =
      basisInclusion (Function.Embedding.piCongrRight f) * L.kraus KrausGate.ev p := by
  ext y' x
  rw [mul_basisInclusion_apply]
  have hgate : ∀ b : (L.encode e f y₀).cells,
      KrausGate.ev ((L.encode e f y₀).gate b) (Sum.inl (p.1 b))
      (fun v ↦ y' v) (fun v ↦ (Function.Embedding.piCongrRight e) x v) =
      (basisInclusion (Function.Embedding.piCongrRight fun v : {v // v ∈ Γ.cell b} ↦ f v)
        * KrausGate.ev (L.gate b) (p.1 b)) (fun v ↦ y' v) (fun v ↦ x v) := fun b ↦
    (mul_basisInclusion_apply _ _ _ _).symm.trans
      (congrFun (congrFun (KrausFamily.encode_op_inl_mul (L.gate b) _ _ _ (p.1 b)) _) _)
  have honsite : ∀ s : (L.encode e f y₀).Free,
      ((L.encode e f y₀).onsite s).op (Sum.inl (p.2 s)) (y' s)
      ((Function.Embedding.piCongrRight e) x s) =
      (basisInclusion (f s) * (L.onsite s).op (p.2 s)) (y' s) (x s) := fun s ↦
    (mul_basisInclusion_apply _ _ _ _).symm.trans
      (congrFun (congrFun (KrausFamily.encode_op_inl_mul (L.onsite s) _ _ _ (p.2 s)) _) _)
  rw [Layer.kraus_apply]
  simp only [encodeIndex]
  rw [Finset.prod_congr rfl fun b _ ↦ hgate b, Finset.prod_congr rfl fun s _ ↦ honsite s]
  by_cases hy : y' ∈ Set.range (Function.Embedding.piCongrRight f)
  · obtain ⟨y, rfl⟩ := hy
    rw [basisInclusion_mul_apply_self, Layer.kraus_apply]
    congr 1
    · exact Finset.prod_congr rfl fun b _ ↦
        basisInclusion_mul_apply_self
          (Function.Embedding.piCongrRight fun v : {v // v ∈ Γ.cell b} ↦ f v) _
          (fun v : {v // v ∈ Γ.cell b} ↦ y v) _
    · exact Finset.prod_congr rfl fun s _ ↦ basisInclusion_mul_apply_self (f s) _ _ _
  · rw [basisInclusion_mul_apply_of_notMem _ _ hy]
    obtain ⟨v, hv⟩ : ∃ v, y' v ∉ Set.range (f v) := by
      by_contra h
      push Not at h
      exact hy ⟨fun v ↦ (h v).choose, funext fun v ↦ (h v).choose_spec⟩
    by_cases hc : v ∈ L.cells.biUnion Γ.cell
    · obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hc
      refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ ⟨b, hb⟩) ?_) _
      exact basisInclusion_mul_apply_of_notMem _ _
        (fun ⟨z, hz⟩ ↦ hv ⟨z ⟨v, hvb⟩, congrFun hz ⟨v, hvb⟩⟩) _
    · exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨v, hc⟩)
        (basisInclusion_mul_apply_of_notMem _ _ hv _))

omit [∀ s, DecidableEq (X s)] [∀ s, DecidableEq (Y s)] in
/-- On the code, the branches of the encoded layer that do not follow the layer vanish. -/
private theorem kraus_encode_mul_eq_zero (L : Layer Γ KrausGate X Y) (e : ∀ s, X s ↪ X' s)
    (f : ∀ s, Y s ↪ Y' s) (y₀ : ∀ s, Y' s) {p : (L.encode e f y₀).Index}
    (hp : p ∉ Set.range (L.encodeIndex e f y₀)) :
    (L.encode e f y₀).kraus KrausGate.ev p *
      basisInclusion (Function.Embedding.piCongrRight e) = 0 := by
  ext y' x
  rw [mul_basisInclusion_apply, Matrix.zero_apply, Layer.kraus_apply]
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
    rw [ha]
    exact (mul_basisInclusion_apply (e s) _ _ _).symm.trans
      (congrFun (congrFun (KrausFamily.encode_op_inr_mul _ _ _ _ a) _) _)
  · push Not at hg
    obtain ⟨b, hb⟩ := hg
    obtain ⟨a, ha⟩ : ∃ a, p.1 b = Sum.inr a := by
      cases h : p.1 b with
      | inl i => exact absurd h (hb i)
      | inr a => exact ⟨a, rfl⟩
    refine mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ b) ?_) _
    rw [KrausGate.ev_apply, ha]
    exact (mul_basisInclusion_apply _ _ _ _).symm.trans
      (congrFun (congrFun (KrausFamily.encode_op_inr_mul _ _ _ _ a) _) _)

/-- The encoded layer, followed by continuations that act on the code as the continuations of
the layer, acts on the code as the layer followed by its continuations. -/
private theorem map_step_encode {Z Z' : S → Type} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    [∀ s, Fintype (Z' s)]
    [∀ s, DecidableEq (Z' s)] (L : Layer Γ KrausGate X Y) (e : ∀ s, X s ↪ X' s)
    (f : ∀ s, Y s ↪ Y' s) (g : ∀ s, Z s ↪ Z' s) (y₀ : ∀ s, Y' s)
    (next : L.Index → Circuit Γ KrausGate Y Z)
    (next' : (L.encode e f y₀).Index → Circuit Γ KrausGate Y' Z')
    (h : ∀ i, (next' (L.encodeIndex e f y₀ i)).map KrausGate.ev ∘ₗ
        (encodeCircuit Γ f).map KrausGate.ev =
      (encodeCircuit Γ g).map KrausGate.ev ∘ₗ (next i).map KrausGate.ev) :
    (Circuit.step (L.encode e f y₀) next').map KrausGate.ev ∘ₗ
        (encodeCircuit Γ e).map KrausGate.ev =
      (encodeCircuit Γ g).map KrausGate.ev ∘ₗ (Circuit.step L next).map KrausGate.ev := by
  refine LinearMap.ext fun ρ ↦ ?_
  simp only [LinearMap.comp_apply, Circuit.map_step, map_sum]
  refine (Fintype.sum_of_injective (L.encodeIndex e f y₀) (L.encodeIndex_injective e f y₀) _ _
    (fun p hp ↦ ?_) fun i ↦ ?_).symm
  · rw [map_encodeCircuit, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      kraus_encode_mul_eq_zero L e f y₀ hp]
    simp
  · have hk := L.kraus_encode_mul e f y₀ i
    have : (L.encode e f y₀).kraus KrausGate.ev (L.encodeIndex e f y₀ i) *
          (encodeCircuit Γ e).map KrausGate.ev ρ *
          ((L.encode e f y₀).kraus KrausGate.ev (L.encodeIndex e f y₀ i))ᴴ =
        (encodeCircuit Γ f).map KrausGate.ev
          (L.kraus KrausGate.ev i * ρ * (L.kraus KrausGate.ev i)ᴴ) := by
      rw [map_encodeCircuit, map_encodeCircuit]
      calc _ = (L.encode e f y₀).kraus KrausGate.ev (L.encodeIndex e f y₀ i) *
              basisInclusion (Function.Embedding.piCongrRight e) * ρ *
            ((L.encode e f y₀).kraus KrausGate.ev (L.encodeIndex e f y₀ i) *
              basisInclusion (Function.Embedding.piCongrRight e))ᴴ := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by
            rw [hk]
            simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this]
    exact (LinearMap.congr_fun (h i) _).symm

/-- The circuit of the encoded layer acts on the code as the circuit of the layer. -/
private theorem map_ofLayer_encode (L : Layer Γ KrausGate X Y) (e : ∀ s, X s ↪ X' s)
    (f : ∀ s, Y s ↪ Y' s) (y₀ : ∀ s, Y' s) :
    (Circuit.ofLayer (L.encode e f y₀)).map KrausGate.ev ∘ₗ (encodeCircuit Γ e).map KrausGate.ev =
      (encodeCircuit Γ f).map KrausGate.ev ∘ₗ (Circuit.ofLayer L).map KrausGate.ev :=
  map_step_encode L e f f y₀ _ _ fun _ ↦ by
    rw [Circuit.map_done, Circuit.map_done, LinearMap.id_comp, LinearMap.comp_id]

/-- A layer of trace-preserving plain gates and onsite families on nonempty bases is carried
along embeddings `e` of its input and `f` of its output system to a layer on the same cells,
again trace-preserving, which acts as the layer on the code. The input bases are nonempty, so
the output bases are nonempty too, and each supplies a fallback basis vector: the branches of the
encoded layer that leave the code send their output to these vectors. -/
theorem exists_encoded [∀ s, Nonempty (X s)] (L : Layer Γ KrausGate X Y)
    (hL : L.Forall KrausGate.ev KrausFamily.IsTP) (e : ∀ s, X s ↪ X' s) (f : ∀ s, Y s ↪ Y' s) :
    ∃ L' : Layer Γ KrausGate X' Y', L'.cells = L.cells ∧
      L'.Forall KrausGate.ev KrausFamily.IsTP ∧
      (Circuit.ofLayer L').map KrausGate.ev ∘ₗ (encodeCircuit Γ e).map KrausGate.ev =
        (encodeCircuit Γ f).map KrausGate.ev ∘ₗ (Circuit.ofLayer L).map KrausGate.ev := by
  have := L.nonempty_output_of_forall_isTP KrausGate.ev hL
  let y₀ : ∀ s, Y' s := fun s ↦ f s (Classical.arbitrary _)
  exact ⟨L.encode e f y₀, rfl, ⟨fun b ↦ (hL.1 b).encode _ _ _, fun s ↦ (hL.2 s).encode _ _ _⟩,
    map_ofLayer_encode L e f y₀⟩

end Layer

namespace Circuit

/-- A circuit of trace-preserving plain gates and onsite families whose bases along it have
between `1` and `B ≤ q` elements is carried along any embeddings `e` of its input and `f` of its
output bases into `Fin q` to a circuit on `Fin q` at every site of the same depth, again
trace-preserving and unbranched when the circuit is, which acts as the circuit on the code. -/
theorem exists_encoded_of_isDimBounded {B q : ℕ} (hB : B ≤ q) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    [∀ s, Fintype (Z s)] → [∀ s, DecidableEq (Z s)] → (c : Circuit Γ KrausGate X Z) →
    c.Forall KrausGate.ev KrausFamily.IsTP → c.IsDimBounded Finset.univ B →
    (e : ∀ s, X s ↪ Fin q) → (f : ∀ s, Z s ↪ Fin q) →
    ∃ c' : Circuit Γ KrausGate (Qudits S q) (Qudits S q),
      c'.Forall KrausGate.ev KrausFamily.IsTP ∧ (c.IsUnbranched → c'.IsUnbranched) ∧
        c'.depth = c.depth ∧
        c'.map KrausGate.ev ∘ₗ (encodeCircuit Γ e).map KrausGate.ev =
          (encodeCircuit Γ f).map KrausGate.ev ∘ₗ c.map KrausGate.ev
  | X, _, i₁, i₂, i₃, i₄, done _, _, hdim, e, f => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    have : ∀ s, Nonempty (X s) := fun s ↦ (Nat.card_pos_iff.mp (hdim s (Finset.mem_univ s)).1).1
    let x₀ : ∀ s, X s := fun _ ↦ Classical.arbitrary _
    refine ⟨(decodeCircuit Γ e x₀).comp (encodeCircuit Γ f),
      Forall.comp _ ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _),
        fun s ↦ KrausFamily.isTP_decode (e s) (x₀ s)⟩, fun _ ↦ trivial⟩
        ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun s ↦ KrausFamily.isTP_embed (f s)⟩,
          fun _ ↦ trivial⟩,
      fun _ ↦ (isUnbranched_ofLayer _).comp (isUnbranched_ofLayer _),
      Nat.le_zero.mp ((depth_comp _ _).trans ?_), ?_⟩
    · rw [decodeCircuit, encodeCircuit, depth_ofLayer, depth_ofLayer, Layer.depth_ofOnsite,
        Layer.depth_ofOnsite]
    · rw [map_comp, LinearMap.comp_assoc, map_decodeCircuit_comp_map_encodeCircuit, map_done,
        LinearMap.comp_id]
  | X, Z, _, _, _, _, step (Y := Y) L next, hc, hdim, e, f => by
    have : ∀ s, Nonempty (X s) := fun s ↦ (Nat.card_pos_iff.mp (hdim.1 s (Finset.mem_univ s)).1).1
    obtain ⟨i₀⟩ := L.nonempty_index_of_forall_isTP KrausGate.ev hc.1
    have := L.nonempty_output_of_forall_isTP KrausGate.ev hc.1
    let g : ∀ s, Y s ↪ Fin q := fun s ↦ (Fintype.equivFin (Y s)).toEmbedding.trans
      (Fin.castLEEmb (by
        rw [← Nat.card_eq_fintype_card]
        exact ((hdim.2 i₀).input s (Finset.mem_univ s)).2.trans hB))
    let y₀ : ∀ s, Fin q := fun s ↦ g s (Classical.arbitrary _)
    have spec := fun i ↦ (exists_encoded_of_isDimBounded hB (next i) (hc.2 i) (hdim.2 i) g f)
    let F : L.Index → Circuit Γ KrausGate (Qudits S q) (Qudits S q) := fun i ↦ (spec i).choose
    let r : (L.encode e g y₀).Index → L.Index := fun p ↦
      (fun b ↦ Sum.elim id (fun _ ↦ i₀.1 b) (p.1 b), fun s ↦ Sum.elim id (fun _ ↦ i₀.2 s) (p.2 s))
    refine ⟨step (L.encode e g y₀) fun p ↦ F (r p),
      ⟨⟨fun b ↦ (hc.1.1 b).encode _ _ _, fun s ↦ (hc.1.2 s).encode _ _ _⟩,
        fun p ↦ (spec (r p)).choose_spec.1⟩,
      fun hu ↦ ⟨fun p p' ↦ by
        have h := hu.1 (r p) (r p')
        simp only [F]
        congr 1
        simp only [h],
        fun p ↦ (spec (r p)).choose_spec.2.1 (hu.2 (r p))⟩, ?_,
      Layer.map_step_encode L e g f y₀ next _ fun i ↦ (spec i).choose_spec.2.2.2⟩
    rw [depth_step, depth_step]
    refine congrArg (L.depth + ·) (le_antisymm (Finset.sup_le fun p _ ↦ ?_)
      (Finset.sup_le fun i _ ↦ ?_))
    · rw [(spec (r p)).choose_spec.2.2.1]
      exact Finset.le_sup (f := fun i ↦ (next i).depth) (Finset.mem_univ _)
    · rw [← (spec i).choose_spec.2.2.1]
      exact Finset.le_sup (f := fun p ↦ (F (r p)).depth)
        (Finset.mem_univ (Layer.encodeIndex L e g y₀ i))

end Circuit

/-- A map realised by a protocol bounded by `B ≤ q` in depth at most `T` is carried along any
embeddings `e` of its input and `f` of its output bases into `Fin q` to a map realised by a
protocol on `Fin q` at every site in depth at most `T`, which acts as the map on the code. -/
theorem IsBoundedProtocol.exists_encoded {Z : S → Type} [∀ s, Fintype (Z s)]
    [∀ s, DecidableEq (Z s)] {B q T : ℕ} (hB : B ≤ q)
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol Γ B T Φ) (e : ∀ s, X s ↪ Fin q) (f : ∀ s, Z s ↪ Fin q) :
    ∃ Φ', IsProtocol Γ T (X := Qudits S q) (Z := Qudits S q) Φ' ∧
      Φ' ∘ₗ (encodeCircuit Γ e).map KrausGate.ev = (encodeCircuit Γ f).map KrausGate.ev ∘ₗ Φ := by
  obtain ⟨c, hc, hT, rfl, hu, hdim⟩ := h
  obtain ⟨c', hc', hu', hd', hm'⟩ := c.exists_encoded_of_isDimBounded hB hc hdim e f
  exact ⟨c'.map KrausGate.ev, ⟨c', hc', hd'.le.trans hT, rfl, hu' hu⟩, hm'⟩

end QuantumCircuit
