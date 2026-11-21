/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.Encoding
import QICLean.Circuit.Model.Channel

/-!
# Protocols on a fixed register

A protocol whose bases along it have between `1` and `B ≤ q` elements is carried along codes of
its input and output bases into `Fin q` to a sequence of layers on `Fin q` at every site: every
intermediate system of the encoded protocol is the register `Fin q`, not only its input and its
output (`Circuit.exists_seq_encoded`). Every layer of the circuit is encoded on its own cells
(`Layer.exists_encoded`), along a code of its output bases into `Fin q`, and the end of the
circuit is a single onsite layer on `Fin q` that changes the code of the last system to the
code of the output. The depth is kept, and the layers are trace-preserving.

This sharpens `Circuit.exists_encoded_of_isDimBounded` for unbranched circuits: there the
encoded circuit ends by decoding to the output bases of the circuit and encoding again, so its
last intermediate system is not the register.

## Main results

* `QuantumCircuit.Circuit.exists_seq_encoded` — an unbranched bounded circuit is a sequence of
  layers on the register, on the code.
* `QuantumCircuit.IsBoundedProtocol.exists_seq_encoded` — the same for bounded protocols.

The declarations restate `IsDimensionBoundedLocalChannelProtocol.exists_fixedRegisterWord` of
`TNLean/Circuit/Channel/EncodedChannelProtocol.lean` at commit
`414a18fb882d1b8c41c8d28d4b0c66d0d6ef2a2e` (Apache-2.0). The changes: the words of onsite
channels and pair-channel layers on the ring are sequences of layers on any geometry; any codes
of the input and output bases are allowed; the fallback of a code is a basis vector instead of a
density.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}

namespace Circuit

/-- **Protocols on a fixed register.** An unbranched circuit of trace-preserving plain gates and
onsite families whose bases along it have between `1` and `B ≤ q` elements is carried along any
codes `e` of its input and `f` of its output bases into `Fin q` to a sequence of layers of
trace-preserving plain gates and onsite families on `Fin q` at every site, of total depth at
most the depth of the circuit, which acts as the circuit on the code.

This statement is formalization-side: it is the register form of the bounded local channel
protocols compared with fixed physical ports in arXiv:2103.13367, Supplement, proof of
Proposition 2, p. 8. -/
theorem exists_seq_encoded {B q : ℕ} (hB : B ≤ q) :
    {X Z : S → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    [∀ s, Fintype (Z s)] → [∀ s, DecidableEq (Z s)] → (c : Circuit Γ KrausGate X Z) →
    c.Forall KrausGate.ev KrausFamily.IsTP → c.IsUnbranched → c.IsDimBounded Finset.univ B →
    (e : ∀ s, X s ↪ Fin q) → (f : ∀ s, Z s ↪ Fin q) →
    ∃ Ls : List (Layer Γ KrausGate (Qudits S q) (Qudits S q)),
      (∀ L ∈ Ls, L.Forall KrausGate.ev KrausFamily.IsTP) ∧
        (Ls.map Layer.depth).sum ≤ c.depth ∧
        (seq Ls).map KrausGate.ev ∘ₗ (encodeCircuit Γ e).map KrausGate.ev =
          (encodeCircuit Γ f).map KrausGate.ev ∘ₗ c.map KrausGate.ev
  | X, _, i₁, i₂, i₃, i₄, done _, _, _, hdim, e, f => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    have : ∀ s, Nonempty (X s) := fun s ↦ (Nat.card_pos_iff.mp (hdim s (Finset.mem_univ s)).1).1
    let L₀ : Layer Γ KrausGate X X := Layer.ofOnsite fun _ ↦ KrausFamily.single 1
    obtain ⟨L', hc', hL', hm'⟩ := L₀.exists_encoded
      (Layer.forall_ofOnsite KrausGate.ev fun _ ↦ (KrausFamily.isUnitary_single (one_mem _)).isTP)
      e f
    refine ⟨[L'], by simpa using hL', ?_, LinearMap.ext fun ρ ↦ ?_⟩
    · simp [Layer.depth, hc', L₀, Layer.ofOnsite]
    · have h := LinearMap.congr_fun hm' ρ
      simp only [LinearMap.comp_apply] at h ⊢
      rw [map_seq_cons, show seq ([] : List (Layer Γ KrausGate (Qudits S q) (Qudits S q))) =
        done _ from rfl, map_done, LinearMap.id_comp, ← map_ofLayer, h,
        map_ofLayer_ofOnsite_single, prodOp_one, conjTranspose_one, Matrix.one_mul,
        Matrix.mul_one, map_done, LinearMap.id_apply]
  | X, Z, _, _, _, _, step (Y := Y) L next, hc, hu, hdim, e, f => by
    have : ∀ s, Nonempty (X s) := fun s ↦ (Nat.card_pos_iff.mp (hdim.1 s (Finset.mem_univ s)).1).1
    obtain ⟨i₀⟩ := L.nonempty_index_of_forall_isTP KrausGate.ev hc.1
    have hY := (hdim.2 i₀).input
    let g : ∀ s, Y s ↪ Fin q := fun s ↦ (Fintype.equivFin (Y s)).toEmbedding.trans
      (Fin.castLEEmb (by
        rw [← Nat.card_eq_fintype_card]
        exact (hY s (Finset.mem_univ s)).2.trans hB))
    obtain ⟨L', hc', hL', hm'⟩ := L.exists_encoded hc.1 e g
    obtain ⟨Ls, hLs, hd, hm⟩ :=
      exists_seq_encoded hB (next i₀) (hc.2 i₀) (hu.2 i₀) (hdim.2 i₀) g f
    refine ⟨L' :: Ls, ?_, ?_, ?_⟩
    · exact fun L₁ hL₁ ↦ (List.mem_cons.mp hL₁).elim (fun h ↦ h ▸ hL') (hLs L₁)
    · have hdepth : L'.depth = L.depth := by
        unfold Layer.depth
        rw [hc']
      have hsup : (Finset.univ.sup fun i ↦ (next i).depth) = (next i₀).depth := by
        simp only [hu.1 _ i₀]
        exact Finset.sup_const ⟨i₀, Finset.mem_univ _⟩ _
      rw [List.map_cons, List.sum_cons, hdepth, depth_step, hsup]
      exact Nat.add_le_add_left hd _
    · rw [map_seq_cons, LinearMap.comp_assoc, ← map_ofLayer, hm', ← LinearMap.comp_assoc, hm,
        step_eq_ofLayer_comp L hu.1 i₀, map_comp, LinearMap.comp_assoc]

end Circuit

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)]
  [∀ s, DecidableEq (Z s)]

/-- **Bounded protocols on a fixed register.** A map realised by a protocol of depth at most `T`
whose bases along it have between `1` and `B ≤ q` elements is carried along any codes `e` of
its input and `f` of its output bases into `Fin q` to the map of a sequence of layers of
trace-preserving plain gates and onsite families on `Fin q` at every site, of total depth at
most `T`, which acts as the map on the code.

This statement is formalization-side; see `Circuit.exists_seq_encoded`. -/
theorem IsBoundedProtocol.exists_seq_encoded {B q T : ℕ} (hB : B ≤ q)
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol Γ B T Φ) (e : ∀ s, X s ↪ Fin q) (f : ∀ s, Z s ↪ Fin q) :
    ∃ Ls : List (Layer Γ KrausGate (Qudits S q) (Qudits S q)),
      (∀ L ∈ Ls, L.Forall KrausGate.ev KrausFamily.IsTP) ∧ (Ls.map Layer.depth).sum ≤ T ∧
        (Circuit.seq Ls).map KrausGate.ev ∘ₗ (encodeCircuit Γ e).map KrausGate.ev =
          (encodeCircuit Γ f).map KrausGate.ev ∘ₗ Φ := by
  obtain ⟨c, hc, hT, rfl, hu, hdim⟩ := h
  obtain ⟨Ls, hLs, hd, hm⟩ := c.exists_seq_encoded hB hc hu hdim e f
  exact ⟨Ls, hLs, hd.trans hT, hm⟩

end QuantumCircuit
