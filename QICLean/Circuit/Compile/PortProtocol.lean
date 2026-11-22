/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Circuit.Compile.Port

/-!
# Protocols on the ring with physical ports

A protocol on the ring of `N ≥ 2` sites whose bases along it have at most `B ≤ d ^ k` elements
is simulated, layer by layer, on the ring with physical ports and `2k + 1` qudits of dimension
`d` at every site: every basis is encoded in a register of `k` digits
(`Layer.exists_encoded`), each layer of the registers is routed through the ports
(`Layer.exists_portRing`), and the registers sit in the data wires of the sites
(`portDataEmbedding`). The depth grows by the factor `2k`.

Every layer of the routed protocol is dilated with environments at the wires of a set `D`
meeting every site (`Circuit.isUnitaryDilation`), since its only families that are not unitary
are gates on whole sites, and the dilations compose (`IsUnitaryDilation.comp`).

## Main results

* `QuantumCircuit.IsBoundedProtocol.exists_portRing` — a bounded protocol on the ring is the
  partial trace of a unitary circuit on the ring with physical ports, with environments at the
  wires of `D` and every other wire of dimension at most `d` throughout, acting on the encoded
  registers.
-/

open Matrix ManyBody

namespace QuantumCircuit

variable {N k d : ℕ} [NeZero d]

/-- The induction behind `IsBoundedProtocol.exists_portRing`, along the circuit. -/
private theorem exists_portRing_of_isDimBounded (hN : 2 ≤ N) {B : ℕ} (hB : B ≤ d ^ k)
    (D : Finset (Fin N × Fin (2 * k + 1))) (hD : ∀ i, ∃ w, (i, w) ∈ D) :
    {X Z : Fin N → Type} → [∀ s, Fintype (X s)] → [∀ s, DecidableEq (X s)] →
    [∀ s, Fintype (Z s)] → [∀ s, DecidableEq (Z s)] →
    (c : Circuit (Geometry.ring N) KrausGate X Z) →
    c.Forall KrausGate.ev KrausFamily.IsTP → c.IsDimBounded Finset.univ B → c.IsUnbranched →
    (e : ∀ s, X s ↪ Fin k → Fin d) → (f : ∀ s, Z s ↪ Fin k → Fin d) →
    ∃ Φ, IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d (2 * k * c.depth) Φ ∧
      Φ ∘ₗ (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) (portDataEmbedding N k d)).map KrausGate.ev ∘ₗ
            (encodeCircuit (Geometry.ring N) e).map KrausGate.ev =
        (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) (portDataEmbedding N k d)).map KrausGate.ev ∘ₗ
            (encodeCircuit (Geometry.ring N) f).map KrausGate.ev ∘ₗ c.map KrausGate.ev
  | X, _, i₁, i₂, i₃, i₄, Circuit.done _, _, hdim, _, e, f => by
    obtain rfl : i₁ = i₃ := Subsingleton.elim _ _
    obtain rfl : i₂ = i₄ := Subsingleton.elim _ _
    have : ∀ s, Nonempty (X s) := fun s ↦ (Nat.card_pos_iff.mp (hdim s (Finset.mem_univ s)).1).1
    let L₀ : Layer (Geometry.ring N) KrausGate X X := Layer.ofOnsite fun _ ↦ KrausFamily.single 1
    obtain ⟨L', hc', hL', hm'⟩ := L₀.exists_encoded
      ⟨fun b ↦ absurd b.2 (Finset.notMem_empty _),
        fun _ ↦ (KrausFamily.isUnitary_single (one_mem _)).isTP⟩ e f
    obtain ⟨Φ, hΦ, hΦm⟩ := Layer.exists_portRing hN L' hL' D hD
    refine ⟨Φ, hΦ.mono le_rfl (le_of_eq ?_), LinearMap.ext fun ρ ↦ ?_⟩
    · rw [show L'.depth = 0 by simp [Layer.depth, hc', L₀, Layer.ofOnsite]]
      rfl
    · have h₁ := LinearMap.congr_fun hΦm ((encodeCircuit (Geometry.ring N) e).map KrausGate.ev ρ)
      have h₂ := LinearMap.congr_fun hm' ρ
      simp only [LinearMap.comp_apply] at h₁ h₂ ⊢
      rw [h₁, h₂, Circuit.map_ofLayer_ofOnsite_single, piKronecker_one, conjTranspose_one,
        Matrix.one_mul, Matrix.mul_one, Circuit.map_done, LinearMap.id_apply]
  | X, Z, _, _, _, _, Circuit.step (Y := Y) L next, hc, hdim, hu, e, f => by
    have : ∀ s, Nonempty (X s) := fun s ↦ (Nat.card_pos_iff.mp (hdim.1 s (Finset.mem_univ s)).1).1
    obtain ⟨i₀⟩ := L.nonempty_index_of_forall_isTP KrausGate.ev hc.1
    have hY := (hdim.2 i₀).input
    let g : ∀ s, Y s ↪ Fin k → Fin d := fun s ↦ Classical.choice
      (Function.Embedding.nonempty_of_card_le (by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card]
        exact (hY s (Finset.mem_univ s)).2.trans hB))
    obtain ⟨L', hc', hL', hm'⟩ := L.exists_encoded hc.1 e g
    obtain ⟨Φ₁, hΦ₁, hΦ₁m⟩ := Layer.exists_portRing hN L' hL' D hD
    obtain ⟨Φ₂, hΦ₂, hΦ₂m⟩ :=
      exists_portRing_of_isDimBounded hN hB D hD (next i₀) (hc.2 i₀) (hdim.2 i₀) (hu.2 i₀) g f
    refine ⟨Φ₂ ∘ₗ Φ₁, (hΦ₁.comp hΦ₂).mono le_rfl (le_of_eq ?_), LinearMap.ext fun ρ ↦ ?_⟩
    · have hsup : (Finset.univ.sup fun i ↦ (next i).depth) = (next i₀).depth := by
        simp only [hu.1 _ i₀]
        exact Finset.sup_const ⟨i₀, Finset.mem_univ _⟩ _
      have hdepth : L'.depth = L.depth := by
        unfold Layer.depth
        rw [hc']
      rw [Circuit.depth_step, hsup, hdepth, Nat.mul_add]
    · rw [Circuit.step_eq_ofLayer_comp L hu.1 i₀, Circuit.map_comp]
      have h₁ := LinearMap.congr_fun hΦ₁m ((encodeCircuit (Geometry.ring N) e).map KrausGate.ev ρ)
      have h₂ := LinearMap.congr_fun hm' ρ
      have h₃ := LinearMap.congr_fun hΦ₂m ((Circuit.ofLayer L).map KrausGate.ev ρ)
      simp only [LinearMap.comp_apply] at h₁ h₂ h₃ ⊢
      rw [h₁, h₂, h₃]

/-- **A bounded protocol on the ring is a unitary circuit on the ring with physical ports.** Let
`Φ` be realised on the ring of `N ≥ 2` sites by a protocol of depth at most `T` whose bases along
it have at most `B ≤ d ^ k` elements, and let `e` and `f` encode its input and output bases in
registers of `k` digits of dimension `d`. Let `D` be a set of wires containing a wire of every
site. On the ring with ports and `2k + 1` qudits of dimension `d` per site, with each register
in the data wires of its site, some map with a unitary dilation of depth at most `2kT` whose
environments lie at the wires of `D` acts on the encoded inputs as `Φ` followed by the encoding
of the outputs; throughout the dilating circuit every wire outside `D` has dimension at most `d`.
For `k ≥ 1` and `D` the non-port wires, each gate on a port-pair cell is therefore a unitary on
the two port wires alone, each of dimension at most `d`.

The source compiles a protocol with gates on pairs of neighbouring sites into a unitary circuit
whose intersite gates act on the physical qudits only, the ancillas staying local
(arXiv:2103.13367, Supplement, proof of Proposition 2, p. 8); the constant `2k` is
formalization-side. Taking `k = ⌈log_d B⌉` gives `B ≤ d ^ k`. -/
theorem IsBoundedProtocol.exists_portRing {X Z : Fin N → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] {B T : ℕ}
    (hN : 2 ≤ N) (hB : B ≤ d ^ k)
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol (Geometry.ring N) B T Φ) (e : ∀ s, X s ↪ Fin k → Fin d)
    (f : ∀ s, Z s ↪ Fin k → Fin d) (D : Finset (Fin N × Fin (2 * k + 1)))
    (hD : ∀ i, ∃ w, (i, w) ∈ D) :
    ∃ Φ', IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d (2 * k * T) Φ' ∧
      Φ' ∘ₗ (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) (portDataEmbedding N k d)).map KrausGate.ev ∘ₗ
            (encodeCircuit (Geometry.ring N) e).map KrausGate.ev =
        (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) (portDataEmbedding N k d)).map KrausGate.ev ∘ₗ
            (encodeCircuit (Geometry.ring N) f).map KrausGate.ev ∘ₗ Φ := by
  obtain ⟨c, hc, hT, rfl, hu, hdim⟩ := h
  obtain ⟨Φ', hΦ', hm⟩ := exists_portRing_of_isDimBounded hN hB D hD c hc hdim hu e f
  exact ⟨Φ', hΦ'.mono le_rfl (Nat.mul_le_mul_left _ hT), hm⟩

end QuantumCircuit
