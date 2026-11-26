/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Isometry.IsometricDomainExtension
import QICLean.Circuit.Compile.DilationOutput
import QICLean.Circuit.Compile.Port

/-!
# Codes on the wires of the ring with ports

On the ring with physical ports and `2k + 1` qudits of dimension `d` at every site, a code of
the sites is a sitewise embedding of a finite basis into the configurations of the wires of the
site. The simulation of bounded protocols (`IsBoundedProtocol.exists_portRing`) is stated on the
code of the data wires; the logical system may equally sit on any other code, such as the
physical port itself, with the data and scratch wires reset to `0` (`portWireEmbedding`).

Changing from one code to another acts on each site separately, so it is free: it is a layer of
gates on whole sites (`Layer.exists_portRing_sites`), dilated with environments at a set of
wires meeting every site, at depth `0` (`exists_portRing_recode`). A bounded protocol of depth
`T` is therefore simulated in depth `2kT` between any two codes on the wires
(`IsBoundedProtocol.exists_portRing_of_code`): the input code is changed to the data code, the
protocol is routed through the ports, and the data code is changed to the output code.

If the protocol sends a pure state `ψ` to within trace distance `ε` of a pure state `φ`, the
unitary of the dilating circuit on the ring with ports sends the encoded `ψ`, together with the
environments prepared in a basis vector, to within `√(2ε)` of the encoded `φ` tensored with a
unit vector of the output environments (`IsBoundedProtocol.exists_portRing_unit_product_approx`);
at `ε = 0` the output is exactly a product.

## Main definitions

* `QuantumCircuit.portWireEmbedding` — the logical qudit of a site on its physical port, the
  other wires in `0`.

## Main results

* `QuantumCircuit.exists_portRing_recode` — a change of the codes of the sites is free.
* `QuantumCircuit.IsBoundedProtocol.exists_portRing_of_code` — bounded protocols between any
  codes on the wires.
* `QuantumCircuit.IsBoundedProtocol.exists_portRing_unit_product_approx` — pure and approximate
  pure outputs on the ring with ports.

The declarations restate the physical-port input and output of
`TNLean/Circuit/Channel/PhysicalPortIO.lean` (`exists_physicalPortIO`),
`TNLean/Circuit/Channel/PhysicalPortCodes.lean` (`portWordCode`, `exists_portDataTransfers`),
`TNLean/Circuit/Channel/PhysicalPortUnitaryCompilation.lean` (`exists_physicalPortUnitaryIO`),
`TNLean/Circuit/Channel/WholeSiteChannels.lean` (`wholeSite_onsiteChannel`),
`TNLean/Circuit/Channel/BoundedPortPureOutput.lean` and
`TNLean/Circuit/Channel/BoundedPortApproximateOutput.lean` at commit
`414a18fb882d1b8c41c8d28d4b0c66d0d6ef2a2e` (Apache-2.0). The changes: any finite bases at the
sites and any codes on the wires instead of the logical alphabet `Fin d` on the port; a bound
`B ≤ d ^ k` in place of `k = ⌈log_d B⌉`; environments at the wires of any set meeting every
site, in place of appended qudits.
* `QuantumCircuit.IsBoundedProtocol.exists_portRing`: protocols on the ring with physical ports.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, main text, paragraph "Quantum circuits and
  LOCC" (free onsite operations, ancillas in a product state), Supplement, proof of
  Proposition 2, p. 8 (intersite gates on the physical qudits only), and paragraph "Phases of
  matter" (the trace-norm criterion).
-/

open Matrix ManyBody

namespace QuantumCircuit

section PortProtocol

/-!
## Protocols on the ring with physical ports

A protocol on the ring of `N ≥ 2` sites whose bases along it have at most `B ≤ d ^ k` elements
is simulated, layer by layer, on the ring with physical ports and `2k + 1` qudits of dimension
`d` at every site: every basis is encoded in a register of `k` digits
(`Layer.exists_encoded`), each layer of the registers is routed through the ports
(`Layer.exists_portRing`), and the registers sit in the data wires of the sites
(`portDataEmbedding`). The depth grows by the factor `2k`.

Every layer of the routed protocol is dilated with environments at the wires of a set `D`
meeting every site (`Circuit.isUnitaryDilation`), since its only families that are not unitary
are gates on whole sites, and the dilations compose (`IsUnitaryDilation.comp`).

### Main results

* `QuantumCircuit.IsBoundedProtocol.exists_portRing` — a bounded protocol on the ring is the
  partial trace of a unitary circuit on the ring with physical ports, with environments at the
  wires of `D` and every other wire of dimension at most `d` throughout, acting on the encoded
  registers.
-/

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

end PortProtocol

section PortCode

variable {N k d : ℕ} [NeZero d]

variable (N k d) in
/-- The logical qudit of a site on its physical port: the value `x` on the port wire `0` and `0`
on the data and scratch wires.

This is the code of arXiv:2103.13367, Supplement, proof of Proposition 2, p. 8: the logical
system sits on the physical qudit, and the local memory starts and ends in `0`. -/
def portWireEmbedding (i : Fin N) :
    Fin d ↪ blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) i where
  toFun x w := if w.1.2 = 0 then x else 0
  inj' x x' h := by
    have := congrFun h ⟨(i, 0), by simp⟩
    simpa using this

omit [NeZero d] in
/-- A code of the sites, read on the wires, is the conjugation by the isometry of the composite
embedding. -/
private theorem reindex_map_encodeCircuit {α : Fin N → Type} [∀ i, Fintype (α i)]
    [∀ i, DecidableEq (α i)] {Γ : Geometry (Fin N)}
    (a : ∀ i, α i ↪ blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) i)
    (ρ : Matrix (Config α) (Config α) ℂ) :
    (reindexAlgEquiv ℂ ℂ (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)))
        ((encodeCircuit Γ a).map KrausGate.ev ρ) =
      basisInclusion ((Function.Embedding.piCongrRight a).trans
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding) * ρ *
        (basisInclusion ((Function.Embedding.piCongrRight a).trans
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding))ᴴ := by
  rw [map_encodeCircuit, reindexAlgEquiv_eq_basisInclusion_mul,
    ← basisInclusion_mul_basisInclusion]
  simp only [conjTranspose_mul, Matrix.mul_assoc]

/-- **Changing the code of the sites is free on the ring with ports.** For any two codes `a`
and `a'` of a nonempty basis at every site into the wires of the site, some map with a unitary
dilation of depth `0` on the ring with ports, with environments at the wires of a set `D`
containing a wire of every site and every wire outside `D` of dimension `d` throughout, sends
the code `a` to the code `a'`.

Source: arXiv:2103.13367, main text, paragraph "Quantum circuits and LOCC" (local operations
on a site and its ancillas are free), and Supplement, proof of Proposition 2, p. 8. -/
theorem exists_portRing_recode {α : Fin N → Type} [∀ i, Fintype (α i)] [∀ i, DecidableEq (α i)]
    [∀ i, Nonempty (α i)]
    (a a' : ∀ i, α i ↪ blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) i)
    (D : Finset (Fin N × Fin (2 * k + 1))) (hD : ∀ i, ∃ w, (i, w) ∈ D) :
    ∃ Ψ, IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d 0 Ψ ∧
      Ψ ∘ₗ (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) a).map KrausGate.ev =
        (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) a').map KrausGate.ev := by
  let L₀ : Layer (Geometry.sites (Fin N)) KrausGate α α :=
    Layer.ofOnsite fun _ ↦ KrausFamily.single 1
  obtain ⟨L', -, hL', hm'⟩ := L₀.exists_encoded (⟨fun b ↦ absurd b.2 (Finset.notMem_empty _),
    fun _ ↦ (KrausFamily.isUnitary_single (one_mem _)).isTP⟩) a a'
  obtain ⟨Ψ, hΨ, hΨm⟩ := Layer.exists_portRing_sites L' hL' D hD
  refine ⟨Ψ, hΨ, LinearMap.ext fun ρ ↦ ?_⟩
  have h₁ := LinearMap.congr_fun hΨm ((encodeCircuit (Geometry.ring N) a).map KrausGate.ev ρ)
  have h₂ := LinearMap.congr_fun hm' ρ
  simp only [LinearMap.comp_apply] at h₁ h₂ ⊢
  rw [h₁, map_encodeCircuit_congr (Geometry.sites (Fin N)), h₂,
    map_encodeCircuit_congr (Γ := Geometry.ring N) (Geometry.sites (Fin N)),
    Circuit.map_ofLayer_ofOnsite_single, piKronecker_one, conjTranspose_one, Matrix.one_mul,
    Matrix.mul_one]

omit [NeZero d] in
/-- A basis of at most `B ≤ d ^ k` elements embeds in a register of `k` digits. -/
private theorem nonempty_register_embedding {α : Type} [Finite α] {B : ℕ} (hB : B ≤ d ^ k)
    (hα : Nat.card α ≤ B) : Nonempty (α ↪ Fin k → Fin d) :=
  have := Fintype.ofFinite α
  Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact hα.trans hB)

/-- **Bounded protocols between any codes on the wires of the ring with ports.** Let `Φ` be
realised on the ring of `N ≥ 2` sites by a protocol of depth at most `T` whose bases along it
have between `1` and `B ≤ d ^ k` elements, and let `a` and `b` be codes of its input and output
bases into the wires of the sites of the ring with ports and `2k + 1` qudits of dimension `d`
per site. Let `D` be a set of wires containing a wire of every site. Then some map with a
unitary dilation of depth at most `2kT`, with environments at the wires of `D` and every wire
outside `D` of dimension at most `d` throughout, acts on the code `a` as `Φ` followed by the
code `b`. With `a` and `b` the codes `portWireEmbedding` of the physical ports, the logical
systems sit on the ports and the local memories start and end in `0`.

The source compiles protocols with intersite gates on the physical qudits only
(arXiv:2103.13367, Supplement, proof of Proposition 2, p. 8); the constant `2k` and the codes
are formalization-side. -/
theorem IsBoundedProtocol.exists_portRing_of_code {X Z : Fin N → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)] {B T : ℕ}
    (hN : 2 ≤ N) (hB : B ≤ d ^ k)
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol (Geometry.ring N) B T Φ)
    (a : ∀ s, X s ↪ blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) s)
    (b : ∀ s, Z s ↪ blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) s)
    (D : Finset (Fin N × Fin (2 * k + 1))) (hD : ∀ i, ∃ w, (i, w) ∈ D) :
    ∃ Φ', IsUnitaryDilation (Geometry.portRing N (2 * k + 1)) D d (2 * k * T) Φ' ∧
      Φ' ∘ₗ (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) a).map KrausGate.ev =
        (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) b).map KrausGate.ev ∘ₗ Φ := by
  obtain ⟨hX, hZ⟩ := h.dimension_bounds
  have : ∀ s, Nonempty (X s) := fun s ↦ (Nat.card_pos_iff.mp (hX s).1).1
  have : ∀ s, Nonempty (Z s) := fun s ↦ (Nat.card_pos_iff.mp (hZ s).1).1
  let e : ∀ s, X s ↪ Fin k → Fin d := fun s ↦
    Classical.choice (nonempty_register_embedding hB (hX s).2)
  let f : ∀ s, Z s ↪ Fin k → Fin d := fun s ↦
    Classical.choice (nonempty_register_embedding hB (hZ s).2)
  obtain ⟨Φ₀, hΦ₀, hm₀⟩ := h.exists_portRing hN hB e f D hD
  obtain ⟨Ψ₁, hΨ₁, hm₁⟩ := exists_portRing_recode a
    (fun s ↦ (e s).trans (portDataEmbedding N k d s)) D hD
  obtain ⟨Ψ₂, hΨ₂, hm₂⟩ := exists_portRing_recode
    (fun s ↦ (f s).trans (portDataEmbedding N k d s)) b D hD
  refine ⟨Ψ₂ ∘ₗ Φ₀ ∘ₗ Ψ₁, ((hΨ₁.comp hΦ₀).comp hΨ₂).mono le_rfl (by omega),
    LinearMap.ext fun ρ ↦ ?_⟩
  rw [map_encodeCircuit_trans] at hm₁ hm₂
  have h₁ := LinearMap.congr_fun hm₁ ρ
  have h₀ := LinearMap.congr_fun hm₀ ρ
  have h₂ := LinearMap.congr_fun hm₂ (Φ ρ)
  simp only [LinearMap.comp_apply] at h₀ h₁ h₂ ⊢
  rw [h₁, h₀, h₂]

/-- **Pure and approximate pure outputs on the ring with ports.** Let `Φ` be a bounded protocol
of depth at most `T` on the ring of `N ≥ 2` sites, with bases along it of between `1` and
`B ≤ d ^ k` elements, sending the pure state `ψ` to within trace distance `ε` of the pure state
`φ`, and let `a`, `b` be codes of its input and output bases into the wires of the ring with
ports, with isometries `J_a`, `J_b`. Let `D` be a set of wires containing a wire of every site.
Then there are environments at every wire, with one element outside `D`, basis vectors `e₀`, and
an unbranched circuit of unitary gates of depth at most `2kT` on the ring with ports, every wire
outside `D` of dimension at most `d` throughout, such that preparing `e₀`, running the circuit
and tracing out the output environments acts on the code `a` as `Φ` followed by the code `b`,
and the unitary of the circuit sends `J_a ψ ⊗ e₀` to within `√(2ε)` of `J_b φ ⊗ η` for a unit
vector `η` of the output environments. At `ε = 0` the output is exactly `J_b φ ⊗ η`.

Source: arXiv:2103.13367, main text, paragraphs "State transformations with QC and LOCC"
(ancillas prepared in a product state) and "Phases of matter" (the trace-norm criterion), with
the port convention of the Supplement, proof of Proposition 2, p. 8. -/
theorem IsBoundedProtocol.exists_portRing_unit_product_approx {X Z : Fin N → Type}
    [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    {B T : ℕ} (hN : 2 ≤ N) (hB : B ≤ d ^ k)
    {Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ}
    (h : IsBoundedProtocol (Geometry.ring N) B T Φ)
    (a : ∀ s, X s ↪ blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) s)
    (b : ∀ s, Z s ↪ blockSystem Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d) s)
    (D : Finset (Fin N × Fin (2 * k + 1))) (hD : ∀ i, ∃ w, (i, w) ∈ D)
    (ψ : EuclideanSpace ℂ (Config X)) (φ : EuclideanSpace ℂ (Config Z)) (hψ : ‖ψ‖ = 1)
    (hφ : ‖φ‖ = 1) {ε : ℝ}
    (herror : rectangularTraceNorm
      (Φ (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) -
        vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ))) ≤ ε) :
    ∃ (E F : Fin N × Fin (2 * k + 1) → Type) (_ : ∀ s, Fintype (E s))
      (_ : ∀ s, DecidableEq (E s)) (_ : ∀ s, Fintype (F s)) (_ : ∀ s, DecidableEq (F s))
      (e₀ : ∀ s, E s)
      (c : Circuit (Geometry.portRing N (2 * k + 1)) KrausGate
        (fun s ↦ Qudits (Fin N × Fin (2 * k + 1)) d s × E s)
        (fun s ↦ Qudits (Fin N × Fin (2 * k + 1)) d s × F s)),
      (∀ s ∉ D, Subsingleton (E s) ∧ Subsingleton (F s)) ∧ c.IsDimBounded Dᶜ d ∧
      c.Forall KrausGate.ev KrausFamily.IsUnitary ∧ c.IsUnbranched ∧ c.depth ≤ 2 * k * T ∧
      ((traceCircuit (Geometry.portRing N (2 * k + 1)) (Qudits (Fin N × Fin (2 * k + 1)) d)
          F).map KrausGate.ev ∘ₗ c.map KrausGate.ev ∘ₗ
          (prepareCircuit (Geometry.portRing N (2 * k + 1)) e₀).map KrausGate.ev) ∘ₗ
          (reindexAlgEquiv ℂ ℂ
            (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) a).map KrausGate.ev =
        (reindexAlgEquiv ℂ ℂ
          (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d))).toLinearMap ∘ₗ
          (encodeCircuit (Geometry.ring N) b).map KrausGate.ev ∘ₗ Φ ∧
      ∀ p : c.Index, ∃ η : EuclideanSpace ℂ (Config F), ‖η‖ = 1 ∧
        ‖(WithLp.toLp 2 (c.kraus KrausGate.ev p *ᵥ fun w ↦
            if (fun s ↦ (w s).2) = e₀ then
              (basisInclusion ((Function.Embedding.piCongrRight a).trans
                (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding) *ᵥ
                  WithLp.ofLp ψ) (fun s ↦ (w s).1)
            else 0) -
          WithLp.toLp 2 (fun w ↦
            (basisInclusion ((Function.Embedding.piCongrRight b).trans
              (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding) *ᵥ
                WithLp.ofLp φ) (fun s ↦ (w s).1) * η (fun s ↦ (w s).2)) :
            EuclideanSpace ℂ (Config fun s ↦ Qudits (Fin N × Fin (2 * k + 1)) d s × F s))‖ ≤
          Real.sqrt (2 * ε) := by
  obtain ⟨Φ', hΦ', hm⟩ := h.exists_portRing_of_code hN hB a b D hD
  set Ja := basisInclusion ((Function.Embedding.piCongrRight a).trans
    (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding)
  set Jb := basisInclusion ((Function.Embedding.piCongrRight b).trans
    (blockConfigEquiv Prod.fst (Qudits (Fin N × Fin (2 * k + 1)) d)).toEmbedding)
  have hJa : Jaᴴ * Ja = 1 := basisInclusion_isIsometry _
  have hJb : Jbᴴ * Jb = 1 := basisInclusion_isIsometry _
  set ψ' : EuclideanSpace ℂ (Config (Qudits (Fin N × Fin (2 * k + 1)) d)) :=
    WithLp.toLp 2 (Ja *ᵥ WithLp.ofLp ψ)
  set φ' : EuclideanSpace ℂ (Config (Qudits (Fin N × Fin (2 * k + 1)) d)) :=
    WithLp.toLp 2 (Jb *ᵥ WithLp.ofLp φ)
  have hvec : ∀ {α : Type} [Fintype α] (J : Matrix (Config (Qudits (Fin N × Fin (2 * k + 1)) d))
      α ℂ) (v : α → ℂ), J * vecMulVec v (star v) * Jᴴ = vecMulVec (J *ᵥ v) (star (J *ᵥ v)) := by
    intro α _ J v
    rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]
  have hout : Φ' (vecMulVec (WithLp.ofLp ψ') (star (WithLp.ofLp ψ'))) =
      Jb * Φ (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ))) * Jbᴴ := by
    have h₁ := LinearMap.congr_fun hm (vecMulVec (WithLp.ofLp ψ) (star (WithLp.ofLp ψ)))
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] at h₁
    rw [reindex_map_encodeCircuit, reindex_map_encodeCircuit, hvec] at h₁
    exact h₁
  have herror' : rectangularTraceNorm (Φ' (vecMulVec (WithLp.ofLp ψ') (star (WithLp.ofLp ψ'))) -
      vecMulVec (WithLp.ofLp φ') (star (WithLp.ofLp φ'))) ≤ ε := by
    rw [hout, show vecMulVec (WithLp.ofLp φ') (star (WithLp.ofLp φ')) =
        Jb * vecMulVec (WithLp.ofLp φ) (star (WithLp.ofLp φ)) * Jbᴴ from (hvec Jb _).symm,
      ← Matrix.sub_mul, ← Matrix.mul_sub, rectangularTraceNorm_isometry_sandwich _ _ _ hJb hJb]
    exact herror
  obtain ⟨E, F, i₁, i₂, i₃, i₄, e₀, c, hD', hB', hu, hb, hd, hΦc, hη⟩ :=
    hΦ'.exists_unit_product_approx ψ' φ' (norm_toLp_mulVec_of_isometry Ja hJa ψ ▸ hψ)
      (norm_toLp_mulVec_of_isometry Jb hJb φ ▸ hφ) herror'
  exact ⟨E, F, i₁, i₂, i₃, i₄, e₀, c, hD', hB', hu, hb, hd, hΦc ▸ hm, hη⟩

end PortCode

end QuantumCircuit
