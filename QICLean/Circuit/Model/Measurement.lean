/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.LinearAlgebra.Center
import QICLean.Circuit.Model.Protocol
import QICLean.Circuit.Model.Unitary

/-!
# Measurement circuits

A *measurement circuit* is a circuit of plain gates whose gates and onsite families are each a
unitary or the measurement of a basis in the computational basis, followed by a relabelling of
the basis (`KrausFamily.IsUnitaryOrMeasurement`). Later layers may depend on earlier outcomes,
so a measurement followed by outcome-dependent unitaries is classical feedforward; the
measurements and the onsite unitaries are free, and only layers using a cell of positive cost are
counted in the depth. Measurement circuits are trace-preserving, so they are adaptive protocols
(`QuantumCircuit.IsAdaptiveProtocol`).

A circuit *implements* a matrix `W` on a set `E` of vectors when on every branch its Kraus
operator maps each `v ∈ E` to a scalar multiple of `W v`: whatever the outcomes, the circuit acts
on `E` as `W`, up to a scalar that may depend on the branch and on `v`. Implementations compose
along `Circuit.append`. On a linear subspace and for an isometry `W` the scalar of each branch
does not depend on the input (`Circuit.IsImplementationOn.exists_smul_of_isometry`).

A *deterministic conversion* of a nonzero vector `φ` into `ψ` in depth `T` is a measurement
circuit of depth at most `T` whose output on every branch is a scalar multiple of `ψ`; a
preparation of `ψ` is a conversion from a basis configuration or from a product vector, which
is a basis configuration after free onsite unitaries (`IsMeasurementConversion.of_prodOp`). The
outputs of zero probability are allowed, as the zero multiple. A deterministic conversion of
unit vectors is an adaptive conversion of their density matrices
(`IsMeasurementConversion.isAdaptiveConversion`).

The *one-round* conversions are the class `QCcc` of Piroli, Styliaris and Cirac: a unitary
circuit, one measurement of a region, outcome-dependent onsite unitaries, and then a fixed
unitary circuit (`IsOneRoundConversion`). With the last circuit of depth `0`, this is the class
`QCcc_ℓ` of the source; with it, it is the composition of a `QCcc_ℓ` channel with a circuit
without measurements, as in the preparation of matrix product states of arXiv:2307.01696.

## Main definitions

* `KrausFamily.IsUnitaryOrMeasurement` — the local families of a measurement circuit.
* `QuantumCircuit.Circuit.IsImplementationOn` — a circuit acting on a set as a matrix, up to
  scalars.
* `QuantumCircuit.Circuit.measureCorrect` — a measurement of a region followed by onsite
  corrections chosen by the outcome.
* `QuantumCircuit.IsMeasurementConversion` — deterministic conversion of vectors by a
  measurement circuit.
* `QuantumCircuit.IsOneRoundConversion` — the same with one round of measurements.

## Main results

* `QuantumCircuit.Circuit.IsImplementationOn.append`,
  `QuantumCircuit.Circuit.IsImplementationOn.comp`
  — implementations compose.
* `QuantumCircuit.Circuit.IsImplementationOn.exists_smul_of_isometry` — input-independent scalars
  of the branches on a subspace.
* `QuantumCircuit.Circuit.exists_kraus_mulVec_ne_zero` — a trace-preserving circuit leaves a
  nonzero vector nonzero on some branch.
* `QuantumCircuit.Circuit.IsImplementationOn.map_vecMulVec_eq` — removal of measurements: a
  circuit implementing an isometry on a subspace has there the map of the isometry.
* `QuantumCircuit.Circuit.kraus_measureCorrect`,
  `QuantumCircuit.Circuit.isImplementationOn_comp_measureCorrect` — the Kraus operator of a
  measurement with corrections, and a round implementing a matrix.
* `QuantumCircuit.IsMeasurementConversion.trans`, `QuantumCircuit.IsMeasurementConversion.ne_zero`,
  `QuantumCircuit.Circuit.IsImplementationOn.isMeasurementConversion`.
* `QuantumCircuit.Circuit.isAdaptiveProtocol_map`,
  `QuantumCircuit.IsMeasurementConversion.isAdaptiveConversion` — measurement circuits are
  adaptive protocols, and deterministic conversions adaptive conversions.
* `QuantumCircuit.Circuit.map_vecMulVec` — the map of a circuit on a pure input.
* `QuantumCircuit.IsUnitaryCircuit.isMeasurementConversion`,
  `QuantumCircuit.IsPreparedInDepth.exists_isMeasurementConversion` — unitary circuits are
  measurement circuits.
* `QuantumCircuit.IsOneRoundConversion.isMeasurementConversion`,
  `QuantumCircuit.IsUnitaryCircuit.isOneRoundConversion` — one round is a measurement circuit,
  and a unitary circuit is one round without measurements.
* `QuantumCircuit.IsOneRoundConversion.mulVec` — a unitary circuit after one round.

The declarations restate, as restrictions of `Circuit`, the measurement-assisted protocols and the
measurement rounds of `TNLean/Circuit/Measurement/Protocol.lean`,
`TNLean/Circuit/Measurement/Rounds.lean`, `TNLean/Circuit/Measurement/CoherentRounds.lean`,
`TNLean/Circuit/Measurement/PreparedComposition.lean`, `TNLean/Circuit/Measurement/Channel.lean`
and `TNLean/Circuit/Measurement/AdaptiveRound.lean` (Apache-2.0). The changes: any geometry and
any finite bases instead of the ring of qudits; a sequence of rounds is a circuit whose later
layers may depend on all earlier outcomes, its outcome histories are the branches of the circuit
and its outputs the images of the Kraus operators of the branches; the measured sites of a round
are a measurement layer, its corrections an onsite layer chosen by the outcome; a preparation is a
conversion from a nonzero vector.

## References

* arXiv:2103.13367 (Piroli, Styliaris, Cirac), main text, paragraphs "Quantum circuits and
  LOCC", "State transformations with QC and LOCC" and "Phases of matter", and Definition
  "Transformations under QC and LOCC".
* arXiv:2307.01696 (Malz, Styliaris, Wei, Cirac), paragraphs "Preparations using measurements",
  "Long-range MPS using measurements" and "Tree-RG circuit with measurements".
-/

open Matrix ManyBody
open scoped ComplexOrder

/-! ### The local families -/

namespace KrausFamily

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The local families of a measurement circuit: one unitary operator, or the measurement of the
basis `α` in the computational basis followed by a relabelling `f : α ≃ β` of the basis, the
operators `|f a⟩⟨a|` indexed by the outcomes `a`.

Source: arXiv:2103.13367, paragraph "Quantum circuits and LOCC" (unitary gates and "local
(orthogonal) measurements"). -/
def IsUnitaryOrMeasurement (K : KrausFamily α β) : Prop :=
  K.IsUnitary ∨ ∃ (e : K.Index ≃ α) (f : α ≃ β), ∀ i, K.op i = Matrix.single (f (e i)) (e i) 1

theorem IsUnitary.isUnitaryOrMeasurement {K : KrausFamily α β} (h : K.IsUnitary) :
    K.IsUnitaryOrMeasurement :=
  Or.inl h

/-- The measurement of a basis is a local family of a measurement circuit. -/
theorem isUnitaryOrMeasurement_measure : (measure α).IsUnitaryOrMeasurement :=
  Or.inr ⟨Equiv.refl _, Equiv.refl _, fun _ ↦ rfl⟩

/-- The local families of a measurement circuit are trace-preserving. -/
theorem IsUnitaryOrMeasurement.isTP {K : KrausFamily α β} (h : K.IsUnitaryOrMeasurement) :
    K.IsTP := by
  rcases h with h | ⟨e, f, hK⟩
  · exact h.isTP
  · have : ∀ i, (K.op i)ᴴ * K.op i = Matrix.single (e i) (e i) 1 := fun i ↦ by
      rw [hK, conjTranspose_single, star_one, single_mul_single_same, mul_one]
    rw [IsTP, effect, Fintype.sum_congr _ _ this,
      e.sum_comp (fun a ↦ (Matrix.single a a 1 : Matrix α α ℂ))]
    ext a b
    rcases eq_or_ne a b with rfl | hab
    · simp [Matrix.sum_apply, single_apply]
    · simp [Matrix.sum_apply, single_apply, one_apply, hab]

end KrausFamily

namespace QuantumCircuit

variable {S : Type} [Fintype S] [DecidableEq S] {Γ : Geometry S}

namespace Circuit

variable {G : Finset S → (S → Type) → (S → Type) → Type 1} [GateFamily G]

/-! ### Implementations -/

section Implementation

variable {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The circuit `c` *implements* the matrix `W` on the set `E` of vectors: on every branch `p`,
its Kraus operator maps each `v ∈ E` to a scalar multiple of `W v`. Whatever the outcomes, the
circuit acts on `E` as `W`, up to a scalar.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements" ("correcting (without
postselection) based on the measurement outcomes"); arXiv:2103.13367, paragraph "State
transformations with QC and LOCC" (deterministic transformations). -/
def IsImplementationOn (ev : Interpretation G) (c : Circuit Γ G X Z) (E : Set (Config X → ℂ))
    (W : Matrix (Config Z) (Config X) ℂ) : Prop :=
  ∀ v ∈ E, ∀ p, ∃ z : ℂ, c.kraus ev p *ᵥ v = z • (W *ᵥ v)

variable {ev : Interpretation G}

theorem IsImplementationOn.mono {c : Circuit Γ G X Z} {E E' : Set (Config X → ℂ)}
    {W : Matrix (Config Z) (Config X) ℂ} (h : c.IsImplementationOn ev E W) (hE : E' ⊆ E) :
    c.IsImplementationOn ev E' W :=
  fun v hv ↦ h v (hE hv)

/-- The empty circuit implements the identity. -/
theorem isImplementationOn_done (E : Set (Config X → ℂ)) :
    (done X : Circuit Γ G X X).IsImplementationOn ev E 1 :=
  fun v _ _ ↦ ⟨1, by rw [kraus_done, one_smul]⟩

/-- A circuit every Kraus operator of which is `U` implements `U` on every set. -/
theorem isImplementationOn_of_kraus_eq {c : Circuit Γ G X Z} {U : Matrix (Config Z) (Config X) ℂ}
    (h : ∀ p, c.kraus ev p = U) (E : Set (Config X → ℂ)) : c.IsImplementationOn ev E U :=
  fun _ _ p ↦ ⟨1, by rw [h p, one_smul]⟩

variable [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)]

/-- **Implementations compose.** If `c` implements `W` on `E`, `W` maps `E` into `E'`, and every
continuation `k p` implements `W'` on `E'`, then `c.append k` implements `W' W` on `E`. -/
theorem IsImplementationOn.append {c : Circuit Γ G X Y} {k : c.Index → Circuit Γ G Y Z}
    {E : Set (Config X → ℂ)} {E' : Set (Config Y → ℂ)} {W : Matrix (Config Y) (Config X) ℂ}
    {W' : Matrix (Config Z) (Config Y) ℂ} (hc : c.IsImplementationOn ev E W)
    (hk : ∀ p, (k p).IsImplementationOn ev E' W') (hE : ∀ v ∈ E, W *ᵥ v ∈ E') :
    (c.append k).IsImplementationOn ev E (W' * W) := by
  intro v hv q
  obtain ⟨z, hz⟩ := hc v hv (c.appendIndexEquiv k q).1
  obtain ⟨z', hz'⟩ := hk _ (W *ᵥ v) (hE v hv) (c.appendIndexEquiv k q).2
  refine ⟨z * z', ?_⟩
  rw [kraus_append, ← mulVec_mulVec, hz, mulVec_smul, hz', smul_smul, mulVec_mulVec]

/-- If `c` implements `W` on `E`, `W` maps `E` into `E'` and `c'` implements `W'` on `E'`, then
`c` followed by `c'` implements `W' W` on `E`. -/
theorem IsImplementationOn.comp {c : Circuit Γ G X Y} {c' : Circuit Γ G Y Z}
    {E : Set (Config X → ℂ)} {E' : Set (Config Y → ℂ)} {W : Matrix (Config Y) (Config X) ℂ}
    {W' : Matrix (Config Z) (Config Y) ℂ} (hc : c.IsImplementationOn ev E W)
    (hc' : c'.IsImplementationOn ev E' W') (hE : ∀ v ∈ E, W *ᵥ v ∈ E') :
    (c.comp c').IsImplementationOn ev E (W' * W) :=
  hc.append (fun _ ↦ hc') hE

omit [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] in
/-- **Input-independent scalars on a subspace.** If `c` implements an isometry `W` on a linear
subspace `E`, then on each branch the scalar does not depend on the input: the Kraus operator of
the branch agrees on `E` with one scalar multiple of `W`. The scalar may be zero.

The linear-algebra step is Mathlib's characterization of the endomorphisms preserving every
line, `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`.

Source: arXiv:2307.01696, paragraphs "Tree-RG circuit with measurements" and "Long-range MPS
using measurements" (superpositions of logical sectors). -/
theorem IsImplementationOn.exists_smul_of_isometry [∀ s, Fintype (Z s)] {c : Circuit Γ G X Z}
    {E : Submodule ℂ (Config X → ℂ)} {W : Matrix (Config Z) (Config X) ℂ}
    (h : c.IsImplementationOn ev (E : Set (Config X → ℂ)) W) (hW : Wᴴ * W = 1) (p : c.Index) :
    ∃ z : ℂ, ∀ v ∈ E, c.kraus ev p *ᵥ v = z • (W *ᵥ v) := by
  set K := c.kraus ev p
  have hpoint : ∀ v ∈ E, ∃ z : ℂ, K *ᵥ v = z • (W *ᵥ v) := fun v hv ↦ h v hv p
  have hback : ∀ v ∈ E, ∀ z : ℂ, K *ᵥ v = z • (W *ᵥ v) → Wᴴ *ᵥ (K *ᵥ v) = z • v := by
    intro v _ z hz
    rw [hz, mulVec_smul, mulVec_mulVec, hW, one_mulVec]
  have hmem : ∀ v : E, Wᴴ *ᵥ (K *ᵥ (v : Config X → ℂ)) ∈ E := fun v ↦ by
    obtain ⟨z, hz⟩ := hpoint v v.2
    rw [hback v v.2 z hz]
    exact E.smul_mem z v.2
  let f : E →ₗ[ℂ] E :=
    { toFun := fun v ↦ ⟨Wᴴ *ᵥ (K *ᵥ (v : Config X → ℂ)), hmem v⟩
      map_add' := fun u v ↦ Subtype.ext (by simp [mulVec_add])
      map_smul' := fun z v ↦ Subtype.ext (by simp [mulVec_smul]) }
  obtain ⟨z, hz⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := f)
    fun v ↦ by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · rw [LinearIndependent.pair_iff' hv]
        obtain ⟨a, ha⟩ := hpoint v v.2
        exact fun hlin ↦ hlin a (Subtype.ext (hback v v.2 a ha)).symm
  refine ⟨z, fun v hv ↦ ?_⟩
  obtain ⟨a, ha⟩ := hpoint v hv
  have hf : Wᴴ *ᵥ (K *ᵥ v) = z • v :=
    congrArg (fun g : E →ₗ[ℂ] E ↦ ((g ⟨v, hv⟩ : E) : Config X → ℂ)) hz
  rw [hback v hv a ha] at hf
  by_cases hv0 : v = 0
  · simp [hv0]
  · rw [ha, smul_left_injective ℂ hv0 hf]

end Implementation

/-! ### A nonzero branch -/

section Branch

variable {X Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)] [∀ s, Finite (Z s)]

/-- A circuit whose local families are trace-preserving leaves a nonzero vector nonzero on some
branch: the outcomes of nonzero probability exist. -/
theorem exists_kraus_mulVec_ne_zero (ev : Interpretation G) (c : Circuit Γ G X Z)
    (h : c.Forall ev KrausFamily.IsTP) {v : Config X → ℂ} (hv : v ≠ 0) :
    ∃ p, c.kraus ev p *ᵥ v ≠ 0 := by
  have := fun s ↦ Fintype.ofFinite (Z s)
  by_contra hc
  push Not at hc
  have hE := c.isTP_krausFamily ev h
  refine hv ?_
  rw [← one_mulVec v, ← hE, KrausFamily.effect, sum_mulVec]
  exact Finset.sum_eq_zero fun p _ ↦ by
    rw [← mulVec_mulVec]
    change (c.kraus ev p)ᴴ *ᵥ (c.kraus ev p *ᵥ v) = 0
    rw [hc p, mulVec_zero]

omit [∀ s, Finite (Z s)] in
/-- On a pure input `|v⟩⟨v|` the map of a circuit is the sum over the branches of the projectors
onto the unnormalized outputs `Kₚ v`; a branch of probability zero contributes `0`. -/
theorem map_vecMulVec [∀ s, Fintype (Z s)] (ev : Interpretation G) (c : Circuit Γ G X Z)
    (v : Config X → ℂ) :
    c.map ev (vecMulVec v (star v)) =
      ∑ p, vecMulVec (c.kraus ev p *ᵥ v) (star (c.kraus ev p *ᵥ v)) := by
  simp only [map, krausFamily, KrausFamily.map_apply]
  change ∑ p, c.kraus ev p * vecMulVec v (star v) * (c.kraus ev p)ᴴ = _
  simp_rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec]

omit [∀ s, Finite (Z s)] in
/-- **Removal of measurements on a subspace.** Let a circuit of trace-preserving local families
implement an isometry `W` on a linear subspace `E`. Then its map agrees on the operators
`|u⟩⟨v|` with `u, v ∈ E` with the conjugation by `W`: averaged over the outcomes, the circuit is
the coherent operation `W` on `E`. Every branch acts on `E` as `zₚ W`
(`IsImplementationOn.exists_smul_of_isometry`), and the trace preservation gives
`∑ₚ |zₚ|² = 1` as soon as `E ≠ 0`.

Source: arXiv:2307.01696, paragraphs "Tree-RG circuit with measurements" and "Long-range MPS
using measurements" (measurements and corrections acting on superpositions of logical
sectors). -/
theorem IsImplementationOn.map_vecMulVec_eq [∀ s, Fintype (Z s)] (ev : Interpretation G)
    {c : Circuit Γ G X Z} (hTP : c.Forall ev KrausFamily.IsTP)
    {E : Submodule ℂ (Config X → ℂ)} {W : Matrix (Config Z) (Config X) ℂ}
    (h : c.IsImplementationOn ev (E : Set (Config X → ℂ)) W) (hW : Wᴴ * W = 1) {u v : Config X → ℂ}
    (hu : u ∈ E) (hv : v ∈ E) :
    c.map ev (vecMulVec u (star v)) = vecMulVec (W *ᵥ u) (star (W *ᵥ v)) := by
  classical
  choose z hz using fun p ↦ h.exists_smul_of_isometry hW p
  have hmap : c.map ev (vecMulVec u (star v)) =
      (∑ p, z p * star (z p)) • vecMulVec (W *ᵥ u) (star (W *ᵥ v)) := by
    simp only [map, krausFamily, KrausFamily.map_apply]
    change ∑ p, c.kraus ev p * vecMulVec u (star v) * (c.kraus ev p)ᴴ = _
    simp_rw [mul_vecMulVec, vecMulVec_mul, ← star_mulVec, hz _ u hu, hz _ v hv, star_smul,
      smul_vecMulVec, vecMulVec_smul, smul_smul, ← Finset.sum_smul]
  rw [hmap]
  by_cases hE : ∃ w ∈ E, w ≠ 0
  · obtain ⟨w, hw, hw0⟩ := hE
    have hnorm : ∀ x : Config X → ℂ, ∀ K : Matrix (Config Z) (Config X) ℂ,
        star (K *ᵥ x) ⬝ᵥ (K *ᵥ x) = star x ⬝ᵥ ((Kᴴ * K) *ᵥ x) := fun x K ↦ by
      rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
    have hsum : (∑ p, z p * star (z p)) * (star w ⬝ᵥ w) = star w ⬝ᵥ w := by
      have hE1 := c.isTP_krausFamily ev hTP
      have : star w ⬝ᵥ w = ∑ p, star (c.kraus ev p *ᵥ w) ⬝ᵥ (c.kraus ev p *ᵥ w) := by
        have h1 : (∑ p, (c.kraus ev p)ᴴ * c.kraus ev p) *ᵥ w = w :=
          calc (∑ p, (c.kraus ev p)ᴴ * c.kraus ev p) *ᵥ w = (c.krausFamily ev).effect *ᵥ w := rfl
            _ = w := by rw [hE1, one_mulVec]
        conv_lhs => arg 2; rw [← h1]
        rw [sum_mulVec, dotProduct_sum]
        exact Finset.sum_congr rfl fun p _ ↦ (hnorm w _).symm
      have key : ∀ p, star (c.kraus ev p *ᵥ w) ⬝ᵥ (c.kraus ev p *ᵥ w) =
          z p * star (z p) * (star w ⬝ᵥ w) := fun p ↦ by
        rw [hz p w hw, star_smul, smul_dotProduct, dotProduct_smul, hnorm, hW, one_mulVec,
          smul_eq_mul, smul_eq_mul, Complex.star_def]
        ring
      rw [Finset.sum_congr rfl fun p _ ↦ key p, ← Finset.sum_mul] at this
      exact this.symm
    have hww : star w ⬝ᵥ w ≠ 0 := fun h0 ↦ hw0 (dotProduct_star_self_eq_zero.mp h0)
    rw [mul_left_eq_self₀.mp hsum |>.resolve_right hww, one_smul]
  · push Not at hE
    rw [hE u hu, hE v hv]
    simp

end Branch

/-! ### Measurement with corrections -/

section MeasureCorrect

variable {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- The measurement of the region `D` in the computational basis, followed by the onsite matrices
`V m s` chosen by the outcome `m`, a configuration of `D`.

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC" ("we sequentially
measure each ancilla ... and apply `U ∈ LU` depending on the outcomes of all previous
measurements"). -/
def measureCorrect (D : Finset S) (V : RegionConfig X D → (s : S) → Matrix (X s) (X s) ℂ) :
    Circuit Γ G X X :=
  step (Layer.measure D) fun i ↦
    ofLayer (Layer.ofOnsite fun s ↦ KrausFamily.single (V (Layer.measure.outcome i) s))

/-- The Kraus operator of a measurement with corrections: the projection onto the outcome `m`,
placed on `D`, followed by the product of the corrections `V m s`. -/
theorem kraus_measureCorrect (ev : Interpretation G) (D : Finset S)
    (V : RegionConfig X D → (s : S) → Matrix (X s) (X s) ℂ)
    (p : (measureCorrect (Γ := Γ) (G := G) D V).Index) :
    (measureCorrect (Γ := Γ) (G := G) D V).kraus ev p =
      prodOp (V (Layer.measure.outcome p.1)) *
        place D (single (Layer.measure.outcome p.1) (Layer.measure.outcome p.1) 1) := by
  obtain ⟨i, q⟩ := p
  change (ofLayer _).kraus ev q * (Layer.measure D).kraus ev i = _
  rw [kraus_ofLayer, Layer.kraus_ofOnsite, Layer.kraus_measure]
  rfl

/-- A measurement with onsite corrections has depth `0`. -/
theorem depth_measureCorrect (D : Finset S)
    (V : RegionConfig X D → (s : S) → Matrix (X s) (X s) ℂ) :
    (measureCorrect (Γ := Γ) (G := G) D V).depth = 0 := by
  rw [measureCorrect, depth_step]
  change (Layer.ofOnsite _).depth + _ = 0
  rw [Layer.depth_ofOnsite, zero_add]
  refine (Finset.sup_eq_bot_iff _ _).mpr fun i _ ↦ ?_
  rw [depth_ofLayer, Layer.depth_ofOnsite]
  rfl

/-- **A round implements a matrix.** Let every Kraus operator of the circuit `u` be `U`. If for
every outcome `m` the operator `(⊗ₛ V m s) P_m U` agrees on `E` with one scalar multiple of `W`,
`P_m` the projection onto `m` placed on `D`, then `u` followed by the measurement of `D` with
the corrections `V` implements `W` on `E`. -/
theorem isImplementationOn_comp_measureCorrect (ev : Interpretation G) {u : Circuit Γ G X X}
    {U : Matrix (Config X) (Config X) ℂ} (hU : ∀ p, u.kraus ev p = U) {D : Finset S}
    {V : RegionConfig X D → (s : S) → Matrix (X s) (X s) ℂ} {E : Set (Config X → ℂ)}
    {W : Matrix (Config X) (Config X) ℂ}
    (h : ∀ m, ∃ z : ℂ, ∀ v ∈ E, (prodOp (V m) * place D (single m m 1) * U) *ᵥ v = z • (W *ᵥ v)) :
    (u.comp (measureCorrect D V)).IsImplementationOn ev E W := by
  intro v hv q
  rw [kraus_comp, kraus_measureCorrect, hU]
  obtain ⟨z, hz⟩ := h (Layer.measure.outcome (u.compIndexEquiv _ q).2.1)
  exact ⟨z, hz v hv⟩

omit [Fintype S] in
/-- A measurement with unitary corrections is a measurement circuit. -/
theorem forall_measureCorrect (D : Finset S)
    {V : RegionConfig X D → (s : S) → Matrix (X s) (X s) ℂ}
    (hV : ∀ m s, V m s ∈ unitaryGroup (X s) ℂ) :
    (measureCorrect (Γ := Γ) (G := KrausGate) D V).Forall KrausGate.ev
      KrausFamily.IsUnitaryOrMeasurement := by
  refine ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun s ↦ ?_⟩, fun i ↦ ?_⟩
  · change (if s.1 ∈ D then KrausFamily.measure (X s) else
      KrausFamily.single 1).IsUnitaryOrMeasurement
    split_ifs
    · exact KrausFamily.isUnitaryOrMeasurement_measure
    · exact (KrausFamily.isUnitary_single (one_mem _)).isUnitaryOrMeasurement
  · refine ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _), fun s ↦ ?_⟩, fun _ ↦ trivial⟩
    exact (KrausFamily.isUnitary_single (hV _ _)).isUnitaryOrMeasurement

end MeasureCorrect

end Circuit

/-! ### Deterministic conversions -/

section Conversion

variable (Γ) {X Y Z : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]
  [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Finite (Z s)]

/-- **Deterministic conversion with measurements.** The nonzero vector `φ` is converted into `ψ`
in depth `T`: some measurement circuit of depth at most `T` maps `φ` on every branch to a scalar
multiple of `ψ`. The branches of probability zero give the zero multiple. A preparation of `ψ`
is a conversion from a basis configuration or from a product vector.

The model counts the layers using a cell of positive cost; measurements, onsite unitaries and the
classical communication of outcomes, to every later layer, are free. The number of rounds of
measurements is not bounded; arXiv:2103.13367 performs one round in its definition of `QCcc_ℓ`
(`IsOneRoundConversion`) and notes "a more general scheme with multiple rounds of LOCC".

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC" (deterministic
transformations, and "a more general scheme with multiple rounds of LOCC"); arXiv:2307.01696,
paragraph "Tree-RG circuit with measurements". -/
def IsMeasurementConversion (T : ℕ) (φ : Config X → ℂ) (ψ : Config Z → ℂ) : Prop :=
  φ ≠ 0 ∧ ∃ c : Circuit Γ KrausGate X Z,
    c.Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement ∧ c.depth ≤ T ∧
      ∀ p, ∃ z : ℂ, c.kraus KrausGate.ev p *ᵥ φ = z • ψ

variable {Γ}

/-- A vector converted from a nonzero vector is nonzero. -/
theorem IsMeasurementConversion.ne_zero {T : ℕ} {φ : Config X → ℂ} {ψ : Config Z → ℂ}
    (h : IsMeasurementConversion Γ T φ ψ) : ψ ≠ 0 := by
  obtain ⟨hφ, c, hc, -, hψ⟩ := h
  obtain ⟨p, hp⟩ := c.exists_kraus_mulVec_ne_zero KrausGate.ev
    (hc.mono fun _ hK ↦ hK.isTP) hφ
  obtain ⟨z, hz⟩ := hψ p
  rintro rfl
  exact hp (by rw [hz, smul_zero])

omit [∀ s, Finite (Z s)] in
theorem IsMeasurementConversion.mono {T T' : ℕ} {φ : Config X → ℂ} {ψ : Config Z → ℂ}
    (h : IsMeasurementConversion Γ T φ ψ) (hT : T ≤ T') : IsMeasurementConversion Γ T' φ ψ :=
  let ⟨hφ, c, hc, hd, hψ⟩ := h
  ⟨hφ, c, hc, hd.trans hT, hψ⟩

/-- Every nonzero vector is converted into itself in depth `0`. -/
theorem IsMeasurementConversion.refl {φ : Config X → ℂ} (hφ : φ ≠ 0) :
    IsMeasurementConversion Γ 0 φ φ :=
  ⟨hφ, .done X, trivial, le_rfl, fun _ ↦ ⟨1, by rw [Circuit.kraus_done, one_mulVec, one_smul]⟩⟩

omit [∀ s, Finite (Z s)] in
/-- A scalar multiple of the target is reached by the same conversion. -/
theorem IsMeasurementConversion.smul {T : ℕ} {φ : Config X → ℂ} {ψ : Config Z → ℂ}
    (h : IsMeasurementConversion Γ T φ ψ) {a : ℂ} (ha : a ≠ 0) :
    IsMeasurementConversion Γ T φ (a • ψ) := by
  obtain ⟨hφ, c, hc, hd, hψ⟩ := h
  refine ⟨hφ, c, hc, hd, fun p ↦ ?_⟩
  obtain ⟨z, hz⟩ := hψ p
  exact ⟨z * a⁻¹, by rw [hz, smul_smul, mul_assoc, inv_mul_cancel₀ ha, mul_one]⟩

omit [∀ s, Finite (Z s)] in
/-- **Composition of conversions.** Converting `φ` into `ψ` in depth `T₁` and `ψ` into `χ` in
depth `T₂` converts `φ` into `χ` in depth `T₁ + T₂`; the second circuit may depend on the
outcomes of the first.

Source: arXiv:2103.13367, paragraph "Phases of matter" (composition of transformations). -/
theorem IsMeasurementConversion.trans {T₁ T₂ : ℕ} {φ : Config X → ℂ} {ψ : Config Y → ℂ}
    {χ : Config Z → ℂ} (h₁ : IsMeasurementConversion Γ T₁ φ ψ)
    (h₂ : IsMeasurementConversion Γ T₂ ψ χ) : IsMeasurementConversion Γ (T₁ + T₂) φ χ := by
  obtain ⟨hφ, c, hc, hd, hψ⟩ := h₁
  obtain ⟨-, c', hc', hd', hχ⟩ := h₂
  refine ⟨hφ, c.comp c', hc.comp _ hc', (Circuit.depth_comp c c').trans (Nat.add_le_add hd hd'),
    fun q ↦ ?_⟩
  obtain ⟨z, hz⟩ := hψ (c.compIndexEquiv c' q).1
  obtain ⟨z', hz'⟩ := hχ (c.compIndexEquiv c' q).2
  exact ⟨z * z', by rw [Circuit.kraus_comp, ← mulVec_mulVec, hz, mulVec_smul, hz', smul_smul]⟩

omit [∀ s, Finite (Z s)] in
/-- **Conversion from an implementation.** A measurement circuit of depth at most `T`
implementing `W` on a set containing the nonzero vector `φ` converts `φ` into `W φ` in depth `T`.

Source: arXiv:2307.01696, paragraph "Tree-RG circuit with measurements". -/
theorem Circuit.IsImplementationOn.isMeasurementConversion {T : ℕ} {c : Circuit Γ KrausGate X Z}
    {E : Set (Config X → ℂ)} {W : Matrix (Config Z) (Config X) ℂ}
    (h : c.IsImplementationOn KrausGate.ev E W)
    (hc : c.Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement) (hd : c.depth ≤ T)
    {φ : Config X → ℂ} (hφ : φ ≠ 0) (hφE : φ ∈ E) : IsMeasurementConversion Γ T φ (W *ᵥ φ) :=
  ⟨hφ, c, hc, hd, h φ hφE⟩

omit [∀ s, Finite (Z s)] in
/-- **Free onsite unitaries.** A conversion from `(⊗ₛ U s) φ`, for unitaries `U s`, is a
conversion from `φ` in the same depth: the unitaries form an onsite layer, of depth `0`. In
particular a conversion from a product vector is a conversion from a basis configuration. -/
theorem IsMeasurementConversion.of_prodOp {T : ℕ} {U : (s : S) → Matrix (X s) (X s) ℂ}
    (hU : ∀ s, U s ∈ unitaryGroup (X s) ℂ) {φ : Config X → ℂ} {ψ : Config Z → ℂ}
    (h : IsMeasurementConversion Γ T (prodOp U *ᵥ φ) ψ) : IsMeasurementConversion Γ T φ ψ := by
  obtain ⟨hφ, c, hc, hd, hψ⟩ := h
  let L : Layer Γ KrausGate X X := Layer.ofOnsite fun s ↦ KrausFamily.single (U s)
  have hL : ∀ i, L.kraus KrausGate.ev i = prodOp U := fun i ↦ Layer.kraus_ofOnsite _ _ i
  refine ⟨fun h0 ↦ hφ (by rw [h0, mulVec_zero]), (Circuit.ofLayer L).comp c,
    Circuit.Forall.comp _ ⟨⟨fun b ↦ absurd b.2 (Finset.notMem_empty _),
      fun s ↦ (KrausFamily.isUnitary_single (hU s)).isUnitaryOrMeasurement⟩, fun _ ↦ trivial⟩ hc,
    ?_, fun q ↦ ?_⟩
  · refine (Circuit.depth_comp _ c).trans ?_
    rw [Circuit.depth_ofLayer, Layer.depth_ofOnsite, zero_add]
    exact hd
  · obtain ⟨z, hz⟩ := hψ ((Circuit.ofLayer L).compIndexEquiv c q).2
    refine ⟨z, ?_⟩
    rw [Circuit.kraus_comp, Circuit.kraus_ofLayer, hL, ← mulVec_mulVec, hz]

omit [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Finite (Z s)] in
/-- **Unitary circuits are measurement circuits.** A unitary circuit `U` of depth at most `T`
converts every nonzero vector `φ` into `U φ`, measuring no site. -/
theorem IsUnitaryCircuit.isMeasurementConversion {T : ℕ} {U : Matrix (Config X) (Config X) ℂ}
    (hU : IsUnitaryCircuit Γ T U) {φ : Config X → ℂ} (hφ : φ ≠ 0) :
    IsMeasurementConversion Γ T φ (U *ᵥ φ) := by
  obtain ⟨c, hd, rfl⟩ := hU
  exact ⟨hφ, c.toCircuit, c.forall_isUnitary.mono fun _ hK ↦ hK.isUnitaryOrMeasurement, hd,
    fun p ↦ ⟨1, by rw [c.kraus_eq_op, one_smul]⟩⟩

omit [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Finite (Z s)] in
/-- A nonzero vector prepared in depth `T` by a unitary circuit from a product vector is
converted from that product vector in depth `T`. -/
theorem IsPreparedInDepth.exists_isMeasurementConversion {T : ℕ} {ψ : Config X → ℂ}
    (h : IsPreparedInDepth Γ T ψ) (hψ : ψ ≠ 0) :
    ∃ v : (s : S) → X s → ℂ, IsMeasurementConversion Γ T (fun σ ↦ ∏ s, v s (σ s)) ψ := by
  obtain ⟨U, hU, v, rfl⟩ := h
  exact ⟨v, hU.isMeasurementConversion fun h0 ↦ hψ (by rw [h0, mulVec_zero])⟩

omit [∀ s, Finite (Z s)] in
/-- **Deterministic conversions are adaptive conversions.** A deterministic conversion of the unit
vector `φ` into the unit vector `ψ` in depth `T` is an adaptive conversion of `|φ⟩⟨φ|` into
`|ψ⟩⟨ψ|` in depth `T`: averaging over the outcomes, the circuit maps `|φ⟩⟨φ|` to
`(∑ₚ |zₚ|²) |ψ⟩⟨ψ|`, and the sum is `1` since the circuit preserves the trace.

Source: arXiv:2103.13367, paragraphs "Quantum circuits and LOCC" and "State transformations with
QC and LOCC". -/
theorem IsMeasurementConversion.isAdaptiveConversion [∀ s, Fintype (Z s)] {T : ℕ}
    {φ : Config X → ℂ}
    {ψ : Config Z → ℂ} (h : IsMeasurementConversion Γ T φ ψ)
    (hφ : (vecMulVec φ (star φ)).trace = 1) (hψ : (vecMulVec ψ (star ψ)).trace = 1) :
    IsAdaptiveConversion Γ T (vecMulVec φ (star φ)) (vecMulVec ψ (star ψ)) := by
  classical
  obtain ⟨-, c, hc, hd, hcψ⟩ := h
  choose z hz using hcψ
  have hTP : c.Forall KrausGate.ev KrausFamily.IsTP := hc.mono fun _ hK ↦ hK.isTP
  have hmap : c.map KrausGate.ev (vecMulVec φ (star φ)) =
      (∑ p, z p * star (z p)) • vecMulVec ψ (star ψ) := by
    simp_rw [c.map_vecMulVec, hz, star_smul, smul_vecMulVec, vecMulVec_smul, smul_smul,
      ← Finset.sum_smul]
  have htr := c.trace_map KrausGate.ev hTP (vecMulVec φ (star φ))
  rw [hmap, trace_smul, hψ, hφ, smul_eq_mul, mul_one] at htr
  exact ⟨_, ⟨c, hTP, hd, rfl⟩, by rw [hmap, htr, one_smul]⟩

omit [∀ s, Fintype (Y s)] [∀ s, DecidableEq (Y s)] [∀ s, Finite (Z s)] in
/-- **Measurement circuits are adaptive protocols.** The map of a measurement circuit of depth at
most `T` is realised by an adaptive protocol of depth at most `T`: the average over the outcomes
of the measurement circuit is a channel.

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC". -/
theorem Circuit.isAdaptiveProtocol_map [∀ s, Fintype (Z s)] {T : ℕ}
    {c : Circuit Γ KrausGate X Z} (hc : c.Forall KrausGate.ev KrausFamily.IsUnitaryOrMeasurement)
    (hd : c.depth ≤ T) : IsAdaptiveProtocol Γ T (c.map KrausGate.ev) :=
  ⟨c, hc.mono fun _ hK ↦ hK.isTP, hd, rfl⟩

end Conversion

/-! ### One round of measurements -/

section OneRound

variable (Γ) {X : S → Type} [∀ s, Fintype (X s)] [∀ s, DecidableEq (X s)]

/-- **Conversion with one round of measurements.** The nonzero vector `φ` is converted into `ψ`
by a unitary circuit `U` of depth at most `T₁`, the measurement of a region `D`, unitaries
`V m s` at every site chosen by the outcome `m`, and a unitary circuit `U'` of depth at most `T₂`
that does not depend on the outcome, so that every output `U' (⊗ₛ V m s) P_m U φ` is a scalar
multiple of `ψ`, `P_m` the projection onto the outcome `m` placed on `D`.

With `T₂ = 0` this is the class `QCcc_ℓ` of arXiv:2103.13367 at `ℓ = T₁`: a circuit of depth
`0` consists of onsite unitaries, free local unitaries in the source. A circuit `U'` of positive
depth is a second transformation, without measurements, composed with the first, as in
"Phases of matter" with `k = 2`. The correction at a site may depend on the whole outcome: the
classical communication is global. The differences from the source: any site may be measured,
in the computational basis fixed in advance, and the corrections are onsite unitaries applied
once after the measurement.

Source: arXiv:2103.13367, paragraph "State transformations with QC and LOCC" ("We first apply a
depth-`ℓ` circuit ... Then, we sequentially measure each ancilla `a_i` in some orthonormal basis
... and apply `U ∈ LU` depending on the outcomes of all previous measurements") and Definition
"Transformations under QC and LOCC"; arXiv:2307.01696, paragraph "Long-range MPS using
measurements" ("First create `|χ_{N/q}⟩`, which can be done in constant depth with measurements
... Subsequently, apply in parallel the isometries `W`"). -/
def IsOneRoundConversion (T₁ T₂ : ℕ) (φ ψ : Config X → ℂ) : Prop :=
  φ ≠ 0 ∧ ∃ (U U' : Matrix (Config X) (Config X) ℂ) (D : Finset S)
    (V : RegionConfig X D → (s : S) → Matrix (X s) (X s) ℂ),
    IsUnitaryCircuit Γ T₁ U ∧ IsUnitaryCircuit Γ T₂ U' ∧ (∀ m s, V m s ∈ unitaryGroup (X s) ℂ) ∧
    ∀ m, ∃ z : ℂ, (U' * prodOp (V m) * place D (single m m 1) * U) *ᵥ φ = z • ψ

variable {Γ}

/-- **One round is a measurement circuit.** A conversion with one round of measurements is a
deterministic conversion in the total depth: the circuit `U`, the measurement with corrections,
and the circuit `U'`. -/
theorem IsOneRoundConversion.isMeasurementConversion {T₁ T₂ : ℕ} {φ ψ : Config X → ℂ}
    (h : IsOneRoundConversion Γ T₁ T₂ φ ψ) : IsMeasurementConversion Γ (T₁ + T₂) φ ψ := by
  obtain ⟨hφ, U, U', D, V, ⟨u, hud, rfl⟩, ⟨u', hu'd, rfl⟩, hV, hψ⟩ := h
  refine ⟨hφ, u.toCircuit.comp ((Circuit.measureCorrect D V).comp u'.toCircuit),
    (u.forall_isUnitary.mono fun _ hK ↦ hK.isUnitaryOrMeasurement).comp _
      ((Circuit.forall_measureCorrect D hV).comp _
        (u'.forall_isUnitary.mono fun _ hK ↦ hK.isUnitaryOrMeasurement)), ?_, fun q ↦ ?_⟩
  · refine (Circuit.depth_comp _ _).trans (Nat.add_le_add hud ?_)
    refine (Circuit.depth_comp _ _).trans ?_
    rw [Circuit.depth_measureCorrect, zero_add]
    exact hu'd
  · rw [Circuit.kraus_comp, Circuit.kraus_comp, Circuit.kraus_measureCorrect, u.kraus_eq_op,
      u'.kraus_eq_op]
    simpa only [Matrix.mul_assoc] using hψ _

theorem IsOneRoundConversion.mono {T₁ T₂ T₁' T₂' : ℕ} {φ ψ : Config X → ℂ}
    (h : IsOneRoundConversion Γ T₁ T₂ φ ψ) (h₁ : T₁ ≤ T₁') (h₂ : T₂ ≤ T₂') :
    IsOneRoundConversion Γ T₁' T₂' φ ψ :=
  let ⟨hφ, U, U', D, V, hU, hU', hV, hψ⟩ := h
  ⟨hφ, U, U', D, V, hU.mono h₁, hU'.mono h₂, hV, hψ⟩

/-- **A circuit after one round.** A conversion with one round of measurements into `ψ`, followed
by a unitary circuit `W` of depth at most `T`, is a conversion into `W ψ`, the second circuit
deeper by `T`. -/
theorem IsOneRoundConversion.mulVec {T₁ T₂ T : ℕ} {φ ψ : Config X → ℂ}
    (h : IsOneRoundConversion Γ T₁ T₂ φ ψ) {W : Matrix (Config X) (Config X) ℂ}
    (hW : IsUnitaryCircuit Γ T W) : IsOneRoundConversion Γ T₁ (T₂ + T) φ (W *ᵥ ψ) := by
  obtain ⟨hφ, U, U', D, V, hU, hU', hV, hψ⟩ := h
  refine ⟨hφ, U, W * U', D, V, hU, add_comm T₂ T ▸ hW.mul hU', hV, fun m ↦ ?_⟩
  obtain ⟨z, hz⟩ := hψ m
  refine ⟨z, ?_⟩
  rw [← mulVec_smul, ← hz, mulVec_mulVec]
  simp only [Matrix.mul_assoc]

/-- **Unitary circuits are one round without measurements.** A unitary circuit `U` of depth at
most `T` converts every nonzero vector `φ` into `U φ` with one round of measurements in depth
`T`, measuring no site. -/
theorem IsUnitaryCircuit.isOneRoundConversion {T : ℕ} {U : Matrix (Config X) (Config X) ℂ}
    (hU : IsUnitaryCircuit Γ T U) {φ : Config X → ℂ} (hφ : φ ≠ 0) :
    IsOneRoundConversion Γ T 0 φ (U *ᵥ φ) := by
  refine ⟨hφ, U, 1, ∅, fun _ _ ↦ 1, hU, IsUnitaryCircuit.one Γ X 0, fun _ _ ↦ one_mem _,
    fun m ↦ ⟨1, ?_⟩⟩
  have hplace : ManyBody.place (∅ : Finset S) (single m m (1 : ℂ)) = 1 := by
    ext y x
    have hy : (fun v : {v // v ∈ (∅ : Finset S)} ↦ y v) = m :=
      funext fun v ↦ absurd v.2 (Finset.notMem_empty _)
    have hx : (fun v : {v // v ∈ (∅ : Finset S)} ↦ x v) = m :=
      funext fun v ↦ absurd v.2 (Finset.notMem_empty _)
    rw [ManyBody.place_apply, single_apply, one_apply, hy, hx]
    by_cases hxy : y = x
    · simp [hxy]
    · rw [ite_eq_right_iff.mpr fun h ↦ absurd (funext fun v ↦ h v (by simp)) hxy,
        ite_eq_right_iff.mpr fun h ↦ absurd h hxy]
  rw [hplace, ManyBody.prodOp_one, Matrix.one_mul, Matrix.one_mul, Matrix.one_mul, one_smul]

end OneRound

end QuantumCircuit
