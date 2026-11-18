import QICLean

/-!
# 3C.2 inventory: the missing core notions, as statements

Scratch definitions (some `sorry`) that the restated (c) theorems need. Each corresponds to a
core gap of the inventory; none of this is meant to be merged as written.
-/

open Matrix ManyBody QuantumCircuit

namespace Inventory

/-! ### Uniform systems (proposal: `ManyBody/Sites`, `abbrev Qudits`) -/

/-- The system with basis `Fin d` at every site of `V`. -/
abbrev Qudits (V : Type) (d : ℕ) : V → Type := fun _ ↦ Fin d

/-- Placement along an embedding: the configurations of the image of `e` are those of `X ∘ e`
(coordinator: one `ManyBody/Sites` identification). -/
noncomputable def regionConfigMapEquiv {V V' : Type} [Fintype V] (X : V' → Type) (e : V ↪ V') :
    RegionConfig X (Finset.univ.map e) ≃ Config (X ∘ e) := sorry

/-! ### Local properties used as predicates -/

/-- Every family is unitary (a local property). -/
abbrev IsUnitaryLocal {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (K : KrausFamily α β) : Prop :=
  K.IsUnitary

/-- Every family is trace-preserving (a local property). -/
abbrev IsTPLocal {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (K : KrausFamily α β) : Prop :=
  K.IsTP

/-! ### Geometries (gap: `Circuit/Geometry`) -/

/-- The ring on `Fin N`: bonds `{k, k + 1}` of cost `1`. -/
def ring (N : ℕ) [NeZero N] : Geometry (Fin N) where
  Cell := Fin N
  cell k := {k, k + 1}
  cost _ := 1

instance (N : ℕ) [NeZero N] : Fintype (ring N).Cell := inferInstanceAs (Fintype (Fin N))

/-- TNLean's layout of wires on sites, verbatim. -/
structure PhysicalPortLayout (N W : ℕ) where
  site : Fin W → Fin N
  port : Fin N ↪ Fin W
  site_port : ∀ i, site (port i) = i

/-- The port geometry on the wires: every set of wires inside one site at cost `0`, the bonds of
the ring between consecutive ports at cost `1`. -/
def portGeometry {N W : ℕ} [NeZero N] (P : PhysicalPortLayout N W) : Geometry (Fin W) where
  Cell := {D : Finset (Fin W) // ∃ i, ∀ w ∈ D, P.site w = i} ⊕ Fin N
  cell
    | .inl D => D.1
    | .inr k => {P.port k, P.port (k + 1)}
  cost
    | .inl _ => 0
    | .inr _ => 1

/-! ### Circuit classes (restrictions of `Circuit`) -/

end Inventory

namespace QuantumCircuit.Circuit

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Every intermediate basis has between `1` and `B` elements (gap: dimension bound). -/
def IsDimBounded {Γ : Geometry S} {G : Finset S → (S → Type) → (S → Type) → Type 1}
    [GateFamily G] (B : ℕ) : {X Z : S → Type} → Circuit Γ G X Z → Prop
  | X, _, done _ => ∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B
  | X, _, step _ next => (∀ s, 0 < Nat.card (X s) ∧ Nat.card (X s) ≤ B) ∧
      ∀ i, (next i).IsDimBounded B

end QuantumCircuit.Circuit

namespace Inventory

variable {S : Type} [Fintype S] [DecidableEq S]


/-- An unbranched circuit of plain gates with trace-preserving local families, of depth at
most `T`, realising the channel `Φ` (TNLean's `IsLocalChannelProtocol` on the ring when
`Γ = ring N` and the end systems are uniform; `IsPhysicalPortProtocol` when
`Γ = portGeometry P`). -/
def IsProtocol (Γ : Geometry S) (T : ℕ) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.IsUnbranched ∧ c.Forall KrausGate.ev IsTPLocal ∧
    c.depth ≤ T ∧ c.map KrausGate.ev = Φ

/-- The same with every local family unitary and the unique Kraus operator `U`
(`IsPhysicalPortUnitary` when `Γ = portGeometry P`). -/
def IsUnitaryCircuit (Γ : Geometry S) (T : ℕ) {X : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] (U : Matrix (Config X) (Config X) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X X, c.IsUnbranched ∧ c.Forall KrausGate.ev IsUnitaryLocal ∧
    c.depth ≤ T ∧ ∀ p, c.kraus KrausGate.ev p = U

/-- A dimension-bounded protocol (`IsDimensionBoundedLocalChannelProtocol B`). -/
def IsBoundedProtocol (Γ : Geometry S) (B T : ℕ) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.IsUnbranched ∧ c.Forall KrausGate.ev IsTPLocal ∧
    c.depth ≤ T ∧ c.IsDimBounded B ∧ c.map KrausGate.ev = Φ

/-- An adaptive protocol: branching allowed, every local family a component of an instrument,
so the Kraus family of the circuit is trace-preserving (`IsAdaptiveChannelProtocol`). -/
def IsAdaptiveProtocol (Γ : Geometry S) (T : ℕ) {X Z : S → Type} [∀ s, Fintype (X s)]
    [∀ s, DecidableEq (X s)] [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (Φ : Matrix (Config X) (Config X) ℂ →ₗ[ℂ] Matrix (Config Z) (Config Z) ℂ) : Prop :=
  ∃ c : Circuit Γ KrausGate X Z, c.Forall KrausGate.ev IsTPLocal ∧ c.depth ≤ T ∧
    c.map KrausGate.ev = Φ

/-! ### Blocking (gap) -/

/-- The system on `S'` whose basis at `s'` is the configurations of the fibre of `f`. -/
abbrev blockSystem {S' : Type} (f : S → S') (X : S → Type) : S' → Type :=
  fun s' ↦ (s : {s // f s = s'}) → X s

/-- The configurations of the blocked system are those of the system. -/
noncomputable def blockConfigEquiv {S' : Type} (f : S → S') (X : S → Type) :
    Config (blockSystem f X) ≃ Config X := sorry

end Inventory

/-! # Group C: physical ports, restated in the circuit core -/

namespace Inventory.C

/-! ### Gaps -/

/-- Gap G1 (port geometry on any type of wires): the wires `V` sit at the spatial sites through
`site`; the cost-0 cells are the sets of wires inside one fibre of `site` (down-closed, gap G2),
the cost-1 cells are the ring bonds `{port k, port (k + 1)}`. `portGeometry P` is the case
`V = Fin W` (see `portGeometry_eq` below). -/
def portGeometryOf {V : Type} [DecidableEq V] {N : ℕ} [NeZero N] (site : V → Fin N)
    (port : Fin N → V) : Geometry V where
  Cell := {D : Finset V // ∃ i, ∀ w ∈ D, site w = i} ⊕ Fin N
  cell
    | .inl D => D.1
    | .inr k => {port k, port (k + 1)}
  cost
    | .inl _ => 0
    | .inr _ => 1

theorem portGeometry_eq {N W : ℕ} [NeZero N] (P : PhysicalPortLayout N W) :
    portGeometry P = portGeometryOf P.site P.port := by
  unfold portGeometry portGeometryOf
  congr 1 <;> funext b <;> rcases b with b | b <;> rfl

/-- Gap G1 (`PhysicalPortLayout.append`): the port geometry on the wires `V ⊕ Fin A`, the new
wire `a` at the site `owner a`, the ports unchanged. -/
def appendGeometry {V : Type} [DecidableEq V] {N A : ℕ} [NeZero N] (site : V → Fin N)
    (port : Fin N → V) (owner : Fin A → Fin N) : Geometry (V ⊕ Fin A) :=
  portGeometryOf (Sum.elim site owner) fun i ↦ .inl (port i)

/-- The port wire `(i, 0)` of the site `i` in the register layout (`PortRegisters.layout`). -/
def portWire (N k : ℕ) : Fin N ↪ Fin N × Fin (1 + k + k) :=
  ⟨fun i ↦ (i, ⟨0, by omega⟩), fun _ _ h ↦ congrArg Prod.fst h⟩

/-- Gap G1 (`PortRegisters.layout N k`, without the encoding `Fin (N * (1 + k + k))`): the port
geometry on the wires `Fin N × Fin (1 + k + k)`, one port, `k` data and `k` scratch wires at
each site. -/
def registers (N k : ℕ) [NeZero N] : Geometry (Fin N × Fin (1 + k + k)) :=
  portGeometryOf Prod.fst (portWire N k)

open Classical in
/-- Gap (change of site set with fresh wires; `appendEnvironmentInput`, and
`wordInitialization (portWordCode d k)` for `ι = portWire N k`): the input on the wires `ι V`,
every other wire prepared at `0`. In the core this is a cost-0 onsite layer `PUnit → Fin d` on
idle sites reached through `mapSites`; the core has no map from configurations of `V` to those
of `V'` that names it on uniform systems. -/
noncomputable def freshInput {V V' : Type} (ι : V ↪ V') (d : ℕ) [NeZero d] :
    Matrix (Config (Qudits V d)) (Config (Qudits V d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits V' d)) (Config (Qudits V' d)) ℂ where
  toFun ρ := Matrix.of fun z z' ↦ ρ (fun v ↦ z (ι v)) (fun v ↦ z' (ι v)) *
    if ∀ w, w ∉ Set.range ι → z w = 0 ∧ z' w = 0 then 1 else 0
  map_add' _ _ := by
    ext; simp only [Matrix.of_apply, Matrix.add_apply, add_mul]
  map_smul' _ _ := by
    ext; simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

open Classical in
/-- The vector form of `freshInput`: `ψ` on the wires `ι V`, `|0⟩` on the other wires
(`fixedEnvEmbedding 0 *ᵥ ψ` in TNLean). -/
noncomputable def freshVector {V V' : Type} (ι : V ↪ V') (d : ℕ) [NeZero d]
    (ψ : Config (Qudits V d) → ℂ) : Config (Qudits V' d) → ℂ :=
  fun z ↦ ψ (fun v ↦ z (ι v)) * if ∀ w, w ∉ Set.range ι → z w = 0 then 1 else 0

/-- Gap (`discardAppendedEnvironment`): the partial trace over the wires `R` of `V ⊕ R`. In the
core this is a cost-0 onsite layer `Fin d → PUnit` on the wires `R`. -/
noncomputable def discardEnvironment (V R : Type) [Fintype R] [DecidableEq R] (d : ℕ) :
    Matrix (Config (Qudits (V ⊕ R) d)) (Config (Qudits (V ⊕ R) d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits V d)) (Config (Qudits V d)) ℂ where
  toFun A := Matrix.of fun x x' ↦ ∑ a : R → Fin d, A (Sum.elim x a) (Sum.elim x' a)
  map_add' _ _ := by
    ext; simp only [Matrix.of_apply, Matrix.add_apply, Finset.sum_add_distrib]
  map_smul' _ _ := by
    ext; simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]

/-- Gap G3 (blocking; `dataChannelLift N k d`): a channel on the native ring `Qudits (Fin N)
(d ^ k)` acting on the `k` data wires `(i, 1), …, (i, k)` of every site `i` of the registers,
through `Fin (d ^ k) ≃ (Fin k → Fin d)`, and as the identity on the port and scratch wires. -/
noncomputable def dataLift (N k d : ℕ) :
    (Matrix (Config (Qudits (Fin N) (d ^ k))) (Config (Qudits (Fin N) (d ^ k))) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin N) (d ^ k))) (Config (Qudits (Fin N) (d ^ k))) ℂ) →
    (Matrix (Config (Qudits (Fin N × Fin (1 + k + k)) d))
        (Config (Qudits (Fin N × Fin (1 + k + k)) d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin N × Fin (1 + k + k)) d))
        (Config (Qudits (Fin N × Fin (1 + k + k)) d)) ℂ) :=
  sorry

/-! ### Channel-level lemmas (to move into `QICLean/Channel`) -/

/- TNLean/Circuit/Channel/PhysicalPortLocalDilation.lean:
theorem exists_qudit_freshEnvironment_unitary {d m : ℕ} [NeZero d]
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ))
    (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix.unitaryGroup ((Fin m → Fin d) × (Fin (2 * m) → Fin d)) ℂ,
      ∀ X : Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ,
        Φ X = partialTraceRight
          ((U : Matrix ((Fin m → Fin d) × (Fin (2 * m) → Fin d))
            ((Fin m → Fin d) × (Fin (2 * m) → Fin d)) ℂ) *
            freshEnvironmentInput (0 : Fin (2 * m) → Fin d) X * Uᴴ)
-/

/-- A trace-preserving Kraus family on `m` qudits is the reduced map of a unitary on the `m`
qudits and `2 m` fresh qudits prepared at `0`. (`IsKrausCPTP Φ` becomes a TP `KrausFamily`,
the form of a gate; the two are equivalent.) -/
theorem exists_qudit_freshEnvironment_unitary {d m : ℕ} [NeZero d]
    (K : KrausFamily (Config (Qudits (Fin m) d)) (Config (Qudits (Fin m) d))) (hK : K.IsTP) :
    ∃ U : Matrix.unitaryGroup (Config (Qudits (Fin m) d) × Config (Qudits (Fin (2 * m)) d)) ℂ,
      ∀ X : Matrix (Config (Qudits (Fin m) d)) (Config (Qudits (Fin m) d)) ℂ,
        K.map X = partialTraceRight
          ((U : Matrix (Config (Qudits (Fin m) d) × Config (Qudits (Fin (2 * m)) d))
            (Config (Qudits (Fin m) d) × Config (Qudits (Fin (2 * m)) d)) ℂ) *
            freshEnvironmentInput (0 : Fin (2 * m) → Fin d) X * Uᴴ) :=
  sorry

/- TNLean/Circuit/Channel/PhysicalPortPureOutput.lean:
private theorem exists_product_of_pure_marginal
    {S E : Type*} [Fintype S] [Fintype E]
    (Ω : S × E → ℂ) (φ : S → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hMarginal : partialTraceRight (vecMulVec Ω (star Ω)) = vecMulVec φ (star φ)) :
    ∃ η : E → ℂ, star η ⬝ᵥ η = 1 ∧ ∀ s e, Ω (s, e) = φ s * η e
-/

/-- A bipartite vector whose marginal is the pure state `φ` is a product `φ ⊗ η` with `η` a
unit vector. A matrix lemma, unchanged and made public. -/
theorem exists_product_of_pure_marginal {S E : Type*} [Fintype S] [Fintype E]
    (Ω : S × E → ℂ) (φ : S → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hMarginal : partialTraceRight (vecMulVec Ω (star Ω)) = vecMulVec φ (star φ)) :
    ∃ η : E → ℂ, star η ⬝ᵥ η = 1 ∧ ∀ s e, Ω (s, e) = φ s * η e :=
  sorry

/-! ### Gate-level dilation (G7) -/

/- TNLean/Circuit/Channel/PhysicalPortLocalDilation.lean:
theorem exists_selected_onsite_dilation (P : PhysicalPortLayout N W) (i : Fin N)
    (e : Fin m ↪ Fin W) (he : ∀ j, P.site (e j) = i)
    (Φ : Module.End ℂ (Matrix (Fin m → Fin d) (Fin m → Fin d) ℂ))
    (hΦ : IsKrausCPTP Φ) :
    ∃ U : Matrix (Fin (W + 2 * m) → Fin d) (Fin (W + 2 * m) → Fin d) ℂ,
      IsPhysicalPortUnitary (P.append (fun _ : Fin (2 * m) => i)) 0 U ∧
      discardAppendedEnvironment W (2 * m) d ∘ₗ singleKrausMap U ∘ₗ
        appendEnvironmentInput W (2 * m) d = registerChannelLift e Φ
-/

/-- A trace-preserving gate on a set `D` of wires of the site `i` is, after `2 |D|` fresh wires at
the site `i` are prepared at `0` and before they are traced out, a unitary circuit of depth `0`.
(The enumeration `e : Fin m ↪ Fin W` becomes the cell `D`, `registerChannelLift e Φ` the one-gate
layer `Layer.single`.) -/
theorem exists_selected_onsite_dilation {d N W : ℕ} [NeZero d] [NeZero N]
    (P : PhysicalPortLayout N W) (i : Fin N) (D : Finset (Fin W)) (hD : ∀ w ∈ D, P.site w = i)
    (K : KrausGate D (Qudits (Fin W) d) (Qudits (Fin W) d)) (hK : KrausFamily.IsTP K) :
    ∃ U, IsUnitaryCircuit (appendGeometry P.site P.port fun _ : Fin (2 * D.card) ↦ i) 0 U ∧
      discardEnvironment (Fin W) (Fin (2 * D.card)) d ∘ₗ (KrausFamily.single U).map ∘ₗ
          freshInput Function.Embedding.inl d =
        (Circuit.seq [Layer.single (Γ := portGeometry P) (.inl ⟨D, i, hD⟩) K]).map
          KrausGate.ev :=
  sorry

/- TNLean/Circuit/Channel/PhysicalPortLocalDilation.lean:
theorem exists_onsite_appended_dilation {r : ℕ}
    (P : PhysicalPortLayout N W) (i : Fin N)
    (K : Fin r → Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)
    (hs : ∀ a, K a ∈ ManyBody.supportedOperators (fun _ ↦ Fin d)
        (Finset.univ.filter fun p ↦ P.site p = i))
    (hnorm : ∑ a, (K a)ᴴ * K a = 1) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary (P.append owner) 0 U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d = rectangularKrausMap K
-/

/-- A trace-preserving gate on the whole fibre of the site `i` is, with fresh wires prepared and
traced out, a unitary circuit of depth `0`. (Operators supported on the fibre with
`∑ Kᴴ K = 1` become a TP gate on the fibre cell; `rectangularKrausMap K` its one-gate layer.) -/
theorem exists_onsite_appended_dilation {d N W : ℕ} [NeZero d] [NeZero N]
    (P : PhysicalPortLayout N W) (i : Fin N)
    (K : KrausGate (Finset.univ.filter fun w ↦ P.site w = i) (Qudits (Fin W) d)
      (Qudits (Fin W) d)) (hK : KrausFamily.IsTP K) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N, ∃ U,
      IsUnitaryCircuit (appendGeometry P.site P.port owner) 0 U ∧
      discardEnvironment (Fin W) (Fin A) d ∘ₗ (KrausFamily.single U).map ∘ₗ
          freshInput Function.Embedding.inl d =
        (Circuit.seq [Layer.single (Γ := portGeometry P)
          (.inl ⟨_, i, fun _ hw ↦ (Finset.mem_filter.mp hw).2⟩) K]).map KrausGate.ev :=
  sorry

/-! ### Circuit dilation -/

/- TNLean/Circuit/Channel/PhysicalPortDilation.lean:
theorem IsPhysicalPortProtocol.exists_appended_unitary_dilation
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary (P.append owner) T U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d = Φ
-/

/-- A protocol of depth `T` on the port geometry is, with fresh wires owned by the sites prepared
at `0` and traced out at the end, a unitary circuit of depth `T` on the appended port geometry. -/
theorem exists_appended_unitary_dilation {d N W : ℕ} [NeZero d] [NeZero N]
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Matrix (Config (Qudits (Fin W) d)) (Config (Qudits (Fin W) d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin W) d)) (Config (Qudits (Fin W) d)) ℂ}
    (hΦ : IsProtocol (portGeometry P) T Φ) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N, ∃ U,
      IsUnitaryCircuit (appendGeometry P.site P.port owner) T U ∧
      discardEnvironment (Fin W) (Fin A) d ∘ₗ (KrausFamily.single U).map ∘ₗ
          freshInput Function.Embedding.inl d = Φ :=
  sorry

/- TNLean/Circuit/Channel/PhysicalPortPureOutput.lean:
theorem IsPhysicalPortProtocol.exists_appended_unitary_dilation_pure_output
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Module.End ℂ (Matrix (Fin W → Fin d) (Fin W → Fin d) ℂ)}
    (hΦ : IsPhysicalPortProtocol P T Φ)
    (ψ φ : (Fin W → Fin d) → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hOutput : Φ (vecMulVec ψ (star ψ)) = vecMulVec φ (star φ)) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        ∃ η : (Fin A → Fin d) → ℂ,
          IsPhysicalPortUnitary (P.append owner) T U ∧
          discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
            appendEnvironmentInput W A d = Φ ∧
          star η ⬝ᵥ η = 1 ∧ ∀ x e,
            ((appendMatrixSplit W A d U) *ᵥ
              (fixedEnvEmbedding (0 : Fin A → Fin d) *ᵥ ψ)) (x, e) = φ x * η e
-/

/-- If a protocol sends the pure state `ψ` to the pure state `φ`, its unitary dilation sends
`ψ ⊗ |0⟩` to a product `φ ⊗ η` of the wires and the fresh wires. -/
theorem exists_appended_unitary_dilation_pure_output {d N W : ℕ} [NeZero d] [NeZero N]
    {P : PhysicalPortLayout N W} {T : ℕ}
    {Φ : Matrix (Config (Qudits (Fin W) d)) (Config (Qudits (Fin W) d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin W) d)) (Config (Qudits (Fin W) d)) ℂ}
    (hΦ : IsProtocol (portGeometry P) T Φ)
    (ψ φ : Config (Qudits (Fin W) d) → ℂ) (hφ : star φ ⬝ᵥ φ = 1)
    (hOutput : Φ (vecMulVec ψ (star ψ)) = vecMulVec φ (star φ)) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N, ∃ U, ∃ η : Config (Qudits (Fin A) d) → ℂ,
      IsUnitaryCircuit (appendGeometry P.site P.port owner) T U ∧
      discardEnvironment (Fin W) (Fin A) d ∘ₗ (KrausFamily.single U).map ∘ₗ
          freshInput Function.Embedding.inl d = Φ ∧
      star η ⬝ᵥ η = 1 ∧
      ∀ z, (U *ᵥ freshVector Function.Embedding.inl d ψ) z =
        φ (fun w ↦ z (.inl w)) * η (fun a ↦ z (.inr a)) :=
  sorry

/-! ### Compilation of native protocols to the registers -/

/- TNLean/Circuit/Channel/NativePortLayer.lean:
theorem dataChannelLift_channelLayer (hd : 0 < d) (hN : 2 ≤ N)
    (L : ChannelLayer (d ^ k) N) :
    IsPhysicalPortProtocol (layout N k) (2 * k) (dataChannelLift N k d L.map)
-/

/-- A layer of trace-preserving gates on disjoint bonds of the native ring, local dimension
`d ^ k`, acting on the data wires is a protocol of depth `2 k` on the registers. -/
theorem dataChannelLift_channelLayer {N k d : ℕ} [NeZero N] (hd : 0 < d) (hN : 2 ≤ N)
    (cells : Finset (ring N).Cell)
    (hcells : (cells : Set (ring N).Cell).PairwiseDisjoint (ring N).cell)
    (g : (b : cells) → KrausGate ((ring N).cell b) (Qudits (Fin N) (d ^ k))
      (Qudits (Fin N) (d ^ k)))
    (hg : ∀ b, KrausFamily.IsTP (g b)) :
    IsProtocol (registers N k) (2 * k)
      (dataLift N k d ((Layer.ofCells cells hcells g).krausFamily KrausGate.ev).map) :=
  sorry

/- TNLean/Circuit/Channel/PhysicalPortIO.lean:
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPortIO
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    ∃ Γ, IsPhysicalPortProtocol (PortRegisters.layout N k) (2 * k * T) Γ ∧
      Γ ∘ₗ PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
        PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ
-/

/-- A dimension-bounded protocol of depth `T` on the ring of qudits is simulated by a protocol of
depth `2 k T` on the registers, `k = ⌈log_d B⌉`, with input and output on the port wires and the
data and scratch wires starting at `0`. -/
theorem exists_physicalPortIO {N B T d : ℕ} [NeZero N] [NeZero d]
    {Ψ : Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ}
    (h : IsBoundedProtocol (ring N) B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    ∃ Ψ', IsProtocol (registers N (Nat.clog d B)) (2 * Nat.clog d B * T) Ψ' ∧
      Ψ' ∘ₗ freshInput (portWire N (Nat.clog d B)) d =
        freshInput (portWire N (Nat.clog d B)) d ∘ₗ Ψ :=
  sorry

/- TNLean/Circuit/Channel/PhysicalPortUnitaryCompilation.lean:
theorem IsDimensionBoundedLocalChannelProtocol.exists_physicalPortUnitaryIO
    {Ψ : Module.End ℂ (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ)}
    (h : IsDimensionBoundedLocalChannelProtocol B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    let k := Nat.clog d B
    let W := N * (1 + k + k)
    ∃ A : ℕ, ∃ owner : Fin A → Fin N,
      ∃ U : Matrix (Fin (W + A) → Fin d) (Fin (W + A) → Fin d) ℂ,
        IsPhysicalPortUnitary ((PortRegisters.layout N k).append owner) (2 * k * T) U ∧
        discardAppendedEnvironment W A d ∘ₗ singleKrausMap U ∘ₗ
          appendEnvironmentInput W A d ∘ₗ
          PortRegisters.wordInitialization (PortRegisters.portWordCode d k) =
          PortRegisters.wordInitialization (PortRegisters.portWordCode d k) ∘ₗ Ψ
-/

/-- A dimension-bounded protocol of depth `T` on the ring of qudits is simulated by a unitary
circuit of depth `2 k T` on the registers with fresh wires owned by the sites, `k = ⌈log_d B⌉`,
input on the port wires, every other wire prepared at `0` and the fresh wires traced out. -/
theorem exists_physicalPortUnitaryIO {N B T d : ℕ} [NeZero N] [NeZero d]
    {Ψ : Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ →ₗ[ℂ]
      Matrix (Config (Qudits (Fin N) d)) (Config (Qudits (Fin N) d)) ℂ}
    (h : IsBoundedProtocol (ring N) B T Ψ) (hd : 2 ≤ d) (hN : 2 ≤ N) :
    ∃ A : ℕ, ∃ owner : Fin A → Fin N, ∃ U,
      IsUnitaryCircuit (appendGeometry Prod.fst (portWire N (Nat.clog d B)) owner)
        (2 * Nat.clog d B * T) U ∧
      discardEnvironment (Fin N × Fin (1 + Nat.clog d B + Nat.clog d B)) (Fin A) d ∘ₗ
          (KrausFamily.single U).map ∘ₗ freshInput Function.Embedding.inl d ∘ₗ
          freshInput (portWire N (Nat.clog d B)) d =
        freshInput (portWire N (Nat.clog d B)) d ∘ₗ Ψ :=
  sorry

end Inventory.C
