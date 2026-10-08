/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.Transport.Defs
import QICLean.Representation.ReplicaSimilarity
import QICLean.Representation.CoherentResolution
import QICLean.Entropy.FiniteProductConditional
import QICLean.Analysis.UnitaryHaar

/-!
# Finite histories, moves and energy terms for the transport estimate

This file fixes the data of the area-law paper, Proposition 7.4 (`prop:transport`),
`06-transport.tex` lines 245--376, on the one-copy space `V = ⨂_v ℂ^{n_v}`:

* tripartitions `(P, Y, F)` of the tensor factors, their band metrics
  `A(P, Y, F) = (W_P^{-1} W_F^{-1} W_Y)²` (display `transport:band-metric`);
* moves transferring a subsystem `x ⊆ Y` entirely to `P` or to `F`, with entropy
  `η = I(x : F | P)` (display `transport:move-eta`; exchange `P, F` for a move to `F`);
* a finite weighted history tree, old partitions in `K` bands, conditional choice trees
  and new partitions, the old and new metrics `A_h`, `A_{h,c}`, and the root `M(p)`;
* cross-band commutation (line 268);
* positive contractions `h_i` with designated supports `D_i`, splits at terminal leaves,
  `η_{i,j}`, `W_i(p)` and `H̄ = ∑_i h̄_i` (lines 335--362);
* the coherent measure `dμ_σ(θ) = D_k Tr(σ P_{θ,k}) dθ` (display
  `transport:coherent-measure`), with `dθ` realized as the image of Haar measure on the
  unitary group under `U ↦ U e`.

The definitions are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder unitInterval Matrix.Norms.L2Operator
open Matrix MeasureTheory PermutationRepresentation Entropy

noncomputable section

namespace TensorPower

section Coherent

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The dimension `D_k = dim 𝒮_k` of the symmetric subspace. -/
abbrev symDim (Ω : Type*) [Fintype Ω] [DecidableEq Ω] (k : ℕ) : ℕ :=
  Module.finrank ℂ (invariantSubspace (copyPerm Ω k))

/-- The coherent integral `∫ f dμ_σ = D_k ∫ f(θ) Tr(σ P_{θ,k}) dθ`, with `θ = U e_a` for
Haar-distributed unitaries `U` (`06-transport.tex`, display `transport:coherent-measure`,
lines 364--373). -/
def coherentIntegral (k : ℕ) (a : Ω) (ρ : Matrix (Fin k → Ω) (Fin k → Ω) ℂ)
    (f : (Ω → ℂ) → ℝ) : ℝ :=
  (symDim Ω k : ℝ) * ∫ U, f ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1) *
    (ρ * coherentProj k ((U : Matrix Ω Ω ℂ) *ᵥ Pi.single a 1)).trace.re ∂(unitaryHaar Ω)

end Coherent

namespace ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Three parts `P, Y, F` of the tensor factors. -/
structure PYF (V : Type*) where
  /-- The outer part `P`. -/
  P : Finset V
  /-- The middle part `Y`. -/
  Y : Finset V
  /-- The outer part `F`. -/
  F : Finset V

/-- `(P, Y, F)` partitions the tensor factors (`06-transport.tex` lines 251--253). -/
def PYF.IsPartition (π : PYF V) : Prop :=
  Disjoint π.P π.Y ∧ Disjoint π.P π.F ∧ Disjoint π.Y π.F ∧ π.P ∪ π.Y ∪ π.F = Finset.univ

/-- A move in one band: do nothing, or transfer `x ⊆ Y` entirely to `P` or to `F`
(`06-transport.tex` lines 262--264). -/
inductive Move (V : Type*) where
  | stay : Move V
  | toP (x : Finset V) : Move V
  | toF (x : Finset V) : Move V

/-- The transferred subsystem (empty for `stay`). -/
def Move.subsystem : Move V → Finset V
  | stay => ∅
  | toP x => x
  | toF x => x

/-- The new partition after a move. -/
def Move.apply : Move V → PYF V → PYF V
  | stay, π => π
  | toP x, π => ⟨π.P ∪ x, π.Y \ x, π.F⟩
  | toF x, π => ⟨π.P, π.Y \ x, π.F ∪ x⟩

/-- A move is valid when the transferred subsystem lies in `Y`. -/
def Move.IsValid (m : Move V) (π : PYF V) : Prop := m.subsystem ⊆ π.Y

variable (n : V → ℕ)

/-- The band metric `A(P, Y, F) = (W_P^{-1} W_F^{-1} W_Y)²` on `k` copies
(`06-transport.tex`, display `transport:band-metric`). -/
def bandMetric (t : ℝ) (k : ℕ) (π : PYF V) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  leafMetric n t k π.P π.Y π.F

/-- `log(e dim x)` for a subsystem `x`. -/
def logDim (x : Finset V) : ℝ := Real.log (Real.exp 1 * ∏ v ∈ x, (n v : ℝ))

/-- The entropy of a move for a unit one-copy vector `θ`: `I_θ(x : F | P)` for a move to
`P`, `I_θ(x : P | F)` for a move to `F`, zero for no move (`06-transport.tex`, display
`transport:move-eta`, lines 315--322). -/
def moveEta (π : PYF V) (m : Move V) (θ : EuclideanSpace ℂ (SiteConfig n)) : ℝ :=
  match m with
  | .stay => 0
  | .toP x => FiniteProduct.conditionalMutualInformation (fun v => Fin (n v)) θ x π.F π.P
  | .toF x => FiniteProduct.conditionalMutualInformation (fun v => Fin (n v)) θ x π.P π.F

/-- The designated support `D` lies in one part of `π`. -/
def PYF.Contains (π : PYF V) (D : Finset V) : Prop := D ⊆ π.P ∨ D ⊆ π.Y ∨ D ⊆ π.F

/-- `D` meets `Y` and `P` but not `F` (a split with receiving side `P`). -/
def PYF.SplitsToP (π : PYF V) (D : Finset V) : Prop :=
  (D ∩ π.Y).Nonempty ∧ (D ∩ π.P).Nonempty ∧ Disjoint D π.F

/-- `D` meets `Y` and `F` but not `P` (a split with receiving side `F`). -/
def PYF.SplitsToF (π : PYF V) (D : Finset V) : Prop :=
  (D ∩ π.Y).Nonempty ∧ (D ∩ π.F).Nonempty ∧ Disjoint D π.P

open Classical in
/-- The entropy `η` of a split of `D` in one band: with `x = D ∩ Y`, `I_θ(x : F | P)` when
the receiving side is `P` and `I_θ(x : P | F)` otherwise (`06-transport.tex`
lines 345--347). -/
def splitBandEta (π : PYF V) (D : Finset V) (θ : EuclideanSpace ℂ (SiteConfig n)) : ℝ :=
  if π.SplitsToP D then
    FiniteProduct.conditionalMutualInformation (fun v => Fin (n v)) θ (D ∩ π.Y) π.F π.P
  else FiniteProduct.conditionalMutualInformation (fun v => Fin (n v)) θ (D ∩ π.Y) π.P π.F

/-- The data of one round: a weighted history tree, old partitions in `K` bands,
conditional choice trees and the moves of every choice (`06-transport.tex`
lines 257--266). -/
structure TransportData (V : Type*) (K : ℕ) (H : Type*) (C : H → Type*) where
  /-- The weighted history tree, leaves `h` with weights `w_h`. -/
  histTree : Matrix.MeanTree H
  /-- The conditional choice tree at `h`, leaves `c` with weights `q_{c|h}`. -/
  choiceTree : ∀ h, Matrix.MeanTree (C h)
  /-- The old partition `(P_{h,g}, Y_{h,g}, F_{h,g})`. -/
  old : H → Fin K → PYF V
  /-- The move of choice `c` at history `h` in band `g`. -/
  move : ∀ h, C h → Fin K → Move V

namespace TransportData

variable {K : ℕ} {H : Type*} {C : H → Type*} (D : TransportData V K H C)

/-- The new partition of choice `c` at history `h` in band `g`. -/
def new (h : H) (c : C h) (g : Fin K) : PYF V := (D.move h c g).apply (D.old h g)

/-- The partition in band `g` at a terminal leaf: old at `(h, old)`, new at
`(h, c, new)`. -/
def leafPart : (Σ h, Option (C h)) → Fin K → PYF V
  | ⟨h, none⟩, g => D.old h g
  | ⟨h, some c⟩, g => D.new h c g

/-- The standing hypotheses on the finite data (`06-transport.tex` lines 257--266): all
history and conditional weights are positive, old parts partition the factors and every
move transfers a subsystem of `Y`. -/
structure IsAdmissible [DecidableEq H] [∀ h, DecidableEq (C h)] : Prop where
  histWeight_pos : ∀ h, 0 < D.histTree.weight h
  choiceWeight_pos : ∀ h c, 0 < (D.choiceTree h).weight c
  old_isPartition : ∀ h g, (D.old h g).IsPartition
  move_isValid : ∀ h c g, (D.move h c g).IsValid (D.old h g)

/-- **Cross-band commutation** (`06-transport.tex` lines 268--271): every old or new metric
from band `g` commutes with every old or new metric from band `g' ≠ g`, at all histories and
choices. -/
def CrossBandCommute (t : ℝ) (k : ℕ) : Prop :=
  ∀ j j' g g', g ≠ g' →
    Commute (bandMetric n t k (D.leafPart j g)) (bandMetric n t k (D.leafPart j' g'))

/-- The old metric `A_h = ∏_g A_{h,g}`. -/
def oldMetric (t : ℝ) (k : ℕ) (h : H) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  (List.ofFn fun g => bandMetric n t k (D.old h g)).prod

/-- The new metric `A_{h,c} = ∏_g A_{h,c,g}`. -/
def newMetric (t : ℝ) (k : ℕ) (h : H) (c : C h) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  (List.ofFn fun g => bandMetric n t k (D.new h c g)).prod

/-- The terminal tree at parameter `p`. -/
def tree (p : I) : Matrix.MeanTree (Σ h, Option (C h)) :=
  Matrix.MeanTree.interpTree D.histTree D.choiceTree p

/-- The terminal inputs. -/
def input (t : ℝ) (k : ℕ) :
    (Σ h, Option (C h)) →
      Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  Matrix.Transport.interpInput (D.oldMetric n t k) (D.newMetric n t k)

/-- The interpolation path `q ↦ M(q)` (clamped to `[0, 1]`). -/
def rootPath (t : ℝ) (k : ℕ) (q : ℝ) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one q)).eval (D.input n t k)

/-- The transport state `σ_{j,u}` at parameter `p` for the filtered vector of `pre`
(`06-transport.tex`, display `transport:states`). -/
def state [DecidableEq H] [∀ h, DecidableEq (C h)] (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) (j : Σ h, Option (C h)) (u : ℝ) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  Matrix.Transport.transportState (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p))
    (D.input n t k) (Matrix.Transport.filteredVector (D.rootPath n t k p) pre) j u

/-- The relative ratio `C_h = A_h^{-1/2} B_h A_h^{-1/2}`. -/
def relRatio (t : ℝ) (k : ℕ) (h : H) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  Matrix.Transport.relRatio D.choiceTree (D.oldMetric n t k) (D.newMetric n t k) h

/-- The right side of the exact derivative,
`∑_h w_h ∫ m_{1/4}(u) Tr(σ_{h,u} log C_h) du` (`06-transport.tex`, display
`transport:exact-derivative`). -/
def exactDerivative [Fintype H] [DecidableEq H] [∀ h, DecidableEq (C h)] (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) : ℝ :=
  ∑ h, D.histTree.weight h * ∫ u, Matrix.Transport.fourierWeight u *
    (D.state n t k pre p ⟨h, none⟩ u * CFC.log (D.relRatio n t k h)).trace.re

variable [∀ v, NeZero (n v)]

/-- The base vector `e` of the coherent parametrization `θ = U e`. -/
def base : SiteConfig n := fun _ => 0

/-- The entropy-gain term
`∑_{h,g} w_h ∫ m_{1/4}(u) ∫ ∑_c q_{c|h} η_{h,c,g}(θ) dμ_{σ_{h,u}}(θ) du`
(`06-transport.tex`, display `transport:entropy-gain`, without the factor `k a`). -/
def entropyGain [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)]
    (t : ℝ) (k : ℕ) (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) : ℝ :=
  ∑ h, ∑ g, D.histTree.weight h * ∫ u, Matrix.Transport.fourierWeight u *
    coherentIntegral k (base n) (D.state n t k pre p ⟨h, none⟩ u) (fun θ =>
      ∑ c, (D.choiceTree h).weight c *
        moveEta n (D.old h g) (D.move h c g) ((EuclideanSpace.equiv _ ℂ).symm θ))

end TransportData

/-- Positive contractions `h_i` with designated tensor supports `D_i`
(`06-transport.tex` lines 335--337). -/
structure EnergyTerms (V : Type*) [Fintype V] (n : V → ℕ) (ι : Type*) where
  /-- The term `h_i`. -/
  term : ι → Matrix (SiteConfig n) (SiteConfig n) ℂ
  /-- The designated support `D_i`. -/
  support : ι → Finset V

namespace TransportData

variable {n} {K : ℕ} {H : Type*} {C : H → Type*} (D : TransportData V K H C) {ι : Type*}

/-- **Designated-support compatibility** (`06-transport.tex` lines 337--342): at every
terminal leaf and band, `D_i` lies in one part, except possibly in one band, where it meets
`Y` and exactly one of `P, F`. -/
def SupportCompatible (E : EnergyTerms V n ι) : Prop :=
  ∀ j i g, (D.leafPart j g).Contains (E.support i) ∨
    (((D.leafPart j g).SplitsToP (E.support i) ∨ (D.leafPart j g).SplitsToF (E.support i)) ∧
      ∀ g' ≠ g, (D.leafPart j g').Contains (E.support i))

open Classical in
/-- The split leaves `𝒥_i` of a term (`06-transport.tex` line 342). -/
def splitLeaves [Fintype H] [∀ h, Fintype (C h)] (E : EnergyTerms V n ι) (i : ι) :
    Finset (Σ h, Option (C h)) :=
  Finset.univ.filter fun j => ∃ g, ¬ (D.leafPart j g).Contains (E.support i)

open Classical in
/-- The entropy `η_{i,j}` of the split of `D_i` at leaf `j`: the split entropy of its
unique exceptional band (`06-transport.tex` lines 342--347). -/
def splitEta (E : EnergyTerms V n ι) (i : ι) (j : Σ h, Option (C h))
    (θ : EuclideanSpace ℂ (SiteConfig n)) : ℝ :=
  ∑ g ∈ Finset.univ.filter fun g => ¬ (D.leafPart j g).Contains (E.support i),
    splitBandEta n (D.leafPart j g) (E.support i) θ

/-- The replica energy `H̄ = ∑_i h̄_i` on `k` copies (`06-transport.tex`, display
`transport:replica-energy`). -/
def _root_.TensorPower.ReplicaTransport.EnergyTerms.replicaEnergy [Fintype ι]
    (E : EnergyTerms V n ι) (k : ℕ) :
    Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ :=
  ∑ i, copyMean n k (E.term i)

/-- The total split weight `W_i(p) = ∑_{j ∈ 𝒥_i} π_j`. -/
def splitWeight [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)]
    (E : EnergyTerms V n ι) (i : ι) (p : ℝ) : ℝ :=
  ∑ j ∈ D.splitLeaves E i, (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).weight j

variable [∀ v, NeZero (n v)]

/-- The energy error
`∑_i W_i(p) ∑_{j∈𝒥_i} π_j ∫ m_{1/4}(u) ∫ η_{i,j}(θ)^{1/8} dμ_{σ_{j,u}}(θ) du`
(`06-transport.tex`, display `transport:energy`, without the factor `C a² ℓ^C`). The
split weight `W_i(p)` occurs twice: once as a factor and once inside the sum. -/
def energyError [Fintype H] [DecidableEq H] [∀ h, Fintype (C h)] [∀ h, DecidableEq (C h)]
    [Fintype ι] (E : EnergyTerms V n ι) (t : ℝ) (k : ℕ)
    (pre : Config k (fun v => Fin (n v)) → ℂ) (p : ℝ) : ℝ :=
  ∑ i, D.splitWeight E i p * ∑ j ∈ D.splitLeaves E i,
    (D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)).weight j *
      ∫ u, Matrix.Transport.fourierWeight u *
        coherentIntegral k (base n) (D.state n t k pre p j u) (fun θ =>
          D.splitEta E i j ((EuclideanSpace.equiv _ ℂ).symm θ) ^ (1 / 8 : ℝ))

end TransportData

end ReplicaTransport

end TensorPower
