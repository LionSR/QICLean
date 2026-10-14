/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.SchmidtBellSharpUpper
import QICLean.Representation.SchmidtBellEnumeratedCompression
import QICLean.Representation.SymmetricProjectionCoordinates

/-!
# The sharp upper rate in the original enumerated physical coordinates

Enumerating the selected left auxiliary register transports the sharp estimate
to the original physical prevector with two equal finite auxiliary registers.
The supplied symmetric coordinates and the original prevector use the same
column space. The actual metric uses the full original family on both sides.
The label sequence is the supplied physical sequence throughout.

Source: OpenAI area-law manuscript, `07-comparators.tex`, lines 80--110,
130--163, 240--308 and 383--418, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Filter Topology Matrix PermutationRepresentation TensorPower
open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

namespace FiniteProduct

attribute [local instance] sharpTreeRegionDecidableEq sharpTreeSiteDecidableEq
  sharpTreeConfigDecidableEq

variable {V : Type} [Fintype V] [DecidableEq V]
variable (β : V → Type) [∀ v, Fintype (β v)] [∀ v, DecidableEq (β v)]
variable (Ω : EuclideanSpace ℂ ((v : V) → β v)) (X : Finset V)
variable (E : Finset (Configuration β X))

local notation "ι₀" => addedSiteSpace (addedSiteSpace β (Fin E.card)) (Fin E.card)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian (reducedPure_posSemidef β Ω X)) E

local instance replicaPrevectorSharpUpperConfigDecidableEq (k : ℕ) :
    DecidableEq (Config k ι₀) := Fintype.decidablePiFintype

open Classical in
/-- The original enumerated physical prevector satisfies the sharp weighted
upper rate for its supplied label sequence. Enumeration changes neither the
actual compressed band metric nor the compressed vector. The uniform constant
and threshold precede every symmetric-coordinate and terminal-tree choice.
Source: area-law manuscript, `07-comparators.tex`, `comparator:sharp-upper`,
lines 80--110, 240--308 and 383--418. -/
theorem eventually_suppliedReplicaPrevector_sharp_upper
    (hΩ : ‖Ω‖ = 1) (hz : 0 < z)
    {a K r : ℝ} (ha : 0 < a) (har : 6 * a ≤ r) (ha1 : 6 * a ≤ 1)
    (ell : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k))) :
    let ΩX := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (FiniteProduct.splitEquiv β X) Ω
    let ψ : Configuration β Xᶜ × Fin E.card → ℂ := fun x ↦
      Matrix.compressedTypicalPureState ΩX E ((Finset.equivFin E).symm x.2, x.1)
    (∀ᶠ k : ℕ in atTop,
      (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
        ‖WithLp.toLp 2
          (((1 : Matrix (Fin k → Configuration β Xᶜ)
            (Fin k → Configuration β Xᶜ) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (ell k)) *ᵥ
            (fun x : (Fin k → Configuration β Xᶜ) × (Fin k → Fin E.card) ↦
              ∏ j, ψ (x.1 j, x.2 j)))‖ ^ 2) →
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ G : ℕ, Tendsto (Real.bellOverlapRemainder E.card C G) atTop (𝓝 0)) ∧
      ∀ᶠ k : ℕ in atTop,
      ∀ (n : ℕ) (Z : Matrix (Config k ι₀) (Fin n) ℂ),
      Zᴴ * Z = 1 →
      Z * Zᴴ = symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k) →
      ∀ (G : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι]
        (U Y : ι → Fin G → Finset V),
      (∀ j g, Disjoint X (U j g)) → (∀ j g, Disjoint X (Y j g)) →
      (∀ j g, Disjoint (U j g) (Y j g)) →
      (∀ j j' g h, g < h → U j g ∪ Y j g ⊆ U j' h) →
      (∀ j g (Q : Finset V), Q = U j g ∨ Q = U j g ∪ Y j g ∨ Q = Y j g →
        ∀ v : ℝ, |v| ≤ r →
          Real.log (Entropy.surprisalMoment
            (reducedPure_posSemidef β Ω Q).isHermitian.eigenvalues v) ≤
            v * vonNeumannEntropy (reducedPure β Ω Q)
              (reducedPure_posSemidef β Ω Q).isHermitian + K * v ^ 2) →
      ∀ (T : MeanTree ι) (s : ℝ), 2 * s ∈ Set.Icc (0 : ℝ) 1 →
      let v : EuclideanSpace ℂ (Config k ι₀) := WithLp.toLp 2
        (replicaPrevector Ω E.card k (ell k) ∘
          globalReplicaCopiesEquiv β (Fin E.card) (Fin E.card) k)
      let W := replicaMetric ι₀ (a / 2) k
      let Q := fun j g ↦ insert (some none)
        ((X ∪ U j g).image fun v ↦ some (some v))
      let F := fun j g ↦ insert none
        (((X ∪ (U j g ∪ Y j g))ᶜ).image fun v ↦ some (some v))
      let ext := fun B : Finset V ↦ (B \ X).image fun v ↦ some (some v)
      let A := fun j g ↦ ((W (Q j g))⁻¹ * (W (F j g))⁻¹ * W (ext (Y j g))) ^ 2
      let M := (List.ofFn fun g ↦ T.eval (fun j ↦ Zᴴ * A j g * Z)).prod
      let Nsq := ‖toEuclideanLin (M ^ (-s)) (toEuclideanLin Zᴴ v)‖ ^ 2
      let S := fun Q : Finset V ↦ vonNeumannEntropy (reducedPure β Ω Q)
        (reducedPure_posSemidef β Ω Q).isHermitian
      0 < Nsq ∧ -Real.log Nsq / (k : ℝ) ≤
        2 * Real.log (E.card : ℝ) - Real.log z +
          2 * s * a * (∑ g, ∑ j, T.weight j *
            (S (U j g) + S (U j g ∪ Y j g) - S (Y j g))) +
          24 * s * G * K * a ^ 2 - 2 * s * G * Real.log z +
            Real.bellOverlapRemainder E.card C G k := by
  classical
  intro ΩX ψ hmass
  obtain ⟨C, hC, hlim, hu⟩ :=
    eventually_suppliedSchmidtBell_sharp_upper (K := K) β Ω hΩ X E hz ha har ha1 ell hmass
  refine ⟨C, hC, hlim, hu.mono ?_⟩
  intro k hk n Z hZ hZZ G ι instF instD U Y hXU hXY hUY hnest hmom T s hs
  intro v W Q F ext A M Nsq S
  let e : Config k ι₀ ≃
      Config k (addedSiteSpace (addedSiteSpace β E) (Fin E.card)) :=
    Equiv.piCongrRight fun _ : Fin k ↦ Equiv.piCongrRight fun o ↦
      match o with
      | none => Equiv.refl (Fin E.card)
      | some none => (Finset.equivFin E).symm
      | some (some v) => Equiv.refl (β v)
  let ZE := Z.submatrix e.symm (id : Fin n → Fin n)
  have hZE : ZEᴴ * ZE = 1 := by
    simpa only [ZE, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_id_id] using hZ
  have hSymm :
      symProj (copyPerm ((o : Option (Option V)) →
        addedSiteSpace (addedSiteSpace β E) (Fin E.card) o) k) =
      (symProj (copyPerm ((o : Option (Option V)) → ι₀ o) k)).submatrix e.symm e.symm := by
    simpa only [Matrix.reindex_apply] using
      (symProj_of_intertwine e
        (φ := copyPerm ((o : Option (Option V)) → ι₀ o) k)
        (ψ := copyPerm ((o : Option (Option V)) →
          addedSiteSpace (addedSiteSpace β E) (Fin E.card) o) k)
        (fun σ x ↦ funext fun j ↦ rfl))
  have hZEZ : ZE * ZEᴴ = symProj (copyPerm ((o : Option (Option V)) →
      addedSiteSpace (addedSiteSpace β E) (Fin E.card) o) k) := by
    simpa only [ZE, Matrix.conjTranspose_submatrix, Equiv.coe_refl] using
      ((Matrix.submatrix_mul_equiv Z Zᴴ e.symm (Equiv.refl (Fin n)) e.symm).trans
        (congrArg (fun P : Matrix (Config k ι₀) (Config k ι₀) ℂ ↦
          P.submatrix e.symm e.symm) hZZ)).trans hSymm.symm
  have hp :
      toEuclideanLin Zᴴ (WithLp.toLp 2
        (replicaPrevector Ω E.card k (ell k) ∘
          globalReplicaCopiesEquiv β (Fin E.card) (Fin E.card) k)) =
      toEuclideanLin ZEᴴ (WithLp.toLp 2
        (schmidtBellSitePrevector β X E k ΩX (ell k) ∘
          schmidtBellWitnessEquiv β X E k)) := by
    simpa only [ZE, e, ΩX, Matrix.toEuclideanLin, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp] using!
      congrArg (WithLp.toLp 2)
        (schmidtBellSitePrevector_compressed_enumerate_C β Ω X E k n Z (ell k))
  have hNsq := congrArg₂
    (fun (P : Matrix (Fin n) (Fin n) ℂ) (u : EuclideanSpace ℂ (Fin n)) ↦
      ‖toEuclideanLin (P ^ (-s)) u‖ ^ 2)
    (replicaMetric_compressed_bandProduct_enumerate_C β X E k n Z (a / 2) G U Y T).2 hp
  exact Eq.mp (congrArg (fun r : ℝ ↦ 0 < r ∧ -Real.log r / (k : ℝ) ≤
    2 * Real.log (E.card : ℝ) - Real.log z +
      2 * s * a * (∑ g, ∑ j, T.weight j *
        (S (U j g) + S (U j g ∪ Y j g) - S (Y j g))) +
      24 * s * G * K * a ^ 2 - 2 * s * G * Real.log z +
        Real.bellOverlapRemainder E.card C G k) hNsq.symm)
    (hk n ZE hZE hZEZ G U Y hXU hXY hUY hnest hmom T s hs)

end FiniteProduct
