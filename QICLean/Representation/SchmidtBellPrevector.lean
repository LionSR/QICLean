/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Entropy.TypicalBellPinPowers
import QICLean.Representation.ReplicaPrevector

/-!
# Schmidt truncation and the common-label Bell projection

Let `Ω` be a physical bipartite vector and let `E` select spectral coordinates
of its actual left reduced density. Positive selected mass suffices to form
the normalized compressed Schmidt vector. Its selected coordinates are
identified with `Fin E.card`, and its actual right marginal is the normalized
diagonal spectrum.

The label sequence is selected from this vector and imposed on the actual
initial uniform auxiliary pair. The Bell projection of that initial vector
has coefficient `(sqrt z / E.card)^k` and retains the same right auxiliary
label. The coordinate equivalence separates the physical--left auxiliary,
right auxiliary, and complementary copies.

These are finite-dimensional ingredients of OpenAI, *A two-dimensional area
law from a global spectral gap* (September 24, 2026), `07-comparators.tex`,
lines 130–147 and 240–290, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The inverse-metric comparator bounds require additional geometric and energy
estimates.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Labels: comparator:bell-pin, comparator:prevector, comparator:high-label.
Provenance-ID: 8753-qic-schmidt-bell-prevector-01
Downstream declaration:
TensorPower.selectedBellProjection_replicaPrevector
Provenance-ID: 8753-qic-schmidt-bell-prevector-02
Downstream declaration:
TensorPower.exists_label_sequence_schmidtBellPrevector
-/

open Matrix PermutationRepresentation Module Filter
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder

noncomputable section

namespace TensorPower

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (Ω : EuclideanSpace ℂ (A × B)) (E : Finset A)

local notation "hρA" => Matrix.PosSemidef.partialTraceRight
  (Matrix.posSemidef_vecMulVec_self_star Ω)
local notation "z" => Matrix.IsHermitian.spectralRestrictionMass
  (Matrix.PosSemidef.isHermitian hρA) E

omit [DecidableEq B] in
private theorem norm_compressedTypicalPureState_equivFin_swap
    (hz : 0 < z) :
    ‖WithLp.toLp 2 (fun x : B × Fin E.card =>
      Matrix.compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.2, x.1))‖ = 1 := by
  exact ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    ((Equiv.prodComm E B).trans ((Equiv.refl B).prodCongr (Finset.equivFin E)))).norm_map
      (Matrix.compressedTypicalPureState Ω E)).trans
    (Matrix.norm_compressedTypicalPureState Ω E hz)

omit [DecidableEq B] in
private theorem partialTraceLeft_compressedTypicalPureState_equivFin_swap (hz : 0 < z) :
    Matrix.partialTraceLeft (Matrix.vecMulVec
      (fun x : B × Fin E.card => Matrix.compressedTypicalPureState Ω E
        ((Finset.equivFin E).symm x.2, x.1))
      (star (fun x : B × Fin E.card => Matrix.compressedTypicalPureState Ω E
        ((Finset.equivFin E).symm x.2, x.1)))) =
      Matrix.diagonal (fun r : Fin E.card =>
        ((((Matrix.PosSemidef.isHermitian hρA).eigenvalues
          ((Finset.equivFin E).symm r)) / z : ℝ) : ℂ)) := by
  ext r s
  simpa only [Matrix.partialTraceLeft_apply, Matrix.partialTraceRight_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Matrix.diagonal_apply,
    (Finset.equivFin E).symm.injective.eq_iff] using
      congrArg (fun M : Matrix E E ℂ =>
        M ((Finset.equivFin E).symm r) ((Finset.equivFin E).symm s))
        (Matrix.partialTraceRight_compressedTypicalPureState Ω E hz)


omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
private theorem bellPinPrevector_equivFin (a : A) (b : B) (c r : Fin E.card) :
    Matrix.bellPinPrevector Ω E
      ((a, (Finset.equivFin E).symm c), ((Finset.equivFin E).symm r, b)) =
      Ω (a, b) * Matrix.omegaVec E.card (c, r) := by
  change Ω (a, b) * Matrix.omegaVec (Fintype.card E)
    ((Fintype.equivFin E) ((Finset.equivFin E).symm c),
      (Fintype.equivFin E) ((Finset.equivFin E).symm r)) = _
  simp [Matrix.omegaVec]

omit [Fintype B] in
private theorem finKronecker_pin_submatrix {X Y R S : Type*} [Fintype X] [Fintype Y]
    [DecidableEq R] [DecidableEq S]
    (eX : X ≃ Y) (eR : R ≃ S) (P : Matrix X X ℂ) (k : ℕ) :
    ((Matrix.finKronecker (fun _ : Fin k => P)) ⊗ₖ
      (1 : Matrix ((Fin k → R) × (Fin k → B)) ((Fin k → R) × (Fin k → B)) ℂ)).submatrix
        ((Equiv.piCongrRight (fun _ : Fin k => eX)).prodCongr
          ((Equiv.piCongrRight (fun _ : Fin k => eR)).prodCongr
            (Equiv.refl (Fin k → B)))).symm
        ((Equiv.piCongrRight (fun _ : Fin k => eX)).prodCongr
          ((Equiv.piCongrRight (fun _ : Fin k => eR)).prodCongr
            (Equiv.refl (Fin k → B)))).symm =
      Matrix.finKronecker (fun _ : Fin k => P.submatrix eX.symm eX.symm) ⊗ₖ
        (1 : Matrix ((Fin k → S) × (Fin k → B)) ((Fin k → S) × (Fin k → B)) ℂ) := by
  change ((Matrix.finKronecker (fun _ : Fin k => P)) ⊗ₖ
    (1 : Matrix ((Fin k → R) × (Fin k → B)) ((Fin k → R) × (Fin k → B)) ℂ)).submatrix
      (Prod.map (Equiv.piCongrRight (fun _ : Fin k => eX)).symm
        ((Equiv.piCongrRight (fun _ : Fin k => eR)).prodCongr
          (Equiv.refl (Fin k → B))).symm)
      (Prod.map (Equiv.piCongrRight (fun _ : Fin k => eX)).symm
        ((Equiv.piCongrRight (fun _ : Fin k => eR)).prodCongr
          (Equiv.refl (Fin k → B))).symm) = _
  rw [← Matrix.kroneckerMap_submatrix_submatrix, Matrix.submatrix_one_equiv]
  rfl

omit [Fintype B] in
private theorem kronecker_one_submatrix {X Y R S : Type*}
    [DecidableEq X] [DecidableEq Y]
    (eX : X ≃ Y) (eR : R ≃ S) (M : Matrix S S ℂ) :
    ((1 : Matrix Y Y ℂ) ⊗ₖ (M ⊗ₖ (1 : Matrix B B ℂ))).submatrix
      (eX.prodCongr (eR.prodCongr (Equiv.refl B)))
      (eX.prodCongr (eR.prodCongr (Equiv.refl B))) =
      (1 : Matrix X X ℂ) ⊗ₖ (M.submatrix eR eR ⊗ₖ (1 : Matrix B B ℂ)) := by
  change ((1 : Matrix Y Y ℂ) ⊗ₖ (M ⊗ₖ (1 : Matrix B B ℂ))).submatrix
    (Prod.map eX (Prod.map eR id)) (Prod.map eX (Prod.map eR id)) = _
  rw [← Matrix.kroneckerMap_submatrix_submatrix, Matrix.submatrix_one_equiv,
    ← Matrix.kroneckerMap_submatrix_submatrix]
  rfl

private theorem submatrix_mulVec_mulVec_eq {X Y : Type*} [Fintype X] [Fintype Y] (e : X ≃ Y)
    (P L : Matrix X X ℂ) (v w : X → ℂ) (c : ℂ)
    (h : WithLp.toLp 2 (P *ᵥ (L *ᵥ v)) = c • WithLp.toLp 2 (L *ᵥ w)) :
    WithLp.toLp 2
      (P.submatrix e.symm e.symm *ᵥ
        (L.submatrix e.symm e.symm *ᵥ (v ∘ e.symm))) =
      c • WithLp.toLp 2 (L.submatrix e.symm e.symm *ᵥ (w ∘ e.symm)) := by
  simp only [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm,
    Function.comp_def, Equiv.symm_apply_apply]
  ext x
  exact congrArg (fun t : EuclideanSpace ℂ X => t (e.symm x)) h

private theorem selectedBellProjection_equivFin (k : ℕ) (hz : 0 < z)
    (Λ : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ) :
    let β : A × Fin E.card → ℂ := fun x =>
      Matrix.selectedBellVector Ω E (x.1, (Finset.equivFin E).symm x.2)
    let χ : Fin E.card × B → ℂ := fun x =>
      Matrix.compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.1, x.2)
    let Pk := Matrix.finKronecker (fun _ : Fin k => Matrix.vecMulVec β (star β)) ⊗ₖ
      (1 : Matrix ((Fin k → Fin E.card) × (Fin k → B))
        ((Fin k → Fin E.card) × (Fin k → B)) ℂ)
    let ΛR := (1 : Matrix (Fin k → A × Fin E.card) (Fin k → A × Fin E.card) ℂ) ⊗ₖ
      (Λ ⊗ₖ (1 : Matrix (Fin k → B) (Fin k → B) ℂ))
    WithLp.toLp 2 (Pk *ᵥ (ΛR *ᵥ
      (fun x => ∏ j, Ω ((x.1 j).1, x.2.2 j) *
        Matrix.omegaVec E.card ((x.1 j).2, x.2.1 j)))) =
      (((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k) •
        WithLp.toLp 2 (ΛR *ᵥ (fun x =>
          (∏ j, β (x.1 j)) * ∏ j, χ (x.2.1 j, x.2.2 j))) := by
  intro β χ Pk ΛR
  let ι := Finset.equivFin E
  let τ := Equiv.piCongrRight (fun _ : Fin k => ι)
  let a := Equiv.piCongrRight (fun _ : Fin k => (Equiv.refl A).prodCongr ι)
  let s := a.prodCongr (τ.prodCongr (Equiv.refl (Fin k → B)))
  let e := (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A × E) (fun _ => E × B)).trans
    ((Equiv.refl (Fin k → A × E)).prodCongr
      (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => E) (fun _ => B)))
  let PE := Matrix.finKronecker (fun _ : Fin k => Matrix.selectedBellProjection Ω E) ⊗ₖ
    (1 : Matrix ((Fin k → E) × (Fin k → B)) ((Fin k → E) × (Fin k → B)) ℂ)
  let LE := (1 : Matrix (Fin k → A × E) (Fin k → A × E) ℂ) ⊗ₖ
    (Λ.submatrix τ τ ⊗ₖ (1 : Matrix (Fin k → B) (Fin k → B) ℂ))
  have h := submatrix_mulVec_mulVec_eq s PE LE
    (fun x => ∏ j, Matrix.bellPinPrevector Ω E (e.symm x j))
    (fun x => ∏ j, Matrix.bellPinPostvector Ω E (e.symm x j))
    (((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k)
    (Matrix.finKronecker_selectedBellProjection_bellPinPrevector_label Ω E k hz
      (Λ.submatrix τ τ))
  have hP : PE.submatrix s.symm s.symm = Pk := by
    exact finKronecker_pin_submatrix ((Equiv.refl A).prodCongr ι) ι
      (Matrix.selectedBellProjection Ω E) k
  have hL : LE.submatrix s.symm s.symm = ΛR := by
    simpa only [LE, ΛR, s, Equiv.prodCongr_symm, Matrix.submatrix_submatrix,
      Equiv.self_comp_symm, Equiv.refl_symm, Matrix.submatrix_id_id] using
      kronecker_one_submatrix (B := Fin k → B) a.symm τ.symm (Λ.submatrix τ τ)
  rw [hP, hL] at h
  change WithLp.toLp 2 (Pk *ᵥ (ΛR *ᵥ (fun x => ∏ j,
    Matrix.bellPinPrevector Ω E
      (((x.1 j).1, ι.symm (x.1 j).2), (ι.symm (x.2.1 j), x.2.2 j))))) =
    (((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k) •
      WithLp.toLp 2 (ΛR *ᵥ (fun x => ∏ j,
        Matrix.bellPinPostvector Ω E
          (((x.1 j).1, ι.symm (x.1 j).2), (ι.symm (x.2.1 j), x.2.2 j)))) at h
  simpa only [ι, bellPinPrevector_equivFin, Matrix.bellPinPostvector,
    Finset.prod_mul_distrib] using h

private theorem kronecker_projected_regroup {D X C R : Type*} [Fintype D] [Fintype C] [Fintype R]
    [DecidableEq D] [DecidableEq C] (left : D → X) (aux : D → C)
    (F : X × B → ℂ) (u : C × R → ℂ) (M : Matrix R R ℂ)
    (x : D × (R × B)) :
    (((1 : Matrix D D ℂ) ⊗ₖ
      (M ⊗ₖ (1 : Matrix B B ℂ))) *ᵥ
        (fun y => F (left y.1, y.2.2) * u (aux y.1, y.2.1))) x =
      F (left x.1, x.2.2) *
        (((1 : Matrix C C ℂ) ⊗ₖ M) *ᵥ u) (aux x.1, x.2.1) := by
  change (((1 : Matrix D D ℂ) ⊗ₖ (M ⊗ₖ (1 : Matrix B B ℂ))) *ᵥ
    Matrix.vec (Matrix.of (fun rb ac => F (left ac, rb.2) * u (aux ac, rb.1)))) x =
    F (left x.1, x.2.2) *
      (((1 : Matrix C C ℂ) ⊗ₖ M) *ᵥ Matrix.vec (Matrix.of (fun r c => u (c, r))))
        (aux x.1, x.2.1)
  rw [← Matrix.vec_mul_eq_mulVec, ← Matrix.vec_mul_eq_mulVec]
  simp [Matrix.vec, Matrix.mul_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, Finset.mul_sum, mul_left_comm, mul_ite]

/-- The actual physical prevector, in canonical physical--auxiliary coordinates,
has the Bell contraction coefficient `(sqrt z / |E|)^k`, with its actual right
Schur-label projector on the selected compressed vector. This holds for every
copy number, including zero, and every actual label.
OpenAI area-law manuscript, `07-comparators.tex`, lines 240–254 and 283–290,
`comparator:bell-pin`. -/
theorem selectedBellProjection_replicaPrevector (k : ℕ) (hz : 0 < z)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    let r := (((Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A)
      (fun _ => Fin E.card)).prodCongr
        (Equiv.prodComm (Fin k → Fin E.card) (Fin k → B))).trans
      (Equiv.prodProdProdComm (Fin k → A) (Fin k → Fin E.card)
        (Fin k → B) (Fin k → Fin E.card))).trans
      ((Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => A) (fun _ => B)).symm.prodCongr
        (Equiv.refl ((Fin k → Fin E.card) × (Fin k → Fin E.card))))
    let β : A × Fin E.card → ℂ := fun x =>
      Matrix.selectedBellVector Ω E (x.1, (Finset.equivFin E).symm x.2)
    let χ : Fin E.card × B → ℂ := fun x =>
      Matrix.compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.1, x.2)
    let Pk := Matrix.finKronecker (fun _ : Fin k => Matrix.vecMulVec β (star β)) ⊗ₖ
      (1 : Matrix ((Fin k → Fin E.card) × (Fin k → B))
        ((Fin k → Fin E.card) × (Fin k → B)) ℂ)
    let ΛR := (1 : Matrix (Fin k → A × Fin E.card) (Fin k → A × Fin E.card) ℂ) ⊗ₖ
      (PermutationRepresentation.labelProj (TensorPower.copyPerm (Fin E.card) k) l ⊗ₖ
        (1 : Matrix (Fin k → B) (Fin k → B) ℂ))
    WithLp.toLp 2 (Pk *ᵥ (TensorPower.replicaPrevector Ω E.card k l ∘ r)) =
      (((Real.sqrt z : ℂ) / (E.card : ℂ)) ^ k) •
        WithLp.toLp 2 (ΛR *ᵥ (fun x =>
          (∏ j, β (x.1 j)) * ∏ j, χ (x.2.1 j, x.2.2 j))) := by
  intro r β χ Pk ΛR
  have hraw : ΛR *ᵥ (fun x => ∏ j, Ω ((x.1 j).1, x.2.2 j) *
      Matrix.omegaVec E.card ((x.1 j).2, x.2.1 j)) =
      TensorPower.replicaPrevector Ω E.card k l ∘ r := by
    funext x
    simpa [ΛR, TensorPower.replicaPrevector, Function.comp_def, r,
      Finset.prod_mul_distrib] using
      kronecker_projected_regroup (B := Fin k → B)
        (fun ac : Fin k → A × Fin E.card => fun j => (ac j).1)
        (fun ac : Fin k → A × Fin E.card => fun j => (ac j).2)
        (fun ab : (Fin k → A) × (Fin k → B) => ∏ j, Ω (ab.1 j, ab.2 j))
        (fun cr : (Fin k → Fin E.card) × (Fin k → Fin E.card) =>
          ∏ j, Matrix.omegaVec E.card (cr.1 j, cr.2 j))
        (PermutationRepresentation.labelProj (TensorPower.copyPerm (Fin E.card) k) l) x
  rw [← hraw]
  exact selectedBellProjection_equivFin Ω E k hz
    (PermutationRepresentation.labelProj (TensorPower.copyPerm (Fin E.card) k) l)

/-- Positive actual selected Schmidt mass determines a unit compressed vector
with normalized diagonal marginal and one common label sequence. The physical
initial vectors are nonzero, have norm at most one, have the physical mean
energy, have both auxiliary labels, and are fixed by simultaneous copy
permutations. The selected tensor powers have inverse polynomial right-label
mass eventually, and the logarithmic label dimension is `k S(ρ_R) + o(k)`.
OpenAI area-law manuscript, `07-comparators.tex`, lines 130–147 and 240–281,
`comparator:prevector` and `comparator:high-label`. -/
theorem exists_label_sequence_schmidtBellPrevector (hz : 0 < z) (hΩ : ‖Ω‖ = 1)
    (H : Matrix (A × B) (A × B) ℂ) (E₀ : ℝ)
    (hE : H *ᵥ Ω = (E₀ : ℂ) • (fun x => Ω x)) :
    let ψ : B × Fin E.card → ℂ := fun x =>
      Matrix.compressedTypicalPureState Ω E ((Finset.equivFin E).symm x.2, x.1)
    ‖WithLp.toLp 2 ψ‖ = 1 ∧
      Matrix.partialTraceLeft (Matrix.vecMulVec ψ (star ψ)) =
        Matrix.diagonal (fun r : Fin E.card =>
          ((((Matrix.PosSemidef.isHermitian hρA).eigenvalues
            ((Finset.equivFin E).symm r)) / z : ℝ) : ℂ)) ∧
    ∃ l : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let v := replicaPrevector Ω E.card k (l k)
        let P := labelProj (copyPerm (Fin E.card) k) (l k)
        WithLp.toLp 2 v ≠ 0 ∧ ‖WithLp.toLp 2 v‖ ≤ 1 ∧
        (((k : ℝ)⁻¹ • replicaHamiltonian H k) ⊗ₖ
          (1 : Matrix ((Fin k → Fin E.card) × (Fin k → Fin E.card))
            ((Fin k → Fin E.card) × (Fin k → Fin E.card)) ℂ)) *ᵥ v = (E₀ : ℂ) • v ∧
        ((1 : Matrix (Fin k → (A × B)) (Fin k → (A × B)) ℂ) ⊗ₖ
          (P ⊗ₖ (1 : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ))) *ᵥ v = v ∧
        ((1 : Matrix (Fin k → (A × B)) (Fin k → (A × B)) ℂ) ⊗ₖ
          ((1 : Matrix (Fin k → Fin E.card) (Fin k → Fin E.card) ℂ) ⊗ₖ P)) *ᵥ v = v ∧
        (∀ σ : Equiv.Perm (Fin k),
          (permOp (copyPerm (A × B) k) σ ⊗ₖ
            (permOp (copyPerm (Fin E.card) k) σ ⊗ₖ permOp (copyPerm (Fin E.card) k) σ)) *ᵥ v = v)) ∧
      (∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (E.card ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → B) (Fin k → B) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin E.card) k) (l k)) *ᵥ
              (fun x : (Fin k → B) × (Fin k → Fin E.card) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ => Real.log (l k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ => (k : ℝ)) := by
  intro ψ
  have hψ : ‖WithLp.toLp 2 ψ‖ = 1 := norm_compressedTypicalPureState_equivFin_swap Ω E hz
  refine ⟨hψ, partialTraceLeft_compressedTypicalPureState_equivFin_swap Ω E hz, ?_⟩
  exact TensorPower.exists_label_sequence_replicaPrevector Ω hΩ ψ hψ H E₀ hE

end TensorPower
