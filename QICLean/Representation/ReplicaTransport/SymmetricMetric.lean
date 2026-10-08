/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Setup
import QICLean.Representation.CoherentSymbol
import QICLean.Analysis.ProjectionCompressionCfc
import QICLean.Analysis.Transport.Defs

/-!
# Band metrics on the symmetric subspace

The band metrics of the area-law paper, Proposition 7.4, are operators on
`𝒮_k = Sym^k V` (`06-transport.tex`, display `transport:band-metric`, lines 251--258), and
cross-band commutation is commutation on `𝒮_k` (lines 268--276). The formal band metric
`bandMetric` acts on `V^{⊗k}` and preserves `𝒮_k`; the mean trees use
`symBandMetric = Π A + (1 - Π)`, which is the same operator on `𝒮_k` and the identity on its
orthogonal complement. This file proves the properties of `symBandMetric` that the
transport argument uses:

* it is positive definite and commutes with the copy permutations;
* two of them commute exactly when the band metrics commute on `𝒮_k`
  (`TransportData.crossBandCommute_iff`);
* the whitened ratio of two of them is the extension of the whitened ratio of the band
  metrics, so the relative coherent pin transfers (`le_whiten_symBandMetric`);
* the skew square of `symBandMetric` agrees with that of the band metric against every
  symmetric density matrix (`mul_skewSquare_symBandMetric`).

The proofs are written from the paper; no Lean source was adapted.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix PermutationRepresentation Entropy

noncomputable section

namespace TensorPower.ReplicaTransport

variable {V : Type*} [Fintype V] [DecidableEq V] {n : V → ℕ}

private theorem commute_inv_right {m : Type*} [Fintype m] [DecidableEq m] {X A : Matrix m m ℂ}
    (h : Commute X A) : Commute X A⁻¹ := by
  by_cases hA : IsUnit A.det
  · have h1 : A⁻¹ * A = 1 := nonsing_inv_mul A hA
    have h2 : A * A⁻¹ = 1 := mul_nonsing_inv A hA
    calc X * A⁻¹ = A⁻¹ * (A * X) * A⁻¹ := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = A⁻¹ * (X * A) * A⁻¹ := by rw [h.eq]
      _ = A⁻¹ * X := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
  · rw [nonsing_inv_apply_not_isUnit A hA]
    exact Commute.zero_right X

/-- Band metrics commute with the permutations of entire copies. -/
theorem commute_permOp_bandMetric (t : ℝ) (k : ℕ) (π : PYF V) (s : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (SiteConfig n) k) s) (bandMetric n t k π) := by
  have hW : ∀ Q : Finset V, Commute (permOp (copyPerm (SiteConfig n) k) s)
      (replicaMetric (fun v => Fin (n v)) t k Q) := fun Q =>
    commute_copyPerm_labelObservable k Q _ s
  unfold bandMetric leafMetric leafRoot
  exact ((((commute_inv_right (hW _)).mul_right (commute_inv_right (hW _))).mul_right
    (hW _)).pow_right 2)

/-- A matrix commuting with every copy permutation commutes with the projection onto `𝒮_k`. -/
theorem commute_symProj_of_forall_commute_permOp {k : ℕ}
    {M : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ}
    (h : ∀ s, Commute (permOp (copyPerm (SiteConfig n) k) s) M) :
    Commute (symProj (copyPerm (SiteConfig n) k)) M := by
  rw [symProj]
  exact (Commute.sum_left _ _ _ fun s _ => h s).smul_left _

/-- The projection onto `𝒮_k` commutes with every copy permutation. -/
theorem commute_permOp_symProj (k : ℕ) (s : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (SiteConfig n) k) s) (symProj (copyPerm (SiteConfig n) k)) := by
  have h := congrArg conjTranspose (permOp_mul_symProj (copyPerm (SiteConfig n) k) s⁻¹)
  rw [conjTranspose_mul, isHermitian_symProj.eq, conjTranspose_permOp, inv_inv] at h
  change _ * _ = _ * _
  rw [permOp_mul_symProj, h]

/-- Band metrics commute with the projection onto `𝒮_k`. -/
theorem commute_symProj_bandMetric (t : ℝ) (k : ℕ) (π : PYF V) :
    Commute (symProj (copyPerm (SiteConfig n) k)) (bandMetric n t k π) :=
  commute_symProj_of_forall_commute_permOp fun s => commute_permOp_bandMetric t k π s

/-- A band metric of a partition is positive definite (`06-transport.tex` line 256). -/
theorem posDef_bandMetric [∀ v, NeZero (n v)] {π : PYF V} (hπ : π.IsPartition) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) : (bandMetric n t k π).PosDef := by
  obtain ⟨hPY, hPF, hYF, -⟩ := hπ
  have hR := posDef_leafRoot (n := n) ht k hPY hPF hYF
  rw [bandMetric, leafMetric, pow_two]
  exact hR.mul_of_commute hR (Commute.refl _)

/-- The extended band metric of a partition is positive definite. -/
theorem posDef_symBandMetric [∀ v, NeZero (n v)] {π : PYF V} (hπ : π.IsPartition) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) : (symBandMetric n t k π).PosDef :=
  (posDef_bandMetric hπ ht k).proj_mul_add_one_sub isHermitian_symProj symProj_mul_symProj
    (commute_symProj_bandMetric t k π)

/-- Extended band metrics commute with the permutations of entire copies. -/
theorem commute_permOp_symBandMetric (t : ℝ) (k : ℕ) (π : PYF V) (s : Equiv.Perm (Fin k)) :
    Commute (permOp (copyPerm (SiteConfig n) k) s) (symBandMetric n t k π) :=
  (commute_proj_mul_add_one_sub (commute_permOp_symProj k s).symm
    (commute_permOp_bandMetric t k π s).symm).symm

/-- An extended band metric commutes with every matrix that commutes with the band metric and
with every copy permutation. -/
theorem commute_symBandMetric_of_commute {t : ℝ} {k : ℕ} {π : PYF V}
    {X : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ}
    (hX : ∀ s, Commute (permOp (copyPerm (SiteConfig n) k) s) X)
    (hAX : Commute (bandMetric n t k π) X) : Commute (symBandMetric n t k π) X :=
  commute_proj_mul_add_one_sub (commute_symProj_of_forall_commute_permOp hX) hAX

/-- The product of two extended band metrics is the extension of the product. -/
theorem symBandMetric_mul (t : ℝ) (k : ℕ) (π π' : PYF V) :
    symBandMetric n t k π * symBandMetric n t k π' =
      symProj (copyPerm (SiteConfig n) k) * (bandMetric n t k π * bandMetric n t k π') +
        (1 - symProj (copyPerm (SiteConfig n) k)) :=
  proj_mul_add_one_sub_mul symProj_mul_symProj (commute_symProj_bandMetric t k π)

/-- Two band metrics commute on `𝒮_k` exactly when their extensions commute. -/
theorem commute_symBandMetric_iff (t : ℝ) (k : ℕ) (π π' : PYF V) :
    Commute (symBandMetric n t k π) (symBandMetric n t k π') ↔
      ∀ w ∈ symmetricSubspace k (fun v => Fin (n v)),
        bandMetric n t k π *ᵥ (bandMetric n t k π' *ᵥ w) =
          bandMetric n t k π' *ᵥ (bandMetric n t k π *ᵥ w) := by
  have hPA := commute_symProj_bandMetric (n := n) t k π
  have hPB := commute_symProj_bandMetric (n := n) t k π'
  rw [symBandMetric, symBandMetric,
    commute_proj_mul_add_one_sub_iff symProj_mul_symProj hPA hPB]
  constructor
  · intro h w hw
    have hw' : symProj (copyPerm (SiteConfig n) k) *ᵥ w = w := symProj_mulVec_of_mem _ hw
    set A := bandMetric n t k π
    set B := bandMetric n t k π'
    set P := symProj (copyPerm (SiteConfig n) k)
    calc A *ᵥ (B *ᵥ w) = (A * B) *ᵥ (P *ᵥ w) := by rw [hw', Matrix.mulVec_mulVec]
      _ = (P * (A * B)) *ᵥ w := by rw [Matrix.mulVec_mulVec, (hPA.mul_right hPB).eq]
      _ = (P * (B * A)) *ᵥ w := by rw [h]
      _ = (B * A) *ᵥ (P *ᵥ w) := by rw [Matrix.mulVec_mulVec, (hPB.mul_right hPA).eq]
      _ = B *ᵥ (A *ᵥ w) := by rw [hw', Matrix.mulVec_mulVec]
  · intro h
    have hz : (bandMetric n t k π * bandMetric n t k π' -
        bandMetric n t k π' * bandMetric n t k π) * symProj (copyPerm (SiteConfig n) k) = 0 := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      have hw := h _ (symProj_mulVec_mem _ w)
      simp only [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, Matrix.sub_mul,
        Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
      rw [hw, sub_self]
    have hc : Commute (symProj (copyPerm (SiteConfig n) k))
        (bandMetric n t k π * bandMetric n t k π' - bandMetric n t k π' * bandMetric n t k π) :=
      (hPA.mul_right hPB).sub_right (hPB.mul_right hPA)
    rw [← sub_eq_zero, ← Matrix.mul_sub, hc.eq, hz]

/-- Whitening one extended band metric by another extends the whitened band metrics. -/
theorem whiten_symBandMetric [∀ v, NeZero (n v)] {π : PYF V} (hπ : π.IsPartition) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) (π' : PYF V) :
    symBandMetric n t k π ^ (-(1 / 2) : ℝ) * symBandMetric n t k π' *
        symBandMetric n t k π ^ (-(1 / 2) : ℝ) =
      symProj (copyPerm (SiteConfig n) k) *
          (bandMetric n t k π ^ (-(1 / 2) : ℝ) * bandMetric n t k π' *
            bandMetric n t k π ^ (-(1 / 2) : ℝ)) + (1 - symProj (copyPerm (SiteConfig n) k)) :=
  (posDef_bandMetric hπ ht k).whiten_proj_mul_add_one_sub isHermitian_symProj
    symProj_mul_symProj (commute_symProj_bandMetric t k π) (commute_symProj_bandMetric t k π')

/-- **Transfer of the relative coherent pin to the extended metrics.** A lower bound
`Q ≤ A^{-1/2} A' A^{-1/2}` by a matrix `Q` supported on `𝒮_k` (`Π Q Π = Q`) also holds for the
extended band metrics. -/
theorem le_whiten_symBandMetric [∀ v, NeZero (n v)] {π : PYF V} (hπ : π.IsPartition) {t : ℝ}
    (ht : 0 ≤ t) (k : ℕ) (π' : PYF V)
    {Q : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ}
    (hQ : symProj (copyPerm (SiteConfig n) k) * Q * symProj (copyPerm (SiteConfig n) k) = Q)
    (hle : Q ≤ bandMetric n t k π ^ (-(1 / 2) : ℝ) * bandMetric n t k π' *
      bandMetric n t k π ^ (-(1 / 2) : ℝ)) :
    Q ≤ symBandMetric n t k π ^ (-(1 / 2) : ℝ) * symBandMetric n t k π' *
      symBandMetric n t k π ^ (-(1 / 2) : ℝ) :=
  (posDef_bandMetric hπ ht k).le_whiten_proj_mul_add_one_sub isHermitian_symProj
    symProj_mul_symProj (commute_symProj_bandMetric t k π) (commute_symProj_bandMetric t k π')
    hQ hle

section SkewSquare

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- `P (P A + (1 - P))^r = P A^r` for an orthogonal projection `P` commuting with a positive
definite `A`. -/
private theorem proj_mul_rpow_extension {P A : Matrix m m ℂ} (hA : A.PosDef)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPA : Commute P A) (r : ℝ) :
    P * (P * A + (1 - P)) ^ r = P * A ^ r := by
  rw [hA.rpow_proj_mul_add_one_sub hP hPP hPA, Matrix.mul_add, ← Matrix.mul_assoc, hPP,
    Matrix.mul_sub, Matrix.mul_one, hPP, sub_self, add_zero]

/-- **The skew square on the range of a projection.** For an orthogonal projection `P`
commuting with a positive definite `A` and with `X`, the skew squares of the extension
`P A + (1 - P)` and of `A` agree after multiplication by `P`. -/
theorem proj_mul_skewSquare_extension {P A X : Matrix m m ℂ} (hA : A.PosDef)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPA : Commute P A) (hPX : Commute P X) :
    P * Transport.skewSquare (P * A + (1 - P)) X = P * Transport.skewSquare A X := by
  set E := P * A + (1 - P)
  have hE : E.PosDef := hA.proj_mul_add_one_sub hP hPP hPA
  have hPE : Commute P E := (Commute.refl P).mul_right hPA |>.add_right
    ((Commute.one_right P).sub_right (Commute.refl P))
  have hPr : ∀ r : ℝ, Commute P (A ^ r) := fun r => by
    rw [CFC.rpow_def]; exact (Commute.cfc_nnreal hPA.symm _).symm
  have hPEr : ∀ r : ℝ, Commute P (E ^ r) := fun r => by
    rw [CFC.rpow_def]; exact (Commute.cfc_nnreal hPE.symm _).symm
  set O := A ^ (-(1 / 2) : ℝ) * X * A ^ (1 / 2 : ℝ)
  set Oc := E ^ (-(1 / 2) : ℝ) * X * E ^ (1 / 2 : ℝ)
  have hPO : Commute P O := ((hPr _).mul_right hPX).mul_right (hPr _)
  have hPOc : Commute P Oc := ((hPEr _).mul_right hPX).mul_right (hPEr _)
  have hPstar : ∀ {M : Matrix m m ℂ}, Commute P M → Commute P Mᴴ := fun {M} h => by
    have := congrArg conjTranspose h.eq
    rw [conjTranspose_mul, conjTranspose_mul, hP.eq] at this
    exact this.symm
  have e1 : P * Oc = P * O := by
    calc P * Oc = P * E ^ (-(1 / 2) : ℝ) * X * E ^ (1 / 2 : ℝ) := by
          simp only [Oc, Matrix.mul_assoc]
      _ = A ^ (-(1 / 2) : ℝ) * (P * X) * E ^ (1 / 2 : ℝ) := by
          rw [proj_mul_rpow_extension hA hP hPP hPA, (hPr _).eq]
          simp only [Matrix.mul_assoc]
      _ = A ^ (-(1 / 2) : ℝ) * X * (P * E ^ (1 / 2 : ℝ)) := by
          rw [hPX.eq]; simp only [Matrix.mul_assoc]
      _ = O * P := by
          rw [proj_mul_rpow_extension hA hP hPP hPA, (hPr _).eq]
          simp only [O, Matrix.mul_assoc]
      _ = P * O := hPO.eq.symm
  have e2 : P * Ocᴴ = P * Oᴴ := by
    have := congrArg conjTranspose e1
    rw [conjTranspose_mul P Oc, conjTranspose_mul P O, hP.eq] at this
    rw [(hPstar hPOc).eq, (hPstar hPO).eq, this]
  have e3 : P * (Oc * Ocᴴ) = P * (O * Oᴴ) := by
    calc P * (Oc * Ocᴴ) = O * (P * Ocᴴ) := by
          rw [← Matrix.mul_assoc, e1, hPO.eq, Matrix.mul_assoc]
      _ = P * (O * Oᴴ) := by rw [e2, ← Matrix.mul_assoc, ← hPO.eq, Matrix.mul_assoc]
  have e4 : P * (Ocᴴ * Oc) = P * (Oᴴ * O) := by
    calc P * (Ocᴴ * Oc) = Oᴴ * (P * Oc) := by
          rw [← Matrix.mul_assoc, e2, (hPstar hPO).eq, Matrix.mul_assoc]
      _ = P * (Oᴴ * O) := by
          rw [e1, ← Matrix.mul_assoc, ← (hPstar hPO).eq, Matrix.mul_assoc]
  have hsq : ∀ {Y Z : Matrix m m ℂ}, Y.PosSemidef → Z.PosSemidef → Commute P Z →
      P * Y = P * Z → P * CFC.sqrt Y = P * CFC.sqrt Z := fun {Y Z} hY hZ hPZ h => by
    rw [CFC.sqrt_eq_real_sqrt Y hY.nonneg, CFC.sqrt_eq_real_sqrt Z hZ.nonneg,
      cfcₙ_eq_cfc, cfcₙ_eq_cfc]
    exact mul_cfc_eq_mul_cfc_of_mul_eq hY.isHermitian hZ.isHermitian hPZ h _
  have s1 := hsq (posSemidef_self_mul_conjTranspose Oc) (posSemidef_self_mul_conjTranspose O)
    (hPO.mul_right (hPstar hPO)) e3
  have s2 := hsq (posSemidef_conjTranspose_mul_self Oc) (posSemidef_conjTranspose_mul_self O)
    ((hPstar hPO).mul_right hPO) e4
  simp only [Transport.skewSquare]
  rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_add, s1, s2, e1, e2, ← Matrix.mul_add,
    ← Matrix.mul_sub, ← Matrix.mul_sub]

/-- Against a density matrix `ρ = P ρ` on the range of `P`, the skew squares of the extension
and of `A` agree. -/
theorem mul_skewSquare_extension {P A X ρ : Matrix m m ℂ} (hA : A.PosDef)
    (hP : P.IsHermitian) (hPP : P * P = P) (hPA : Commute P A) (hPX : Commute P X)
    (hρ : ρ.IsHermitian) (hPρ : P * ρ = ρ) :
    ρ * Transport.skewSquare (P * A + (1 - P)) X = ρ * Transport.skewSquare A X := by
  have hρP : ρ * P = ρ := by
    have := congrArg conjTranspose hPρ
    rwa [conjTranspose_mul, hP.eq, hρ.eq] at this
  rw [← hρP, Matrix.mul_assoc, Matrix.mul_assoc, proj_mul_skewSquare_extension hA hP hPP hPA hPX]

end SkewSquare

/-- **The skew square of an extended band metric** against a density matrix on `𝒮_k` is that
of the band metric, for every `X` commuting with the copy permutations. -/
theorem mul_skewSquare_symBandMetric [∀ v, NeZero (n v)] {π : PYF V} (hπ : π.IsPartition)
    {t : ℝ} (ht : 0 ≤ t) {k : ℕ}
    {X ρ : Matrix (Config k fun v => Fin (n v)) (Config k fun v => Fin (n v)) ℂ}
    (hX : ∀ s, Commute (permOp (copyPerm (SiteConfig n) k) s) X) (hρ : ρ.IsHermitian)
    (hPρ : symProj (copyPerm (SiteConfig n) k) * ρ = ρ) :
    ρ * Transport.skewSquare (symBandMetric n t k π) X =
      ρ * Transport.skewSquare (bandMetric n t k π) X :=
  mul_skewSquare_extension (posDef_bandMetric hπ ht k) isHermitian_symProj symProj_mul_symProj
    (commute_symProj_bandMetric t k π) (commute_symProj_of_forall_commute_permOp hX) hρ hPρ

namespace TransportData

variable {K : ℕ} {H : Type*} {C : H → Type*} (D : TransportData V K H C)

/-- **Cross-band commutation, operator form**: the band metrics commute on `𝒮_k` exactly when
their extensions commute on `V^{⊗k}`. -/
theorem crossBandCommute_iff (t : ℝ) (k : ℕ) :
    D.CrossBandCommute n t k ↔ ∀ j j' g g', g ≠ g' →
      Commute (symBandMetric n t k (D.leafPart j g)) (symBandMetric n t k (D.leafPart j' g')) :=
  forall₄_congr fun _ _ _ _ => imp_congr_right fun _ => (commute_symBandMetric_iff t k _ _).symm

end TransportData

end TensorPower.ReplicaTransport
