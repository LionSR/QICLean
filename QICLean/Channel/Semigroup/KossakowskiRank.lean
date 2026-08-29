/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.Semigroup.KossakowskiForm

/-!
# Rank of the Kossakowski matrix

This file relates the minimum number of Lindblad operators representing a
generator to the rank of its Kossakowski matrix in Wolf's traceless basis.

## Main definitions

* `lindbladSpan` is the linear span of a displayed Lindblad family.
* `kossakowskiRank` is the minimum size of a Lindblad representation.

## Main results

* `LindbladForm.exists_equivalent_rank_le_finrank` compresses a Lindblad
  family to the dimension of a subspace containing its operators.
* `TracelessBasisKossakowskiForm.kossakowskiRank_toLinearMap_eq_rank` proves
  that this minimum equals the rank of Wolf's Kossakowski matrix `C`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Section 7.1.2,
  Theorem 7.1 and Corollary 7.2]
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder TNOperatorSpace
open Matrix Finset Module

noncomputable section

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- The `ℂ`-linear span of the operators in a Lindblad family. -/
def lindbladSpan (F : LindbladForm D) : Submodule ℂ Mat :=
  Submodule.span ℂ (Set.range F.L)

/-- The minimum number of Lindblad operators among all representations of a
fixed generator. -/
def kossakowskiRank (L : Mat →ₗ[ℂ] Mat) : ℕ :=
  sInf {n : ℕ | ∃ F : LindbladForm D, F.toLinearMap = L ∧ F.r = n}

namespace LindbladForm

/-- Bilinear sum identity for rectangular coefficient matrices:
`Σⱼ (Σₖ Aⱼₖ•Fₖ) * M * (Σₖ Aⱼₖ•Fₖ)†`
equals `Σₖₗ (A†A)ₗₖ • (Fₖ * M * Fₗ†)`. -/
private lemma bilinear_sum_identity {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℂ)
    (f : Fin n → Mat)
    (M : Mat) :
    ∑ j : Fin r, (∑ k, A j k • f k) * M * (∑ k, A j k • f k)ᴴ =
    ∑ k : Fin n, ∑ l : Fin n, (Aᴴ * A) l k • (f k * M * (f l)ᴴ) := by
  simp_rw [conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    smul_smul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [← Finset.sum_smul]; congr 1
  simp [conjTranspose_apply, mul_apply, mul_comm]

/-- Adjoint variant of `bilinear_sum_identity`. -/
private lemma bilinear_adj_sum_identity {r n : ℕ}
    (A : Matrix (Fin r) (Fin n) ℂ)
    (f : Fin n → Mat) :
    ∑ j : Fin r, (∑ k, A j k • f k)ᴴ * (∑ k, A j k • f k) =
    ∑ l : Fin n, ∑ k : Fin n, (Aᴴ * A) l k • ((f l)ᴴ * f k) := by
  simp_rw [conjTranspose_sum, Matrix.conjTranspose_smul, Complex.star_def]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  rw [← Finset.sum_smul]; congr 1

/-- If every operator in a Lindblad family lies in a subspace `V`, the same
generator admits a Lindblad representation with at most `finrank ℂ V`
operators. -/
theorem exists_equivalent_rank_le_finrank
    (G : LindbladForm D) (V : Submodule ℂ Mat)
    (hV : ∀ j : Fin G.r, G.L j ∈ V) :
    ∃ G' : LindbladForm D,
      G'.toLinearMap = G.toLinearMap ∧ G'.r ≤ Module.finrank ℂ V := by
  set m := Module.finrank ℂ V
  let e := Module.finBasis ℂ V
  let α : Matrix (Fin G.r) (Fin m) ℂ := fun j k => (e.repr ⟨G.L j, hV j⟩) k
  have hL_expand : ∀ j, G.L j = ∑ k : Fin m, α j k • (e k : Mat) := by
    intro j
    have hrepr : (⟨G.L j, hV j⟩ : V) =
        ∑ k, (e.repr ⟨G.L j, hV j⟩) k • e k := by
      rw [← e.sum_equivFun ⟨G.L j, hV j⟩]
      simp [Basis.equivFun_apply]
    have hval := congrArg Subtype.val hrepr
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hval
    exact hval
  have hC_psd : (αᴴ * α).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self α
  set B := CFC.sqrt (αᴴ * α)
  have hC_factor : (αᴴ * α) = Bᴴ * B := by
    have hB_psd := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (αᴴ * α))
    rw [hB_psd.isHermitian.eq]
    simpa using
      (CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hC_psd)).symm
  let L' : Fin m → Mat := fun i => ∑ k : Fin m, B i k • (e k : Mat)
  refine ⟨⟨m, G.H, L', G.H_hermitian⟩, ?_, le_refl m⟩
  let f : Fin m → Mat := fun k => (e k : Mat)
  have hsum_expand : ∀ N : Mat,
      ∑ j : Fin G.r, G.L j * N * (G.L j)ᴴ =
      ∑ j : Fin G.r, (∑ k, α j k • f k) * N * (∑ k, α j k • f k)ᴴ := by
    intro N
    apply Finset.sum_congr rfl
    intro j _
    rw [hL_expand j]
  have hadj_expand :
      ∑ j : Fin G.r, (G.L j)ᴴ * G.L j =
      ∑ j : Fin G.r, (∑ k, α j k • f k)ᴴ * (∑ k, α j k • f k) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hL_expand j]
  have hcp_eq : ∀ N : Mat,
      ∑ j : Fin G.r, G.L j * N * (G.L j)ᴴ =
      ∑ i : Fin m, L' i * N * (L' i)ᴴ := by
    intro N
    rw [hsum_expand N, bilinear_sum_identity α f N]
    rw [show (∑ i : Fin m, L' i * N * (L' i)ᴴ) =
      ∑ k, ∑ l, (Bᴴ * B) l k • (f k * N * (f l)ᴴ) from
        bilinear_sum_identity B f N]
    rw [hC_factor]
  have hadj_eq :
      ∑ j : Fin G.r, (G.L j)ᴴ * G.L j =
      ∑ i : Fin m, (L' i)ᴴ * L' i := by
    rw [hadj_expand, bilinear_adj_sum_identity α f]
    rw [show (∑ i : Fin m, (L' i)ᴴ * L' i) =
      ∑ l, ∑ k, (Bᴴ * B) l k • ((f l)ᴴ * f k) from
        bilinear_adj_sum_identity B f]
    rw [hC_factor]
  ext1 ρ
  simp only [LindbladForm.toLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  congr 1
  simp only [dissipator]
  simp_rw [Finset.sum_sub_distrib]
  congr 1
  · congr 1
    · exact (hcp_eq ρ).symm
    · rw [← Finset.smul_sum, ← Finset.smul_sum,
          ← Finset.sum_mul, ← Finset.sum_mul, hadj_eq]
  · rw [← Finset.smul_sum, ← Finset.smul_sum,
        ← Finset.mul_sum, ← Finset.mul_sum, hadj_eq]

/-- The span of a family of `F.r` Lindblad operators has dimension at most
`F.r`. -/
theorem finrank_lindbladSpan_le_rank (F : LindbladForm D) :
    Module.finrank ℂ (lindbladSpan F) ≤ F.r := by
  calc
    Module.finrank ℂ (lindbladSpan F) ≤
        (Set.range F.L).toFinset.card := finrank_span_le_card (Set.range F.L)
    _ = Fintype.card (Set.range F.L) := Set.toFinset_card _
    _ ≤ Fintype.card (Fin F.r) := Fintype.card_range_le F.L
    _ = F.r := Fintype.card_fin F.r

/-- Every member of a zero-padded Lindblad family belongs to the span of the
original family. -/
private theorem zeroPad_mem_lindbladSpan (F : LindbladForm D) {n : ℕ}
    (i : Fin n) : Kraus.zeroPad F.L i ∈ lindbladSpan F := by
  simp only [Kraus.zeroPad]
  split_ifs with hi
  · exact Submodule.subset_span
      (Set.mem_range_self (⟨i, hi⟩ : Fin F.r))
  · exact Submodule.zero_mem _

/-- A zero-padded linear mixing of one Lindblad family by another gives the
corresponding inclusion of their spans. -/
private theorem lindbladSpan_le_of_zeroPad_relation
    (F G : LindbladForm D)
    (hU : ∃ U : Matrix.unitaryGroup (Fin (max F.r G.r)) ℂ,
      ∀ i, Kraus.zeroPad G.L i =
        ∑ j, (U : Matrix (Fin (max F.r G.r)) (Fin (max F.r G.r)) ℂ) i j •
          Kraus.zeroPad F.L j) :
    lindbladSpan G ≤ lindbladSpan F := by
  obtain ⟨U, hU⟩ := hU
  rw [lindbladSpan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hi := hU (Fin.castLE (Nat.le_max_right F.r G.r) i)
  rw [Kraus.zeroPad_castLE (Nat.le_max_right F.r G.r) G.L i] at hi
  rw [hi]
  exact Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (zeroPad_mem_lindbladSpan F j)

/-- Traceless Lindblad representations of the same generator have the same
linear span. This is the span consequence of Wolf, Proposition 7.4(2). -/
theorem lindbladSpan_eq_of_toLinearMap_eq_of_hasTracelessKraus
    (F G : LindbladForm D)
    (hFG : F.toLinearMap = G.toLinearMap)
    (hF : F.HasTracelessKraus) (hG : G.HasTracelessKraus) :
    lindbladSpan F = lindbladSpan G := by
  have hle : ∀ (A B : LindbladForm D),
      A.toLinearMap = B.toLinearMap →
      A.HasTracelessKraus → B.HasTracelessKraus →
      lindbladSpan B ≤ lindbladSpan A := by
    intro A B hAB hAtr hBtr
    apply lindbladSpan_le_of_zeroPad_relation A B
    exact (generatorDecomp_traceless_representation_freedom
      A.toGeneratorDecomp B.toGeneratorDecomp A.L B.L
      (fun _ ↦ rfl) (fun _ ↦ rfl)
      (by
        rw [← A.toLinearMap_eq_generatorDecomp,
          ← B.toLinearMap_eq_generatorDecomp, hAB])
      hAtr hBtr).2.2
  exact le_antisymm (hle G F hFG.symm hG hF) (hle F G hFG hF hG)

end LindbladForm

/-- The span of the square-root Lindblad operators has dimension equal to the
rank of Wolf's Kossakowski matrix `C`. -/
theorem TracelessBasisKossakowskiForm.finrank_lindbladSpan_sqrtLindbladForm
    (K : TracelessBasisKossakowskiForm D) :
    Module.finrank ℂ (lindbladSpan K.sqrtLindbladForm) = K.C.rank := by
  let B : Matrix (Fin (D ^ 2 - 1)) (Fin (D ^ 2 - 1)) ℂ := CFC.sqrt K.C
  let E : (Fin (D ^ 2 - 1) → ℂ) ≃ₗ[ℂ] tracelessMatrixSubspace D :=
    K.F.equivFun.symm
  let ι : tracelessMatrixSubspace D →ₗ[ℂ] Mat :=
    (tracelessMatrixSubspace D).subtype
  let S : Submodule ℂ (Fin (D ^ 2 - 1) → ℂ) :=
    Submodule.span ℂ (Set.range B.row)
  have hL : K.sqrtLindbladForm.L = fun j ↦ ι (E (B.row j)) := by
    funext j
    simp [TracelessBasisKossakowskiForm.sqrtLindbladForm, B, E, ι,
      TracelessBasisKossakowskiForm.toKossakowskiForm,
      Basis.equivFun_symm_apply]
    rfl
  have hspan :
      lindbladSpan K.sqrtLindbladForm =
        Submodule.map ι (Submodule.map (E : _ →ₗ[ℂ] _) S) := by
    rw [lindbladSpan, hL, ← Submodule.map_comp, Submodule.map_span]
    congr 1
    rw [← Set.range_comp]
    rfl
  have hfinrank :
      Module.finrank ℂ (lindbladSpan K.sqrtLindbladForm) =
        Module.finrank ℂ S := by
    rw [hspan, Submodule.finrank_map_subtype_eq,
      LinearEquiv.finrank_map_eq]
  have hC_factor : K.C = Bᴴ * B := by
    have hC_nonneg : 0 ≤ K.C :=
      Matrix.nonneg_iff_posSemidef.mpr K.C_posSemidef
    have hB_psd : B.PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K.C)
    change K.C = Bᴴ * B
    rw [hB_psd.isHermitian.eq]
    simpa [B] using (CFC.sqrt_mul_sqrt_self K.C hC_nonneg).symm
  calc
    Module.finrank ℂ (lindbladSpan K.sqrtLindbladForm) =
        Module.finrank ℂ S := hfinrank
    _ = B.rank := (Matrix.rank_eq_finrank_span_row B).symm
    _ = K.C.rank := by
      rw [hC_factor, Matrix.rank_conjTranspose_mul_self]

/-- For Wolf's basis-level representation, the minimum number of Lindblad
operators is exactly the rank of the Kossakowski matrix `C`. -/
theorem TracelessBasisKossakowskiForm.kossakowskiRank_toLinearMap_eq_rank
    (K : TracelessBasisKossakowskiForm D) :
    kossakowskiRank K.toLinearMap = K.C.rank := by
  apply le_antisymm
  · have hsqrt_mem : ∀ j : Fin K.sqrtLindbladForm.r,
        K.sqrtLindbladForm.L j ∈ lindbladSpan K.sqrtLindbladForm := fun j ↦
      Submodule.subset_span (Set.mem_range_self j)
    obtain ⟨F, hF, hFr⟩ :=
      K.sqrtLindbladForm.exists_equivalent_rank_le_finrank
        (lindbladSpan K.sqrtLindbladForm) hsqrt_mem
    calc
      kossakowskiRank K.toLinearMap ≤ F.r := by
        apply Nat.sInf_le
        exact ⟨F, hF.trans K.toLinearMap_eq_sqrtLindbladForm.symm, rfl⟩
      _ ≤ Module.finrank ℂ (lindbladSpan K.sqrtLindbladForm) := hFr
      _ = K.C.rank := K.finrank_lindbladSpan_sqrtLindbladForm
  · by_cases hD : D = 0
    · subst D
      have hCrank : K.C.rank = 0 := by
        have hle := Matrix.rank_le_card_width K.C
        simpa using Nat.eq_zero_of_le_zero hle
      rw [hCrank]
      exact Nat.zero_le _
    · let _ : NeZero D := ⟨hD⟩
      have hrepresentations :
          {n : ℕ | ∃ F : LindbladForm D,
            F.toLinearMap = K.toLinearMap ∧ F.r = n}.Nonempty := by
        refine ⟨K.sqrtLindbladForm.r, K.sqrtLindbladForm, ?_, rfl⟩
        exact K.toLinearMap_eq_sqrtLindbladForm.symm
      have hminimum :
          kossakowskiRank K.toLinearMap ∈
            {n : ℕ | ∃ F : LindbladForm D,
              F.toLinearMap = K.toLinearMap ∧ F.r = n} := by
        exact Nat.sInf_mem hrepresentations
      obtain ⟨F, hF, hFr⟩ := hminimum
      obtain ⟨Ftr, hFtr, htr, -, hFtr_r⟩ :=
        F.exists_traceless_in_submodule_same_rank ⊤ (by simp) (fun _ ↦ by simp)
      have hFtr_sqrt : Ftr.toLinearMap = K.sqrtLindbladForm.toLinearMap :=
        hFtr.trans (hF.trans K.toLinearMap_eq_sqrtLindbladForm)
      have hspan : lindbladSpan Ftr = lindbladSpan K.sqrtLindbladForm :=
        Ftr.lindbladSpan_eq_of_toLinearMap_eq_of_hasTracelessKraus
          K.sqrtLindbladForm hFtr_sqrt htr
          K.sqrtLindbladForm_hasTracelessKraus
      calc
        K.C.rank = Module.finrank ℂ (lindbladSpan K.sqrtLindbladForm) :=
          K.finrank_lindbladSpan_sqrtLindbladForm.symm
        _ = Module.finrank ℂ (lindbladSpan Ftr) := by rw [hspan]
        _ ≤ Ftr.r := Ftr.finrank_lindbladSpan_le_rank
        _ = F.r := hFtr_r
        _ = kossakowskiRank K.toLinearMap := hFr

end -- noncomputable section
