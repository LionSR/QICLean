/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.GroupedCopies
import QICLean.Representation.SchurLabelCommutation

/-!
# Merging the labels of disjoint subsystems

This file proves the dimension inequalities of part 3 of Lemma 6.1 (`lem:schur`) of the
area-law paper (*A two-dimensional area law from a global spectral gap*,
`05-replicas.tex`, lines 105–111, proof lines 183–189): if `Q, E` are disjoint and their
labels `λ, μ` are compatible with the label `ν` on `QE`, then `d_ν ≤ d_λ d_μ` and
`d_λ ≤ d_ν d_μ`.

The argument is stated for two pointwise-commuting permutation actions `φ_Q, φ_E` of a
finite group and their product action `φ_{QE} = φ_Q φ_E`: a joint block of `λ` and `μ`
has dimension at most `d_λ d_μ`, is invariant under the product action, and its image
under `π^ν` is a nonzero invariant subspace of the `ν`-isotypic component.

## Main declarations

* `PermutationRepresentation.dim_le_mul_dim_of_compatible` — `d_ν ≤ d_λ d_μ`.
* `PermutationRepresentation.dim_le_mul_dim_of_compatible'` — `d_λ ≤ d_ν d_μ`, through the
  action `M ↦ U_{QE}(σ) M U_E(σ)⁻¹` on matrices, which replaces the duality argument.
* `TensorPower.merge_dim_le` — both inequalities for disjoint subsystems.
-/

open MonoidAlgebra Matrix Module

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  {φQ φE φQE : G →* Equiv.Perm X}

/-- **Lemma 6.1(3), first merge inequality** (`05-replicas.tex`, lines 105–111, 183–186).
For pointwise-commuting actions `φ_Q, φ_E` with product `φ_{QE}`, if the labels `λ, μ` of
`φ_Q, φ_E` are compatible with the label `ν` of `φ_{QE}`, then `d_ν ≤ d_λ d_μ`. -/
theorem dim_le_mul_dim_of_compatible (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) {l μ ν : IrrepLabel G}
    (hP : labelProj φQ l * labelProj φE μ * labelProj φQE ν ≠ 0) :
    ν.dim ≤ l.dim * μ.dim := by
  set ol : Fin l.dim := ⟨0, l.dim_pos⟩
  set oμ : Fin μ.dim := ⟨0, μ.dim_pos⟩
  -- `π^ν` commutes with the central functions of `φ_Q` and `φ_E`.
  have hνl : Commute (labelProj φQ l) (labelProj φQE ν) :=
    commute_groupAlgebraRep_of_eq_mul φQ φE φQE hprod hcomm
      (IrrepLabel.centralIdem_mem_center l) _
  have hνμ : Commute (labelProj φE μ) (labelProj φQE ν) :=
    commute_groupAlgebraRep_of_eq_mul φE φQ φQE (fun g => by rw [hprod, (hcomm g g).eq])
      (fun g h => (hcomm h g).symm) (IrrepLabel.centralIdem_mem_center μ) _
  obtain ⟨i, a, hia⟩ : ∃ i a, labelProj φQE ν *
      ((matrixUnitOp φQ l i ol * matrixUnitOp φE μ a oμ) *
        (matrixUnitOp φQ l ol i * matrixUnitOp φE μ oμ a)) ≠ 0 := by
    by_contra! h
    apply hP
    rw [mul_assoc, hνμ.eq, ← mul_assoc, hνl.eq, mul_assoc, ← sum_matrixUnitOp_diag φQ l,
      ← sum_matrixUnitOp_diag φE μ, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    have hsplit : (matrixUnitOp φQ l i ol * matrixUnitOp φE μ a oμ) *
        (matrixUnitOp φQ l ol i * matrixUnitOp φE μ oμ a) =
          matrixUnitOp φQ l i i * matrixUnitOp φE μ a a := by
      rw [mul_assoc, ← mul_assoc (matrixUnitOp φE μ a oμ),
        ← (commute_matrixUnitOp_pair hcomm l μ ol i a oμ).eq, mul_assoc, ← mul_assoc,
        matrixUnitOp_mul_matrixUnitOp_self, matrixUnitOp_mul_matrixUnitOp_self]
    have := h i a
    rwa [hsplit] at this
  obtain ⟨x, hx⟩ := exists_mulVec_ne_zero hia
  set w := (matrixUnitOp φQ l ol i * matrixUnitOp φE μ oμ a) *ᵥ x
  set W := pairBlockSpan φQ φE l μ w
  have hWinv : ∀ g, ∀ y ∈ W, permOp φQE g *ᵥ y ∈ W := by
    intro g y hy
    rw [permOp_of_eq_mul φQ φE φQE hprod g, ← mulVec_mulVec]
    exact permOp_mulVec_mem_pairBlockSpan_left φQ φE l μ w g
      (permOp_mulVec_mem_pairBlockSpan_right hcomm l μ w g hy)
  set V := Submodule.map (toLin' (labelProj φQE ν)) W
  have hVinv : ∀ g, ∀ y ∈ V, permOp φQE g *ᵥ y ∈ V := by
    rintro g _ ⟨y, hy, rfl⟩
    refine ⟨permOp φQE g *ᵥ y, hWinv g y hy, ?_⟩
    simp only [toLin'_apply, mulVec_mulVec, (commute_labelProj_permOp φQE ν g).eq]
  have hVν : ∀ y ∈ V, labelProj φQE ν *ᵥ y = y := by
    rintro _ ⟨y, -, rfl⟩
    rw [toLin'_apply, mulVec_mulVec, labelProj_mul_self]
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hmem : labelProj φQE ν *ᵥ
        ((matrixUnitOp φQ l i ol * matrixUnitOp φE μ a oμ) *ᵥ w) ∈ V :=
      ⟨_, Submodule.subset_span ⟨(i, a), rfl⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    apply hx
    simpa [w, mulVec_mulVec, mul_assoc] using hmem
  calc ν.dim ≤ finrank ℂ V := dim_le_finrank_of_invariant φQE ν hVinv hVν hVne
    _ ≤ finrank ℂ W := Submodule.finrank_map_le _ _
    _ ≤ l.dim * μ.dim := finrank_pairBlockSpan_le φQ φE l μ w

/-- The action on pairs `σ • (x, y) = (φ σ x, ψ σ y)`; on matrices it is
`M ↦ U_φ(σ) M U_ψ(σ)⁻¹`. -/
def pairAction (φ ψ : G →* Equiv.Perm X) : G →* Equiv.Perm (X × X) where
  toFun σ := Equiv.prodCongr (φ σ) (ψ σ)
  map_one' := by ext <;> simp
  map_mul' σ τ := by ext <;> simp

/-- A matrix as a vector indexed by pairs. -/
def vecOfMatrix (M : Matrix X X ℂ) : X × X → ℂ := fun p => M p.1 p.2

omit [Fintype G] in
theorem permOp_pairAction_mulVec (φ ψ : G →* Equiv.Perm X) (σ : G) (M : Matrix X X ℂ) :
    permOp (pairAction φ ψ) σ *ᵥ vecOfMatrix M =
      vecOfMatrix (permOp φ σ * M * permOp ψ σ⁻¹) := by
  funext p
  rw [permOp_mulVec, permOp_apply, permOp_apply, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp [vecOfMatrix, pairAction, Equiv.Perm.inv_def, map_inv]

omit [Fintype G] [Fintype X] [DecidableEq X] in
theorem vecOfMatrix_injective : Function.Injective (vecOfMatrix (X := X)) := by
  intro M N h
  ext i j
  exact congrFun h (i, j)

omit [Fintype G] [Fintype X] [DecidableEq X] in
theorem vecOfMatrix_smul (c : ℂ) (M : Matrix X X ℂ) :
    vecOfMatrix (c • M) = c • vecOfMatrix M := rfl

omit [Fintype G] [Fintype X] [DecidableEq X] in
theorem vecOfMatrix_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix X X ℂ) :
    vecOfMatrix (∑ i ∈ s, M i) = ∑ i ∈ s, vecOfMatrix (M i) := by
  funext p
  simp [vecOfMatrix, Matrix.sum_apply, Finset.sum_apply]

/-- **Lemma 6.1(3), second merge inequality** (`05-replicas.tex`, lines 105–111, 186–189).
For pointwise-commuting actions `φ_Q, φ_E` with product `φ_{QE}`, if the labels `λ, μ` of
`φ_Q, φ_E` are compatible with the label `ν` of `φ_{QE}`, then `d_λ ≤ d_ν d_μ`.

The paper derives this from `Hom([ν], [λ] ⊗ [μ]) ≅ Hom([λ], [ν] ⊗ [μ]^*)` and
self-duality. Here the role of `[ν] ⊗ [μ]^*` is played by the matrices
`E^ν_{jo} N E^μ_{ob}` under the action `M ↦ U_{QE}(σ) M U_E(σ)⁻¹`, whose restriction to
the copies of `Q` is `U_Q(σ)`. -/
theorem dim_le_mul_dim_of_compatible' (hcomm : ∀ g h, Commute (φQ g) (φE h))
    (hprod : ∀ g, φQE g = φQ g * φE g) {l μ ν : IrrepLabel G}
    (hP : labelProj φQ l * labelProj φE μ * labelProj φQE ν ≠ 0) :
    l.dim ≤ ν.dim * μ.dim := by
  set oν : Fin ν.dim := ⟨0, ν.dim_pos⟩
  set oμ : Fin μ.dim := ⟨0, μ.dim_pos⟩
  have hprod' : ∀ g, φQE g = φE g * φQ g := fun g => by rw [hprod, (hcomm g g).eq]
  have h1 : ∀ σ, Commute (labelProj φQ l) (permOp φQE σ) := fun σ => by
    rw [labelProj]
    simpa using commute_groupAlgebraRep_of_eq_mul φQ φE φQE hprod hcomm
      (IrrepLabel.centralIdem_mem_center l) (single σ 1)
  have h2 : ∀ σ, Commute (labelProj φE μ) (permOp φQE σ) := fun σ => by
    rw [labelProj]
    simpa using commute_groupAlgebraRep_of_eq_mul φE φQ φQE hprod'
      (fun g h => (hcomm h g).symm) (IrrepLabel.centralIdem_mem_center μ) (single σ 1)
  have hνl : Commute (labelProj φQ l) (labelProj φQE ν) :=
    commute_groupAlgebraRep_of_eq_mul φQ φE φQE hprod hcomm
      (IrrepLabel.centralIdem_mem_center l) _
  have hνμ : Commute (labelProj φE μ) (labelProj φQE ν) :=
    commute_groupAlgebraRep_of_eq_mul φE φQ φQE hprod'
      (fun g h => (hcomm h g).symm) (IrrepLabel.centralIdem_mem_center μ) _
  have hlμ : Commute (labelProj φQ l) (labelProj φE μ) :=
    commute_groupAlgebraRep_of_commute φQ φE hcomm _ _
  have hPQE : ∀ σ, Commute (labelProj φQ l * labelProj φE μ * labelProj φQE ν)
      (permOp φQE σ) := fun σ =>
    ((h1 σ).mul_left (h2 σ)).mul_left (commute_labelProj_permOp φQE ν σ)
  have hPl : labelProj φQ l * labelProj φE μ * labelProj φQE ν * labelProj φQ l =
      labelProj φQ l * labelProj φE μ * labelProj φQE ν := by
    rw [mul_assoc (labelProj φQ l * labelProj φE μ), ← hνl.eq, ← mul_assoc,
      mul_assoc (labelProj φQ l) (labelProj φE μ), ← hlμ.eq, ← mul_assoc, labelProj_mul_self]
  have hνP : labelProj φQE ν * (labelProj φQ l * labelProj φE μ * labelProj φQE ν) =
      labelProj φQ l * labelProj φE μ * labelProj φQE ν := by
    rw [← mul_assoc, ← mul_assoc, ← hνl.eq, mul_assoc (labelProj φQ l), ← hνμ.eq, ← mul_assoc,
      mul_assoc _ (labelProj φQE ν), labelProj_mul_self]
  have hPμ : labelProj φQ l * labelProj φE μ * labelProj φQE ν * labelProj φE μ =
      labelProj φQ l * labelProj φE μ * labelProj φQE ν := by
    rw [mul_assoc (labelProj φQ l * labelProj φE μ), ← hνμ.eq, ← mul_assoc,
      mul_assoc (labelProj φQ l) (labelProj φE μ), labelProj_mul_self]
  generalize labelProj φQ l * labelProj φE μ * labelProj φQE ν = P at hP hPQE hPl hνP hPμ
  have hPU : ∀ σ, permOp φQE σ * P * permOp φE σ⁻¹ = P * permOp φQ σ := by
    intro σ
    rw [← (hPQE σ).eq, mul_assoc, permOp_of_eq_mul φQ φE φQE hprod σ, mul_assoc,
      permOp_mul_inv_self, mul_one]
  -- The label projection of `P` under the pair action is `P` itself.
  have hΛP : labelProj (pairAction φQE φE) l *ᵥ vecOfMatrix P = vecOfMatrix P := by
    rw [labelProj, groupAlgebraRep_eq_sum, sum_mulVec]
    simp_rw [smul_mulVec, permOp_pairAction_mulVec, hPU, ← vecOfMatrix_smul,
      ← vecOfMatrix_sum, ← Matrix.mul_smul, ← Finset.mul_sum]
    rw [← groupAlgebraRep_eq_sum, ← labelProj, hPl]
  -- Decompose `P` through the matrix units.
  have hdec : P = ∑ j, ∑ b, matrixUnitOp φQE ν j oν *
      (matrixUnitOp φQE ν oν j * P * matrixUnitOp φE μ b oμ) * matrixUnitOp φE μ oμ b := by
    have hterm : ∀ j b, matrixUnitOp φQE ν j oν *
        (matrixUnitOp φQE ν oν j * P * matrixUnitOp φE μ b oμ) * matrixUnitOp φE μ oμ b =
          matrixUnitOp φQE ν j j * P * matrixUnitOp φE μ b b := by
      intro j b
      rw [← matrixUnitOp_mul_matrixUnitOp_self φQE ν j oν j,
        ← matrixUnitOp_mul_matrixUnitOp_self φE μ b oμ b]
      simp only [mul_assoc]
    simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, sum_matrixUnitOp_diag]
    rw [mul_assoc, hPμ, hνP]
  obtain ⟨j, b, hjb⟩ : ∃ j b,
      labelProj (pairAction φQE φE) l *ᵥ vecOfMatrix (matrixUnitOp φQE ν j oν *
        (matrixUnitOp φQE ν oν j * P * matrixUnitOp φE μ b oμ) * matrixUnitOp φE μ oμ b) ≠ 0 := by
    by_contra! h
    apply hP
    apply vecOfMatrix_injective
    rw [← hΛP, hdec, vecOfMatrix_sum, mulVec_sum]
    refine (Finset.sum_eq_zero fun j _ => ?_).trans (by funext; simp [vecOfMatrix])
    rw [vecOfMatrix_sum, mulVec_sum]
    exact Finset.sum_eq_zero fun b _ => h j b
  set N := matrixUnitOp φQE ν oν j * P * matrixUnitOp φE μ b oμ
  let f : Fin ν.dim × Fin μ.dim → X × X → ℂ := fun pq =>
    vecOfMatrix (matrixUnitOp φQE ν pq.1 oν * N * matrixUnitOp φE μ oμ pq.2)
  set W := Submodule.span ℂ (Set.range f)
  have hWinv : ∀ σ, ∀ y ∈ W, permOp (pairAction φQE φE) σ *ᵥ y ∈ W := by
    intro σ y hy
    refine Submodule.span_induction (fun x hx => ?_) (by simp) (fun x y _ _ hx hy => ?_)
      (fun a x _ hx => ?_) hy
    · obtain ⟨⟨p, q⟩, rfl⟩ := hx
      have key : permOp φQE σ * (matrixUnitOp φQE ν p oν * N * matrixUnitOp φE μ oμ q) *
          permOp φE σ⁻¹ = ∑ p', ∑ q', (IrrepLabel.wedderburnEquiv G (single σ 1) ν p' p *
            IrrepLabel.wedderburnEquiv G (single σ⁻¹ 1) μ q q') •
              (matrixUnitOp φQE ν p' oν * N * matrixUnitOp φE μ oμ q') := by
        have e1 : permOp φQE σ * (matrixUnitOp φQE ν p oν * N * matrixUnitOp φE μ oμ q) *
            permOp φE σ⁻¹ = (permOp φQE σ * matrixUnitOp φQE ν p oν) * N *
              (matrixUnitOp φE μ oμ q * permOp φE σ⁻¹) := by
          simp only [mul_assoc]
        rw [e1, permOp_mul_matrixUnitOp, matrixUnitOp_mul_permOp, Finset.sum_mul,
          Finset.sum_mul]
        refine Finset.sum_congr rfl fun p' _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
      change permOp (pairAction φQE φE) σ *ᵥ
        vecOfMatrix (matrixUnitOp φQE ν p oν * N * matrixUnitOp φE μ oμ q) ∈ W
      rw [permOp_pairAction_mulVec, key, vecOfMatrix_sum]
      refine Submodule.sum_mem _ fun p' _ => ?_
      rw [vecOfMatrix_sum]
      refine Submodule.sum_mem _ fun q' _ => ?_
      rw [vecOfMatrix_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p', q'), rfl⟩)
    · rw [mulVec_add]; exact Submodule.add_mem _ hx hy
    · rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
  set V := Submodule.map (toLin' (labelProj (pairAction φQE φE) l)) W
  have hVinv : ∀ σ, ∀ y ∈ V, permOp (pairAction φQE φE) σ *ᵥ y ∈ V := by
    rintro σ _ ⟨y, hy, rfl⟩
    refine ⟨permOp (pairAction φQE φE) σ *ᵥ y, hWinv σ y hy, ?_⟩
    simp only [toLin'_apply, mulVec_mulVec, (commute_labelProj_permOp (pairAction φQE φE) l σ).eq]
  have hVl : ∀ y ∈ V, labelProj (pairAction φQE φE) l *ᵥ y = y := by
    rintro _ ⟨y, -, rfl⟩
    rw [toLin'_apply, mulVec_mulVec, labelProj_mul_self]
  have hVne : V ≠ ⊥ := by
    intro hbot
    have hmem : labelProj (pairAction φQE φE) l *ᵥ f (j, b) ∈ V :=
      ⟨_, Submodule.subset_span ⟨(j, b), rfl⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hjb hmem
  calc l.dim ≤ finrank ℂ V := dim_le_finrank_of_invariant (pairAction φQE φE) l hVinv hVl hVne
    _ ≤ finrank ℂ W := Submodule.finrank_map_le _ _
    _ ≤ Fintype.card (Fin ν.dim × Fin μ.dim) := finrank_range_le_card f
    _ = ν.dim * μ.dim := by simp

end PermutationRepresentation


namespace TensorPower

open PermutationRepresentation

variable {F : Type*} [Fintype F] [DecidableEq F] {ι : F → Type*} [∀ f, Fintype (ι f)]
  [∀ f, DecidableEq (ι f)] {k : ℕ}

/-- **Lemma 6.1(3), merge dimensions** (`05-replicas.tex`, lines 105–111, equation
`replicas:merge-dimensions`): if `Q, E` are disjoint and their labels `λ, μ` are compatible
with the label `ν` on `QE`, then `d_ν ≤ d_λ d_μ` and `d_λ ≤ d_ν d_μ`. -/
theorem merge_dim_le {Q E : Finset F} (hQE : Disjoint Q E)
    {l μ ν : IrrepLabel (Equiv.Perm (Fin k))}
    (hP : labelProj (subsystemPerm k ι Q) l * labelProj (subsystemPerm k ι E) μ *
      labelProj (subsystemPerm k ι (Q ∪ E)) ν ≠ 0) :
    ν.dim ≤ l.dim * μ.dim ∧ l.dim ≤ ν.dim * μ.dim :=
  ⟨dim_le_mul_dim_of_compatible (commute_subsystemPerm_of_disjoint k ι hQE)
    (subsystemPerm_union k ι hQE) hP,
   dim_le_mul_dim_of_compatible' (commute_subsystemPerm_of_disjoint k ι hQE)
    (subsystemPerm_union k ι hQE) hP⟩

end TensorPower
