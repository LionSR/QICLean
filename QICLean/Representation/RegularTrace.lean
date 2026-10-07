/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Representation.Branching

/-!
# Traces of permutation representations and the character projection

For a permutation representation `ρ` of a finite group `G` with multiplicities `m_λ`,
`tr ρ(a) = ∑_λ m_λ tr W_λ(a)`, where `W_λ(a)` is the `λ` block of `a`. Applied to the regular
representation, whose multiplicities are the dimensions `d_λ`, this gives the coefficients
of the central idempotents, `|G| e_λ(g) = d_λ tr W_λ(g⁻¹)`, and hence the character
projection `∑_g tr ρ(g⁻¹) g = ∑_λ (|G| m_λ / d_λ) e_λ`.

This is the central-idempotent formula
`π^λ = (d_λ/k!) ∑_π χ_λ(π⁻¹) U(π)` of the area-law paper (*A two-dimensional area law from a
global spectral gap*, `05-replicas.tex`, lines 164–169), used here to compute the
multiplicities of the Schur labels.

## Main declarations

* `PermutationRepresentation.trace_groupAlgebraRep`.
* `PermutationRepresentation.multiplicity_regular` — `m_λ = d_λ` for the regular
  representation.
* `IrrepLabel.card_mul_coeff_centralIdem` — `|G| e_λ(g) = d_λ tr W_λ(g⁻¹)`.
* `PermutationRepresentation.characterSum_eq` — the character projection.
-/

open Finset Matrix PermutationRepresentation MonoidAlgebra

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
  (φ : G →* Equiv.Perm X)

/-- `tr ρ(a) = ∑_λ tr W_λ(a) m_λ`. -/
theorem trace_groupAlgebraRep (a : MonoidAlgebra ℂ G) :
    (groupAlgebraRep φ a).trace =
      ∑ l, (IrrepLabel.block l a).trace * multiplicity φ l := by
  have h1 : (groupAlgebraRep φ a).trace = ∑ l, (groupAlgebraRep φ a * labelProj φ l).trace := by
    rw [← trace_sum, ← mul_sum, sum_labelProj, mul_one]
  rw [h1]
  refine sum_congr rfl fun l _ => ?_
  have h := trace_mul_groupAlgebraRep_mul_labelProj φ (M := 1) (fun g => Commute.one_right _) a l
  simp only [one_mul] at h
  rw [trace_labelProj] at h
  have hl : (l.dim : ℂ) ≠ 0 := by exact_mod_cast l.dim_pos.ne'
  apply mul_left_cancel₀ hl
  rw [h]
  push_cast
  ring

variable (G) in
/-- The regular permutation representation `g • x = g x`. -/
abbrev regular : G →* Equiv.Perm G := MulAction.toPermHom G G

theorem groupAlgebraRep_regular_apply [DecidableEq G] (a : MonoidAlgebra ℂ G) (x y : G) :
    groupAlgebraRep (regular G) a x y = a.coeff (x * y⁻¹) := by
  rw [groupAlgebraRep_eq_sum, Matrix.sum_apply, sum_eq_single (x * y⁻¹)]
  · have e : (regular G (x * y⁻¹)) y = x := by simp [regular]
    rw [Matrix.smul_apply, permOp_apply_apply, ite_eq_left e, smul_eq_mul, mul_one]
  · intro g _ hg
    have : (regular G g) y ≠ x := fun h => hg (by simp [regular] at h; simp [← h])
    rw [Matrix.smul_apply, permOp_apply_apply, ite_eq_right this, smul_zero]
  · simp

theorem trace_groupAlgebraRep_regular [DecidableEq G] (a : MonoidAlgebra ℂ G) :
    (groupAlgebraRep (regular G) a).trace = Fintype.card G * a.coeff 1 := by
  simp [Matrix.trace, groupAlgebraRep_regular_apply]

/-- The coordinates of an element of `ℂ[G]`. -/
noncomputable def coordEquiv : MonoidAlgebra ℂ G ≃ₗ[ℂ] (G → ℂ) :=
  (coeffLinearEquiv ℂ).trans (Finsupp.linearEquivFunOnFinite ℂ ℂ G)

theorem coordEquiv_apply (a : MonoidAlgebra ℂ G) (g : G) : coordEquiv a g = a.coeff g := rfl

theorem groupAlgebraRep_regular_mulVec [DecidableEq G] (b : MonoidAlgebra ℂ G) (v : G → ℂ) :
    groupAlgebraRep (regular G) b *ᵥ v = coordEquiv (b * coordEquiv.symm v) := by
  funext x
  rw [coordEquiv_apply]
  have hv : coordEquiv.symm v = ∑ y, single y (v y) := by
    apply coordEquiv.injective
    funext g
    rw [LinearEquiv.apply_symm_apply, coordEquiv_apply, coeff_sum, Finset.sum_apply',
      sum_eq_single g]
    · simp [coeff_single]
    · intro h _ hh; simp [coeff_single, Finsupp.single_apply, hh]
    · simp
  rw [hv, mul_sum, coeff_sum, Finset.sum_apply']
  simp only [mulVec, dotProduct, groupAlgebraRep_regular_apply]
  refine sum_congr rfl fun y _ => ?_
  rw [coeff_mul_single_apply]

/-- The multiplicity of every label in the regular representation is its dimension. -/
theorem multiplicity_regular [DecidableEq G] (l : IrrepLabel G) :
    multiplicity (regular G) l = l.dim := by
  set o : Fin l.dim := ⟨0, l.dim_pos⟩
  set e := IrrepLabel.matrixUnit l o o
  set P : (Π μ : IrrepLabel G, Matrix (Fin μ.dim) (Fin μ.dim) ℂ) := Pi.single l (Matrix.single o o 1)
  -- the range of `ρ(e)` is the left ideal `e ℂ[G]`
  have h1 : LinearMap.range (toLin' (matrixUnitOp (regular G) l o o)) =
      (LinearMap.range (LinearMap.mulLeft ℂ e)).map
        (coordEquiv : MonoidAlgebra ℂ G ≃ₗ[ℂ] (G → ℂ)).toLinearMap := by
    ext x
    simp only [LinearMap.mem_range, toLin'_apply, Submodule.mem_map, exists_exists_eq_and,
      LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨coordEquiv.symm v, (groupAlgebraRep_regular_mulVec e v).symm⟩
    · rintro ⟨w, rfl⟩
      refine ⟨coordEquiv w, ?_⟩
      rw [matrixUnitOp, groupAlgebraRep_regular_mulVec, LinearEquiv.symm_apply_apply]
      rfl
  -- through the Artin–Wedderburn isomorphism
  have h2 : (LinearMap.range (LinearMap.mulLeft ℂ e)).map
      (IrrepLabel.wedderburnEquiv G).toLinearEquiv.toLinearMap =
      LinearMap.range (LinearMap.mulLeft ℂ P) := by
    ext f
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearMap.mulLeft_apply,
      exists_exists_eq_and, AlgEquiv.toLinearEquiv_toLinearMap, AlgEquiv.toLinearMap_apply]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨IrrepLabel.wedderburnEquiv G w, by simp [e, P]⟩
    · rintro ⟨g, rfl⟩
      refine ⟨(IrrepLabel.wedderburnEquiv G).symm g, by simp [e, P]⟩
  -- the left ideal generated by `P` is the first row of the `λ` factor
  let L : (Fin l.dim → ℂ) →ₗ[ℂ] (Π μ : IrrepLabel G, Matrix (Fin μ.dim) (Fin μ.dim) ℂ) :=
    { toFun := fun c => Pi.single l (Matrix.of fun i j => if i = o then c j else 0)
      map_add' := fun c c' => by
        rw [← Pi.single_add]; congr 1; ext i j; simp only [Matrix.of_apply, Matrix.add_apply]
        split_ifs <;> simp
      map_smul' := fun z c => by
        rw [RingHom.id_apply, ← Pi.single_smul]; congr 1; ext i j
        simp only [Matrix.of_apply, Matrix.smul_apply]; split_ifs <;> simp }
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    funext j
    have := congrFun (congrFun (congrFun hc l) o) j
    simpa [L] using this
  have h3 : LinearMap.range (LinearMap.mulLeft ℂ P) = LinearMap.range L := by
    ext f
    simp only [LinearMap.mem_range, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨fun j => g l o j, ?_⟩
      funext μ
      by_cases hμ : μ = l
      · subst hμ
        ext i j
        simp only [L, P, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply, Pi.single_eq_same,
          Matrix.mul_apply, Matrix.single, Matrix.of_apply]
        rw [sum_eq_single o]
        · by_cases hi : i = o <;> simp [hi, eq_comm]
        · intro b _ hb; simp [Ne.symm hb]
        · simp
      · simp [L, P, hμ]
    · rintro ⟨c, rfl⟩
      refine ⟨L c, ?_⟩
      funext μ
      by_cases hμ : μ = l
      · subst hμ
        ext i j
        simp only [L, P, LinearMap.coe_mk, AddHom.coe_mk, Pi.mul_apply, Pi.single_eq_same,
          Matrix.mul_apply, Matrix.single, Matrix.of_apply]
        rw [sum_eq_single o]
        · by_cases hi : i = o <;> simp [hi, eq_comm]
        · intro b _ hb; simp [hb]
        · simp
      · simp [L, P, hμ]
  rw [multiplicity, h1, LinearEquiv.finrank_map_eq,
    ← LinearEquiv.finrank_map_eq (IrrepLabel.wedderburnEquiv G).toLinearEquiv, h2, h3,
    LinearMap.finrank_range_of_inj hL, Module.finrank_fin_fun]

end PermutationRepresentation

namespace IrrepLabel

variable {G : Type*} [Group G] [Fintype G]

theorem block_centralIdem_mul (l μ : IrrepLabel G) (a : MonoidAlgebra ℂ G) :
    block μ (centralIdem l * a) = if μ = l then block μ a else 0 := by
  simp only [block, map_mul, wedderburnEquiv_centralIdem, Pi.mul_apply]
  split_ifs with h
  · subst h; simp
  · simp [h]

/-- `|G| e_λ(g) = d_λ tr W_λ(g⁻¹)`. -/
theorem card_mul_coeff_centralIdem [DecidableEq G] (l : IrrepLabel G) (g : G) :
    (Fintype.card G : ℂ) * (centralIdem l).coeff g = l.dim * (block l (single g⁻¹ 1)).trace := by
  have h := trace_groupAlgebraRep (regular G) (centralIdem l * single g⁻¹ 1)
  rw [trace_groupAlgebraRep_regular, coeff_mul_single_apply, one_mul, inv_inv, mul_one] at h
  rw [h, sum_eq_single l]
  · rw [block_centralIdem_mul, ite_eq_left rfl, multiplicity_regular, mul_comm]
  · intro μ _ hμ
    rw [block_centralIdem_mul, ite_eq_right hμ, trace_zero, zero_mul]
  · simp

end IrrepLabel

namespace PermutationRepresentation

variable {G X : Type*} [Group G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]
  (φ : G →* Equiv.Perm X)

/-- **Character projection** (`05-replicas.tex`, lines 164–169):
`∑_g tr ρ(g⁻¹) g = ∑_λ (|G| m_λ / d_λ) e_λ`. -/
theorem characterSum_eq :
    ∑ g, (groupAlgebraRep φ (single g⁻¹ 1)).trace • single g (1 : ℂ) =
      ∑ l, ((Fintype.card G : ℂ) * multiplicity φ l / l.dim) • IrrepLabel.centralIdem l := by
  apply coeff_injective
  ext g
  simp only [coeff_sum, coeff_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul]
  rw [sum_eq_single g]
  · rw [coeff_single, Finsupp.single_eq_same, mul_one, trace_groupAlgebraRep]
    refine sum_congr rfl fun l _ => ?_
    have h := IrrepLabel.card_mul_coeff_centralIdem l g
    have hl : (l.dim : ℂ) ≠ 0 := by exact_mod_cast l.dim_pos.ne'
    field_simp
    linear_combination -(multiplicity φ l : ℂ) * h
  · intro h _ hh
    simp [coeff_single, hh]
  · simp

end PermutationRepresentation
