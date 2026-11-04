/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import Mathlib.Analysis.Convex.Jensen
import QICLean.Channel.ComplementaryWeylTwirl
import QICLean.Channel.EnvironmentDilation

/-!
# Convex functionals under quantum channels

Wolf, Theorem 5.16 and Equations (5.49)--(5.50), for arbitrary tuples
of complex matrices. No positivity condition is imposed on the tuple components.

`ConvexMatrixFunctional` uses finite coordinate types to express a family defined
in every dimension. Its reindexing conditions identify different bases of the
same dimension. Domain closure accompanies each invariance. Lower-dimensional
membership is explicit in the partial-trace and channel theorems: the source
silently assumes its displayed evaluations are well-defined. In particular,
one-way closure under tensor products does not imply membership of a marginal.
The full-domain corollary has no membership hypotheses.

The channel theorem requires a nonempty input space. This is necessary: the
constant functional which is zero in dimension zero and one in every positive
dimension satisfies the three invariances but increases under the zero channel
from dimension zero to dimension one. The partial-trace theorem allows an empty
retained space, but requires a nonempty environment for its normalized identity.
-/

open scoped Matrix Kronecker ComplexOrder
open Matrix

namespace Matrix

/-- A tuple of square complex matrices with a common coordinate space. -/
abbrev MatrixTuple (ι α : Type) := ι → Matrix α α ℂ

/-- A family of tuple domains indexed by finite-dimensional coordinate spaces. -/
abbrev MatrixTupleDomains (ι : Type) :=
  ∀ (α : Type), [Fintype α] → [DecidableEq α] → Set (MatrixTuple ι α)

/-- Real functionals on matrix tuples in every finite dimension. -/
abbrev MatrixTupleFunctional (ι : Type) :=
  ∀ (α : Type), [Fintype α] → [DecidableEq α] → MatrixTuple ι α → ℝ

/-- Joint convexity and the two invariances in Wolf, Theorem 5.16. Reindexing
identifies coordinate spaces of the same dimension. Each closure field concerns
only domain membership, never an inequality between functional values. -/
structure ConvexMatrixFunctional {ι : Type} (D : MatrixTupleDomains ι)
    (F : MatrixTupleFunctional ι) : Prop where
  /-- Joint convexity, including convexity of the domain. -/
  convex (α : Type) [Fintype α] [DecidableEq α] : ConvexOn ℝ (D α) (F α)
  /-- The domain is closed under simultaneous unitary conjugation. -/
  unitary_mem {α : Type} [Fintype α] [DecidableEq α]
    {A : MatrixTuple ι α} (hA : A ∈ D α) (U : unitaryGroup α ℂ) :
    (fun i => (U : Matrix α α ℂ) * A i * Uᴴ) ∈ D α
  /-- Simultaneous unitary conjugation does not change the functional. -/
  unitary_eq {α : Type} [Fintype α] [DecidableEq α]
    {A : MatrixTuple ι α} (hA : A ∈ D α) (U : unitaryGroup α ℂ) :
    F α (fun i => (U : Matrix α α ℂ) * A i * Uᴴ) = F α A
  /-- Tensoring every component with the same density state stays in the domain. -/
  tensor_mem {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {A : MatrixTuple ι α} (hA : A ∈ D α) {τ : Matrix β β ℂ}
    (hτ : τ.PosSemidef) (htr : τ.trace = 1) :
    (fun i => A i ⊗ₖ τ) ∈ D (α × β)
  /-- Tensoring with a common density state leaves the functional unchanged. -/
  tensor_eq {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {A : MatrixTuple ι α} (hA : A ∈ D α) {τ : Matrix β β ℂ}
    (hτ : τ.PosSemidef) (htr : τ.trace = 1) :
    F (α × β) (fun i => A i ⊗ₖ τ) = F α A
  /-- Changing finite coordinates preserves domain membership. -/
  reindex_mem {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {A : MatrixTuple ι α} (hA : A ∈ D α) (e : α ≃ β) :
    (fun i => reindex e e (A i)) ∈ D β
  /-- Coordinate independence of a dimension-indexed functional. -/
  reindex_eq {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {A : MatrixTuple ι α} (hA : A ∈ D α) (e : α ≃ β) :
    F β (fun i => reindex e e (A i)) = F α A

namespace ConvexMatrixFunctional

variable {ι : Type} {D : MatrixTupleDomains ι} {F : MatrixTupleFunctional ι}
  (hF : ConvexMatrixFunctional D F)

private theorem normalizedIdentity_density {C : Type} [Fintype C] [DecidableEq C]
    [Nonempty C] :
    (((Fintype.card C : ℝ)⁻¹ : ℝ) • (1 : Matrix C C ℂ)).PosSemidef ∧
      (((Fintype.card C : ℝ)⁻¹ : ℝ) • (1 : Matrix C C ℂ)).trace = 1 := by
  refine ⟨PosSemidef.one.smul (by positivity), ?_⟩
  rw [trace_smul, trace_one]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

/-- Wolf, Equation (5.50), in real scalar form on arbitrary finite coordinate
spaces. This is the actual finite Weyl average, componentwise for any tuple. -/
theorem weyl_average_eq_partialTraceRight {S C : Type} [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (e : C ≃ ZMod (Fintype.card C)) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (Fintype.card C))
    (M : Matrix (S × C) (S × C) ℂ) :
    ((Fintype.card C : ℝ) ^ 2)⁻¹ •
        ∑ p : ZMod (Fintype.card C) × ZMod (Fintype.card C),
          ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ p.1 p.2) * M *
            ((1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ p.1 p.2)ᴴ =
      partialTraceRight M ⊗ₖ ((Fintype.card C : ℝ)⁻¹ • (1 : Matrix C C ℂ)) := by
  let : NeZero (Fintype.card C) := ⟨Fintype.card_ne_zero⟩
  rw [Fintype.sum_prod_type, ← Complex.coe_smul, ← Complex.coe_smul]
  simp only [Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast]
  exact sum_kronecker_one_reindexedWeyl_conj e hζ M

include hF

/-- A jointly convex invariant tuple functional decreases under a right partial
trace (Wolf, Theorem 5.16). Membership of the marginal is an explicit
well-definedness assumption, not a consequence of tensor closure. -/
theorem partialTraceRight_le {S C : Type} [Fintype S] [DecidableEq S]
    [Fintype C] [DecidableEq C] [Nonempty C]
    {A : MatrixTuple ι (S × C)} (hA : A ∈ D (S × C))
    (htrA : (fun i => partialTraceRight (A i)) ∈ D S) :
    F S (fun i => partialTraceRight (A i)) ≤ F (S × C) A := by
  classical
  let d := Fintype.card C
  let : NeZero d := ⟨Fintype.card_ne_zero⟩
  let e : C ≃ ZMod d := (Fintype.equivFin C).trans (ZMod.finEquiv d).toEquiv
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)
  have hζ : IsPrimitiveRoot ζ d := Complex.isPrimitiveRoot_exp d (NeZero.ne d)
  let U (p : ZMod d × ZMod d) : unitaryGroup (S × C) ℂ :=
    ⟨(1 : Matrix S S ℂ) ⊗ₖ reindexedWeyl e ζ p.1 p.2,
      kronecker_mem_unitary (Submonoid.one_mem _)
        (reindex_mem_unitaryGroup e.symm _ (weyl_mem_unitary hζ p.1 p.2))⟩
  let w : ZMod d × ZMod d → ℝ := fun _ => ((d : ℝ) ^ 2)⁻¹
  let P (p : ZMod d × ZMod d) : MatrixTuple ι (S × C) :=
    fun i => (U p : Matrix (S × C) (S × C) ℂ) * A i * (U p)ᴴ
  have hw : ∑ p, w p = 1 := by
    simp [w, Fintype.card_prod, ZMod.card, ← sq, d, Fintype.card_ne_zero]
  have havg : (∑ p, w p • P p) =
      (fun i => partialTraceRight (A i) ⊗ₖ ((d : ℝ)⁻¹ • (1 : Matrix C C ℂ))) := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, w, P, ← Finset.smul_sum]
    exact weyl_average_eq_partialTraceRight e hζ (A i)
  have hJ := (hF.convex (S × C)).map_sum_le (t := Finset.univ) (w := w)
    (fun _ _ => by positivity) hw (fun p _ => hF.unitary_mem hA (U p))
  change F (S × C) (∑ p, w p • P p) ≤ ∑ p, w p • F (S × C) (P p) at hJ
  rw [havg, hF.tensor_eq htrA normalizedIdentity_density.1
    normalizedIdentity_density.2] at hJ
  simpa only [P, hF.unitary_eq hA, ← Finset.sum_smul, hw, one_smul] using hJ

end ConvexMatrixFunctional

/-- A rectangular CPTP map has an actual unitary dilation after adjoining a
density state on the output and Kraus factors, then discarding the Kraus and input
factors. The permutations specify all tensor orders. This is Wolf's
Theorem 2.5 in the rectangular form needed for Theorem 5.16. -/
theorem exists_rectangular_unitary_dilation {α β : Type}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
    {T : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hT : IsKrausCPTP T) :
    ∃ (r : ℕ), Nonempty (Fin r) ∧
      ∃ (τ : Matrix (β × Fin r) (β × Fin r) ℂ), τ.PosSemidef ∧ τ.trace = 1 ∧
        ∃ U : unitaryGroup ((β × Fin r) × α) ℂ,
          ∀ X : Matrix α α ℂ,
            T X = partialTraceRight
              (reindex (Equiv.prodAssoc β (Fin r) α) (Equiv.prodAssoc β (Fin r) α)
                ((U : Matrix ((β × Fin r) × α) ((β × Fin r) × α) ℂ) *
                  reindex (Equiv.prodComm α (β × Fin r))
                    (Equiv.prodComm α (β × Fin r)) (X ⊗ₖ τ) * Uᴴ)) := by
  classical
  obtain ⟨r, K, hK, hnorm⟩ := hT
  let V := stinespringV K
  have hV : Vᴴ * V = 1 := by rw [stinespringV_conjTranspose_mul, hnorm]
  have hC : Nonempty (β × Fin r) := by
    by_contra h
    have : IsEmpty (β × Fin r) := not_nonempty_iff.mp h
    have he := congrArg (fun M : Matrix α α ℂ => M (Classical.choice ‹Nonempty α›)
      (Classical.choice ‹Nonempty α›)) hV
    simp [Matrix.mul_apply] at he
  let c₀ : β × Fin r := Classical.choice hC
  let a₀ : α := Classical.choice ‹Nonempty α›
  let E := fixedEnvEmbedding (S := β × Fin r) a₀
  let J := (fixedEnvEmbedding (S := α) c₀).submatrix
    (Equiv.prodComm (β × Fin r) α) id
  have hJ : Jᴴ * J = 1 := by
    rw [conjTranspose_submatrix, submatrix_mul_equiv,
      fixedEnvEmbedding_conjTranspose_mul_self, submatrix_id_id]
  have hEV : (E * V)ᴴ * (E * V) = Jᴴ * J := by
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Eᴴ,
      fixedEnvEmbedding_conjTranspose_mul_self, Matrix.one_mul, hV, hJ]
  obtain ⟨U, hU⟩ := exists_unitary_mul_eq_of_conjTranspose_mul_eq (E * V) J hEV
  let τ : Matrix (β × Fin r) (β × Fin r) ℂ := single c₀ c₀ 1
  have hτ : τ.PosSemidef := by
    have heq : τ = diagonal (fun c => if c = c₀ then (1 : ℂ) else 0) := by
      ext i j
      simp only [τ, Matrix.single, Matrix.of_apply, diagonal_apply]
      split_ifs <;> simp_all [eq_comm]
    rw [heq]
    exact PosSemidef.diagonal (fun c => by split_ifs <;> positivity)
  refine ⟨r, ⟨c₀.2⟩, τ, hτ, trace_single_eq_same _ _, U, fun X => ?_⟩
  have hJX : J * X * Jᴴ =
      reindex (Equiv.prodComm α (β × Fin r)) (Equiv.prodComm α (β × Fin r))
        (X ⊗ₖ τ) := by
    rw [← freshEnvironmentInput_eq_kronecker c₀ X]
    change _ = reindex _ _ (fixedEnvEmbedding c₀ * X * (fixedEnvEmbedding c₀)ᴴ)
    ext i j
    rfl
  have hEX : (E * V) * X * (E * V)ᴴ = (V * X * Vᴴ) ⊗ₖ single a₀ a₀ 1 := by
    rw [← freshEnvironmentInput_eq_kronecker a₀ (V * X * Vᴴ)]
    change _ = E * (V * X * Vᴴ) * Eᴴ
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [← hJX]
  have hsand : (U : Matrix ((β × Fin r) × α) ((β × Fin r) × α) ℂ) *
      (J * X * Jᴴ) * Uᴴ = (E * V) * X * (E * V)ᴴ := by
    rw [hU]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [hsand, hEX, hK X]
  ext i j
  rw [stinespring_schrodinger_representation]
  simp only [partialTraceRight_apply, reindex_apply, submatrix_apply,
    Equiv.prodAssoc_symm_apply, kronecker_apply, Fintype.sum_prod_type]
  simp [Matrix.single, a₀]
  rfl

namespace ConvexMatrixFunctional

variable {ι : Type} {D : MatrixTupleDomains ι} {F : MatrixTupleFunctional ι}

/-- Wolf, Theorem 5.16 and Equation (5.49), for arbitrary rectangular CPTP
maps and arbitrary tuples in a family of domains. The final tuple's membership
expresses the source's well-definedness convention. Positive input dimension is
necessary; no positivity or invertibility assumption is placed on the inputs.

**Local fix (well-definedness and zero dimension):** The domain convention and
the necessary positive-input boundary are documented in
`docs/paper-gaps/wolf_ch5_monotonicity_domains.tex`. -/
theorem map_le (hF : ConvexMatrixFunctional D F) {α β : Type}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
    {T : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hT : IsKrausCPTP T)
    {A : MatrixTuple ι α} (hA : A ∈ D α) (hTA : (fun i => T (A i)) ∈ D β) :
    F β (fun i => T (A i)) ≤ F α A := by
  obtain ⟨r, hr, τ, hτ, htr, U, hU⟩ := exists_rectangular_unitary_dilation hT
  let : Nonempty (Fin r) := hr
  let B : MatrixTuple ι (α × (β × Fin r)) := fun i => A i ⊗ₖ τ
  let e := Equiv.prodComm α (β × Fin r)
  let f := Equiv.prodAssoc β (Fin r) α
  let C : MatrixTuple ι ((β × Fin r) × α) := fun i => reindex e e (B i)
  let M : MatrixTuple ι ((β × Fin r) × α) := fun i =>
    (U : Matrix ((β × Fin r) × α) ((β × Fin r) × α) ℂ) * C i * Uᴴ
  have hB : B ∈ D _ := hF.tensor_mem hA hτ htr
  have hC : C ∈ D _ := hF.reindex_mem hB e
  have hM : M ∈ D _ := hF.unitary_mem hC U
  have hmarg : (fun i => partialTraceRight (reindex f f (M i))) =
      (fun i => T (A i)) := funext fun i => (hU (A i)).symm
  have hle := hF.partialTraceRight_le (hF.reindex_mem hM f) (hmarg ▸ hTA)
  rw [hmarg, hF.reindex_eq hM f, hF.unitary_eq hC U,
    hF.reindex_eq hB e, hF.tensor_eq hA hτ htr] at hle
  exact hle

/-- Full-domain specialization of Wolf, Theorem 5.16. -/
theorem map_le_univ {F : MatrixTupleFunctional ι}
    (hF : ConvexMatrixFunctional (fun _ => Set.univ) F) {α β : Type}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β] [DecidableEq β]
    {T : Matrix α α ℂ →ₗ[ℂ] Matrix β β ℂ} (hT : IsKrausCPTP T)
    (A : MatrixTuple ι α) : F β (fun i => T (A i)) ≤ F α A :=
  hF.map_le hT (Set.mem_univ A) (Set.mem_univ _)

end ConvexMatrixFunctional

end Matrix
