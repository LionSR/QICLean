/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.HighLabelWindow
import QICLean.Representation.UniformBellLabel
import QICLean.Analysis.ReplicaDefect
import QICLean.Representation.SchurSectorMass
import QICLean.Algebra.PiProductTrace

/-!
# The actual initial vector with a common auxiliary label

The initial vector in the OpenAI area-law manuscript,
`07-comparators.tex`, lines 130–147 and 273–281, is the physical tensor
power multiplied by the projection of the literal repeated uniform pair.
Its auxiliary projection leaves the physical mean-energy equation unchanged.
The auxiliary label is selected from a unit bipartite vector using its
actual reduced density. No inverse metric or comparator tree is asserted here.
-/

/-
Original construction of the actual common-label initial vector supporting
OpenAI, A two-dimensional area law from a global spectral gap, September 24, 2026,
07-comparators.tex lines 130–147 and 255–281, comparator:prevector and comparator:high-label.
Independently formalized; no upstream Lean proof text reused.
Provenance-ID: 8753-qic-replica-prevector-01
TensorPower.replicaPrevector
Provenance-ID: 8753-qic-replica-prevector-02
TensorPower.exists_label_sequence_replicaPrevector
-/

open Matrix PermutationRepresentation Module Filter
open scoped BigOperators Matrix Kronecker InnerProductSpace ComplexOrder Matrix.Norms.L2Operator

namespace TensorPower

/-- The literal initial vector with its selected right auxiliary label.
OpenAI area-law manuscript, `07-comparators.tex`, lines 130–147 and 273–281,
`comparator:prevector`. The physical and two auxiliary copy groups are
written in canonical product coordinates. -/
noncomputable def replicaPrevector {A : Type*} [Fintype A]
    (Ω : A → ℂ) (d k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) :
    (Fin k → A) × ((Fin k → Fin d) × (Fin k → Fin d)) → ℂ :=
  fun x => (∏ i, Ω (x.1 i)) *
    (((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ
      labelProj (copyPerm (Fin d) k) l) *ᵥ
        (fun y : (Fin k → Fin d) × (Fin k → Fin d) =>
          ∏ i, omegaVec d (y.1 i, y.2 i))) x.2

private theorem norm_prod_of_unit {A : Type*} [Fintype A]
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (k : ℕ) :
    ‖WithLp.toLp 2 (fun x : Fin k → A => ∏ i, Ω (x i))‖ = 1 := by
  have hself : star Ω ⬝ᵥ Ω = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
    change ⟪WithLp.toLp 2 Ω, WithLp.toLp 2 Ω⟫_ℂ = 1
    simp [hΩ]
  have hprod : star (fun x : Fin k → A => ∏ i, Ω (x i)) ⬝ᵥ
      (fun x => ∏ i, Ω (x i)) = 1 := by
    simp only [dotProduct, Pi.star_apply, star_prod, ← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun (_ : Fin k) (a : A) => star (Ω a) * Ω a)]
    change (∏ _ : Fin k, star Ω ⬝ᵥ Ω) = 1
    simp [hself]
  have hnorm := re_star_dotProduct_self_eq_norm_sq (fun x : Fin k → A => ∏ i, Ω (x i))
  rw [hprod] at hnorm
  change 1 = ‖WithLp.toLp 2 (fun x : Fin k → A => ∏ i, Ω (x i))‖ ^ 2 at hnorm
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun x : Fin k → A => ∏ i, Ω (x i)))]

private theorem norm_product_of_unit {A C : Type*} [Fintype A]
    [Fintype C] (v : A → ℂ) (hv : ‖WithLp.toLp 2 v‖ = 1)
    (w : C → ℂ) :
    ‖WithLp.toLp 2 (fun x : A × C => v x.1 * w x.2)‖ = ‖WithLp.toLp 2 w‖ := by
  classical
  have hself : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp]
    change ⟪WithLp.toLp 2 v, WithLp.toLp 2 v⟫_ℂ = 1
    simp [hv]
  have hprod := star_dotProduct_kronecker_mulVec_prod
    (1 : Matrix A A ℂ) (1 : Matrix C C ℂ) v w
  simp only [one_kronecker_one, one_mulVec, hself, one_mul] at hprod
  have hn := congrArg (RCLike.re : ℂ → ℝ) hprod
  rw [re_star_dotProduct_self_eq_norm_sq, re_star_dotProduct_self_eq_norm_sq] at hn
  change ‖WithLp.toLp 2 (fun x : A × C => v x.1 * w x.2)‖ ^ 2 =
    ‖WithLp.toLp 2 w‖ ^ 2 at hn
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun x : A × C => v x.1 * w x.2)),
    norm_nonneg (WithLp.toLp 2 w)]

private theorem norm_mulVec_projection_le {C : Type*} [Fintype C]
    {P : Matrix C C ℂ} (hP : IsStarProjection P) (w : C → ℂ) :
    ‖WithLp.toLp 2 (P *ᵥ w)‖ ≤ ‖WithLp.toLp 2 w‖ := by
  classical
  have h := l2_opNorm_mulVec P (WithLp.toLp 2 w)
  change ‖WithLp.toLp 2 (P *ᵥ w)‖ ≤ ‖P‖ * ‖WithLp.toLp 2 w‖ at h
  exact h.trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (IsStarProjection.norm_le P hP) (norm_nonneg (WithLp.toLp 2 w)))

private theorem isStarProjection_one_kronecker_label (d k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    IsStarProjection ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ
      labelProj (copyPerm (Fin d) k) l) := by
  rw [isStarProjection_iff', ← mul_kronecker_mul, one_mul, labelProj_mul_self]
  refine ⟨rfl, ?_⟩
  change (_ ⊗ₖ _)ᴴ = _
  rw [conjTranspose_kronecker, conjTranspose_one, (isHermitian_labelProj _ _).eq]

private theorem norm_prod_omegaVec (d k : ℕ) (hd : 0 < d) :
    ‖WithLp.toLp 2 (fun x : (Fin k → Fin d) × (Fin k → Fin d) =>
      ∏ i, omegaVec d (x.1 i, x.2 i))‖ = 1 := by
  have hn := norm_sq_one_kronecker_mulVec_prod_omegaVec d k 1 (by simp [isStarProjection_iff'])
  simp only [one_kronecker_one, one_mulVec, trace_one, Fintype.card_fun,
    Fintype.card_fin, Complex.natCast_re] at hn
  rw [Nat.cast_pow, div_self (pow_ne_zero k (Nat.cast_ne_zero.mpr hd.ne'))] at hn
  nlinarith [norm_nonneg (WithLp.toLp 2
    (fun x : (Fin k → Fin d) × (Fin k → Fin d) => ∏ i, omegaVec d (x.1 i, x.2 i)))]

private theorem kronecker_mulVec_product {A C : Type*} [Fintype A] [Fintype C]
    (M : Matrix A A ℂ) (N : Matrix C C ℂ) (v : A → ℂ) (w : C → ℂ) :
    (M ⊗ₖ N) *ᵥ (fun x : A × C => v x.1 * w x.2) =
      fun x : A × C => (M *ᵥ v) x.1 * (N *ᵥ w) x.2 := by
  ext x
  simp only [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  ring

private theorem one_kronecker_mulVec {A C : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] (N : Matrix C C ℂ) (v : A × C → ℂ) (x : A × C) :
    (((1 : Matrix A A ℂ) ⊗ₖ N) *ᵥ v) x = (N *ᵥ fun c => v (x.1, c)) x.2 := by
  simp [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
    one_apply, ite_mul, Finset.sum_ite_eq]

private theorem kronecker_one_mulVec {A C : Type*} [Fintype A]
    [Fintype C] [DecidableEq C] (M : Matrix A A ℂ) (v : A × C → ℂ) (x : A × C) :
    ((M ⊗ₖ (1 : Matrix C C ℂ)) *ᵥ v) x = (M *ᵥ fun a => v (a, x.2)) x.1 := by
  simp [mulVec, dotProduct, kroneckerMap_apply, Fintype.sum_prod_type,
    one_apply, mul_ite, Finset.sum_ite_eq]

private theorem kronecker_permOp_mulVec {A C : Type*} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] {G : Type*} [Group G]
    (φ : G →* Equiv.Perm A) (γ : G →* Equiv.Perm C) (σ : G) (v : A × C → ℂ) :
    (permOp φ σ ⊗ₖ permOp γ σ) *ᵥ v =
      fun x => v ((φ σ)⁻¹ x.1, (γ σ)⁻¹ x.2) := by
  rw [show permOp φ σ ⊗ₖ permOp γ σ =
    (permOp φ σ ⊗ₖ (1 : Matrix C C ℂ)) *
      ((1 : Matrix A A ℂ) ⊗ₖ permOp γ σ) by
        rw [← mul_kronecker_mul, mul_one, one_mul], ← mulVec_mulVec]
  ext x
  rw [kronecker_one_mulVec, permOp_mulVec]
  change (((1 : Matrix A A ℂ) ⊗ₖ permOp γ σ) *ᵥ v) ((φ σ)⁻¹ x.1, x.2) = _
  rw [one_kronecker_mulVec, permOp_mulVec]
  rfl

private theorem prod_copyPerm_fixed {A : Type*} [Fintype A] [DecidableEq A]
    (Ω : A → ℂ) (k : ℕ) (σ : Equiv.Perm (Fin k)) :
    permOp (copyPerm A k) σ *ᵥ (fun x : Fin k → A => ∏ i, Ω (x i)) =
      (fun x : Fin k → A => ∏ i, Ω (x i)) := by
  rw [permOp_mulVec]
  ext x
  change (∏ i, Ω (x (σ i))) = ∏ i, Ω (x i)
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

private theorem prod_omegaVec_copyPerm_fixed (d k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (permOp (copyPerm (Fin d) k) σ ⊗ₖ permOp (copyPerm (Fin d) k) σ) *ᵥ
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) =>
        ∏ i, omegaVec d (x.1 i, x.2 i)) =
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) =>
        ∏ i, omegaVec d (x.1 i, x.2 i)) := by
  rw [kronecker_permOp_mulVec]
  ext x
  change (∏ i, omegaVec d (x.1 (σ i), x.2 (σ i))) =
    ∏ i, omegaVec d (x.1 i, x.2 i)
  exact Fintype.prod_equiv σ _ _ (fun _ => rfl)

private theorem projected_prod_omegaVec_fixed (d k : ℕ)
    (l : IrrepLabel (Equiv.Perm (Fin k))) :
    let P := labelProj (copyPerm (Fin d) k) l
    let w := ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ
      (fun x : (Fin k → Fin d) × (Fin k → Fin d) =>
        ∏ i, omegaVec d (x.1 i, x.2 i))
    (P ⊗ₖ (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) *ᵥ w = w ∧
    ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ w = w ∧
    ∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm (Fin d) k) σ ⊗ₖ permOp (copyPerm (Fin d) k) σ) *ᵥ w = w := by
  intro P w
  have hright : ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ w = w := by
    dsimp only [w, P]
    rw [mulVec_mulVec, ← mul_kronecker_mul, one_mul, labelProj_mul_self]
  have hleft : (P ⊗ₖ (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) *ᵥ w = w := by
    dsimp only [w]
    rw [mulVec_mulVec,
      show (P ⊗ₖ (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ)) * (1 ⊗ₖ P) =
        (1 ⊗ₖ P) * (P ⊗ₖ 1) by simp only [← mul_kronecker_mul, one_mul, mul_one],
      ← mulVec_mulVec]
    rw [labelProj_kronecker_mulVec_prod_omegaVec]
    exact hright
  refine ⟨hleft, hright, ?_⟩
  intro σ
  have hc : Commute
      (permOp (copyPerm (Fin d) k) σ ⊗ₖ permOp (copyPerm (Fin d) k) σ)
      ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) := by
    change _ * _ = _ * _
    simp only [← mul_kronecker_mul, one_mul, mul_one]
    exact congrArg (fun M => permOp (copyPerm (Fin d) k) σ ⊗ₖ M)
      (commute_labelProj_permOp _ l σ).eq.symm
  dsimp only [w]
  rw [mulVec_mulVec, hc.eq, ← mulVec_mulVec, prod_omegaVec_copyPerm_fixed]

private theorem replicaPrevector_properties {A : Type*} [Fintype A] [DecidableEq A]
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1) (H : Matrix A A ℂ) (E₀ : ℝ)
    (hE : H *ᵥ Ω = (E₀ : ℂ) • Ω) (d k : ℕ) (hd : 0 < d) (hk : 0 < k)
    (l : IrrepLabel (Equiv.Perm (Fin k)))
    (hPne : labelProj (copyPerm (Fin d) k) l ≠ 0) :
    let v := replicaPrevector Ω d k l
    let P := labelProj (copyPerm (Fin d) k) l
    WithLp.toLp 2 v ≠ 0 ∧ ‖WithLp.toLp 2 v‖ ≤ 1 ∧
    (((k : ℝ)⁻¹ • replicaHamiltonian H k) ⊗ₖ
      (1 : Matrix ((Fin k → Fin d) × (Fin k → Fin d))
        ((Fin k → Fin d) × (Fin k → Fin d)) ℂ)) *ᵥ v = (E₀ : ℂ) • v ∧
    ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      (P ⊗ₖ (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ))) *ᵥ v = v ∧
    ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
      ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P)) *ᵥ v = v ∧
    (∀ σ : Equiv.Perm (Fin k),
      (permOp (copyPerm A k) σ ⊗ₖ
        (permOp (copyPerm (Fin d) k) σ ⊗ₖ permOp (copyPerm (Fin d) k) σ)) *ᵥ v = v) := by
  classical
  let P := labelProj (copyPerm (Fin d) k) l
  let u : (Fin k → Fin d) × (Fin k → Fin d) → ℂ :=
    fun x => ∏ i, omegaVec d (x.1 i, x.2 i)
  let w := ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P) *ᵥ u
  have hwne : WithLp.toLp 2 w ≠ 0 :=
    (one_kronecker_mulVec_prod_omegaVec_ne_zero_iff d k hd P).mpr hPne
  have hn : ‖WithLp.toLp 2 (replicaPrevector Ω d k l)‖ = ‖WithLp.toLp 2 w‖ :=
    norm_product_of_unit _ (norm_prod_of_unit Ω hΩ k) w
  have hvne : WithLp.toLp 2 (replicaPrevector Ω d k l) ≠ 0 := by
    intro hz
    have hn0 : ‖WithLp.toLp 2 w‖ = 0 := by rw [← hn, hz, norm_zero]
    exact hwne (norm_eq_zero.mp hn0)
  have hvnorm : ‖WithLp.toLp 2 (replicaPrevector Ω d k l)‖ ≤ 1 := by
    rw [hn]
    exact (norm_mulVec_projection_le (isStarProjection_one_kronecker_label d k l) u).trans_eq
      (norm_prod_omegaVec d k hd)
  obtain ⟨hleft, hright, hsym⟩ := projected_prod_omegaVec_fixed d k l
  refine ⟨hvne, hvnorm,
    replicaMeanHamiltonian_kronecker_mulVec_prod hE hk w, ?_, ?_, ?_⟩
  · change ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ (P ⊗ₖ 1)) *ᵥ
      (fun x => (∏ i, Ω (x.1 i)) * w x.2) = _
    rw [kronecker_mulVec_product _ _ (fun x : Fin k → A => ∏ i, Ω (x i)) w, one_mulVec, hleft]
    rfl
  · change ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ (1 ⊗ₖ P)) *ᵥ
      (fun x => (∏ i, Ω (x.1 i)) * w x.2) = _
    rw [kronecker_mulVec_product _ _ (fun x : Fin k → A => ∏ i, Ω (x i)) w, one_mulVec, hright]
    rfl
  · intro σ
    change (permOp (copyPerm A k) σ ⊗ₖ
      (permOp (copyPerm (Fin d) k) σ ⊗ₖ permOp (copyPerm (Fin d) k) σ)) *ᵥ
      (fun x => (∏ i, Ω (x.1 i)) * w x.2) = _
    rw [kronecker_mulVec_product _ _ (fun x : Fin k → A => ∏ i, Ω (x i)) w,
      prod_copyPerm_fixed, hsym]
    rfl

/-- The initial vector is constructed with the very same sequence selected
from the actual reduced density of the unit bipartite vector. For every
positive copy number it is nonzero, has norm at most one, has both auxiliary
labels, is invariant
under simultaneous copy permutations, and has the one-copy physical energy.
The selected bipartite tensor powers retain inverse polynomial mass, and
the common label has logarithmic dimension `k S(ρ) + o(k)`.
OpenAI area-law manuscript, `07-comparators.tex`, lines 130–147 and 255–281,
`comparator:prevector` and `comparator:high-label`. This is the initial-vector
construction; no comparator or inverse-metric assertion is included. -/
theorem exists_label_sequence_replicaPrevector {A S : Type*}
    [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S] {d : ℕ}
    (Ω : A → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
    (ψ : S × Fin d → ℂ) (hψ : ‖WithLp.toLp 2 ψ‖ = 1)
    (H : Matrix A A ℂ) (E₀ : ℝ) (hE : H *ᵥ Ω = (E₀ : ℂ) • Ω) :
    ∃ l : (k : ℕ) → IrrepLabel (Equiv.Perm (Fin k)),
      (∀ k : ℕ, 0 < k →
        let v := replicaPrevector Ω d k (l k)
        let P := labelProj (copyPerm (Fin d) k) (l k)
        WithLp.toLp 2 v ≠ 0 ∧ ‖WithLp.toLp 2 v‖ ≤ 1 ∧
        (((k : ℝ)⁻¹ • replicaHamiltonian H k) ⊗ₖ
          (1 : Matrix ((Fin k → Fin d) × (Fin k → Fin d))
            ((Fin k → Fin d) × (Fin k → Fin d)) ℂ)) *ᵥ v = (E₀ : ℂ) • v ∧
        ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
          (P ⊗ₖ (1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ))) *ᵥ v = v ∧
        ((1 : Matrix (Fin k → A) (Fin k → A) ℂ) ⊗ₖ
          ((1 : Matrix (Fin k → Fin d) (Fin k → Fin d) ℂ) ⊗ₖ P)) *ᵥ v = v ∧
        (∀ σ : Equiv.Perm (Fin k),
          (permOp (copyPerm A k) σ ⊗ₖ
            (permOp (copyPerm (Fin d) k) σ ⊗ₖ permOp (copyPerm (Fin d) k) σ)) *ᵥ v = v)) ∧
      (∀ᶠ k : ℕ in atTop,
        (2 * (((k + 1) ^ (d ^ 2) : ℕ) : ℝ))⁻¹ ≤
          ‖WithLp.toLp 2
            (((1 : Matrix (Fin k → S) (Fin k → S) ℂ) ⊗ₖ
              labelProj (copyPerm (Fin d) k) (l k)) *ᵥ
              (fun x : (Fin k → S) × (Fin k → Fin d) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2) ∧
      Asymptotics.IsLittleO atTop
        (fun k : ℕ => Real.log (l k).dim - (k : ℝ) *
          vonNeumannEntropy (partialTraceLeft (vecMulVec ψ (star ψ)))
            (posSemidef_vecMulVec_self_star ψ).partialTraceLeft.isHermitian)
        (fun k : ℕ => (k : ℝ)) := by
  classical
  have hd : 0 < d := by
    by_contra h
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h
    subst d
    have hz : WithLp.toLp 2 ψ = 0 := Subsingleton.elim _ _
    rw [hz, norm_zero] at hψ
    exact zero_ne_one hψ
  let ρ := partialTraceLeft (vecMulVec ψ (star ψ))
  have hρ : ρ.PosSemidef := (posSemidef_vecMulVec_self_star ψ).partialTraceLeft
  have htr : ρ.trace = 1 := by
    rw [trace_partialTraceLeft, trace_vecMulVec, ← EuclideanSpace.inner_toLp_toLp]
    simp [hψ]
  let mass (k : ℕ) (l : IrrepLabel (Equiv.Perm (Fin k))) : ℝ :=
    ‖WithLp.toLp 2
      (((1 : Matrix (Fin k → S) (Fin k → S) ℂ) ⊗ₖ labelProj (copyPerm (Fin d) k) l) *ᵥ
        (fun x : (Fin k → S) × (Fin k → Fin d) => ∏ i, ψ (x.1 i, x.2 i)))‖ ^ 2
  have hex (k : ℕ) : ∃ l : IrrepLabel (Equiv.Perm (Fin k)), 0 < mass k l := by
    have hρk := finKronecker_posSemidef (fun _ : Fin k => ρ) (fun _ => hρ)
    have htrk : (finKronecker (fun _ : Fin k => ρ)).trace = 1 := by
      change Matrix.trace (fun x y : Fin k → Fin d => ∏ i, ρ (x i) (y i)) = 1
      rw [trace_piProduct (fun _ : Fin k => ρ)]
      simp [htr]
    obtain ⟨l, hl⟩ := exists_labelProj_trace_mass_ge (Fin d) k _ hρk htrk
    have hP : IsStarProjection (labelProj (copyPerm (Fin d) k) l) := by
      rw [isStarProjection_iff']
      exact ⟨labelProj_mul_self _ _, (isHermitian_labelProj _ _).isSelfAdjoint⟩
    refine ⟨l, ?_⟩
    dsimp only [mass]
    rw [norm_sq_one_kronecker_mulVec_prod ψ k _ hP]
    exact lt_of_lt_of_le (by positivity) hl
  obtain ⟨l₀, hmass, hdim⟩ := exists_label_sequence_pure_norm_entropy_asymptotic ψ hψ
  simp only [Fintype.card_fin] at hmass
  have hchoice : ∀ k, ∃ l, 0 < mass k l ∧ (0 < mass k (l₀ k) → l = l₀ k) := by
    intro k
    by_cases hk : 0 < mass k (l₀ k)
    · exact ⟨l₀ k, hk, fun _ => rfl⟩
    · exact ⟨(hex k).choose, (hex k).choose_spec, fun h => False.elim (hk h)⟩
  choose l hl using hchoice
  have hsame : ∀ᶠ k : ℕ in atTop, l₀ k = l k := hmass.mono fun k hk =>
    ((hl k).2 (lt_of_lt_of_le (by positivity) hk)).symm
  refine ⟨l, ?_, ?_, hdim.congr'
    (hsame.mono (fun k hk => by dsimp only; rw [hk])) Filter.EventuallyEq.rfl⟩
  · intro k hk
    apply replicaPrevector_properties Ω hΩ H E₀ hE d k hd hk
    intro hz
    have hpos := (hl k).1
    simp only [mass, hz, kronecker_zero, zero_mulVec, WithLp.toLp_zero, norm_zero,
      zero_pow (by norm_num : 2 ≠ 0)] at hpos
    exact lt_irrefl 0 hpos
  · filter_upwards [hmass, hsame] with k hk hs
    rw [← hs]
    exact hk

end TensorPower
