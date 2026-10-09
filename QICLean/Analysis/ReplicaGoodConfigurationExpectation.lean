/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodAuxiliaryLabelBound
import QICLean.Analysis.ReplicaGoodConfigurationDensity
import QICLean.Representation.GroupedConfigurationTransport
import QICLean.Representation.CompatiblePhysicalLabel

/-!
# Good-copy expectations in the actual five-factor density

Splitting all copies into the same good and bad groups yields the actual
five-factor good density. The apparent difference in the traced coordinates
is precisely the existing five-factor equivalence on the bad copies,
followed by the enumeration of the excited physical subset. Only the traced
coordinates are changed; every good middle physical coordinate is retained.

Consequently an arbitrary finite real linear combination of actual
good-subgroup label entropies has exactly the same exponential expectation
in the original excitation component and in the actual good density.
No normalization, symmetry, commutation between the regions, or supplied
density identification is needed.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `07-comparators.tex`, lines 454--560,
`comparator:whole-inverse` and `comparator:merge-moments`, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Matrix Kronecker Matrix.Norms.L2Operator

namespace TensorPower

/-- Identify bad five-factor configurations with the traced coordinates
in the actual good density. Only the bad physical copies change from the
chosen finite enumeration to the literal excited subset.
Source: `07-comparators.tex`, lines 520--549. -/
def badConfigurationTraceEquiv (ι : Fin 5 → Type*) {k : ℕ} (B : Finset (Fin k)) :
    Config B.card ι ≃ (↥B → ι 0 × (ι 1 × ι 2)) ×
      ((Fin B.card → ι 3) × (Fin B.card → ι 4)) :=
  (fiveFactorCopiesEquiv ι B.card).trans
    ((Equiv.arrowCongr B.equivFin.symm (Equiv.refl (ι 0 × (ι 1 × ι 2)))).prodCongr
      (Equiv.refl ((Fin B.card → ι 3) × (Fin B.card → ι 4))))

private theorem groupedConfigurationEquiv_reconstruct
    (ι : Fin 5 → Type*) {k : ℕ} (B : Finset (Fin k))
    (x : Config Bᶜ.card ι) (y : Config B.card ι) :
    let e := Matrix.replicaGoodBadSplit B
    let g := fiveFactorCopiesEquiv ι Bᶜ.card x
    let b := badConfigurationTraceEquiv ι B y
    fiveFactorCopiesEquiv ι k ((groupedConfigurationEquiv ι e).symm (x, y)) =
      ((FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).symm
        (b.1, fun i => g.1 ((Finset.equivFin Bᶜ) i)),
        ((goodBadCopiesEquiv (ι 3) B).symm (g.2.1, b.2.1),
          (goodBadCopiesEquiv (ι 4) B).symm (g.2.2, b.2.2))) := by
  intro e g b
  let z := (groupedConfigurationEquiv ι e).symm (x, y)
  have hg (j : Fin Bᶜ.card) : z (e (Sum.inl j)) = x j := by
    change Sum.elim x y (e.symm (e (Sum.inl j))) = x j
    rw [Equiv.symm_apply_apply]
    rfl
  have hb (j : Fin B.card) : z (e (Sum.inr j)) = y j := by
    change Sum.elim x y (e.symm (e (Sum.inr j))) = y j
    rw [Equiv.symm_apply_apply]
    rfl
  have hgi (i : ↥(Bᶜ)) : z i = x (Bᶜ.equivFin i) := by
    have hi : (i : Fin k) = e (Sum.inl (Bᶜ.equivFin i)) := by
      change (i : Fin k) = (Bᶜ.equivFin.symm (Bᶜ.equivFin i)).val
      rw [Equiv.symm_apply_apply]
    rw [hi, hg]
  have hbi (i : ↥B) : z i = y (B.equivFin i) := by
    have hi : (i : Fin k) = e (Sum.inr (B.equivFin i)) := by
      change (i : Fin k) = (B.equivFin.symm (B.equivFin i)).val
      rw [Equiv.symm_apply_apply]
    rw [hi, hb]
  apply Prod.ext
  · apply (FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).injective
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · funext i
      change (z i 0, (z i 1, z i 2)) =
        (y (B.equivFin i) 0, (y (B.equivFin i) 1, y (B.equivFin i) 2))
      exact congrArg (fun t : (f : Fin 5) → ι f => (t 0, (t 1, t 2))) (hbi i)
    · funext i
      change (z i 0, (z i 1, z i 2)) =
        (x (Bᶜ.equivFin i) 0, (x (Bᶜ.equivFin i) 1, x (Bᶜ.equivFin i) 2))
      exact congrArg (fun t : (f : Fin 5) → ι f => (t 0, (t 1, t 2))) (hgi i)
  · apply Prod.ext
    · apply (goodBadCopiesEquiv (ι 3) B).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · funext j
        change z (e (Sum.inl j)) 3 = x j 3
        exact congrFun (hg j) 3
      · funext j
        change z (e (Sum.inr j)) 3 = y j 3
        exact congrFun (hb j) 3
    · apply (goodBadCopiesEquiv (ι 4) B).injective
      rw [Equiv.apply_symm_apply]
      apply Prod.ext
      · funext j
        change z (e (Sum.inl j)) 4 = x j 4
        exact congrFun (hg j) 4
      · funext j
        change z (e (Sum.inr j)) 4 = y j 4
        exact congrFun (hb j) 4

end TensorPower

namespace Matrix

open TensorPower

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]

local instance replicaGoodConfigurationExpectation_decidableEqConfig (k : ℕ) :
    DecidableEq (Config k ι) := Fintype.decidablePiFintype

/-- Splitting all copies by the actual good/bad enumeration and tracing
the bad five-factor configurations gives the existing good density.
Source: `07-comparators.tex`, lines 520--549. -/
theorem replicaGoodConfigurationMarginal_eq_grouped_partialTrace
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ) :
    let e := replicaGoodBadSplit B
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let f := (w ∘ fiveFactorCopiesEquiv ι k) ∘ (groupedConfigurationEquiv ι e).symm
    replicaGoodConfigurationMarginal ι Ω k B u = partialTraceRight (vecMulVec f (star f)) := by
  intro e w f
  let g := fun q : Config Bᶜ.card ι ×
      ((↥B → ι 0 × (ι 1 × ι 2)) × ((Fin B.card → ι 3) × (Fin B.card → ι 4))) =>
    let x := fiveFactorCopiesEquiv ι Bᶜ.card q.1
    w ((FiniteProduct.splitEquiv (fun _ : Fin k => ι 0 × (ι 1 × ι 2)) B).symm
      (q.2.1, fun i => x.1 ((Finset.equivFin Bᶜ) i)),
      ((goodBadCopiesEquiv (ι 3) B).symm (x.2.1, q.2.2.1),
        (goodBadCopiesEquiv (ι 4) B).symm (x.2.2, q.2.2.2)))
  have hvalue (x : Config Bᶜ.card ι) (y : Config B.card ι) :
      g (x, badConfigurationTraceEquiv ι B y) = f (x, y) := by
    exact congrArg w (groupedConfigurationEquiv_reconstruct ι B x y).symm
  change partialTraceRight (vecMulVec g (star g)) = _
  ext x y
  simp only [partialTraceRight_apply, vecMulVec_apply, Pi.star_apply]
  rw [← (badConfigurationTraceEquiv ι B).sum_comp
    (fun z => g (x, z) * star (g (y, z)))]
  simp_rw [hvalue]

/-- Every finite linear combination of actual good-subgroup label
entropies has the same exponential expectation in the literal excitation
component and in the actual five-factor good density. The regions and real
coefficients are arbitrary. Source: `07-comparators.tex`, lines 454--560. -/
theorem replicaExcitationComponent_exp_good_eq_trace_goodConfigurationMarginal
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    {J : Type*} [Fintype J] (S : J → Finset (Fin 5)) (a : J → ℝ) :
    let e := replicaGoodBadSplit B
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let f := w ∘ fiveFactorCopiesEquiv ι k
    star f ⬝ᵥ (NormedSpace.exp (∑ j, (a j : ℂ) •
      labelEntropy ((subsystemPerm k ι (S j)).comp (groupHom₁ e))) *ᵥ f) =
      (replicaGoodConfigurationMarginal ι Ω k B u *
        NormedSpace.exp (∑ j, (a j : ℂ) •
          labelEntropy (subsystemPerm Bᶜ.card ι (S j)))).trace := by
  intro e w f
  let η := groupedConfigurationEquiv ι e
  let g := f ∘ η.symm
  let H := NormedSpace.exp (∑ j, (a j : ℂ) •
    labelEntropy ((subsystemPerm k ι (S j)).comp (groupHom₁ e)))
  let K := NormedSpace.exp (∑ j, (a j : ℂ) •
    labelEntropy (subsystemPerm Bᶜ.card ι (S j)))
  have hH : H.submatrix η.symm η.symm =
      K ⊗ₖ (1 : Matrix (Config B.card ι) (Config B.card ι) ℂ) :=
    groupedConfigurationEquiv_exp_sum_labelEntropy ι e S a
  have hvec : (vecMulVec f (star f)).submatrix η.symm η.symm =
      vecMulVec g (star g) := by
    ext x y
    rfl
  have hρ : replicaGoodConfigurationMarginal ι Ω k B u =
      partialTraceRight (vecMulVec g (star g)) :=
    replicaGoodConfigurationMarginal_eq_grouped_partialTrace ι Ω k B u
  change star f ⬝ᵥ (H *ᵥ f) = (replicaGoodConfigurationMarginal ι Ω k B u * K).trace
  calc
    star f ⬝ᵥ (H *ᵥ f) = (vecMulVec f (star f) * H).trace := by
      rw [trace_mul_comm, mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
    _ = ((vecMulVec f (star f)).submatrix η.symm η.symm *
        H.submatrix η.symm η.symm).trace := by
      rw [submatrix_mul_equiv, trace_submatrix_equiv]
    _ = (partialTraceRight (vecMulVec g (star g)) * K).trace := by
      rw [hH, hvec, ← trace_partialTraceRight_mul]
    _ = (replicaGoodConfigurationMarginal ι Ω k B u * K).trace := by rw [hρ]

/-- The actual good-subgroup exponent remaining after removal of the
auxiliary entropy terms is the difference of the two merge deficits and
the physical label expression, in the same good density. This is an exact
identity for every real parameter and does not require simultaneous copy
symmetry or normalization. Source: `07-comparators.tex`, lines 501--560,
`comparator:merge-decomposition` and `comparator:component-inverse`. -/
theorem replicaExcitationComponent_exp_good_without_auxiliary_eq_trace
    (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (k : ℕ) (B : Finset (Fin k))
    (u : (Fin k → ι 0 × (ι 1 × ι 2)) × ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)
    (a : ℝ) :
    let e := replicaGoodBadSplit B
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let f := w ∘ fiveFactorCopiesEquiv ι k
    let Lg := fun S => labelEntropy ((subsystemPerm k ι S).comp (groupHom₁ e))
    let F := fun S => labelEntropy (subsystemPerm Bᶜ.card ι S)
    star f ⬝ᵥ (NormedSpace.exp ((-a) •
      (Lg {0, 3} + Lg {2, 4} - Lg {1} - (Lg {3} + Lg {4}))) *ᵥ f) =
      (replicaGoodConfigurationMarginal ι Ω k B u * NormedSpace.exp ((a : ℂ) •
        ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4}) -
          physicalMergeDeficit ι Bᶜ.card))).trace := by
  intro e w f Lg F
  let S : Fin 5 → Finset (Fin 5) := ![{0, 3}, {2, 4}, {1}, {3}, {4}]
  let c : Fin 5 → ℝ := ![-a, -a, a, a, a]
  have hleft : (∑ j, (c j : ℂ) • Lg (S j)) =
      (-a) • (Lg {0, 3} + Lg {2, 4} - Lg {1} - (Lg {3} + Lg {4})) := by
    simp only [S, c, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, Complex.ofReal_neg]
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.real_smul, Complex.ofReal_neg]
    ring
  have hright : (∑ j, (c j : ℂ) • F (S j)) =
      (a : ℂ) • ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4}) -
        physicalMergeDeficit ι Bᶜ.card) := by
    change (∑ j, (c j : ℂ) • F (S j)) =
      (a : ℂ) • ((F {0} + F {3} - F {0, 3}) + (F {2} + F {4} - F {2, 4}) -
        (F {0} + F {2} - F {1}))
    simp only [S, c, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.sum_univ_zero, add_zero, Complex.ofReal_neg]
    ext x y
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h := replicaExcitationComponent_exp_good_eq_trace_goodConfigurationMarginal
    ι Ω k B u S c
  change star f ⬝ᵥ (NormedSpace.exp (∑ j, (c j : ℂ) • Lg (S j)) *ᵥ f) =
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp (∑ j, (c j : ℂ) • F (S j))).trace at h
  rw [hleft, hright] at h
  exact h

end Matrix
