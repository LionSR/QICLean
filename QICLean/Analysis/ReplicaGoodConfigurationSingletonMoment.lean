/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ReplicaGoodConfigurationRegionalMoment
import QICLean.Representation.SubsystemTransport
import QICLean.Representation.ReplicaMetric
import QICLean.Analysis.GaussianFilter.Reindex

/-!
# The three physical singleton moments in the actual good density

Each of the three original physical factors is separated from the other
two by its literal coordinate equivalence. The corresponding singleton
copy action is then the original copy action on that factor, with
identities on its physical complement and both good auxiliary registers.
This yields the signed label moment of the actual five-factor density
directly from the tensor power of the original one-copy marginal.

Source: *A two-dimensional area law from a global spectral gap*,
September 24, 2026, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
`07-comparators.tex`, lines 550–560, `comparator:component-inverse`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Kronecker Matrix.Norms.Operator

namespace TensorPower

private def physicalTripleEquiv (ι : Fin 5 → Type*) :
    (ι 0 × (ι 1 × ι 2)) ≃ ((j : Fin 3) → ι (j.castAdd 2)) where
  toFun x := Fin.cons x.1 (Fin.cons x.2.1
    (Fin.cons x.2.2 (fun i ↦ Fin.elim0 i)))
  invFun x := (x 0, (x 1, x 2))
  left_inv _ := rfl
  right_inv x := by
    funext j
    fin_cases j <;> rfl

/-- Separate one of the three original physical factors from its two
remaining factors, preserving their original labels. Source:
`07-comparators.tex`, lines 550–560. -/
def physicalSingletonEquiv (ι : Fin 5 → Type*) (j : Fin 3) :
    (ι 0 × (ι 1 × ι 2)) ≃ ι (j.castAdd 2) ×
      ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)) :=
  (physicalTripleEquiv ι).trans (Equiv.piSplitAt j (fun l ↦ ι (l.castAdd 2)))

private def physicalSingletonCopiesEquiv (ι : Fin 5 → Type*) (m : ℕ) (j : Fin 3) :=
  (fiveFactorCopiesEquiv ι m).trans
    ((copiesProductEquiv (physicalSingletonEquiv ι j) m).prodCongr
      (Equiv.refl ((Fin m → ι 3) × (Fin m → ι 4))))

private theorem physicalTripleEquiv_fiveFactorCopies (ι : Fin 5 → Type*)
    (m : ℕ) (x : Config m ι) (r : Fin m) (j : Fin 3) :
    physicalTripleEquiv ι ((fiveFactorCopiesEquiv ι m x).1 r) j =
      x r (j.castAdd 2) := by
  fin_cases j <;> rfl

private theorem physicalSingletonCopiesEquiv_apply (ι : Fin 5 → Type*)
    (m : ℕ) (j : Fin 3) (x : Config m ι) :
    physicalSingletonCopiesEquiv ι m j x =
      (((fun r ↦ x r (j.castAdd 2)), fun r (l : {l : Fin 3 // l ≠ j}) ↦
        x r (l.1.castAdd 2)),
        ((fun r ↦ x r 3), fun r ↦ x r 4)) := by
  apply Prod.ext
  · apply Prod.ext
    · funext r
      exact physicalTripleEquiv_fiveFactorCopies ι m x r j
    · funext r l
      exact physicalTripleEquiv_fiveFactorCopies ι m x r l.1
  · rfl

private theorem physicalSingletonCopies_intertwine (ι : Fin 5 → Type*)
    (m : ℕ) (j : Fin 3) (σ : Equiv.Perm (Fin m)) (x : Config m ι) :
    prodLeft ((Fin m → ι 3) × (Fin m → ι 4))
      (prodLeft (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)))
        (copyPerm (ι (j.castAdd 2)) m)) σ
      (physicalSingletonCopiesEquiv ι m j x) =
        physicalSingletonCopiesEquiv ι m j
          (subsystemPerm m ι {j.castAdd 2} σ x) := by
  simp only [physicalSingletonCopiesEquiv_apply, prodLeft_apply]
  apply Prod.ext
  · apply Prod.ext
    · funext r
      simp [copyPerm_apply, subsystemPerm_apply]
    · funext r l
      have hne : l.1.castAdd 2 ≠ j.castAdd 2 := by
        intro h
        exact l.2 (Fin.castAdd_inj.mp h)
      simp only [subsystemPerm_apply, Finset.mem_singleton, hne, ite_false]
  · have h3 : (3 : Fin 5) ≠ j.castAdd 2 := by
      intro h
      have hv := congrArg Fin.val h
      change 3 = j.val at hv
      have hj := j.isLt
      omega
    have h4 : (4 : Fin 5) ≠ j.castAdd 2 := by
      intro h
      have hv := congrArg Fin.val h
      change 4 = j.val at hv
      have hj := j.isLt
      omega
    ext r <;>
      simp only [subsystemPerm_apply, Finset.mem_singleton, h3, h4, ite_false]

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (m : ℕ) (j : Fin 3)

local instance goodSingletonMoment_decidableEqConfig :
    DecidableEq (Config m ι) := Fintype.decidablePiFintype

local instance goodSingletonMoment_decidableEqCopies (f : Fin 5) :
    DecidableEq (Fin m → ι f) := Fintype.decidablePiFintype

local instance goodSingletonMoment_decidableEqComplement :
    DecidableEq ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)) :=
  Fintype.decidablePiFintype

local instance goodSingletonMoment_decidableEqComplementCopies :
    DecidableEq (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2))) :=
  Fintype.decidablePiFintype

local instance goodSingletonMoment_decidableEqPhysicalPair :
    DecidableEq ((Fin m → ι (j.castAdd 2)) ×
      (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)))) := inferInstance

local instance goodSingletonMoment_decidableEqAuxiliaryPair :
    DecidableEq ((Fin m → ι 3) × (Fin m → ι 4)) := inferInstance

local instance goodSingletonMoment_decidableEqWhole :
    DecidableEq (((Fin m → ι (j.castAdd 2)) ×
      (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)))) ×
      ((Fin m → ι 3) × (Fin m → ι 4))) := inferInstance

/-- The actual singleton label observable is the original physical-factor
observable in its literal bipartite coordinates, tensored with the two
auxiliary identities. Source: `07-comparators.tex`, lines 550–560. -/
theorem fiveFactorCopies_labelObservable_singleton
    (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    let c := copiesProductEquiv (physicalSingletonEquiv ι j) m
    (labelObservable (subsystemPerm m ι {j.castAdd 2}) f).submatrix
      (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      ((labelObservable (copyPerm (ι (j.castAdd 2)) m) f ⊗ₖ
        (1 : Matrix (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)))
          (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2))) ℂ)).submatrix c c) ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
  intro c
  let d := c.prodCongr (Equiv.refl ((Fin m → ι 3) × (Fin m → ι 4)))
  have h : (labelObservable (subsystemPerm m ι {j.castAdd 2}) f).submatrix
      (physicalSingletonCopiesEquiv ι m j).symm
      (physicalSingletonCopiesEquiv ι m j).symm =
      (labelObservable (copyPerm (ι (j.castAdd 2)) m) f ⊗ₖ
        (1 : Matrix (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)))
          (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2))) ℂ)) ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
    simp only [labelObservable_eq_groupAlgebraRep]
    rw [← reindex_apply,
      ← groupAlgebraRep_of_intertwine (physicalSingletonCopiesEquiv ι m j)
        (physicalSingletonCopies_intertwine ι m j),
      groupAlgebraRep_prodLeft, groupAlgebraRep_prodLeft]
  have he : (physicalSingletonCopiesEquiv ι m j).symm ∘ d =
      (fiveFactorCopiesEquiv ι m).symm := by
    funext x
    exact congrArg (fiveFactorCopiesEquiv ι m).symm (d.symm_apply_apply x)
  have hpull := congrArg (fun M ↦ M.submatrix d d) h
  rw [submatrix_submatrix, he] at hpull
  exact hpull

/-- The same literal coordinate identity holds for the exponential of
the singleton label entropy, with any real parameter.
Source: `07-comparators.tex`, lines 550–560. -/
theorem fiveFactorCopies_exp_labelEntropy_singleton (a : ℝ) :
    let c := copiesProductEquiv (physicalSingletonEquiv ι j) m
    (NormedSpace.exp ((a : ℂ) • labelEntropy
      (subsystemPerm m ι {j.castAdd 2}))).submatrix
        (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm =
      ((NormedSpace.exp ((a : ℂ) • labelEntropy (copyPerm (ι (j.castAdd 2)) m)) ⊗ₖ
        (1 : Matrix (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2)))
          (Fin m → ((l : {l : Fin 3 // l ≠ j}) → ι (l.1.castAdd 2))) ℂ)).submatrix c c) ⊗ₖ
        (1 : Matrix ((Fin m → ι 3) × (Fin m → ι 4))
          ((Fin m → ι 3) × (Fin m → ι 4)) ℂ) := by
  intro c
  have hF := fiveFactorCopies_labelObservable_singleton ι m j
    (fun l ↦ Real.log l.dim)
  change (labelEntropy (subsystemPerm m ι {j.castAdd 2})).submatrix
      (fiveFactorCopiesEquiv ι m).symm (fiveFactorCopiesEquiv ι m).symm = _ at hF
  rw [← reindex_apply, reindex_exp, reindex_apply, submatrix_smul,
    Pi.smul_apply, Pi.smul_apply, hF,
    ← smul_kronecker, exp_kronecker_one]
  congr 1
  rw [← Pi.smul_apply, ← Pi.smul_apply, ← submatrix_smul,
    ← reindex_apply c.symm c.symm, ← reindex_exp, reindex_apply,
    ← smul_kronecker, exp_kronecker_one]

end TensorPower

namespace Matrix
open TensorPower

variable (ι : Fin 5 → Type*) [∀ f, Fintype (ι f)] [∀ f, DecidableEq (ι f)]
variable (Ω : ι 0 × (ι 1 × ι 2) → ℂ) (hΩ : ‖WithLp.toLp 2 Ω‖ = 1)
variable (k : ℕ) (B : Finset (Fin k))
variable (u : (Fin k → ι 0 × (ι 1 × ι 2)) ×
  ((Fin k → ι 3) × (Fin k → ι 4)) → ℂ)

local instance goodSingletonTrace_decidableEqConfig :
    DecidableEq (Config Bᶜ.card ι) := Fintype.decidablePiFintype

include hΩ

/-- For each of the three original physical singleton regions, the signed
label moment in the actual five-factor density is the original iid
regional moment times the same excitation-component mass. No symmetry
or nonzero-component premise is needed. Source: `07-comparators.tex`,
lines 550–560. -/
theorem trace_replicaGoodConfigurationMarginal_exp_singleton_labelEntropy
    (j : Fin 3) (a : ℝ) :
    let w := (replicaExcitationProjection Ω k B ⊗ₖ
      (1 : Matrix ((Fin k → ι 3) × (Fin k → ι 4))
        ((Fin k → ι 3) × (Fin k → ι 4)) ℂ)) *ᵥ u
    let e := physicalSingletonEquiv ι j
    let ρ := partialTraceRight ((vecMulVec Ω (star Ω)).submatrix e.symm e.symm)
    (replicaGoodConfigurationMarginal ι Ω k B u *
      NormedSpace.exp ((a : ℂ) •
        labelEntropy (subsystemPerm Bᶜ.card ι {j.castAdd 2}))).trace =
      (‖WithLp.toLp 2 w‖ ^ 2 : ℂ) *
        (finKronecker (fun _ : Fin Bᶜ.card ↦ ρ) *
          NormedSpace.exp ((a : ℂ) •
            labelEntropy (copyPerm (ι (j.castAdd 2)) Bᶜ.card))).trace := by
  intro w e ρ
  have h := trace_replicaGoodConfigurationMarginal_regional_exp_labelEntropy
    ι Ω hΩ k B u e a
  rw [← fiveFactorCopies_exp_labelEntropy_singleton ι Bᶜ.card j a,
    submatrix_mul_equiv, trace_submatrix_equiv] at h
  exact h

end Matrix
