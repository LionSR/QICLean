/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.GroupedCopies
import QICLean.Representation.SubsystemTransport
import QICLean.Representation.ReplicaSimilarity
import QICLean.Analysis.GaussianFilter.Reindex
import QICLean.Analysis.KroneckerExponential
import QICLean.Algebra.FinSum

/-!
# Subgroup observables in the coordinates of two groups of copies

Splitting the copies by a specified equivalence identifies the action of
the first subgroup on any subsystem with the original subsystem action
on the first group of copies and the identity on the second. The same
identity holds for label observables and for exponentials of their linear
combinations. All coordinate identifications are derived from the actual
permutation actions.

Source: *A two-dimensional area law from a global spectral gap*, September 24,
2026, `07-comparators.tex`, lines 454–560, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section
open Matrix PermutationRepresentation
open scoped BigOperators Kronecker Matrix.Norms.Operator

namespace TensorPower

variable {V : Type*} (ι : V → Type*) {m r k : ℕ}

/-- Split all physical and auxiliary configurations by the same division
of the copies. Source: `07-comparators.tex`, lines 454–560. -/
def groupedConfigurationEquiv (e : Fin m ⊕ Fin r ≃ Fin k) :
    Config k ι ≃ Config m ι × Config r ι :=
  (Equiv.arrowCongr e.symm (Equiv.refl ((v : V) → ι v))).trans
    (Equiv.sumArrowEquivProdArrow (Fin m) (Fin r) ((v : V) → ι v))

variable [DecidableEq V]

/-- In split coordinates, the first copy subgroup acts only on the first
group, on precisely the specified subsystem. Source: `07-comparators.tex`,
lines 454–560. -/
theorem groupedConfigurationEquiv_subsystemPerm
    (e : Fin m ⊕ Fin r ≃ Fin k) (S : Finset V)
    (σ : Equiv.Perm (Fin m)) (x : Config k ι) :
    prodLeft (Config r ι) (subsystemPerm m ι S) σ
        (groupedConfigurationEquiv ι e x) =
      groupedConfigurationEquiv ι e (subsystemPerm k ι S (groupHom₁ e σ) x) := by
  apply Prod.ext
  · funext j v
    by_cases hv : v ∈ S <;>
      simp [groupedConfigurationEquiv, prodLeft_apply, subsystemPerm_apply,
        hv, groupHom₁, youngHom, Equiv.permCongrHom, Equiv.permCongr_def]
  · funext j v
    by_cases hv : v ∈ S <;>
      simp [groupedConfigurationEquiv, prodLeft_apply, subsystemPerm_apply,
        hv, groupHom₁, youngHom, Equiv.permCongrHom, Equiv.permCongr_def,
        Equiv.Perm.one_def]

variable [Fintype V] [∀ v, Fintype (ι v)] [∀ v, DecidableEq (ι v)]

local instance groupedConfigurationTransport_decidableEqConfig (n : ℕ) :
    DecidableEq (Config n ι) := Fintype.decidablePiFintype

/-- A first-subgroup label observable is the corresponding observable on
the first group of copies, tensored with the identity on the second.
Source: `07-comparators.tex`, lines 454–560. -/
theorem groupedConfigurationEquiv_labelObservable
    (e : Fin m ⊕ Fin r ≃ Fin k) (S : Finset V)
    (f : IrrepLabel (Equiv.Perm (Fin m)) → ℝ) :
    (labelObservable ((subsystemPerm k ι S).comp (groupHom₁ e)) f).submatrix
        (groupedConfigurationEquiv ι e).symm (groupedConfigurationEquiv ι e).symm =
      labelObservable (subsystemPerm m ι S) f ⊗ₖ
        (1 : Matrix (Config r ι) (Config r ι) ℂ) := by
  simp only [labelObservable_eq_groupAlgebraRep]
  rw [← reindex_apply,
    ← groupAlgebraRep_of_intertwine (groupedConfigurationEquiv ι e)
      (groupedConfigurationEquiv_subsystemPerm ι e S), groupAlgebraRep_prodLeft]

/-- The exponential of any finite real linear combination of actual
first-subgroup label entropies becomes the same exponential on the first
group, tensored with the identity. No disjointness or commutation between
the specified subsystems is needed for this coordinate identity.
Source: `07-comparators.tex`, lines 454–560. -/
theorem groupedConfigurationEquiv_exp_sum_labelEntropy
    {J : Type*} [Fintype J] (e : Fin m ⊕ Fin r ≃ Fin k)
    (S : J → Finset V) (a : J → ℝ) :
    (NormedSpace.exp (∑ j, (a j : ℂ) •
      labelEntropy ((subsystemPerm k ι (S j)).comp (groupHom₁ e)))).submatrix
      (groupedConfigurationEquiv ι e).symm (groupedConfigurationEquiv ι e).symm =
        NormedSpace.exp (∑ j, (a j : ℂ) • labelEntropy (subsystemPerm m ι (S j))) ⊗ₖ
          (1 : Matrix (Config r ι) (Config r ι) ℂ) := by
  rw [← reindex_apply, reindex_exp, reindex_apply]
  rw [submatrix_sum]
  simp only [submatrix_smul, Pi.smul_apply]
  simp_rw [labelEntropy, groupedConfigurationEquiv_labelObservable]
  simp_rw [← smul_kronecker]
  have hsum : (∑ j, ((a j : ℂ) • labelObservable (subsystemPerm m ι (S j))
      (fun ell => Real.log ell.dim)) ⊗ₖ (1 : Matrix (Config r ι) (Config r ι) ℂ)) =
      (∑ j, (a j : ℂ) • labelObservable (subsystemPerm m ι (S j))
        (fun ell => Real.log ell.dim)) ⊗ₖ (1 : Matrix (Config r ι) (Config r ι) ℂ) := by
    ext x y
    simp only [Matrix.sum_apply, kroneckerMap_apply, Finset.sum_mul]
  rw [hsum, exp_kronecker_one]

end TensorPower
