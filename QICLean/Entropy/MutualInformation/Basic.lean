/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.VonNeumann.Entropy

/-!
# Quantum mutual information

This module exposes the bipartite mutual information defined in
`TNLean.Analysis.Entropy` under the `Entropy` namespace without importing
strong subadditivity or its consequences.

## Main definitions

* `Entropy.mutualInformation` is the namespaced alias of
  `_root_.mutualInformation`.

## Main results

* `Entropy.mutualInformation_congr` shows that mutual information respects
  equality of the matrix independently of its Hermiticity witness.
* `Entropy.vonNeumannEntropy_nonneg_of_posSemidef_trace_one` is the namespaced
  nonnegativity of the entropy of a positive semidefinite trace-one matrix over an
  arbitrary finite index set.
* `Entropy.mutualInformation_le_log_dim_add_log_dim` is the elementary area-law
  bound `I(A:B) ≤ log d_A + log d_B`.

## References

* arXiv:1606.00608 §4.4 (Prop 4.5)
* Blueprint `def:entropy_mutual_information` and
  `thm:mutual_information_le_log_dim_add_log_dim`
-/

namespace Entropy

/-- **Quantum mutual information** between subsystems A and B,
namespaced alias.

`I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)` measures the total correlations
between A and B. Definitionally equal to `_root_.mutualInformation`.

Source: blueprint `def:entropy_mutual_information`. -/
noncomputable alias mutualInformation := _root_.mutualInformation

/-- Mutual information is independent of the Hermiticity witness and respects
equality of the underlying bipartite matrix. -/
theorem mutualInformation_congr
    {dA dB : ℕ}
    {ρ σ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ}
    (h : ρ = σ) (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    mutualInformation ρ hρ = mutualInformation σ hσ := by
  subst σ
  rfl

section Bounds

open scoped Matrix ComplexOrder
open Matrix Finset Real

/-! ## Entropy nonnegativity for finite index sets

The `Fin D`-restricted `_root_.vonNeumannEntropy_nonneg` does not directly
apply to bipartite density matrices indexed by `Fin dA × Fin dB`. The
following version records the same assertion for an arbitrary finite index set. -/

section FiniteIndexEntropyNonneg

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Nonnegativity of the von Neumann entropy for a PSD+trace-1
Hermitian matrix. Mirrors `_root_.vonNeumannEntropy_nonneg` without the
`Fin D`-index restriction. -/
alias vonNeumannEntropy_nonneg_of_posSemidef_trace_one :=
  _root_.vonNeumannEntropy_nonneg_of_posSemidef_trace_one

end FiniteIndexEntropyNonneg

/-! ## Elementary area-law bound on mutual information

Combining the single-system entropy bound `S(ρ) ≤ log D` with
nonnegativity of the joint entropy gives the elementary area-law bound
`I(A:B) ≤ log d_A + log d_B` for any bipartite density matrix whose
reduced states are density matrices. This is the entropy bound underlying
the MPDO area-law bound `I_L ≤ 4 log D` (arXiv:1606.00608 line 1319 and
references therein), prior to the MPS/MPDO-specific
bond-dimension refinement. -/

section AreaLaw

variable {dA dB : ℕ}

/-- **Elementary area-law bound on mutual information**. For a bipartite
density matrix `ρ_AB` on `Fin d_A × Fin d_B` with `0 < d_A`, `0 < d_B`
and whose reduced states are density matrices, the quantum mutual
information satisfies

  `I(A:B) ≤ log d_A + log d_B`.

The reduced states are density matrices because partial trace preserves
positive semidefiniteness and trace. Then `S(ρ_A) ≤ log d_A` and
`S(ρ_B) ≤ log d_B` by
`vonNeumannEntropy_le_log_dim`, and `S(ρ_AB) ≥ 0` by
`vonNeumannEntropy_nonneg_of_posSemidef_trace_one`.

This is the entropy-level bound underlying the MPDO area-law bound
`I_L ≤ 4 log D` (arXiv:1606.00608 line 1319); the MPS/MPDO-specific
bond-dimension refinement specialises this bound by taking `d_A = d_B`
to be controlled by the bond dimension via the MPDO representation. -/
theorem mutualInformation_le_log_dim_add_log_dim
    (ρ_AB : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ)
    (hρ_AB : ρ_AB.PosSemidef ∧ ρ_AB.trace = 1)
    (hdA : 0 < dA) (hdB : 0 < dB) :
    Entropy.mutualInformation ρ_AB hρ_AB.1.isHermitian
      ≤ Real.log dA + Real.log dB := by
  have h_A_dm : Matrix.traceRight ρ_AB ∈ densityMatrices dA := by
    exact ⟨hρ_AB.1.traceRight, by
      rw [Matrix.traceRight, Matrix.trace_partialTraceRight]
      exact hρ_AB.2⟩
  have h_B_dm : Matrix.traceLeft ρ_AB ∈ densityMatrices dB := by
    exact ⟨hρ_AB.1.traceLeft, by
      rw [← Matrix.trace_eq_trace_traceLeft ρ_AB]
      exact hρ_AB.2⟩
  have hSA : _root_.vonNeumannEntropy (Matrix.traceRight ρ_AB)
      (Matrix.traceRight_isHermitian hρ_AB.1.isHermitian)
        ≤ Real.log dA :=
    _root_.vonNeumannEntropy_le_log_dim h_A_dm hdA
  have hSB : _root_.vonNeumannEntropy (Matrix.traceLeft ρ_AB)
      (Matrix.traceLeft_isHermitian hρ_AB.1.isHermitian)
        ≤ Real.log dB :=
    _root_.vonNeumannEntropy_le_log_dim h_B_dm hdB
  have hSAB : 0 ≤ _root_.vonNeumannEntropy ρ_AB hρ_AB.1.isHermitian :=
    vonNeumannEntropy_nonneg_of_posSemidef_trace_one hρ_AB.1 hρ_AB.2
  change _root_.vonNeumannEntropy (Matrix.traceRight ρ_AB)
            (Matrix.traceRight_isHermitian hρ_AB.1.isHermitian)
        + _root_.vonNeumannEntropy (Matrix.traceLeft ρ_AB)
            (Matrix.traceLeft_isHermitian hρ_AB.1.isHermitian)
        - _root_.vonNeumannEntropy ρ_AB hρ_AB.1.isHermitian
      ≤ Real.log dA + Real.log dB
  linarith

end AreaLaw

end Bounds

end Entropy
