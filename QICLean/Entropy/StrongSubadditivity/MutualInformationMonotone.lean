/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.VonNeumann.Entropy
import QICLean.Entropy.StrongSubadditivity.Basic
import QICLean.Entropy.MutualInformation.Basic

/-!
# Mutual information from strong subadditivity

The quantum mutual information of a bipartite density matrix is
`I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)`. This module records two
consequences of strong subadditivity for it, used for matrix product
density operators and renormalization fixed points:

* the **nonnegativity** of the mutual information in the trivial-middle
  tripartite form, a corollary of subadditivity;
* a **monotonicity** inequality under enlargement of a subsystem
  (`mutualInformation_monotone_tripartite`), which is the SSA-level
  inequality underlying the MPDO `I_L ≤ I_{L+1}` monotonicity
  (arXiv:1606.00608 Prop C.1).

The namespaced mutual information, the nonnegativity of the entropy over
arbitrary finite index sets and the elementary area-law bound
`I(A:B) ≤ log d_A + log d_B` need no strong subadditivity and are
stated with the definition of the mutual information.

## Main declarations

* `Entropy.mutualInformation_ssa_trivial_B_nonneg` — the nonnegativity
  of the tripartite mutual information in the trivial-middle form,
  derived from `subadditivity_ssa_trivial_B` with no extra reduced-trace
  hypothesis.
* `Entropy.mutualInformation_monotone_tripartite` — mutual information
  is monotone under enlargement of a subsystem, in the tripartite form
  `I(A:B) ≤ I(A:BC)` directly used by the MPDO area-law argument.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8][Wolf2012QChannels]
* arXiv:1606.00608 §4.4 (Prop 4.5) and Appendix C (Prop C.1)
* Blueprint `thm:mutual_information_nonneg` and
  `thm:mutual_information_monotone_tripartite`
-/

open scoped Matrix ComplexOrder
open Matrix Finset Real

namespace Entropy

/-! ## Nonnegativity via subadditivity (trivial-middle form)

When a bipartite state on `A ⊗ C` is embedded in a trivial-middle
tripartite state on `A ⊗ 1 ⊗ C`, subadditivity (Theorem
`subadditivity_ssa_trivial_B`) immediately gives nonnegativity of the
tripartite mutual information `I(A:C) = S(ρ_A) + S(ρ_C) − S(ρ_AC)`.

We state this corollary in the same tripartite form used by
`subadditivity_ssa_trivial_B` to avoid any reshuffling of indices; it
is the version directly consumed by MPDO RFP applications. -/

section Nonnegativity

variable {dA dC : ℕ}

/-- Mutual information is nonneg in the tripartite trivial-middle
form: `S(ρ_AB) + S(ρ_BC) − S(ρ_ABC) ≥ 0`. Direct corollary of
`subadditivity_ssa_trivial_B`.

Source: blueprint `thm:mutual_information_nonneg`. -/
theorem mutualInformation_ssa_trivial_B_nonneg
    (ρ_ABC : Matrix (Fin dA × Fin 1 × Fin dC)
      (Fin dA × Fin 1 × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    0 ≤ Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
          (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
        + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian)
        - Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian := by
  have h := subadditivity_ssa_trivial_B ρ_ABC hρ_dm
  linarith

end Nonnegativity

/-! ## Monotonicity under enlargement of a subsystem

The MPDO mutual-information monotonicity `I_L ≤ I_{L+1}`
(arXiv:1606.00608 Prop C.1) decomposes into two steps: an SSA-level
monotonicity `I(A:B) ≤ I(A:BC)` on a tripartite state, and a
translation-invariance step identifying contiguous-block entropies.
The SSA-level step is the entropy-theoretic content formalised here;
the translation-invariance step belongs to the downstream MPDO module. -/

section Monotonicity

variable {dA dB dC : ℕ}

/-- The bipartite `B` reduced state matches the tripartite `B` reduced
state: for any `ρ_ABC` on `A ⊗ B ⊗ C`,
`tr_A (tr_C ρ_ABC) = tr_{AC} ρ_ABC` as matrices on `Fin dB`. -/
private theorem traceLeft_traceC_ABC_eq_traceAC_ABC
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ) :
    Matrix.traceLeft (traceC_ABC (dA := dA) (dB := dB) (dC := dC) ρ_ABC)
      = traceAC_ABC ρ_ABC := by
  ext b₁ b₂
  simp only [Matrix.traceLeft_apply, traceC_ABC, traceAC_ABC]

/-- **Mutual information is monotone under enlargement of a subsystem**
(tripartite form). For a tripartite density matrix `ρ_ABC` on
`A ⊗ B ⊗ C`:

`I(A:B)` evaluated on the reduced state `ρ_AB = tr_C(ρ_ABC)` is bounded
above by `I(A:BC)` evaluated on the full state `ρ_ABC` viewed bipartitely
as `A ⊗ (B ⊗ C)`:

  `I(A:B) = S(ρ_A) + S(ρ_B) − S(ρ_AB)
         ≤ S(ρ_A) + S(ρ_BC) − S(ρ_ABC) = I(A:BC)`.

After cancelling `S(ρ_A)` on both sides, the inequality reduces to
strong subadditivity
`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)` (Lieb–Ruskai 1973).

The right-hand side uses the tripartite partial traces:
`ρ_BC = tr_A(ρ_ABC)` (`traceA_ABC`). The left-hand side uses the bipartite
mutual information of the reduced `ρ_AB = tr_C(ρ_ABC)` (`traceC_ABC`).

This is the SSA-level monotonicity consumed by the MPDO area-law
argument (arXiv:1606.00608 Prop C.1); translation invariance lifts it
to the `I_L ≤ I_{L+1}` statement on contiguous-block mutual information. -/
theorem mutualInformation_monotone_tripartite
    (ρ_ABC : Matrix (Fin dA × Fin dB × Fin dC)
      (Fin dA × Fin dB × Fin dC) ℂ)
    (hρ_dm : ρ_ABC.PosSemidef ∧ ρ_ABC.trace = 1) :
    Entropy.mutualInformation (traceC_ABC ρ_ABC)
        (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
      ≤ Entropy.vonNeumannEntropy
            (Matrix.traceRight (traceC_ABC ρ_ABC))
            (Matrix.traceRight_isHermitian
              (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian)
        - Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian := by
  have h_SSA :
      Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
        + Entropy.vonNeumannEntropy (traceAC_ABC ρ_ABC)
            (traceAC_ABC_isHermitian hρ_dm.1.isHermitian)
      ≤ Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
            (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
        + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian) :=
    Entropy.strongSubadditivity ρ_ABC hρ_dm
  have h_rhoB_eq :=
    traceLeft_traceC_ABC_eq_traceAC_ABC (dA := dA) (dB := dB) (dC := dC) ρ_ABC
  have h_rhoB_entropy :
      Entropy.vonNeumannEntropy
          (Matrix.traceLeft (traceC_ABC ρ_ABC))
          (Matrix.traceLeft_isHermitian
            (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        = Entropy.vonNeumannEntropy (traceAC_ABC ρ_ABC)
            (traceAC_ABC_isHermitian hρ_dm.1.isHermitian) := by
    cases h_rhoB_eq
    rfl
  change Entropy.vonNeumannEntropy
          (Matrix.traceRight (traceC_ABC ρ_ABC))
          (Matrix.traceRight_isHermitian
            (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        + Entropy.vonNeumannEntropy
            (Matrix.traceLeft (traceC_ABC ρ_ABC))
            (Matrix.traceLeft_isHermitian
              (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        - Entropy.vonNeumannEntropy (traceC_ABC ρ_ABC)
            (traceC_ABC_isHermitian hρ_dm.1.isHermitian)
      ≤ Entropy.vonNeumannEntropy
            (Matrix.traceRight (traceC_ABC ρ_ABC))
            (Matrix.traceRight_isHermitian
              (traceC_ABC_isHermitian hρ_dm.1.isHermitian))
        + Entropy.vonNeumannEntropy (traceA_ABC ρ_ABC)
            (traceA_ABC_isHermitian hρ_dm.1.isHermitian)
        - Entropy.vonNeumannEntropy ρ_ABC hρ_dm.1.isHermitian
  rw [h_rhoB_entropy]
  linarith

end Monotonicity


end Entropy
