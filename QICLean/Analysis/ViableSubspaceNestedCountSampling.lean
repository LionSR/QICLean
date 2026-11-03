/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.ViableSubspaceNestedSampling
import QICLean.Analysis.NestedSamplingNaturalParameters

/-!
# An actual nested-target sample from a dyadic count comparison

The natural quotient, failure estimate and final error are derived from
the count comparison and the calibrated suppression of the same chosen
family. The conclusion retains the actual Haar unitary, sample and image.
This supports ALVV, arXiv:1602.08828v2, Proposition `prop:albootstrap-ld`,
lines 1112–1128. The physical target comparisons and improving family
remain hypotheses of this abstract auxiliary.

**Local fix (strict dimension decrease):** The sample has dimension
`p / (2 * D^2)`, and its image has dimension at most `p/2`. See
`docs/paper-gaps/alvv16_low_density_sampling.tex` and the complex-sphere
correction in `docs/paper-gaps/alvv16_random_sampling_net_count.tex`.
-/

open scoped TensorProduct InnerProductSpace

namespace Submodule

variable {M F : Type*}
  [NormedAddCommGroup M] [InnerProductSpace ℂ M] [FiniteDimensional ℂ M]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

/-- At a bad-to-good dyadic count comparison, one actual half-size sample
and its improving image retain the lower original target. Both numerical
sampling premises are consequences of the displayed count and suppression
bounds. Auxiliary to ALVV, arXiv:1602.08828v2, Proposition
`prop:albootstrap-ld`, lines 1112–1128. -/
theorem exists_isViable_nested_sample_of_count_comparison
    {D Dnext r p : ℕ} {Delta : ℝ}
    {Gplus Gminus Thi Tlo : Submodule ℂ (M ⊗[ℂ] F)}
    (hupper : IsCloseTo (1 / 200) Gplus Thi)
    (hlower : IsCloseTo (1 / 200) Tlo Gminus)
    (A : Fin (D ^ 2) → M →L[ℂ] M)
    (himprove : ∀ delta < 1, ∀ S : Submodule ℂ M,
      IsViable delta S Thi →
      IsViable (Delta / (1 - delta) ^ 2)
        (⨆ i, S.map (A i : M →ₗ[ℂ] M)) Tlo)
    (hDelta : 0 ≤ Delta) (hlogD : 100 ≤ Real.log (D : ℝ)) (hr : 1 ≤ r)
    (htarget : Module.finrank ℂ Thi ≤ r)
    (hcount : Real.log (Dnext : ℝ) ≤ (13 / 6) * Real.log (D : ℝ))
    (hbad : r * D ^ 3 < p)
    {W : Submodule ℂ M} (hW : IsViable (3 / 200) W Gplus)
    (hpW : p ≤ Module.finrank ℂ W)
    (hupperDim : Module.finrank ℂ W ≤ r * Dnext ^ 3)
    (htrade : (D : ℝ) ^ 12 * Delta ≤ 1 / 100000) :
    let Q : ℕ := Module.finrank ℂ W
    let s : ℕ := p / (2 * D ^ 2)
    let alpha : ℝ := (1 - 1 / 25) * (s : ℝ) / (8 * (Q : ℝ))
    let Coord : Finset (Fin Q) := Finset.univ.map
      (Fin.castLEEmb ((Nat.div_le_self p (2 * D ^ 2)).trans hpW))
    ∃ U : Matrix.unitaryGroup (Fin Q) ℂ,
      let sample := randomSubspace (stdOrthonormalBasis ℂ W) Coord U
      let image : Submodule ℂ M := ⨆ i, sample.map (A i : M →ₗ[ℂ] M)
      1 ≤ s ∧ 0 < alpha ∧ sample ≤ W ∧ Module.finrank ℂ sample = s ∧
      IsViable (1 - alpha) sample Thi ∧ Module.finrank ℂ image ≤ p / 2 ∧
      Module.finrank ℂ image < p ∧
      IsViable (2 * (Delta / alpha ^ 2 + 1 / 200)) image Gminus ∧
      IsViable (3 / 200) image Gminus := by
  intro Q s alpha Coord
  obtain ⟨hD, hp4, _hs1, _halpha, hfailure, herror⟩ :=
    Real.nested_sampling_natural_conditions hlogD hr htarget hcount hbad hpW hupperDim
      htrade
  obtain ⟨U, hs1, halpha, hsample, hsampledim, hsampleviable, hhalf, hraw, hfinal⟩ :=
    exists_isViable_nested_randomSubspace_finrank_le_half hupper hlower A himprove
      (by omega) hDelta hp4 hW hpW hfailure herror
  refine ⟨U, hs1, halpha, hsample, hsampledim, hsampleviable, hhalf, ?_, hraw, hfinal⟩
  exact hhalf.trans_lt (Nat.div_lt_self (lt_of_le_of_lt (Nat.zero_le _) hbad) (by decide))

end Submodule
