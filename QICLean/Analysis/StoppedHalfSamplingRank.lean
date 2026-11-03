/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CanonicalHalfSamplingDimension

/-!
# The initial-rank ceiling along the actual stopped resampling iteration

Every actual stopped round is nonincreasing in rank, independently of
sampling success. Thus a bound on the initial input rank controls every
intermediate image basis without using the potentially larger ambient
dimension. Supporting ALVV, arXiv:1602.08828v2, the resampling description,
lines 749–755. No viability or probability hypothesis is used.
-/

namespace Entropy

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
  {n : V → ℕ} {d : ℕ}

/-- Every actual stopped iterate has rank at most the initial rank, on
every sampling history. Supporting ALVV, arXiv:1602.08828v2,
the resampling description, lines 749–755. -/
theorem rank_canonicalHalfSampleTrimIterate_le
    (e : Fin d ≃ SiteConfig n) (cuts : ℕ → Finset V) (xi : ℝ)
    (k D threshold : ℕ) (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (hcard : Fintype.card ι ≤ D ^ 2)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : ℕ → Matrix.rankUnitaryProduct d) (i : ℕ) :
    (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U i).rank ≤ P.rank := by
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
      change (canonicalHalfSampleTrimMatrix e cuts xi k D threshold F
        (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U i) (U i)).rank ≤ _
      have hs := rank_canonicalHalfSampleTrimMatrix_le e cuts xi k D threshold F hcard
        (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U i) (U i)
      apply hs.trans
      split_ifs
      · exact (Nat.div_le_self _ _).trans ih
      · exact ih

end Entropy
