/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CanonicalSamplingTrimmingMeasurable

/-!
# A stopped iteration of canonical sampling and collective trimming

The actual input rank determines both whether another round is taken and
the quotient sample size. A successful or unsuccessful sample is subjected
to the same finite operator family and the same collective trim. Below the
stopping threshold the current matrix is retained.

This construction supports repeated amplification associated with ALVV,
arXiv:1602.08828v2, the merge process, lines 711–736.
This module treats a repeated-resampling variant of the merge procedure
sketched at arXiv:1602.08828v2, lines 711–755; Figure `fig:merge-prime` and
Theorem `t:alg1` are not formalized here. See
`docs/paper-gaps/alvv16_bootstrap_constants.tex`.
A fresh sample is taken at each active round.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Entropy

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    {n : V → ℕ} {d : ℕ}

/-- One stopped round uses the actual quotient sample, its fixed-family
image and the existing collective trim. The resulting actual projection
is returned to the same fixed input coordinates. Source: ALVV,
arXiv:1602.08828v2, the merge process, lines 711–736. -/
def canonicalHalfSampleTrimMatrix (e : Fin d ≃ SiteConfig n)
    (cuts : ℕ → Finset V) (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : Matrix.rankUnitaryProduct d) :
    Matrix (Fin d) (Fin d) ℂ :=
  if threshold ≤ P.rank then
    let S := trimMatrixRange e cuts xi k (Matrix.familySupportProj (fun i ↦ F i *
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
        (Matrix.randomRangeSubspace P (P.rank / (2 * D ^ 2)) U).starProjection))
    ((Matrix.toEuclideanCLM (n := SiteConfig n) (𝕜 := ℂ)).symm
      S.starProjection).reindex e.symm e.symm
  else P

/-- The actual stopped sampling-and-trimming round has a jointly Borel
matrix in the current input and the fixed product of unitary coordinates.
Auxiliary for ALVV, arXiv:1602.08828v2, the merge process, lines 711–736. -/
theorem measurable_canonicalHalfSampleTrimMatrix (e : Fin d ≃ SiteConfig n)
    (cuts : ℕ → Finset V) (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℂ × Matrix.rankUnitaryProduct d ↦
      canonicalHalfSampleTrimMatrix e cuts xi k D threshold F p.1 p.2) := by
  have htrim := measurable_projectionMatrix_trim_sample_family_image_rank_size
    e cuts xi k (fun q ↦ q / (2 * D ^ 2)) F
  have hcoordinates : Continuous (fun P : Matrix (SiteConfig n) (SiteConfig n) ℂ ↦
      P.reindex e.symm e.symm) := by fun_prop
  have hstop : MeasurableSet {p : Matrix (Fin d) (Fin d) ℂ ×
      Matrix.rankUnitaryProduct d | threshold ≤ p.1.rank} :=
    measurableSet_le measurable_const (Matrix.measurable_rank.comp measurable_fst)
  exact Measurable.ite hstop (hcoordinates.measurable.comp htrim) measurable_fst


/-- Iterate the same stopped canonical sampling-and-trimming round, using
a fresh prescribed unitary coordinate at each active round. Source: ALVV,
arXiv:1602.08828v2, the merge process, lines 711–736. -/
def canonicalHalfSampleTrimIterate (e : Fin d ≃ SiteConfig n)
    (cuts : ℕ → Finset V) (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ) (U : ℕ → Matrix.rankUnitaryProduct d) :
    ℕ → Matrix (Fin d) (Fin d) ℂ :=
  Nat.rec P (fun i Q ↦ canonicalHalfSampleTrimMatrix e cuts xi k D threshold F Q (U i))

/-- At each predetermined round the actual iterated matrix is Borel in
the initial matrix and the unitary coordinates. This is a measurability
auxiliary for ALVV, arXiv:1602.08828v2, the merge process, lines 711–736;
no probability bound on successful rounds is assumed or asserted. -/
theorem measurable_canonicalHalfSampleTrimIterate (e : Fin d ≃ SiteConfig n)
    (cuts : ℕ → Finset V) (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ) (r : ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℂ ×
        (ℕ → Matrix.rankUnitaryProduct d) ↦
      canonicalHalfSampleTrimIterate e cuts xi k D threshold F p.1 p.2 r) := by
  induction r with
  | zero => exact measurable_fst
  | succ r ih =>
      let input := fun p : Matrix (Fin d) (Fin d) ℂ ×
          (ℕ → Matrix.rankUnitaryProduct d) ↦
        (canonicalHalfSampleTrimIterate e cuts xi k D threshold F p.1 p.2 r, p.2 r)
      have hu : Measurable (fun p : Matrix (Fin d) (Fin d) ℂ ×
          (ℕ → Matrix.rankUnitaryProduct d) ↦ p.2 r) :=
        (measurable_pi_apply r).comp measurable_snd
      have hinput : Measurable input := ih.prodMk hu
      change Measurable
        ((fun p : Matrix (Fin d) (Fin d) ℂ × Matrix.rankUnitaryProduct d ↦
          canonicalHalfSampleTrimMatrix e cuts xi k D threshold F p.1 p.2) ∘ input)
      exact (measurable_canonicalHalfSampleTrimMatrix e cuts xi k D threshold F).comp
        (f := input) hinput

/-- The current iterate depends only on unitary coordinates from earlier
rounds. This permits fixing the current input before the next Haar sample.
Auxiliary to ALVV, arXiv:1602.08828v2, the merge process, lines 711–736. -/
theorem canonicalHalfSampleTrimIterate_eq_of_seed_prefix (e : Fin d ≃ SiteConfig n)
    (cuts : ℕ → Finset V) (xi : ℝ) (k D threshold : ℕ)
    (F : ι → Matrix (SiteConfig n) (Fin d) ℂ)
    (P : Matrix (Fin d) (Fin d) ℂ)
    (U U' : ℕ → Matrix.rankUnitaryProduct d) (r : ℕ) :
    (∀ i < r, U i = U' i) →
      canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U r =
        canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U' r := by
  induction r with
  | zero =>
      intro _
      rfl
  | succ r ih =>
      intro hU
      change canonicalHalfSampleTrimMatrix e cuts xi k D threshold F
        (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U r) (U r) =
        canonicalHalfSampleTrimMatrix e cuts xi k D threshold F
          (canonicalHalfSampleTrimIterate e cuts xi k D threshold F P U' r) (U' r)
      exact congrArg₂ (canonicalHalfSampleTrimMatrix e cuts xi k D threshold F)
        (ih (fun i hi ↦ hU i (hi.trans (Nat.lt_succ_self r))))
        (hU r (Nat.lt_succ_self r))

end Entropy
