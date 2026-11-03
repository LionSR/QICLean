/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.CanonicalSampleProjectionMeasurable
import QICLean.Analysis.MatrixRankMeasurable
import QICLean.Analysis.MatrixFamilySupportMeasurable

/-!
# A Borel canonical sampler with varying input rank

A fixed finite product contains one coordinate unitary for every possible
input rank. The actual existing random-subspace sampler uses the unitary
at the actual matrix rank and the canonical orthonormal basis of its range.
Thus the sample projector and its image under a fixed finite operator family
are jointly Borel across changes of input rank. This supports ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558. No adaptive probability
estimate or running-time conclusion is asserted here.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace Matrix

/-- One coordinate unitary for each possible rank of a d by d matrix. -/
abbrev rankUnitaryProduct (d : ℕ) :=
  (r : Fin (d + 1)) → unitaryGroup (Fin r.val) ℂ

/-- The existing canonical-basis sample, using the actual-rank coordinate
of the fixed finite unitary product and the first min(s,rank) columns. -/
def randomRangeSubspace {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (s : ℕ) (U : rankUnitaryProduct d) : Submodule ℂ (EuclideanSpace ℂ (Fin d)) :=
  Submodule.randomSubspace (rangeOrthonormalBasis ⟨P, rfl⟩)
    (Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s P.rank)))
    (U ⟨P.rank, Nat.lt_succ_of_le P.rank_le_width⟩)

/-- On each rank stratum, the global sample is literally the existing
fixed-rank canonical sampler, with the corresponding unitary coordinate. -/
theorem randomRangeSubspace_eq_on_rank {d r : ℕ}
    (P : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r})
    (s : ℕ) (U : rankUnitaryProduct d) (hr : r ≤ d) :
    randomRangeSubspace P.val s U =
      Submodule.randomSubspace (rangeOrthonormalBasis P)
        (Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s r)))
        (U ⟨r, Nat.lt_succ_of_le hr⟩) := by
  rcases P with ⟨P, hP⟩
  subst r
  rfl

/-- The requested sample size may be any function of the actual input rank.
The existing canonical sample still has a jointly Borel ambient projection.
Measurability auxiliary for ALVV, arXiv:1602.08828v2, Lemma l:rs, lines 530–558. -/
theorem measurable_randomRangeSubspace_projection_rank_size {d : ℕ} (s : ℕ → ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℂ × rankUnitaryProduct d ↦
      (toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
        (randomRangeSubspace p.1 (s p.1.rank) p.2).starProjection) := by
  apply measurable_of_matrix_rank_strata (P := Prod.fst) measurable_fst
  intro r
  by_cases hr : r ≤ d
  · have hmap : Measurable (fun x : {x : Matrix (Fin d) (Fin d) ℂ ×
        rankUnitaryProduct d // x.1.rank = r} ↦
        ((⟨x.val.1, x.property⟩ : {P : Matrix (Fin d) (Fin d) ℂ // P.rank = r}),
          x.val.2 ⟨r, Nat.lt_succ_of_le hr⟩)) :=
      ((measurable_fst.comp measurable_subtype_coe).subtype_mk).prodMk
        ((measurable_pi_apply (⟨r, Nat.lt_succ_of_le hr⟩ : Fin (d + 1))).comp
          (measurable_snd.comp measurable_subtype_coe))
    have h := (measurable_randomSubspace_rangeOrthonormalBasis_projection
      (d := d) (r := r) (Finset.univ.map (Fin.castLEEmb (Nat.min_le_right (s r) r)))).comp hmap
    convert h using 1
    funext x
    rw [show s x.val.1.rank = s r from congrArg s x.property]
    rw [randomRangeSubspace_eq_on_rank ⟨x.val.1, x.property⟩ (s r) x.val.2 hr]
    rfl
  · let : IsEmpty {x : Matrix (Fin d) (Fin d) ℂ × rankUnitaryProduct d // x.1.rank = r} :=
      ⟨fun x ↦ hr (x.property ▸ x.val.1.rank_le_width)⟩
    exact measurable_of_empty _

/-- The ambient orthogonal projector of the actual sample is jointly
Borel in an arbitrary input matrix and the fixed finite unitary product. -/
theorem measurable_randomRangeSubspace_projection {d : ℕ} (s : ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℂ × rankUnitaryProduct d ↦
      (toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
        (randomRangeSubspace p.1 s p.2).starProjection) :=
  measurable_randomRangeSubspace_projection_rank_size (fun _ ↦ s)

/-- A fixed finite operator family applied to the actual sample with
rank-dependent requested size has a jointly Borel support projector.
Auxiliary to ALVV, arXiv:1602.08828v2, Lemma l:rs, lines 530–558. -/
theorem measurable_familySupportProj_randomRangeSubspace_rank_size
    {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m] {d : ℕ}
    (F : ι → Matrix m (Fin d) ℂ) (s : ℕ → ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℂ × rankUnitaryProduct d ↦
      familySupportProj (fun i ↦ F i *
        (toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
          (randomRangeSubspace p.1 (s p.1.rank) p.2).starProjection)) :=
  (measurable_familySupportProj_mul F).comp (measurable_randomRangeSubspace_projection_rank_size s)

/-- Applying a fixed finite operator family to the actual canonical
sample has a Borel support projector, jointly in input matrix and unitaries. -/
theorem measurable_familySupportProj_randomRangeSubspace
    {ι m : Type*} [Fintype ι] [Fintype m] [DecidableEq m] {d : ℕ}
    (F : ι → Matrix m (Fin d) ℂ) (s : ℕ) :
    Measurable (fun p : Matrix (Fin d) (Fin d) ℂ × rankUnitaryProduct d ↦
      familySupportProj (fun i ↦ F i *
        (toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).symm
          (randomRangeSubspace p.1 s p.2).starProjection)) :=
  measurable_familySupportProj_randomRangeSubspace_rank_size F (fun _ ↦ s)

end Matrix
