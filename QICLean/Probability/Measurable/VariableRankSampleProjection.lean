/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Probability.Measurable.CanonicalSampleProjectionMeasurable
import QICLean.Probability.Measurable.MatrixFamilySupportMeasurable
import QICLean.Analysis.Topology.MatrixRankClosed
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# A Borel canonical sampler with varying input rank

A fixed finite product contains one coordinate unitary for every possible
input rank. The actual existing random-subspace sampler uses the unitary
at the actual matrix rank and the canonical orthonormal basis of its range.
Thus the sample projector and its image under a fixed finite operator family
are jointly Borel across changes of input rank. This supports ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558. No adaptive probability
estimate or running-time conclusion is asserted here.

It also contains the following results.

* `Matrix.measurable_rank`, `measurable_of_matrix_rank_strata`: Borel gluing along matrix-rank
  strata.
-/

open MeasureTheory

section MatrixRankMeasurable

/-!
## Borel gluing along matrix-rank strata

Finite complex matrix rank is Borel. A map whose restrictions to the
rank strata of a Borel matrix-valued map are Borel is therefore Borel.
This elementary auxiliary permits varying input dimensions in ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558.
-/

namespace Matrix

/-- Finite complex matrix rank is a Borel function. -/
theorem measurable_rank {m n : Type*} [Finite m] [Fintype n] :
    Measurable (Matrix.rank : Matrix m n ℂ → ℕ) :=
  lowerSemicontinuous_rank.measurable

end Matrix

/-- Borel restrictions to the matrix-rank strata give a Borel map on the
whole domain. No measurable choice of bases is assumed. -/
theorem measurable_of_matrix_rank_strata {X Y m n : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [Finite m] [Fintype n]
    {P : X → Matrix m n ℂ} (hP : Measurable P) {f : X → Y}
    (hf : ∀ r : ℕ, Measurable (fun x : {x : X // (P x).rank = r} ↦ f x.val)) :
    Measurable f := by
  intro s hs
  have hstratum (r : ℕ) : MeasurableSet {x : X | (P x).rank = r} :=
    measurableSet_eq_fun (Matrix.measurable_rank.comp hP) measurable_const
  have heq : f ⁻¹' s = ⋃ r : ℕ,
      Subtype.val '' ((fun x : {x : X // (P x).rank = r} ↦ f x.val) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_image]
    constructor
    · intro hx
      exact ⟨(P x).rank, ⟨x, rfl⟩, hx, rfl⟩
    · rintro ⟨r, y, hy, rfl⟩
      exact hy
  rw [heq]
  exact MeasurableSet.iUnion fun r ↦ (hstratum r).subtype_image (hf r hs)

end MatrixRankMeasurable

section VariableRankSampleProjection

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

section RandomRangeSubspaceDimension

/-!
# The exact dimension of the canonical range sample

The existing canonical range sampler retains exactly min(s,rank P)
independent orthonormal coordinates. Any linear image of that actual
sample has dimension at most s, for every seed, including rank zero.
This is the deterministic dimension assertion in ALVV,
arXiv:1602.08828v2, Lemma `l:rs`, lines 530–558.
-/

namespace Matrix

/-- The actual canonical sample has exactly the retained coordinate count. -/
theorem finrank_randomRangeSubspace {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ)
    (s : ℕ) (U : rankUnitaryProduct d) :
    Module.finrank ℂ (randomRangeSubspace P s U) = min s P.rank := by
  change Module.finrank ℂ (Submodule.randomSubspace (rangeOrthonormalBasis ⟨P, rfl⟩)
    (Finset.univ.map (Fin.castLEEmb (Nat.min_le_right s P.rank)))
      (U ⟨P.rank, Nat.lt_succ_of_le P.rank_le_width⟩)) = _
  rw [Submodule.finrank_randomSubspace]
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Every linear image of the actual canonical sample has dimension at
most the nominal sample bound, without any viability condition. -/
theorem finrank_map_randomRangeSubspace_le {d : ℕ} {E : Type*}
    [AddCommGroup E] [Module ℂ E] (P : Matrix (Fin d) (Fin d) ℂ)
    (s : ℕ) (U : rankUnitaryProduct d) (f : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E) :
    Module.finrank ℂ ((randomRangeSubspace P s U).map f) ≤ s :=
  (Submodule.finrank_map_le _ _).trans ((finrank_randomRangeSubspace P s U).le.trans
    (Nat.min_le_left s P.rank))

end Matrix

end RandomRangeSubspaceDimension

end

end VariableRankSampleProjection
