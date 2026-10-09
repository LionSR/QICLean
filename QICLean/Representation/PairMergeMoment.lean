/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.MergeMoment
import QICLean.Algebra.PositiveSemidefiniteNormalization
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Merge moments on paired copy spaces

For two finite bases `Q` and `C`, the copy space has literal basis
`(Fin m → Q) × (Fin m → C)`. The separate copy actions move one factor
and fix the other; their product is the simultaneous copy action.

A positive matrix invariant under the two separate actions satisfies the
Schur-label merge-moment bound with polynomial exponent
`(Fintype.card Q * Fintype.card C)^2`. The trace-one form is transported
from the finite-family theorem. Total trace normalization gives the
homogeneous form, with the actual trace mass on the right side. Zero
copies, empty bases and zero-trace components are included.

OpenAI, *A two-dimensional area law from a global spectral gap*
(September 24, 2026), `05-replicas.tex`, lines 14–27 and 112–115,
`replicas:merge-moment`; `07-comparators.tex`, lines 520–549,
`comparator:merge-moments`, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The construction of the physical components, their separate invariance,
and the exponential deficit interpretation are additional assertions.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/
/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/05-replicas.tex
Label: sec:replicas.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/05-replicas.tex
Label: sec:replicas.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/05-replicas.tex
Label: sec:replicas.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/05-replicas.tex
Label: sec:replicas.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/05-replicas.tex
Label: sec:replicas.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/05-replicas.tex
Label: replicas:merge-moment.
-/

/-
Source: September 24, 2026.
Independently formalized; no upstream Lean proof text reused.
Manuscript: preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/
build/sections/07-comparators.tex
Label: comparator:merge-moments.
-/

open Matrix PermutationRepresentation
open scoped ComplexOrder
namespace TensorPower

private def productPermAction {G X Y : Type*} [Group G]
    (φ : G →* Equiv.Perm X) (ψ : G →* Equiv.Perm Y) : G →* Equiv.Perm (X × Y) where
  toFun σ := Equiv.prodCongr (φ σ) (ψ σ)
  map_one' := by ext <;> simp
  map_mul' σ τ := by ext <;> simp

variable (Q C : Type*) (m : ℕ)

/-- Permute the Q copies and leave the C copies fixed.
OpenAI, September 24, 2026, `05-replicas.tex`, lines 24–27. -/
def pairCopyLeft : Equiv.Perm (Fin m) →* Equiv.Perm ((Fin m → Q) × (Fin m → C)) :=
  productPermAction (copyPerm Q m) 1

/-- Permute the C copies and leave the Q copies fixed.
OpenAI, September 24, 2026, `05-replicas.tex`, lines 24–27. -/
def pairCopyRight : Equiv.Perm (Fin m) →* Equiv.Perm ((Fin m → Q) × (Fin m → C)) :=
  productPermAction 1 (copyPerm C m)

/-- Permute the Q and C copies simultaneously.
OpenAI, September 24, 2026, `05-replicas.tex`, lines 24–27. -/
def pairCopyBoth : Equiv.Perm (Fin m) →* Equiv.Perm ((Fin m → Q) × (Fin m → C)) :=
  productPermAction (copyPerm Q m) (copyPerm C m)

/-- Copy permutations of the two separate factors commute.
OpenAI, September 24, 2026, `05-replicas.tex`, lines 24–27. -/
theorem commute_pairCopy (σ τ : Equiv.Perm (Fin m)) :
    Commute (pairCopyLeft Q C m σ) (pairCopyRight Q C m τ) := by
  ext <;> rfl

/-- The simultaneous action is the product of the two separate actions.
OpenAI, September 24, 2026, `05-replicas.tex`, lines 24–27. -/
theorem pairCopyBoth_eq_mul (σ : Equiv.Perm (Fin m)) :
    pairCopyBoth Q C m σ = pairCopyLeft Q C m σ * pairCopyRight Q C m σ := by
  ext <;> rfl

universe u v

private def pairFamily (Q : Type u) (C : Type v) (i : Fin 2) : Type (max u v) :=
  Fin.cases (ULift.{v} Q) (fun _ => ULift.{u} C) i

private instance pairFamilyFintype [Fintype Q] [Fintype C] (i : Fin 2) :
    Fintype (pairFamily Q C i) := by
  refine Fin.cases ?_ (fun _ => ?_) i <;> dsimp [pairFamily] <;> infer_instance

private instance pairFamilyDecidableEq [DecidableEq Q] [DecidableEq C] (i : Fin 2) :
    DecidableEq (pairFamily Q C i) := by
  refine Fin.cases ?_ (fun _ => ?_) i <;> dsimp [pairFamily] <;> infer_instance

private def pairConfigEquiv : Config m (pairFamily Q C) ≃
    ((Fin m → Q) × (Fin m → C)) :=
  (Equiv.piCongrRight fun _ => (piFinTwoEquiv (pairFamily Q C)).trans
    (Equiv.prodCongr Equiv.ulift Equiv.ulift)).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Q) (fun _ => C))

private lemma pairConfig_left (σ : Equiv.Perm (Fin m)) (x : Config m (pairFamily Q C)) :
    pairConfigEquiv Q C m (subsystemPerm m (pairFamily Q C) {0} σ x) =
      pairCopyLeft Q C m σ (pairConfigEquiv Q C m x) := by
  ext j <;> simp [pairConfigEquiv, pairCopyLeft, productPermAction, subsystemPerm_apply,
    copyPerm_apply, Equiv.prodCongr]

private lemma pairConfig_right (σ : Equiv.Perm (Fin m)) (x : Config m (pairFamily Q C)) :
    pairConfigEquiv Q C m (subsystemPerm m (pairFamily Q C) {0}ᶜ σ x) =
      pairCopyRight Q C m σ (pairConfigEquiv Q C m x) := by
  ext j <;> simp [pairConfigEquiv, pairCopyRight, productPermAction, subsystemPerm_apply,
    copyPerm_apply, Equiv.prodCongr]

private lemma pairConfig_both (σ : Equiv.Perm (Fin m)) (x : Config m (pairFamily Q C)) :
    pairConfigEquiv Q C m (copyPerm ((i : Fin 2) → pairFamily Q C i) m σ x) =
      pairCopyBoth Q C m σ (pairConfigEquiv Q C m x) := by
  ext j <;> rfl

private lemma permOp_submatrix {G X Y : Type*} [Group G]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (φ : G →* Equiv.Perm X) (ψ : G →* Equiv.Perm Y)
    (he : ∀ g x, e (φ g x) = ψ g (e x)) (g : G) :
    (permOp ψ g).submatrix e e = permOp φ g := by
  ext x y
  simp only [submatrix_apply, permOp_apply_apply, ← he g y, e.injective.eq_iff]

private lemma labelProj_submatrix {G X Y : Type*} [Group G] [Fintype G]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (φ : G →* Equiv.Perm X) (ψ : G →* Equiv.Perm Y)
    (he : ∀ g x, e (φ g x) = ψ g (e x)) (l : IrrepLabel G) :
    (labelProj ψ l).submatrix e e = labelProj φ l := by
  ext x y
  simp only [labelProj, groupAlgebraRep_eq_sum, submatrix_apply, Matrix.sum_apply,
    Matrix.smul_apply]
  simp_rw [← submatrix_apply (permOp ψ _), permOp_submatrix e φ ψ he]

private lemma trace_submatrix {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (M : Matrix Y Y ℂ) : (M.submatrix e e).trace = M.trace := by
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private lemma commute_submatrix {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) {M N : Matrix Y Y ℂ} (h : Commute M N) :
    Commute (M.submatrix e e) (N.submatrix e e) := by
  change M.submatrix e e * N.submatrix e e = N.submatrix e e * M.submatrix e e
  simp only [submatrix_mul_equiv, h.eq]

private lemma card_pairFamily [Fintype Q] [Fintype C] :
    Fintype.card ((i : Fin 2) → pairFamily Q C i) = Fintype.card Q * Fintype.card C := by
  simpa using Fintype.card_congr ((piFinTwoEquiv (pairFamily Q C)).trans
    (Equiv.prodCongr Equiv.ulift Equiv.ulift))

variable [Fintype Q] [Fintype C] [DecidableEq Q] [DecidableEq C]

/-- The merge moment on the literal paired copy basis.

This is the paired-coordinate form of OpenAI, September 24, 2026,
`05-replicas.tex`, lines 112–115, equation `replicas:merge-moment`.
The actual density is positive, has trace one and is invariant under each
separate copy action. No additional representation or multiplicity premise
is supplied. The statement includes zero copies and empty finite factors. -/
theorem pair_merge_moment_le
    {ρ : Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (hρQ : ∀ σ, Commute (permOp (pairCopyLeft Q C m) σ) ρ)
    (hρC : ∀ σ, Commute (permOp (pairCopyRight Q C m) σ) ρ) {b : ℝ} (hb : b ≤ 1) :
    ∑ l, ∑ μ, ∑ ν, (ρ * (labelProj (pairCopyLeft Q C m) l *
        labelProj (pairCopyRight Q C m) μ * labelProj (pairCopyBoth Q C m) ν)).trace.re *
        (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b ≤
      ((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) := by
  let e := pairConfigEquiv Q C m
  have hρQ' : ∀ σ, Commute (permOp (subsystemPerm m (pairFamily Q C) {0}) σ)
      (ρ.submatrix e e) := by
    intro σ
    have h := commute_submatrix e (hρQ σ)
    rwa [permOp_submatrix e _ _ (pairConfig_left Q C m)] at h
  have hρC' : ∀ σ, Commute (permOp (subsystemPerm m (pairFamily Q C) {0}ᶜ) σ)
      (ρ.submatrix e e) := by
    intro σ
    have h := commute_submatrix e (hρC σ)
    rwa [permOp_submatrix e _ _ (pairConfig_right Q C m)] at h
  have h := merge_moment_le (ι := pairFamily Q C) (k := m) {0} (hρ.submatrix e)
    (by rw [trace_submatrix e, htr]) hρQ' hρC' hb
  rw [card_pairFamily Q C] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  congr 1
  rw [← trace_submatrix e (ρ * (labelProj (pairCopyLeft Q C m) l *
    labelProj (pairCopyRight Q C m) μ * labelProj (pairCopyBoth Q C m) ν))]
  simp only [← submatrix_mul_equiv _ _ e e e]
  rw [labelProj_submatrix e _ _ (pairConfig_left Q C m),
    labelProj_submatrix e _ _ (pairConfig_right Q C m),
    labelProj_submatrix e _ _ (pairConfig_both Q C m)]

/-- The paired merge moment for an unnormalized positive component.

OpenAI, September 24, 2026, `05-replicas.tex`, lines 112–115,
`replicas:merge-moment`; `07-comparators.tex`, lines 520–549,
`comparator:merge-moments`. The right side retains the actual component
trace mass. Empty bases and zero-trace components are included; no
positive-mass hypothesis or physical component certificate is supplied. -/
theorem pair_merge_moment_le_mul_trace
    {ρ : Matrix ((Fin m → Q) × (Fin m → C)) ((Fin m → Q) × (Fin m → C)) ℂ}
    (hρ : ρ.PosSemidef)
    (hρQ : ∀ σ, Commute (permOp (pairCopyLeft Q C m) σ) ρ)
    (hρC : ∀ σ, Commute (permOp (pairCopyRight Q C m) σ) ρ) {b : ℝ} (hb : b ≤ 1) :
    ∑ l, ∑ μ, ∑ ν, (ρ * (labelProj (pairCopyLeft Q C m) l *
        labelProj (pairCopyRight Q C m) μ * labelProj (pairCopyBoth Q C m) ν)).trace.re *
        (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b ≤
      ((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) * ρ.trace.re := by
  classical
  by_cases hX : Nonempty ((Fin m → Q) × (Fin m → C))
  · let _ : Nonempty ((Fin m → Q) × (Fin m → C)) := hX
    let x₀ : (Fin m → Q) × (Fin m → C) := Classical.arbitrary _
    let η := normalizePosSemidef x₀ ρ
    have hη : η.PosSemidef := normalizePosSemidef_posSemidef x₀ hρ
    have htr : η.trace = 1 := normalizePosSemidef_trace x₀ hρ
    have hf : (ρ.trace.re : ℂ) • η = ρ := trace_re_smul_normalizePosSemidef x₀ hρ
    have hinv (φ : Equiv.Perm (Fin m) →* Equiv.Perm ((Fin m → Q) × (Fin m → C)))
        (hφ : ∀ σ, Commute (permOp φ σ) ρ) (σ : Equiv.Perm (Fin m)) :
        Commute (permOp φ σ) η := by
      dsimp [η, normalizePosSemidef]
      split_ifs
      · convert (Commute.one_right (permOp φ σ)).smul_right
          ((Fintype.card ((Fin m → Q) × (Fin m → C)) : ℂ)⁻¹) using 1
        ext i j
        by_cases hij : i = j <;> simp [Matrix.smul_apply, hij]
      · exact (hφ σ).smul_right (((ρ.trace.re)⁻¹ : ℝ) : ℂ)
    have h := pair_merge_moment_le Q C m hη htr
      (hinv (pairCopyLeft Q C m) hρQ) (hinv (pairCopyRight Q C m) hρC) hb
    have hterm (P : Matrix ((Fin m → Q) × (Fin m → C))
        ((Fin m → Q) × (Fin m → C)) ℂ) :
        (ρ * P).trace.re = ρ.trace.re * (η * P).trace.re := by
      calc
        _ = (((ρ.trace.re : ℂ) • η) * P).trace.re :=
          congrArg (fun M : Matrix _ _ ℂ => (M * P).trace.re) hf.symm
        _ = _ := by
          simp only [smul_mul_assoc, trace_smul, smul_eq_mul, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      _ = ρ.trace.re * (∑ l, ∑ μ, ∑ ν,
          (η * (labelProj (pairCopyLeft Q C m) l * labelProj (pairCopyRight Q C m) μ *
            labelProj (pairCopyBoth Q C m) ν)).trace.re *
            (((l.dim * μ.dim : ℕ) : ℝ) / ν.dim) ^ b) := by
        simp_rw [hterm]
        simp only [Finset.mul_sum, mul_assoc]
      _ ≤ ρ.trace.re * ((m + 1) ^ ((Fintype.card Q * Fintype.card C) ^ 2) : ℕ) :=
        mul_le_mul_of_nonneg_left h (Complex.nonneg_iff.mp hρ.trace_nonneg).1
      _ = _ := mul_comm _ _
  · have : IsEmpty ((Fin m → Q) × (Fin m → C)) := not_nonempty_iff.mp hX
    have hzero : ρ = 0 := Subsingleton.elim _ _
    simp [hzero]

end TensorPower
