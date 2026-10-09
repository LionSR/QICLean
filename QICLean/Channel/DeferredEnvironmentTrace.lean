/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Channel.PartialTrace
import QICLean.Algebra.MatrixReindexUnitary

/-!
# Deferring the trace of a previously used environment

After a first operation on a system and its environment, a second operation can use a
fresh environment while leaving the earlier one untouched. Tracing both environments
only after the second operation gives the composition of the two reduced maps. The
intermediate system and earlier environment may be arbitrarily correlated.

The identities below are on complete operator spaces. The explicit rearrangement of
product indices describes which factor each operation acts on; it does not assert
that an intersite rearrangement is an available free physical gate.
-/

open Matrix
open scoped BigOperators Kronecker

namespace Matrix.DeferredEnvironment

noncomputable section

variable {S E F : Type*}

/-- Put the fresh environment beside the system, leaving the old environment last. -/
def freshEnvironmentEquiv (S E F : Type*) : ((S × E) × F) ≃ ((S × F) × E) :=
  (Equiv.prodAssoc S E F).trans (Matrix.rightSplitEquiv (Equiv.prodComm E F))

@[simp] theorem freshEnvironmentEquiv_apply (s : S) (e : E) (f : F) :
    freshEnvironmentEquiv S E F ((s, e), f) = ((s, f), e) := rfl

@[simp] theorem freshEnvironmentEquiv_symm_apply (s : S) (e : E) (f : F) :
    (freshEnvironmentEquiv S E F).symm ((s, f), e) = ((s, e), f) := rfl

/-- Act on the system and fresh environment, as the identity on the earlier environment. -/
def freshEnvironmentOp (E : Type*) [DecidableEq E]
    (V : Matrix (S × F) (S × F) ℂ) : Matrix ((S × E) × F) ((S × E) × F) ℂ :=
  Matrix.reindex (freshEnvironmentEquiv S E F).symm (freshEnvironmentEquiv S E F).symm
    (V ⊗ₖ (1 : Matrix E E ℂ))

variable [Fintype E] [Fintype F]

/-- The order in which old and fresh environments are discarded does not matter. -/
theorem partialTraceRight_freshEnvironmentEquiv
    (X : Matrix ((S × E) × F) ((S × E) × F) ℂ) :
    partialTraceRight (partialTraceRight X) =
      partialTraceRight (partialTraceRight
        (Matrix.reindex (freshEnvironmentEquiv S E F) (freshEnvironmentEquiv S E F) X)) := by
  rw [partialTraceRight_partialTraceRight, partialTraceRight_partialTraceRight]
  exact partialTraceRight_submatrix_right (Equiv.prodComm F E)
    (X.submatrix (Equiv.prodAssoc S E F).symm (Equiv.prodAssoc S E F).symm)

omit [Fintype F] in
/-- Discarding an old, possibly correlated environment commutes with adding a fresh factor. -/
theorem partialTraceRight_freshInput (Y : Matrix (S × E) (S × E) ℂ)
    (τ : Matrix F F ℂ) :
    partialTraceRight
      (Matrix.reindex (freshEnvironmentEquiv S E F) (freshEnvironmentEquiv S E F) (Y ⊗ₖ τ)) =
        partialTraceRight Y ⊗ₖ τ := by
  ext ⟨s, f⟩ ⟨t, g⟩
  simp only [partialTraceRight_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    freshEnvironmentEquiv_symm_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

variable [Fintype S] [DecidableEq E]

/-- The second operation leaves the old environment untouched, including all correlations. -/
theorem partialTraceRight_freshEnvironmentOp
    (V : Matrix (S × F) (S × F) ℂ)
    (X : Matrix ((S × E) × F) ((S × E) × F) ℂ) :
    partialTraceRight (Matrix.reindex (freshEnvironmentEquiv S E F)
      (freshEnvironmentEquiv S E F) (freshEnvironmentOp E V * X * (freshEnvironmentOp E V)ᴴ)) =
        V * partialTraceRight
          (Matrix.reindex (freshEnvironmentEquiv S E F) (freshEnvironmentEquiv S E F) X) *
          Vᴴ := by
  classical
  let R := Matrix.reindexAlgEquiv ℂ ℂ (freshEnvironmentEquiv S E F)
  have hstar (A : Matrix ((S × E) × F) ((S × E) × F) ℂ) : R Aᴴ = (R A)ᴴ := rfl
  change partialTraceRight (R (R.symm (V ⊗ₖ 1) * X * (R.symm (V ⊗ₖ 1))ᴴ)) =
    V * partialTraceRight (R X) * Vᴴ
  simp only [map_mul, hstar, R.apply_symm_apply]
  exact partialTraceRight_kronecker_conj_of_right_isometry V (1 : Matrix E E ℂ)
    (by simp) (R X)

/-- A fresh-environment operation may be performed before discarding an arbitrarily
correlated old environment. No product-state assumption on the intermediate input is needed. -/
theorem trace_deferred_freshEnvironment
    (V : Matrix (S × F) (S × F) ℂ) (Y : Matrix (S × E) (S × E) ℂ)
    (τ : Matrix F F ℂ) :
    partialTraceRight (partialTraceRight
      (freshEnvironmentOp E V * (Y ⊗ₖ τ) * (freshEnvironmentOp E V)ᴴ)) =
        partialTraceRight (V * (partialTraceRight Y ⊗ₖ τ) * Vᴴ) := by
  rw [partialTraceRight_freshEnvironmentEquiv, partialTraceRight_freshEnvironmentOp,
    partialTraceRight_freshInput]

variable [DecidableEq F]

/-- Two successive environment dilations compose with both partial traces deferred to
one final discard. The initial operator and both environment matrices are arbitrary. -/
theorem deferredEnvironment_comp
    (U : Matrix (S × E) (S × E) ℂ) (V : Matrix (S × F) (S × F) ℂ)
    (X : Matrix S S ℂ) (σ : Matrix E E ℂ) (τ : Matrix F F ℂ) :
    partialTraceRight (partialTraceRight
      ((freshEnvironmentOp E V * (U ⊗ₖ (1 : Matrix F F ℂ))) * ((X ⊗ₖ σ) ⊗ₖ τ) *
        (freshEnvironmentOp E V * (U ⊗ₖ (1 : Matrix F F ℂ)))ᴴ)) =
      partialTraceRight
        (V * (partialTraceRight (U * (X ⊗ₖ σ) * Uᴴ) ⊗ₖ τ) * Vᴴ) := by
  have hfirst : (U ⊗ₖ (1 : Matrix F F ℂ)) * ((X ⊗ₖ σ) ⊗ₖ τ) *
      (U ⊗ₖ (1 : Matrix F F ℂ))ᴴ = (U * (X ⊗ₖ σ) * Uᴴ) ⊗ₖ τ := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      ← mul_kronecker_mul, one_mul, mul_one]
  have hcomp :
      (freshEnvironmentOp E V * (U ⊗ₖ (1 : Matrix F F ℂ))) * ((X ⊗ₖ σ) ⊗ₖ τ) *
        (freshEnvironmentOp E V * (U ⊗ₖ (1 : Matrix F F ℂ)))ᴴ =
      freshEnvironmentOp E V * ((U * (X ⊗ₖ σ) * Uᴴ) ⊗ₖ τ) *
        (freshEnvironmentOp E V)ᴴ := by
    rw [conjTranspose_mul]
    calc
      _ = freshEnvironmentOp E V *
          ((U ⊗ₖ (1 : Matrix F F ℂ)) * ((X ⊗ₖ σ) ⊗ₖ τ) *
            (U ⊗ₖ (1 : Matrix F F ℂ))ᴴ) * (freshEnvironmentOp E V)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hfirst]
  rw [hcomp]
  exact trace_deferred_freshEnvironment V (U * (X ⊗ₖ σ) * Uᴴ) τ

variable [DecidableEq S]

/-- Extending a unitary by the identity on the old environment preserves unitarity. -/
theorem freshEnvironmentOp_mem_unitary {V : Matrix (S × F) (S × F) ℂ}
    (hV : V ∈ unitary (Matrix (S × F) (S × F) ℂ)) :
    freshEnvironmentOp E V ∈ unitary (Matrix ((S × E) × F) ((S × E) × F) ℂ) :=
  Matrix.reindex_mem_unitaryGroup (freshEnvironmentEquiv S E F).symm _
    (Matrix.kronecker_mem_unitary hV (Submonoid.one_mem _))

/-- The deferred-discard composition uses an actual unitary on the joint system. -/
theorem deferredEnvironment_comp_mem_unitary
    {U : Matrix (S × E) (S × E) ℂ} {V : Matrix (S × F) (S × F) ℂ}
    (hU : U ∈ unitary (Matrix (S × E) (S × E) ℂ))
    (hV : V ∈ unitary (Matrix (S × F) (S × F) ℂ)) :
    freshEnvironmentOp E V * (U ⊗ₖ (1 : Matrix F F ℂ)) ∈
      unitary (Matrix ((S × E) × F) ((S × E) × F) ℂ) :=
  Submonoid.mul_mem _ (freshEnvironmentOp_mem_unitary hV)
    (Matrix.kronecker_mem_unitary hU (Submonoid.one_mem _))

end

end Matrix.DeferredEnvironment
