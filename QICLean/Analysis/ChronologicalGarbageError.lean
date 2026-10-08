/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Analysis.SourceOnlyDensityError
import QICLean.Analysis.ChronologicalGarbage

/-!
# Marked approximation with actual chronological garbage

The replacement circuit keeps all earlier inventory registers idle. Only
marked stages use rescaled replacement maps; all other stages use the exact
working-memory gate and append its supplied ideal inventory vector. Applying
the actual final readout and discarding both inventories and the originally
owned register gives a physical density within `4 |S| δ` of the ORIGINAL
working circuit's density. The proof identifies the ideal discarded density
by an exact register calculation, rather than assuming a density identity.

Per-gate inventory spaces, vectors and replacement maps are caller data.
Their effect-elimination construction, party ownership and source-only
generated semantics remain separate. No output is renormalized and no
memory, inventory or discarded-register dimension enters the bound.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
Theorem 5.2, `eq:compression-effect-circuit-error`, `04-compression.tex:199–229`,
immutable revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are original proofs; no OpenAI Lean code is copied or adapted.
-/

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

namespace Matrix

variable {D B : ℕ → Type*}
  [∀ t, Fintype (D t)] [∀ t, DecidableEq (D t)]
  [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

/-- Use the supplied replacement at marked stages, rescaled by `1 + δ`;
every other stage is exactly the ideal gate with its fresh pure inventory. -/
def markedChronologicalGarbageChain
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (A : (t : ℕ) → Matrix (D (t + 1) × B t) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (S : Finset ℕ) (δ : ℝ) :
    (t : ℕ) → Matrix (D (t + 1) × garbageInventory B (t + 1))
      (D t × garbageInventory B t) ℂ :=
  markedRescaledGateChain (D := fun t ↦ D t × garbageInventory B t)
    (chronologicalGarbageChain G γ) (chronologicalReplacementChain A) S δ

variable {P E : Type*} [Fintype E]

/-- Physical density of an actual augmented gate chain. The common readout
acts as `K ⊗ I`; first discard the accumulated inventory, then the originally
owned readout register. The initial inventory has the scalar coefficient one. -/
def chronologicalGarbageDensity
    (H : (t : ℕ) → Matrix (D (t + 1) × garbageInventory B (t + 1))
      (D t × garbageInventory B t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ)
    (K : Matrix (P × E) (D n) ℂ) : Matrix P P ℂ :=
  partialTraceRight (sourceOnlyReadoutDensity
    (D := fun t ↦ D t × garbageInventory B t) H
    (euclideanTensorVector ψ (cumulativeGarbageVector γ 0)) n
    (K ⊗ₖ (1 : Matrix (garbageInventory B n) (garbageInventory B n) ℂ)))

/-- The actual ideal augmented circuit has exactly the original physical
density, for arbitrary gates, input and common readout. -/
theorem chronologicalGarbageDensity_ideal
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (hγ : ∀ t, ‖γ t‖ = 1)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ) :
    chronologicalGarbageDensity (chronologicalGarbageChain G γ) γ ψ n K =
      sourceOnlyReadoutDensity G ψ n K := by
  simpa only [chronologicalGarbageDensity, sourceOnlyReadoutDensity,
    sourceOnlyReadoutVector, chronologicalGarbageReadout, toLpLin_mul_same,
    LinearMap.comp_apply] using chronologicalGarbageReadout_discard_density G γ hγ ψ n K

/-- An empty marked set retains the original physical density exactly,
regardless of the circuit length, replacement maps or approximation scale. -/
@[simp]
theorem chronologicalGarbageDensity_marked_empty
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (A : (t : ℕ) → Matrix (D (t + 1) × B t) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (hγ : ∀ t, ‖γ t‖ = 1)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ) (δ : ℝ) :
    chronologicalGarbageDensity (markedChronologicalGarbageChain G A γ ∅ δ) γ ψ n K =
      sourceOnlyReadoutDensity G ψ n K := by
  have heq : markedChronologicalGarbageChain G A γ ∅ δ = chronologicalGarbageChain G γ := by
    funext t
    simp only [markedChronologicalGarbageChain, markedRescaledGateChain,
      Finset.notMem_empty, ↓reduceIte]
  rw [heq]
  exact chronologicalGarbageDensity_ideal G γ hγ ψ n K

/-- Zero stages give the original physical density even when future fresh
spaces are empty and their vectors are unnormalized. No gate is evaluated. -/
@[simp]
theorem chronologicalGarbageDensity_zero
    (H : (t : ℕ) → Matrix (D (t + 1) × garbageInventory B (t + 1))
      (D t × garbageInventory B t) ℂ)
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (ψ : EuclideanSpace ℂ (D 0))
    (K : Matrix (P × E) (D 0) ℂ) :
    chronologicalGarbageDensity H γ ψ 0 K = sourceOnlyReadoutDensity G ψ 0 K := by
  have hzero : ‖cumulativeGarbageVector γ 0‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    simp [cumulativeGarbageVector, EuclideanSpace.norm_sq_eq]
  simp only [chronologicalGarbageDensity, sourceOnlyReadoutDensity,
    sourceOnlyReadoutVector, contractionPrefix, Matrix.mul_one]
  rw [kronecker_one_tensorVector, partialTraceRight_tensorVector _ _ hzero]

variable [Fintype P] [DecidableEq P]

/-- The actual marked replacement circuit's physical density is within
`4 |S| δ` of the ORIGINAL circuit's density. Only marked replacement maps
need approximate their ideal appended-vector gates. The marked set may contain
stages beyond `n`; they merely weaken the bound. Source: Theorem 5.2,
`eq:compression-effect-circuit-error`, `04-compression.tex:199–229`. -/
theorem rectangularTraceNorm_chronologicalGarbageDensity_marked_sub_le
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (A : (t : ℕ) → Matrix (D (t + 1) × B t) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (hγ : ∀ t, ‖γ t‖ = 1)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (S : Finset ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ∀ t ∈ S, ‖A t - appendGarbageGate (G t) (γ t)‖ ≤ δ)
    (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm
      (chronologicalGarbageDensity (markedChronologicalGarbageChain G A γ S δ) γ ψ n K -
        sourceOnlyReadoutDensity G ψ n K) ≤ 4 * S.card * δ := by
  classical
  let ψ' := euclideanTensorVector ψ (cumulativeGarbageVector γ 0)
  let K' := K ⊗ₖ (1 : Matrix (garbageInventory B n) (garbageInventory B n) ℂ)
  have hψ' : ‖ψ'‖ ≤ 1 := by
    dsimp only [ψ']
    rw [norm_euclideanTensorVector, norm_cumulativeGarbageVector γ hγ 0, mul_one]
    exact hψ
  have hK' : ‖K'‖ ≤ 1 := (l2_opNorm_kronecker_one_le K).trans hK
  have herr : ∀ t ∈ S,
      ‖chronologicalReplacementChain A t - chronologicalGarbageChain G γ t‖ ≤ δ :=
    fun t ht ↦ (chronologicalReplacementChain_sub_norm_le A G γ t).trans (herror t ht)
  have hbound := rectangularTraceNorm_sourceOnlyReadoutDensity_marked_sub_le
    (D := fun t ↦ D t × garbageInventory B t)
    (chronologicalGarbageChain G γ) (chronologicalReplacementChain A) ψ' n K' S δ hδ
    (chronologicalGarbageChain_norm_le_one G γ hG hγ) herr hψ' hK'
  rw [← chronologicalGarbageDensity_ideal G γ hγ ψ n K]
  change rectangularTraceNorm (partialTraceRightLM _ - partialTraceRightLM _) ≤ _
  rw [← map_sub partialTraceRightLM]
  exact (rectangularTraceNorm_partialTraceRight_le _).trans hbound

/-- The paper's approximation scale `ε / (8 |S|)` gives the actual physical
density budget `ε / 2`, counting only marked occurrences. -/
theorem rectangularTraceNorm_chronologicalGarbageDensity_marked_sub_le_half
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (A : (t : ℕ) → Matrix (D (t + 1) × B t) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (hγ : ∀ t, ‖γ t‖ = 1)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ)
    (S : Finset ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hS : 0 < S.card) (hG : ∀ t, ‖G t‖ ≤ 1)
    (herror : ∀ t ∈ S, ‖A t - appendGarbageGate (G t) (γ t)‖ ≤ ε / (8 * S.card))
    (hψ : ‖ψ‖ ≤ 1) (hK : ‖K‖ ≤ 1) :
    rectangularTraceNorm
      (chronologicalGarbageDensity
        (markedChronologicalGarbageChain G A γ S (ε / (8 * S.card))) γ ψ n K -
        sourceOnlyReadoutDensity G ψ n K) ≤ ε / 2 := by
  have hδ : 0 ≤ ε / (8 * S.card) := div_nonneg hε (by positivity)
  have h := rectangularTraceNorm_chronologicalGarbageDensity_marked_sub_le G A γ hγ ψ n K S
    (ε / (8 * S.card)) hδ hG herror hψ hK
  have hS' : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  convert h using 1
  field_simp
  ring

/-- Empty marked set has zero absolute error against the original physical
density; no contraction or input normalization hypothesis is needed. -/
@[simp]
theorem rectangularTraceNorm_chronologicalGarbageDensity_marked_empty
    (G : (t : ℕ) → Matrix (D (t + 1)) (D t) ℂ)
    (A : (t : ℕ) → Matrix (D (t + 1) × B t) (D t) ℂ)
    (γ : (t : ℕ) → EuclideanSpace ℂ (B t)) (hγ : ∀ t, ‖γ t‖ = 1)
    (ψ : EuclideanSpace ℂ (D 0)) (n : ℕ) (K : Matrix (P × E) (D n) ℂ) (δ : ℝ) :
    rectangularTraceNorm
      (chronologicalGarbageDensity (markedChronologicalGarbageChain G A γ ∅ δ) γ ψ n K -
        sourceOnlyReadoutDensity G ψ n K) = 0 := by
  rw [chronologicalGarbageDensity_marked_empty G A γ hγ, sub_self, rectangularTraceNorm_zero]

end Matrix
