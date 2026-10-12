/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.Representation.ReplicaTransport.Energy
import QICLean.Analysis.PositiveProjectionCompression
import QICLean.Analysis.IsometricIntertwiningCommute
import QICLean.Analysis.OperatorMean.MeanTreeIntertwine
import QICLean.Analysis.Transport.FilteringIntertwine

/-!
# The transport root in supplied symmetric coordinates

The actual transport root intertwines with the ordered product of the
means of its compressed raw band metrics. The terminal labels, weighted
tree, interpolation parameter and symmetric coordinates are retained.

The statement concerns arbitrary admissible transport data. Identifying
physical regions and changing the description of the sites are separate
applications. Real powers and the filtering normalization can subsequently
be transported by the existing rectangular-intertwining theorems.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, `06-transport.tex`, `transport:means`, lines 57--61,
120--128 and 268--286; `07-comparators.tex`, `comparator:metrics`,
lines 80--110, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix PermutationRepresentation Entropy
open scoped Matrix ComplexOrder MatrixOrder unitInterval

noncomputable section

namespace TensorPower.ReplicaTransport.TransportData

/-- The root of the actual transport tree intertwines with the ordered
product of the means of its compressed raw band metrics. Both sides use
the same supplied isometry, terminal labels and interpolation parameter.

Source: area-law manuscript, `06-transport.tex`, `transport:means`, lines
57--61, 120--128 and 268--286; `07-comparators.tex`, `comparator:metrics`,
lines 80--110, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem rootPath_compressed_bandProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (n : V → ℕ) [∀ v, NeZero (n v)]
    {K : ℕ} {H : Type*} [DecidableEq H] {C : H → Type*}
    [∀ h, DecidableEq (C h)]
    (D : TransportData V K H C) (hD : D.IsAdmissible)
    {t : ℝ} (ht : 0 ≤ t) (k d : ℕ)
    (hcomm : D.CrossBandCommute n t k)
    (Z : Matrix (Config k (fun v ↦ Fin (n v))) (Fin d) ℂ)
    (hZ : Zᴴ * Z = 1)
    (hZZ : Z * Zᴴ = symProj (copyPerm (SiteConfig n) k)) (p : ℝ) :
    let T := D.tree (Set.projIcc (0 : ℝ) 1 zero_le_one p)
    let A := fun j g ↦ bandMetric n t k (D.leafPart j g)
    let B := fun j g ↦ Zᴴ * A j g * Z
    let M := (List.ofFn fun g : Fin K ↦ T.eval (B · g)).prod
    M.PosDef ∧ D.rootPath n t k p * Z = Z * M := by
  classical
  intro T A B M
  have hleaf (j : Σ h, Option (C h)) (g : Fin K) :
      (B j g).PosDef ∧ A j g * Z = Z * B j g :=
    let h := (posDef_bandMetric
      (D.isPartition_leafPart hD j g) ht k).compression_of_projection_intertwine hZ hZZ
      (commute_symProj_bandMetric t k (D.leafPart j g)).symm.eq
      (commute_symProj_bandMetric t k (D.leafPart j g)).symm
    ⟨h.2.1, h.2.2.1⟩
  have hPZ : symProj (copyPerm (SiteConfig n) k) * Z = Z := by
    rw [← hZZ, Matrix.mul_assoc, hZ, Matrix.mul_one]
  have hext (j : Σ h, Option (C h)) (g : Fin K) :
      symBandMetric n t k (D.leafPart j g) * Z = Z * B j g := by
    simpa only [symBandMetric, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
      (commute_symProj_bandMetric t k (D.leafPart j g)).eq, Matrix.mul_assoc,
      hPZ, sub_self, add_zero] using (hleaf j g).2
  have hBcomm (j j' : Σ h, Option (C h)) (g g' : Fin K) (hgg' : g ≠ g') :
      Commute (B j g) (B j' g') :=
    Matrix.commute_of_isometric_intertwine hZ (hext j g) (hext j' g')
      ((D.crossBandCommute_iff (n := n) t k).mp hcomm j j' g g' hgg')
  have hM : M.PosDef :=
    MeanTree.posDef_listProd_ofFn
      (fun g ↦ MeanTree.posDef_eval (fun j ↦ (hleaf j g).1) T)
      (fun g g' hgg' ↦ MeanTree.commute_eval_band
        (fun j g ↦ (hleaf j g).1) hBcomm T hgg')
  done

end TensorPower.ReplicaTransport.TransportData
