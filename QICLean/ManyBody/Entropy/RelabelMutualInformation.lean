/-
Copyright (c) 2026 QICLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QICLean contributors
-/
import QICLean.ManyBody.Entropy.RegionEntropy
import QICLean.ManyBody.Sites.Relabel

/-!
# Regional mutual information under bijections of tensor factors

A bijection `e` of the sites, together with bijections of the basis labels, carries regions `D`
and `T` to regions `D'` and `T'`. The mutual information of `D'` and `T'` in the transported
vector is the mutual information of `D` and `T` in the original vector: each of the three
regional entropies is invariant (`ManyBody.regionEntropy_relabel`). No normalization or
disjointness is assumed.

This is TNLean's `ManyBody.regionMutualInformation_relabelSites`
(`Lattice/SiteRelabelEntropy`, at commit `707a50e56c`), stated for the transport
`ManyBody.relabelVector`.

## Main results

* `ManyBody.regionMutualInformation_relabel`.
-/

namespace ManyBody

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  {X : V → Type*} {X' : V' → Type*} [∀ v, Fintype (X v)] [∀ v, Fintype (X' v)]
  [∀ v, DecidableEq (X v)] [∀ v, DecidableEq (X' v)]

/-- **Mutual information is invariant under relabelling.** If `e` carries `D` to `D'` and `T`
to `T'`, the mutual information of `D'` and `T'` in the transported vector is the mutual
information of `D` and `T`. -/
theorem regionMutualInformation_relabel (D T : Finset V) (D' T' : Finset V') (e : V ≃ V')
    (hD : ∀ v, v ∈ D ↔ e v ∈ D') (hT : ∀ v, v ∈ T ↔ e v ∈ T') (f : ∀ v, X v ≃ X' (e v))
    (Ω : EuclideanSpace ℂ (Config X)) :
    regionMutualInformation (relabelVector e f Ω) D' T' = regionMutualInformation Ω D T := by
  have hU (v : V) : v ∈ D ∪ T ↔ e v ∈ D' ∪ T' := by
    rw [Finset.mem_union, Finset.mem_union, hD, hT]
  rw [regionMutualInformation, regionMutualInformation, regionEntropy_relabel D D' e hD f,
    regionEntropy_relabel T T' e hT f, regionEntropy_relabel (D ∪ T) (D' ∪ T') e hU f]

end ManyBody
