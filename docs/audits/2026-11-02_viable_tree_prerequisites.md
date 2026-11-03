# Fixed-target prerequisites for a viable-subspace tree

This contribution is based on the normalized-projection commit
`ca0aea30e44e2d56f2cf2620e4bae76325e8319b`, whose dependency base is
`ba01733099b5a18bed5c9bfb62f95f175b4c9b57`. It selectively recovers sixteen
mathematical modules from the preserved source revision
`24a2ee589c5ff8da34a5cc6d8b7026dc7700e929`. No existing mathematical
module is replaced by an older version.

The results retain the whole exterior in a regional cut, transport viability
through the actual tensor-coordinate diagrams, merge candidates for one
possibly entangled global target, construct sample-or-full spaces with
fixed-input measurable Haar success events, and apply actual ordered words
in a single improving family. The cubic dimension profile, corrected sampling
size and trimming radius are derived explicitly. These are prerequisites;
no recursive tree, adaptive probability bound, final spectral extraction or
running time is established by this QIC contribution.

## Source reconciliation

The sole change to a recovered Lean file is an import in `SubregionCut`:
`Channel.FiniteProduct` replaces the unnecessary `Entropy.RegionRank`.
The configuration equivalence is owned by the former, while the rank identity
uses the partial-trace coefficient formula already supplied by
`CutEnvironment`. Statements and proof bodies are unchanged. This removes
an unrelated entropy chain from the selected imports.

The blueprint additions are selective fragments. Existing entries are
preserved. Supporting results are stated as lemmas, retaining their historical
labels. The sampled-word statement refers to the sum of all word images,
not to each individual image. No source algorithm is marked complete.

## Verification

Each actual module passed strict private compilation separately. The provider
was the immutable warmed source revision `24a2ee58`; every reused selected
dependency source and all three package inputs were checked byte-identical
to the declared dependency revision `ba01733099`. Changed current sources and
every unchanged importer above them were separately re-elaborated as explicit
private dependencies. The selected source, object, input and prebuilt Mathlib
hashes were checked before and after every run. No build artifact was copied,
no cache was changed, and Mathlib was not rebuilt.

| New module | Strict private seconds |
| --- | ---: |
| Entropy.SubregionCut | 31.419 |
| Entropy.RegionalViability | 29.142 |
| Analysis.ViableSubspaceTensorTransport | 27.218 |
| Entropy.RegionTensorSplitting | 29.297 |
| Entropy.RegionalTensorMerge | 50.64 |
| Analysis.ViableSubspaceSampleOrFull | 24.415 |
| Analysis.ViableSubspaceSamplingEvent | 25.396 |
| Analysis.SpectralProjectorPower | 18.633 |
| Analysis.TensorOperatorPower | 35.932 |
| Analysis.SampledOperatorImage | 41.702 |
| Analysis.ViableNodeParameters | 31.996 |
| Analysis.SampledWordImageBounds | 44.895 |
| Analysis.ChebyshevWordPower | 29.899 |
| Analysis.ViableTrimmingRadius | 29.579 |
| Analysis.ViableNodeSamplingParameters | 6.675 |
| Analysis.ViableTrimmingRank | 24.795 |

An imported inspection covered all 55 explicit public declarations, including
the inline attributes recorded in the external manifest. Every declaration
used only a subset of `propext`, `Classical.choice` and `Quot.sound`.
The inspection passed in 26.989 seconds over seventy selected QIC source/object
pairs. Its temporary source was deleted after inspection. No permanent test
or foundation fixture is added.

`RegionalTensorMerge` took 50.640 seconds, above the unchanged fifty-second
limit. This timing concern is unresolved; it is not waived by the logical
check. The full ordinary build, affected regressions, compiled blueprint and
sufficiently quiet changed-module timing checks remain required before final
integration. The other new modules were below that limit in these runs.
