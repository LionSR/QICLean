# Two merge moments of an actual excitation component

The one-copy physical space is Q ⊗ Y ⊗ V. The middle region Y is independent of the exterior regions. The common good-copy matrix retains QC and VR and traces every Y coordinate, together with all bad-copy coordinates. It is the actual, unnormalized marginal of the selected excitation component w.

For a unit ground vector and an original vector fixed under simultaneous physical and auxiliary copy permutations, the exponential of a times the sum of the two actual lifted merge deficits has real trace at most the average of the two polynomial bounds, multiplied by ‖w‖². The sole exponent condition is 2a ≤ 1; negative a, zero components, zero copies and an empty good set are included.

The first local moment uses physical complement Y ⊗ V. The second is derived by the literal exterior-region exchange (q,y,v) ↦ (v,y,q), together with C ↔ R, and uses complement Y ⊗ Q. Coordinate transport derives the exchanged ground norm, simultaneous copy symmetry and component norm. There is no independently supplied swapped symmetry, covariance, moment, or marginal equation.

The result is Matrix.replicaGoodPairMarginal_exp_sum_mergeDeficit_le in QICLean/Analysis/ReplicaTwoMergeMoment.lean. It uses the actual common density, the actual local component moments, the common-space deficit trace identities and the weighted arithmetic-mean bound.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*, September 24, 2026, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, 07-comparators.tex, lines 23, 103–110 and 524–555, equations comparator:merge-moments and comparator:component-inverse. This is an auxiliary arithmetic-mean consequence, sufficient for the polynomial part of the rough estimate. The printed Cauchy–Schwarz geometric mean, physical spectral restriction and full inverse-filter estimate remain separate statements.
