# Uniform fixed-input Haar sections

The product Haar sampler admits a common failure estimate before the input
range and its rank are chosen. Let `D ≥ 2`, `r ≥ 1`, and `0 < beta ≤ 1`, and put

\[
 A=1+\log r+\log D+\log(1/\beta),\qquad
 s=\lceil4096rA\rceil,\qquad a=\frac3{32D^{12}s^5}.
\]

For every matrix `P` on a finite complex Euclidean space and every target `T`
with an arbitrary finite-dimensional exterior factor, the new theorem proves
that the actual canonical sample fails to be `(1-a)`-viable with measure at
most `beta`, provided that the actual range is quarter-viable, its rank is at
most `D^12*s^6`, and the target dimension is at most `r`.

The proof separates full samples, whose failure set is empty even at rank
zero, from proper samples. For proper samples, the existing overlap estimate
bounds the actual sampled overlap below by `a`. Monotonicity of viability
includes the true failure set in the existing failure set. The corrected
sphere-net estimate and the existing scalar ceiling theorem finish the proof.
No probability bound or measurable success event is added as a hypothesis.

These statements are auxiliaries to ALVV, arXiv:1602.08828v2, Lemma `l:rs`,
lines 530–558, and the merge analysis, lines 1777–1817. The corrected exponent
is twice the complex target dimension; see
`docs/paper-gaps/alvv16_random_sampling_net_count.tex`. The explicit constant
4096 is an auxiliary sufficient choice. The result is a fixed-input section
estimate, not a probability theorem for an entire adaptive construction.
Transport to a native regional sampler requires its actual coordinate identity;
no equality with an arbitrary changing orthonormal-basis choice is assumed.
