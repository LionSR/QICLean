# Weighted reference-space control of collective trimming

The final refinement in ALVV (arXiv:1602.08828v2, proof of Theorem t:alg1,
lines 1801–1813) controls trimming through an approximating space R whose
vectors have bounded Schmidt rank. The new auxiliary follows this argument
using the actual collective projections and two applications of weighted
robustness. If S is δ-viable for T, and T and R are ε-close in both directions,
then the collective trim is E-viable for T, with

    E = (1+θ)((1+θ)δ+(1+1/θ)ε+2ξ√(mb))+(1+1/θ)ε

for every θ>0. Here m is the number of actual cuts, b is the uniform Schmidt
rank of vectors in R, and ξ>0 is the actual trimming threshold. The coefficient
of δ tends to one with θ, which permits combination with a weak filter.

The error increment 2ξ√(mb) is the proved correction recorded in
`docs/paper-gaps/alvv16_trimming_constant.tex`. The estimate concerns the target
and reference spaces. It assumes no approximation of every vector in the
entire filtered subspace by its trim. Construction of the sufficiently accurate
physical reference space, iteration with automatic parameters and the final
compressed spectral extraction remain separate steps.
