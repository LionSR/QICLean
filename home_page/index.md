---
layout: default
---

QICLean is a [Lean 4](https://lean-lang.org/) formalization of
finite-dimensional quantum information theory, built on
[Mathlib](https://github.com/leanprover-community/mathlib4). It follows
M. Wolf's lecture notes, *Quantum Channels & Operations: A Guided Tour*:
the basics of quantum mechanics (density matrices, POVMs, the Schmidt
decomposition, purification and steering, Wigner's theorem), quantum
channels in their Kraus, Choi, and Stinespring representations,
Kadison-Schwarz inequalities, quantum Perron-Frobenius theory
(irreducibility, primitivity, peripheral spectrum), GKSL semigroups,
entanglement theory (entanglement witnesses, Schmidt number, separability,
the partial transpose and reduction criteria),
positive-but-not-completely-positive maps, and entropy.

## Relation to TNLean

QICLean was extracted from [TNLean](https://github.com/LionSR/TNLean), which
formalizes the fundamental theorem of matrix product states and remains the
home for matrix-product-state and tensor-network content; its blueprint and
documentation are published at
[sirui-lu.com/TNLean](https://sirui-lu.com/TNLean/). TNLean depends on
QICLean as an ordinary Lake package; QICLean never imports TNLean or any
matrix-product-state vocabulary.

## Companion Paper

S. Lu, E. Tjoa, J. I. Cirac, *Multi-agent Autoformalization of Tensor Network
Theory*, [arXiv:2607.07857](https://arxiv.org/abs/2607.07857), documents the
formalization effort this library and TNLean were both extracted from.
