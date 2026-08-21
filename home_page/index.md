---
layout: default
---

QICLean is a [Lean 4](https://lean-lang.org/) formalization of
finite-dimensional quantum-channel theory, built on
[Mathlib](https://github.com/leanprover-community/mathlib4). It follows
M. Wolf's lecture notes, *Quantum Channels & Operations: A Guided Tour*:
Kraus, Choi, and Stinespring representations, Kadison-Schwarz inequalities,
quantum Perron-Frobenius theory (irreducibility, primitivity, peripheral
spectrum), GKSL semigroups, positive-but-not-completely-positive maps, and
entropy.

## Relation to TNLean

QICLean was extracted from [TNLean](https://github.com/LionSR/TNLean), which
formalizes the fundamental theorem of matrix product states and remains the
home for matrix-product-state and tensor-network content. TNLean depends on
QICLean as an ordinary Lake package; QICLean never imports TNLean or any
matrix-product-state vocabulary.

## Companion Paper

S. Lu, E. Tjoa, J. I. Cirac, *Multi-agent Autoformalization of Tensor Network
Theory*, [arXiv:2607.07857](https://arxiv.org/abs/2607.07857), documents the
formalization effort this library and TNLean were both extracted from.
