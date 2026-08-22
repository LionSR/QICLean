---
layout: default
---

QICLean is a [Lean 4](https://lean-lang.org/) formalization of
finite-dimensional quantum information theory, built on
[Mathlib](https://github.com/leanprover-community/mathlib4): the basics of
quantum mechanics (density matrices, POVMs, the Schmidt
decomposition, purification and steering, Wigner's theorem), quantum
channels in their Kraus, Choi, and Stinespring representations,
Kadison-Schwarz inequalities, quantum Perron-Frobenius theory
(irreducibility, primitivity, peripheral spectrum), GKSL semigroups,
entanglement theory (entanglement witnesses, Schmidt number, separability,
the partial transpose and reduction criteria),
positive-but-not-completely-positive maps, and entropy. The library draws
heavily on M. Wolf's lecture notes, *Quantum Channels & Operations: A Guided
Tour*, alongside results
formalized from the wider quantum-information literature.

## Relation to TNLean

QICLean was extracted from [TNLean](https://github.com/LionSR/TNLean), a
formalization of tensor-network theory centered on the fundamental theorem
of matrix product states; its blueprint and documentation are published at
[sirui-lu.com/TNLean](https://sirui-lu.com/TNLean/). TNLean builds on
QICLean as an ordinary Lake dependency.

## Paper-Gap Notes

Where the formalization deviates from a cited source &mdash; a missing
hypothesis, a scalar correction, a scope restriction, a replacement proof
route &mdash; the deviation is recorded as a standalone mathematical note.
The [paper-gap notes](paper-gaps/) are indexed by source paper; each note has
a stable link, a PDF, and a citation entry. The notes on Wolf's *Quantum
Channels & Operations* moved here from TNLean together with the
channel-theory library.

## Companion Paper

S. Lu, E. Tjoa, J. I. Cirac, *Multi-agent Autoformalization of Tensor Network
Theory*, [arXiv:2607.07857](https://arxiv.org/abs/2607.07857), documents the
formalization effort this library and TNLean were both extracted from.
