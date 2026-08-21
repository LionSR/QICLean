<p align="center">
  <b>Quantum information and channels, formalized in Lean 4.</b>
</p>

[![PR CI](https://github.com/LionSR/QICLean/actions/workflows/pr-ci.yml/badge.svg)](https://github.com/LionSR/QICLean/actions/workflows/pr-ci.yml)
[![Compile blueprint](https://github.com/LionSR/QICLean/actions/workflows/blueprint.yml/badge.svg)](https://github.com/LionSR/QICLean/actions/workflows/blueprint.yml)

QICLean is a [Lean 4](https://lean-lang.org/) library, built on
[Mathlib](https://github.com/leanprover-community/mathlib4), that formalizes
finite-dimensional quantum information theory: the basics of quantum
mechanics (density matrices, POVMs, the Schmidt decomposition, purification
and steering, Wigner's theorem), quantum channels in their Kraus, Choi, and
Stinespring representations, Kadison-Schwarz inequalities, quantum
Perron-Frobenius theory (irreducibility, primitivity, peripheral spectrum),
GKSL semigroups, entanglement theory (entanglement witnesses, Schmidt
number, separability, the partial transpose and reduction criteria),
positive-but-not-completely-positive maps, and entropy. The library draws
heavily on M. Wolf's lecture notes, *Quantum Channels & Operations: A Guided
Tour*, alongside results
formalized from the wider quantum-information literature.

## Relation to TNLean

QICLean was extracted from [TNLean](https://github.com/LionSR/TNLean), a
formalization of tensor-network theory centered on the fundamental theorem
of matrix product states. TNLean builds on QICLean as an ordinary Lake
dependency.

## Getting started

```bash
# Fetch pre-built Mathlib artifacts first; never build Mathlib from source
# in a fresh clone.
lake exe cache get
lake build
```

See [`CLAUDE.md`](CLAUDE.md) for the full cache policy and local development
workflow, and [`docs/getting_started.md`](docs/getting_started.md) for a
fuller guide: what to install, a table of entry-point modules, a first
reading path through the source, how the blueprint is built locally, and
the contributing conventions carried over from TNLean.

## License

QICLean is released under the Apache License 2.0 (see
[`LICENSE`](LICENSE)), matching TNLean's license.
