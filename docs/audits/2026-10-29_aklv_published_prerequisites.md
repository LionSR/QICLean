# Published prerequisites for the AKLV entropy and approximation theorems

This revision assembles the finite-dimensional prerequisites needed by TNLean's
AKLV entropy and accuracy-dependent matrix product state approximation.
Its base is QICLean PR #1005 at
`ae966f98ecaa3b9b959bed1a4afa6361d6d993ef`. Each additional mathematical source
file is byte-for-byte the version in the public pull request listed below.
No new mathematical statement or proof is introduced by this assembly.
PR #1008 is based on #979. The independent PRs remain the units of review;
this combined revision supplies one immutable dependency for TNLean.

| Source file | Public PR | Exact source revision |
|---|---|---|
| `QICLean/Analysis/LowEnergyCluster.lean` | [#978](https://github.com/LionSR/QICLean/pull/978) | `56694e30d5fc5fc8e7a6169b75c6cbeba1b36c4d` |
| `QICLean/Analysis/LowEnergyCoordinates.lean` | [#978](https://github.com/LionSR/QICLean/pull/978) | `56694e30d5fc5fc8e7a6169b75c6cbeba1b36c4d` |
| `QICLean/Analysis/NormSquaredTriangle.lean` | [#1006](https://github.com/LionSR/QICLean/pull/1006) | `87d4edf51ce675bb7c2b2e4b30f458505b38205e` |
| `QICLean/Channel/FilterNormalization.lean` | [#1006](https://github.com/LionSR/QICLean/pull/1006) | `87d4edf51ce675bb7c2b2e4b30f458505b38205e` |
| `QICLean/Analysis/EuclideanEigenvectorBasis.lean` | [#1007](https://github.com/LionSR/QICLean/pull/1007) | `fc5653ff0395973ec1e5b488de0b7e83df3ebccc` |
| `QICLean/Analysis/GroundEnergyBounds.lean` | [#1007](https://github.com/LionSR/QICLean/pull/1007) | `fc5653ff0395973ec1e5b488de0b7e83df3ebccc` |
| `QICLean/Analysis/OptimizedPureStateTraceError.lean` | [#1007](https://github.com/LionSR/QICLean/pull/1007) | `fc5653ff0395973ec1e5b488de0b7e83df3ebccc` |
| `QICLean/Analysis/ProbabilityEntropyRankTails.lean` | [#1008](https://github.com/LionSR/QICLean/pull/1008) | `d60e228022f8d949d26abf361d34608606b4722c` |

The canonical generated imports are regenerated for this exact file set.
