# Order properties of close subspaces

`Submodule.IsCloseTo.of_le` is moved from `ViableSubspaceBootstrap` to the
thin `ViableSubspaceOrder` module. Its public signature, docstring and proof
are unchanged. The bootstrap module imports the new module, preserving its
mathematical interface. No alias or duplicate proof is added.

The new `Submodule.isCloseTo_of_le` states that a subspace containing the
target is close to it at every nonnegative error. Equality gives the
self-closeness used in the two existing physical gapped short-interval
branches and in the low-energy interval construction. All are consequences
of the existing projection characterization of closeness.

Strict actual-name checks passed against the verified immutable TNLean
provider `5fc343a57d70eefd2902780107851ab9b0753a82` and its own QICLean
package `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`: the order module
took 4.202 seconds, and the modified bootstrap module took 9.067 seconds.
The bootstrap source and every selected changed-dependency importer were
checked with explicit source/object overrides. Selected dependency hashes
and the prebuilt Mathlib sentinel were guarded before and after checking.
The two public order declarations have an imported foundation inspection
using only propositional extensionality, classical choice and quotient
soundness, completed in 4.071 seconds. The temporary diagnostic source
was deleted.

Ordinary integration, the full library and compiled blueprint checks remain
required. No provider, ordinary build or cache was changed.
