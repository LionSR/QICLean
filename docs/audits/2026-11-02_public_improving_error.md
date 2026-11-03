# Public inverse-scale improving-error estimate

The existing `Submodule.improving_error_le_inverse_scale` is made public so
that original-band refinement can use the same numerical estimate as the
gapped bootstrapping argument. Its statement, proof and existing use are
unchanged; only the `private` modifier is removed. The reader blueprint
states the numerical implication explicitly. No duplicate helper is added.

The modified module passed an actual-name strict private check in 9.709 s
against fully built TN5e19c052 / its own QIC518e8d20. Imported inspection of
the new public name passed in 4.901 s, with only `propext`, `Classical.choice`
and `Quot.sound`. Source/object/input guards and transitive changed-importer
checks were enabled; selected downstream modules used fresh private objects.
The temporary inspection source was removed after checking.

Added-prose and whitespace checks passed. No ordinary/full-library build or
compiled blueprint check is claimed for this source-only checkpoint. Those
remain for coordinated integration. No shared source, build cache or Mathlib
artifact was modified.
