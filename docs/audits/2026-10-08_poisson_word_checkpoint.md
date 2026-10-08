# Poissonized word decay source checkpoint

## Historical first checkpoint

This recovery checkpoint contributes to TNLean issue #8757. At local25b52a1, the184-line finite-word matrix module has passed targeted native and strict compilation on proof-identical source4cb9ee3. Its tests and axiom guards are pending. The201-line probability-law and169-line spectator modules are proof candidates that have not yet compiled; no completed result is claimed for them. Probability consumers and a blueprint leaf are present but unvalidated.

The intended law assigns each length-m word mass exp(-N*t)*t^m/m!, where N is the number of labels, and should derive normalization, the Poisson count marginal, integrability and exponential expected squared-norm decay from actual root matrices and a global gap. Identifying this concrete law with chronological events from independent rate-one clocks is a separate bridge. Coupled-clock locality and full amplification remain outside this package.

Source: pinned openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a, area-law manuscript09-amplification.tex:235–249. Proofs are independently written; no upstream Lean code is copied. Dependency/toolchain pins are unchanged. This checkpoint contains source/text only.

## Checked concrete word-law package

At source `64cb622e9b786d0f5437c96212918474b8a2e20a`, all 14 integrated checks pass: targeted native build, strict compilation of four production modules and eight consumer/guard files, and the raw 52-constant axiom inventory. There are 639 production lines, 24 consumers and 52 guarded public constants (50 explicitly named declarations and two generated measurable-space instances). All transitive axiom inventories use only standard axioms; there are no placeholders or new axioms.

The actual atomic probability law, Poisson count marginal, integrability and exponential squared-norm estimate are proved, including finite entangled spectators and the case where the gap exceeds the number of labels. Consumers cover empty labels, time zero, empty spectators, noncommuting positive factors, a genuinely entangled input, and positive time with a nonzero excited input. Independent review found no mathematical defect. Focused rendering passes all seven PDF pages, six static HTML pages, 52 public links and 33 labels. The explicit names of two existing instances let the source scanner verify both references without changing their public names or definitions; five additional checks pass at source3c911be. Full hosted CI has not run on this checked checkpoint. The formal identification with independent rate-one clocks and the coupled-clock locality estimate remain separate, so this does not close amplification.
