# Poissonized word decay source checkpoint

This recovery checkpoint contributes to TNLean issue #8757. At local25b52a1, the184-line finite-word matrix module has passed targeted native and strict compilation on proof-identical source4cb9ee3. Its tests and axiom guards are pending. The201-line probability-law and169-line spectator modules are proof candidates that have not yet compiled; no completed result is claimed for them. Probability consumers and a blueprint leaf are present but unvalidated.

The intended law assigns each length-m word mass exp(-N*t)*t^m/m!, where N is the number of labels, and should derive normalization, the Poisson count marginal, integrability and exponential expected squared-norm decay from actual root matrices and a global gap. Identifying this concrete law with chronological events from independent rate-one clocks is a separate bridge. Coupled-clock locality and full amplification remain outside this package.

Source: pinned openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a, area-law manuscript09-amplification.tex:235–249. Proofs are independently written; no upstream Lean code is copied. Dependency/toolchain pins are unchanged. This checkpoint contains source/text only.
