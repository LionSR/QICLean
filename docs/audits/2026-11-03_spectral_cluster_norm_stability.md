# Stability of a separated low spectral cluster

Let A and B be Hermitian matrices with norm difference at most xi>0.
Suppose their four real cutoffs satisfy a<b<=c<d and the original matrix
has the same closed spectral space at a and d. Two actual finite-window
losses, separately retained for the buffers b-a and d-c, control the two
directed comparisons. If each loss is below one, the approximant's own
closed spectral spaces at b and c coincide and have the dimension of the
original cluster. Every intervening cutoff yields that same space and
both directed estimates. No positivity, simple spectrum, nonzero-space
or additional residual on the new spectral space is assumed.

The proof applies the existing buffered norm-comparison theorem twice,
then the existing dimension comparison for nested approximating
subspaces. It does not infer exact invariance of the original target
under an approximate operator. This is a finite-dimensional auxiliary for
ALVV, arXiv:1602.08828v2, t:aisefficient, lines 1412-1420; physical soft
residuals and the Hermitian middle-MPO construction remain separate.

The final actual-name strict private check passed in 7.708 seconds with
six selected source/object pairs, and the imported one-public foundation
inspection passed in 8.512 seconds with seven pairs. Its only axioms are
propext, Classical.choice and Quot.sound. The temporary inspection source
was deleted. Each proof step was checked before the next was written.
Earlier incomplete checks reached only the expected unfinished goal;
the first two took 42.531 and 43.540 seconds, above the 25-second warning
threshold but below 50 seconds. Later required logical checks took
25.552, 19.295, 23.794 and 18.474 seconds. These observations are retained;
no timing-only rerun or proof-budget increase was used.

Checks used immutable TN 88ab31ce57 and its own QIC e817ea0a, with exact
source/object, root-input, transitive importer and verified prebuilt
Mathlib guards. The source-only branch starts at exact QIC e817ea0a and
has no .lake. No provider or cache was changed, no compiled artifact was
copied and no Mathlib source was built. Generated imports, source
blueprint synchronization, reader-facing prose, tactic-pattern scanning,
proof integrity and whitespace checks passed. Canonical ordinary and
compiled blueprint checks remain part of the coordinated integration.
