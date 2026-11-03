# Shared order of low-energy cutoffs

The existing private theorem `spectralSpanLE_mono_cutoff` is moved from
`LowEnergyCluster` to the thin `LowEnergyOrder` module and made public.
Its statement, documentation and proof are otherwise unchanged. The seven
existing cluster uses retain their calls, and the cluster module imports
the new leaf. No second proof or compatibility alias remains.

The physical low-density minimum argument needs this order fact for
increasing canonical targets, target-rank bounds and the final restriction
of the requested cutoff. It imports the order leaf directly, without
importing a spectral-cluster comparison merely for span inclusion.

The new leaf and the modified cluster module passed strict actual-name
private checks in 4.280 and 6.443 seconds, respectively, against immutable
TNLean `994a1963ab36a234e1b02689a13bf1da965573b2` and its own QICLean
package `67a788fdb9660c16c70c97bf36be5da6bbbaa348`. The changed dependency
was supplied explicitly when checking the cluster module. An imported
inspection of the public order theorem and both existing public cluster
theorems passed in 4.541 seconds with only `propext`, `Classical.choice`
and `Quot.sound`. Its temporary diagnostic source was removed.

Blueprint synchronization and reverse coverage, reader-facing prose and
whitespace checks passed. Ordinary combined compilation and compiled
blueprint checking remain integration checks. The all-interval physical
family has no dependency on the cluster module, so its selected import
closure requires no further existing importer to be re-elaborated for
this relocation.
