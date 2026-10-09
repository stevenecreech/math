# QRH and Siegel-zero formalizations

Use the pinned Lean toolchain in `lean-toolchain`. From this directory:

```sh
lake update
lake exe cache get
lake build
lake build ComparatorChallenges
```

The default `OAI` target imports the Riemann zeta and Dirichlet 7/8 nonvanishing theorem, the Hecke 7/8 theorem, and the Siegel-zero conclusions. All 3,236 supporting and comparator modules were retained by following imports recursively. Dependencies are mathlib, PrimeNumberTheoremAnd, and rellich-kondrachov, together with their transitive dependencies. The latter two retain the upstream compatibility patches, applied by `lake update`.

[Scope and limitations](docs/003.md) · [Comparator verification](ComparatorChallenges/README.md)

The collection-wide `lake-manifest.json` was removed because it includes unrelated packages. `lake update` generates a fresh lockfile for this subset; the three direct dependencies remain pinned to their original commits.

The separate [parameter-audit project](parameter-audit/README.md) verifies the uploaded 0.874958 candidate's arithmetic and several analytic generalizations. A complete draft under `OAI/NumberTheory/DirichletL/Improved/` applies the simpler fixed-baseline route to the actual probe and ends in `OAI.SevenEighths.ImprovedNonvanishing.exists_strictly_improved_zeta_region`. Its full dependency build and final axiom checks are pending. It is not imported by the default target and does not yet establish a verified improvement of the theorem above. The audit README gives the resumable verification command and distinguishes checked components from the draft application.
