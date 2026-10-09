# Comparator checks

Install `comparator`, `landrun`, and `lean4export`, and make them available on `PATH`. After the setup in [the Lean README](../README.md), run from `lean/`:

```sh
lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json
lake env comparator ComparatorChallenges/DirichletSevenEighths.json
lake env comparator ComparatorChallenges/HeckeSevenEighths.json
lake env comparator ComparatorChallenges/SiegelZeros.json
```

These configurations retain the original theorem names and permitted axioms. See [the scope notes](../docs/003.md).
