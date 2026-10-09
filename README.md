# Quasi-Riemann hypothesis and Siegel zeros

This is a focused subset of the OpenAI mathematics repository. It retains the QRH manuscripts (the 7/8 result and alternate 11/12 argument), the Landau–Siegel-zero manuscript, and the Lean dependency closure of the four associated theorem checks.

- [Manuscripts](CONTENTS.md)
- [Formalization scope](lean/docs/003.md)
- [Lean setup and verification](lean/README.md)

The Lean sources retain their original namespaces and proofs. The alternate 11/12 manuscript is included as reading material; the retained comparator checks concern the 7/8 results and the uniform real-zero gap. Inclusion here does not constitute independent verification of the mathematical claims.

The original collection remains available in Git history. Both original license files are retained.

The uploaded [parameter audit](preprints/quasi_riemann_parameter_audit.pdf) proposes the improved boundary **437479/500000 = 0.874958**. Its [Lean implementation](lean/parameter-audit/README.md) verifies the arithmetic and several analytic generalizations. A complete draft now connects the modified probe to an existential strict improvement below 7/8, using the simpler fixed-baseline route. Its full dependency build and final axiom checks are pending, so the default L-function theorems still assert the original 7/8 region. [Verification status and analytic details](lean/parameter-audit/ANALYTIC_OBLIGATIONS.md) distinguish the checked components from that draft.
