# Parameter audit: 437479/500000

The new candidate is **437479/500000 = 0.874958**, not 437479/50000. Its improvement over 7/8 is exactly 21/500000.

This project formalizes the **unconditional arithmetic** in Appendices B–D of [the uploaded audit](../../preprints/quasi_riemann_parameter_audit.pdf), plus partial analytic generalizations: Mellin continuation at a variable boundary, polynomial height absorption, and extensions of the original local Euler factor, its infinite product, and compensated slot multiplier. It does **not** prove an improved zero-free region for zeta or an L-function. The existing 7/8 nonvanishing results and their comparator configurations retain their original statements.

The certificate is `OAI.QRHParameterAudit.arithmetic_parameter_certificate`. Its full type and axioms are printed in [verification.log](verification.log). In particular, `high_margin` proves the exact inequality `highE d x ≤ -gammaSave` for **every real** `0 ≤ d ≤ 3/4` and `0 ≤ x ≤ 1/2`. The proof clears denominators, proves the polynomial/discriminant identities, and bounds a square below by zero. It uses neither sampling nor decimal approximations.

The modules are in [../QRHParameterAudit/](../QRHParameterAudit/). The low estimate is an inequality of exponents, not an estimate of the actual physical probe. The original `OtherRegimes` module proves only the Euler exponent arithmetic. `EulerExtension`, `EulerProductExtension`, and `SlotExtension` prove local complex estimates, a product theorem with explicit summability assumptions, and slot decay on the extended region. `IdealSummability` and `IdealEulerProduct` remove that summability assumption for actual number-field prime ideals using unconditional ideal counting. `WeightedSlotExtension` carries the decay through finite weighted window products, conditional on positive window masses. These have not yet been connected to the complete modified Hecke probe. The tiny-row saving retains its interpretation relative to `C(beta)`, as required by the audit.

## Reproduce

The standalone Lake project depends only on mathlib and its dependencies. It also builds selected scalar support modules from the repository; it does not build the full Hecke dependency chain. It uses the same Lean and mathlib revisions as the parent repository:

```sh
cd lean/parameter-audit
lake update
lake exe cache get
lake build
lake env lean ../QRHParameterAudit/TrustReport.lean
```

The root Lean project also declares `QRHParameterAudit` as a separate build target. The standalone project avoids resolving the two additional analytic libraries or building the full original QRH library.

If the same mathlib revision and its compiled dependencies are already available in another project, run from the repository root:

```sh
python3 scripts/check-parameter-audit.py --mathlib-project /path/to/cached/project
```

This checks all cached dependency Git revisions against the lockfile and the source PDF fingerprint, compiles the scalar support and every audit module with `autoImplicit=false`, prints theorem types and axioms, rejects axioms outside the standard foundational list, and writes `verification.log`. It reads the cached project and writes only inside this repository. The recorded verification used this route. The standalone download/Lake build sequence is provided for reproduction, rather than claimed as a second completed build.

The later prime-ideal and weighted-slot additions have a separate [extension verification log](analytic-extension-verification.log). To check just those changes against the previously built audit dependencies:

```sh
python3 scripts/check-parameter-audit.py --mathlib-project /path/to/cached/project \
  --log-name analytic-extension-verification.log \
  --module OAI.NumberTheory.DirichletL.PrincipalSlotKernel \
  --module QRHParameterAudit.SlotExtension \
  --module QRHParameterAudit.IdealSummability \
  --module QRHParameterAudit.IdealEulerProduct \
  --module QRHParameterAudit.WeightedSlotExtension \
  --module QRHParameterAudit \
  --module QRHParameterAudit.TrustReport
```

The original `verification.log` records the preceding full check. The extension check rebuilds the seven selected modules in dependency order and prints the updated theorem/axiom report; it does not claim a fresh full-library build. A default run now includes all additions.

The later variable-geometry and fixed-baseline work is recorded in
[low-extension-verification.log](low-extension-verification.log),
[high-row-verification.log](high-row-verification.log), and
[baseline-verification.log](baseline-verification.log). The combined import and updated axiom report
are in [bounds-verification.log](bounds-verification.log). These checks cover
`LowReflectedExtension`, `LowNormExtension`, `HighRowAssembly`, and `BaselineImprovement`,
including the extracted scalar support and the unchanged old reflected-length theorem.

The fixed-baseline route targets **any strict improvement**, using
`baselineBoundary m = max(sigma0 + 21/1000000, 7/8-m/2)` for any positive all-regime saving `m`.
Lean proves this boundary is below `7/8` and proves the corresponding continuation implication
from explicit probe bounds. Source implementations of the actual modified-probe energy,
endpoint moments, and contour estimates are assembled as a complete draft under
`OAI/NumberTheory/DirichletL/Improved/` and the corresponding `Baseline*` modules.
The draft ends in `Improved/Nonvanishing.lean`, whose actual zeta theorem has no
analytic-bound hypotheses. Its full dependency build and final axiom inspection
are pending; these actual applications are not yet verified.
In particular, the illustrative `firstBoundary = 0.87499975` is not a proved zero-free region.

The new numerical version targets the exact rational margin
`delta = 1 / 2^1000000000000000000`, with boundary `7/8 - delta`.
`Improved/Nonvanishing.lean:explicit_zeta_nonvanishing` states that boundary
directly. This is a deliberately conservative target, not the full PDF margin.
Its parameter construction fixes `N = 2^999999999999999990` slots with
quantitative upper and lower bounds, so the margin is independent of every
character and height choice. These powers stay symbolic; the proof never
enumerates the slots or expands the enormous denominator. The final analytic
application remains subject to the pending full build and axiom check.

The newly checked finite slot construction is recorded in
[slots-verification.log](slots-verification.log). The direct continuation lemma accepting an
already-absorbed error bound is checked in
[direct-baseline-verification.log](direct-baseline-verification.log). The actual central
prefactor arithmetic and the floor-bin exponent arithmetic are checked in
[central-verification.log](central-verification.log). These reports include the integrated
audit import and transitive axiom checks. They do not certify the actual Hecke applications.

The separate actual-source builder uses the same pinned mathlib cache and the repository's
pinned, patched `rellich-kondrachov` and `PrimeNumberTheoremAnd` checkouts. It follows local
imports and resumes successful checks using recursive source hashes:

```sh
python3 scripts/check-qrh-actual.py --mathlib-project /path/to/cached/project \
  --jobs 2 --lean-threads 1 \
  --trust-declaration OAI.SevenEighths.ImprovedNonvanishing.exists_hecke_boundary \
  --trust-declaration OAI.SevenEighths.ImprovedNonvanishing.exists_dirichlet_boundary \
  --trust-declaration OAI.SevenEighths.ImprovedNonvanishing.exists_strictly_improved_zeta_region \
  --trust-declaration OAI.SevenEighths.ImprovedNonvanishing.explicit_zeta_nonvanishing \
  OAI.NumberTheory.DirichletL.Improved.Nonvanishing
```

Add `--plan` to validate dependency revisions and inspect the build size without compiling.
Progress and compiler diagnostics are written under `lean/.lake/actual-check/`.

## Provenance

- Lean: `leanprover/lean4:v4.34.1`.
- mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Source: the local 199-page `The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf`.
- Source SHA-256: `8fe93046f8cf5ef1ba5969c89addc02d76311adc4ee907509ff9cd96f7ec99e7`, matching Appendix A.
- Audit: `preprints/quasi_riemann_parameter_audit.pdf`.

[The remaining analytic work](ANALYTIC_OBLIGATIONS.md) distinguishes the verified arithmetic and analytic components from the missing estimates needed to improve the repository's nonvanishing theorem.
