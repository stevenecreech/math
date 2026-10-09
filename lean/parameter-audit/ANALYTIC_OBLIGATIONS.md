# Analytic obligations for the improved boundary

Status: the arithmetic certificate and several analytic generalizations have passed Lean checks. A complete **draft source chain** now ends in `Improved/Nonvanishing.lean`, with an existential strict improvement for the actual zeta function and no analytic-bound hypotheses in its statement. **That chain has not yet passed its full dependency build or final axiom check; no improved nonvanishing result is claimed as verified.** No new axioms or admitted proofs were introduced.

The eventual zeta target is the actual mathlib function:

```lean
∀ {s : ℂ}, OAI.QRHParameterAudit.sigma0 < s.re → s ≠ 1 → riemannZeta s ≠ 0
```

The audit's intended boundary is 437479/500000, at every height, with strict inequality. The immediate goal also allows any fixed strict improvement below 7/8. The audit itself describes a conditional analytic argument and instructs the formalizer to report missing analytic applications rather than assume an improved zero bound.

## Applying the simpler route to the actual probe

Work is now proceeding at the fixed envelope `B = 7/8`. New source files under
`OAI/NumberTheory/DirichletL/Improved/`, together with the `Baseline*` energy,
moment and row-count modules, apply the generalizations to the original ideal
sums, Hecke characters, and contour integrals. **These actual applications are
implemented as a complete draft and their dependency build is in progress. They are not yet
Lean-verified results and do not establish an improved zero-free region.**

The principal pieces are:

- `Improved/LowOriginalEnergy.lean`: propagates the variable-total reflection
  estimate through the original completed sums, with exponent
  `1-total-2*d + max 0 (5*total-1+d)/4 + 507*eta`.
- `Improved/LowUnselectedMass.lean` and `LowCentralTuple.lean`: retain decay from
  the actual unselected tuple weights to absorb the additional reflection cost.
  Splitting the inverse-square norm weight at exponent `-3/2` provides a
  `Z^(-d/2)` bound using existing ideal summability.
- `Moments/BaselineGeometry.lean` separates the moving moment geometry from the
  old `HighData` condition requiring a positive gap above `7/8`.
  `Detector/BaselineMomentAssembly.lean` supplies source code for all four
  endpoint moment estimates from the actual energy theorems at `kappa = 3/4`.
  `PrimeRows/BaselineMaximum.lean` bounds the actual detector bins by `7/8`,
  without an extra bin-width loss.
- `Detector/ImprovedCorrection.lean` identifies the actual Hecke correction
  with the extended ideal Euler product and enlarges the source exclusions.
- `Improved/Normalizer.lean`, `PrincipalResidue.lean`, and
  `PrincipalRemainder.lean` adapt the principal normalization and contours to
  the audited physical scales. For this first improvement the high contour
  can remain above `7/8`; only the correction used in the final continuation
  needs the larger holomorphic domain.
- `Improved/Probe.lean` defines the modified compensated physical probe and
  connects bounds on that specific function to actual Hecke nonvanishing.
  Its low and high bounds are explicit hypotheses of the continuation lemma.
- `Improved/ProbeLow.lean` and `Improved/HighError.lean` supply source proofs
  of those bounds for the actual probe. `Improved/HighData.lean` constructs a
  common geometry and strictly positive saving before the character is chosen.
- `Improved/Nonvanishing.lean` assembles those applications and transfers the
  resulting boundary to Dirichlet L-functions and mathlib's `riemannZeta`.
  Its target is `exists_strictly_improved_zeta_region`: a fixed `delta > 0`
  with nonvanishing on `Re(s) > 7/8-delta`. This is an unverified draft,
  not a completed Lean result or a claim of the full boundary `0.874958`.
- The numerical version fixes `delta = 2^(-1000000000000000000)` and states
  `Re(s) > 7/8 - delta` directly in `explicit_zeta_nonvanishing`.
  `ExplicitSlots`, `ExplicitCarrier`, `BaselineExplicitMesh` and
  `ExplicitHighData` replace the unquantified slot choice with a prescribed
  finite dimension and lower slot bound. This is a draft application with
  the same pending full-build verification requirement.

The targeted builder `scripts/check-qrh-actual.py` compiles each requested
module's full local dependency closure with `autoImplicit=false`, using the
pinned cached mathlib and the pinned, patched Rellich and PrimeNumberTheoremAnd dependencies. Successful
modules are cached by source and recursive dependency hashes. Diagnostics are
in `lean/.lake/actual-check/build.log` and its `logs/` directory. An optional
`--trust-declaration` argument checks the transitive axiom list after a successful
build. This is separate from the already completed standalone audit checks.

The final application also has separate source implementations in
`Improved/Baseline.lean` (the known envelope and the case below the energy
theorem's `51/100` gate), `SourceData.lean` (simultaneous source exclusions and
extended correction), and `Transfer.lean` (actual Hecke-to-Dirichlet/zeta
factorization at any positive boundary). These are subject to the same pending
actual dependency verification. The target can be existential: a fixed
positive improvement determined by the common slot system suffices.

## Analytic components now implemented

These additions use actual complex norms, infinite products, real powers, Mellin integrals, and holomorphic functions. They are mathematical lemmas with explicit hypotheses, not new axioms.

- `QRHParameterAudit/HeightAbsorption.lean`: `absorb_height_and_tail` proves the continuous real-scale error estimate with saving **m/2** from the full “every tail order, every allowed height” bound. It chooses the height after the finite order `A`, then the tail order `N`; the saving does not depend on the target's orders. `absorbed_error_isBigO` exports the asymptotic form.
- `QRHParameterAudit/Continuation.lean`: the original Mellin/identity-theorem argument now also has a boundary-parametric implementation. `nonzero_of_common_signal` works with any boundary, explicitly supplied low/high bounds, holomorphic correction, exact Mellin product identity, and pole regularization. Its continuation margin is `min(beta-boundary-omega,saving)`.
- `QRHParameterAudit/AnalyticAssembly.lean`: `nonzero_of_height_controlled_signal` combines the two preceding analytic arguments. All hypotheses appear in its theorem type. It has **not** been instantiated with the modified Hecke probe or the actual zeta function.
- `QRHParameterAudit/EulerExtension.lean`: for the repository's existing `SevenEighths.ProbeEuler.unramifiedClosed`, proves **norm defect ≤ 240 Q^(-149/100)** on `Re s ≥ 3/4`, `Re w ≥ 19/20`, `Re z ≥ 33/200`. It also proves separation of all geometric denominators and holomorphy in `s` on `Re s > 3/4`, including the principal specialization above `sigma0`.
- `QRHParameterAudit/EulerProductExtension.lean`: proves holomorphy and `norm(H-1) ≤ 1/2` for the infinite product of these same local factors, given the explicit summability of `240 Q_i^(-149/100)` and a small excluded tail. `exists_uniform_extended_cutoff` chooses the finite cutoff **before** all target phases and external parameters. The actual prime-ideal norm application is supplied by `IdealEulerProduct`; equality with the Hecke source correction remains.
- `QRHParameterAudit/SlotExtension.lean`: for the original `regionSlot` and `principalSlot`, proves the audit's **1440 Q^(-37/50)** error from `-1` throughout the extended second region, for `Q ≥ 480` and unit target phases. It includes the required correction inverse bound. The full prime-window normalizer and contour estimates have not been assembled from this bound.
- `QRHParameterAudit/IdealSummability.lean`: `ideal_norm_rpow_summable` proves unconditional summability of `N(I)^(-r)` for every number field and every real `r > 1`, using mathlib's ideal-counting asymptotic. No GRH or zero-free hypothesis enters this proof.
- `QRHParameterAudit/IdealEulerProduct.lean`: specializes the extended rational Euler factors to **actual prime ideals and absolute norms**, with summability now proved rather than assumed. `exists_uniform_ideal_cutoff` supplies a single natural-number norm cutoff before all phase choices, external parameters, and enlargements of the exclusion set. `exists_ideal_correction` constructs finite ideal exclusions containing any prescribed set. The phase functions are still arguments; identification with the Hecke source correction and its admissible exclusions remains to be connected.
- `QRHParameterAudit/WeightedSlotExtension.lean`: extends the original nonnegative weighted-slot and finite-product error argument to the second region. `weighted_region_product_error_linear` proves the original principal scalar is nonzero **given positive window masses**, and bounds the normalized product error by `card(S) * 2^card(S) * 1440 * P^(-37/50)`. The principal specialization uses the original `principalSlot` and `principalScalar`. Actual prime-window mass positivity and contour integration remain separate obligations.
- `QRHParameterAudit/LowReflectedExtension.lean`: generalizes the repository's original `reflectedExponent` to total slot length `total`, row length `1-total-2*d`, and surviving slot length at most `total-d`. It proves the extra cost `max 0 (5*total-1+d)/4 + 40*epsilon`. After square root and tuple compensation, the extra exponent is at most `-7*d/8` when `total ≤ 1/5`. These are statements about the original reflected exponent, whose two scalar definitions were extracted unchanged into `Inversion/TerminalExponent.lean`.
- `QRHParameterAudit/LowNormExtension.lean`: generalizes the physical-scale square-root normalization to arbitrary row exponent, retains the compensated `-7*d/8` gain, and identifies the candidate Gram square-root exponent with `signal sigma0`. The completed-energy norm bound remains an explicit input; this is not yet the actual low-probe estimate.
- `QRHParameterAudit/HighRowAssembly.lean`: proves the audit's `rowR` and witness cutoff equal the existing `Endpoint` quantities exactly. It assembles explicit cardinality and per-row norm bounds into a bound for a finite complex row sum with `gammaSave/2` saving, including loss budgets and the short height extension. Actual modified-probe cardinality and per-row bounds remain inputs.
- `QRHParameterAudit/BaselineImprovement.lean`: proves direct continuation from a fixed baseline `7/8`. For any **positive** all-regime saving `m`, the resulting boundary is `max(sigma0 + 21/1000000, 7/8-m/2) < 7/8`. The theorem explicitly requires the actual low/high estimates and exact signal identity; it does not assert them. The numerical `firstBoundary = 3499999/4000000` is an illustrative weaker target if the full high estimate retains `gammaSave`, not an established zeta region.
- `QRHParameterAudit/PhysicalSlots.lean`: constructs actual finite arrays of
  distinct positive slot lengths with any prescribed positive total, including
  the audited `ell`. Their minimum and capacity bounds are uniform over the
  chosen row range and are fixed before the target character and height orders.
- `QRHParameterAudit/CentralExponent.lean` and `Improved/FloorScales.lean`:
  verify the physical-prefactor identities and the central/floor exponent
  budgets used by the new actual row-sum applications. These scalar proofs
  passed the strict standalone check and transitive axiom report in
  `central-verification.log`; the row-sum applications themselves are still pending.

The scalar coordinate and slot definitions, together with the general weighted-sum and finite-product lemmas, were moved into `Detector/EulerCoordinatesScalar.lean` and `PrincipalSlotKernel.lean` without changing their namespaces, formulas, or existing proofs. Their original Hecke-facing modules import them. This makes the local analytic claims testable without building the full Hecke dependency chain.

These results discharge the general continuation/height mechanism, local Euler/slot estimates, prime-ideal norm-weight convergence, and the finite weighted-product error mechanism. They do not yet discharge the actual probe estimates, identification of the source product, contour shifts, common Hecke-family supremum argument, or transfer to zeta. The standalone verification covers the scalar support and audit modules; the full original 7/8 library has not been rebuilt as part of this addition.

## A shorter route to any strict improvement

For the user's immediate goal, one need not reach `sigma0` in the first step. Keep the **known upper envelope** `B = 7/8`. Prove the low estimate with fixed loss `omega = 21/1000000` and the high-error estimate with exponent `signal B - m` for some target-independent `m > 0`. Height absorption and the exact Mellin identity then give nonvanishing beyond `baselineBoundary m`. This boundary is strictly below `7/8` for every `m > 0`; the new `nonzero_of_fixed_baseline_bounds` theorem checks that implication. No second supremum contradiction is needed. Character-dependent constants and late height choices remain allowed.

There are concrete existing inputs for this route:

- `Energy/CertifiedExistence.lean:terminal_certificate` already permits `kappa = 3/4`: its condition `2*HeckeZeroSupremum.beta-1 ≤ kappa` follows from the baseline. Its additional `51/100 ≤ beta` gate needs a case split; if the supremum is below `51/100`, the requested near-`7/8` region already follows. The supremum sentinel itself is only `1/2`.
- `PrimeRows/NonfloorCount.lean:balanced_adaptive_count_from_raw_moments` and `SourceCount.lean` accept `Delta = 0`. At that value the count exponent has no `Delta/4` loss and agrees with `rowR`. A limit of positive-Delta moment estimates is unnecessary and would require care because their admissible capacities are smaller.
- `PrimeRows/PhysicalDyad.lean:finitePhysicalRows_eq_integral` already allows an arbitrary outer contour `sigma` with `7/8 ≤ sigma` and `beta+8*e ≤ sigma`. The baseline allows `sigma = 7/8+8*e`.

The draft propagates the new geometry through the actual completed-energy and physical-probe proofs, specializes the endpoint moment certificate to the source row family, and exports all-regime high and contour estimates relative to the fixed envelope. These applications must now pass the full dependency build and final axiom checks. The selected-row saving alone does not give an all-regime saving: the latter also depends on the chosen minimum slot length. The generic fixed-baseline theorem deliberately accepts any positive `m`.

The low-energy generalization now has source implementations in separate
`Improved/LowExponent.lean` through `Improved/LowOriginalEnergy.lean` modules,
followed by the physical normalization and tuple estimates. They must compile
with their actual dependencies before this obligation can be marked discharged.
The original `LowExponent` dependency closure has 491 local modules; the
standalone audit checks do not rebuild that chain. The high estimate and its
low/high instantiation now have draft source implementations, subject to the
same verification requirement. The final target's closure contains 3,062 local
modules, including the original analytic library and the new applications.

The metaplectic cancellation is already used in the source: the September manuscript differentiates away the theta constant term at each cusp (around `paper.tex:2331`), and its marked local compensation cancels the scalar prime contribution (around `paper.tex:6913`). The low bound still pays for exceptional sixth-power Gram frequencies (`Detector/LowGramExceptional.lean:lowGramExceptional_count`), which contribute the `b/12` term after square root. Another formal subtraction of the same residue does not remove that cost.

## Dunn–Radziwiłł and stronger candidate boundaries

The [published paper *Bias in cubic Gauss sums: Patterson's conjecture*](https://annals.math.princeton.edu/2024/200-3/p03) supplies relevant cubic Gauss sum and theta-transform ideas. Its prime-sum asymptotic and its dispersion estimate assume GRH for Hecke L-functions. Those conditional estimates cannot serve as unconditional inputs to the nonvanishing theorem being sought here. The repository's October 5 manuscript already cites their Lemma 5.4, Proposition 5.3 and Section 5 for cube completion and theta transformation. Any improvement using these ideas still requires an independently justified estimate in our precise family and normalization.

The `3/4` in the extended Euler region is a domain for the **correction factor**, not a proved zero-free boundary for zeta. Similarly, the audit's fixed row parameter `kappa = 3/4` is not by itself a zero-free theorem. Within the supplied probe geometry, `sigma = 11/12 - ell/4` and `ell < 1/5` imply `sigma > 13/15`; thus neither `5/6` nor `3/4` follows by merely retuning this audit's parameters. The immediate target is any fixed positive improvement below `7/8`. The stronger `437479/500000` boundary has a checked arithmetic certificate, but remains a separate analytic target.

## What prevents applying the existing theorem directly

These are restrictions in the actual Lean definitions and theorem types, not just in comments:

- `OAI/NumberTheory/DirichletL/ParametersHighData.lean`: `HighData.slots_sum` requires the slot lengths to sum to **1/6**. The candidate sum is **62563/375000**, which is larger.
- `OAI/NumberTheory/DirichletL/Detector/FinalAssemblySource.lean`: `normalizedProbe` uses **Z^(17/48)**, **Z^(23/48)** and a **1/6** normalizer. `normalizedProbe_low` assumes the old slot sum and concludes an exponent **3/16 + loss**. The needed candidate exponent is **93729/500000 + loss**.
- `OAI/NumberTheory/DirichletL/Detector/FinalAssemblyData.lean`: `SourceData.probe` instantiates that old probe, and `SourceData.probe_low` imports that old exponent.
- `OAI/NumberTheory/DirichletL/PrincipalSignalComparison.lean`: `sourceCorrection_differentiable` and `sourceCorrection_bound` certify the region to the right of **7/8**. `Detector/FinalAssemblySource.lean` exports precisely this domain through `actual_source_analytic`.
- `OAI/NumberTheory/DirichletL/Detector/FinalAssemblyHigh.lean` requires **7/8 ≤ beta**, uses the old physical geometry and the moment gap **beta - 7/8**. In the proposed contradiction, **sigma0 < beta ≤ 7/8**; that old gap is nonpositive.
- `OAI/NumberTheory/DirichletL/Detector/FinalAssemblyChosenData.lean` and `Hecke/CommonProbe.lean` quantify their contradiction contracts using **7/8 < beta**.
- `OAI/NumberTheory/DirichletL/Hecke/SignalIdentity.lean`, `SignalBounds.lean`, and `SignalShift.lean` use **7/8** as the holomorphic correction's lower boundary.

The initial 7/8 theorem can supply a baseline upper bound. It cannot supply the strictly stronger conclusion by weakening a hypothesis: `sigma0 < s.re` permits points with `s.re ≤ 7/8`.

## Six required modifications

1. **New physical probe.** Define the actual compensated ideal/prime tuple sum from source (12.5), with positive slot lengths summing to `ell`, scales `Z^lx` and `Z^ly`, the same masks, and the appropriate prime normalizer. Retain the quotient-free tuple correction (16.3). Establish the reflection/completion identities for these definitions. An arbitrary function called a probe is insufficient.

2. **Actual low estimate.** Reprove source Lemma 15.1 with `M' = 1-ell-2u`, `ell' = ell-u`, and the row-norm exponent `M' + max 0 (5*ell-1+u)/4 + epsilon`, uniformly in fixed tuples and surviving slot mesh. Then prove the coefficient/rescaled-tuple factor `Z^(-u)`, the Gram dominance conditions, and the normalized probe estimate `‖J_eta Z‖ ≤ C_eta * Z^(signal sigma0 + omega)` for all sufficiently large real `Z`. `low_extra_bound` proves only the exponent inequality used in this step.

3. **Actual row counts with fixed kappa = 3/4.** Reprove the application of source Proposition 19.2 from Lemmas 17.1, 17.2, 17.6 and 18.1. The baseline `beta ≤ 7/8` permits this kappa. Establish the count with the new balanced `rowR`, arbitrarily small capacity/mesh losses, the fixed polynomial height factor, and the small/zero-capacity cases. Do not import the old positive `beta-7/8` gap or its capacity-comparison loss. `row_balancing` proves equality of the ideal exponents, not a bound for a cardinality of actual rows.

4. **Euler product and contours below 7/8.** Extend the actual principal correction to the second Euler region with `Re s ≥ 3/4`, `Re z ≥ 33/200`, `Re w ≥ 19/20`. Prove local denominator separation, uniform summability/normal convergence, the divisor bound, polynomial height bounds, `‖H_eta s-1‖ ≤ 1/2` for `sigma0 < Re s`, and a nonzero prime normalizer. Reprove the needed source Lemmas 10.3–10.6, keeping the nonprincipal region, extending the principal region, and using first-region parameter **1/4** for the small-row contour. `euler_exponents` verifies the exponent arithmetic; the newly proved `EulerExtension`, `EulerProductExtension`, and `SlotExtension` supply the local complex estimates and a generic product theorem. The actual prime-ideal application, normalizer and contour shifts remain.

5. **Actual high estimate in all regimes.** Reprove source Lemma 20.1 with the candidate geometry and `generalE`, including the amplitude term `q*ell`, the errors from bins/witnesses, and the full original sum over moving rows. Use the verified `high_margin`, `floor_margin`, `unselected_margin`, `tiny_margin`, and `extended_high_margin` in their respective regimes. For rows beyond `geomH+extension`, prove the absolute-line estimate with a sufficiently large fixed outer line. The tiny-row saving is relative to `signal beta`, not `signal sigma0`.

6. **Common-height assembly, continuation, and transfer.** Reprove source Section 20.6/Proposition 20.3, generalize the continuation statements to `sigma0`, and apply the actual Hecke-to-Dirichlet transfer (Proposition 11.3) to the resulting Hecke theorem. All moving internal Hecke characters remain present even when the final target is zeta.

## Quantifier order for the full PDF target

This section describes the stronger `sigma0` target. The simpler draft above
instead fixes the known envelope `7/8` and accepts any common positive saving;
it does not use the second supremum contradiction described here.

For every hypothetical `sigma0 < beta ≤ 7/8`, let `Delta = beta-sigma0 > 0`. Choose the common geometry, finite mesh, detector/bin widths, losses, and outer line **before** the target. Choose common `0 < omega < Delta` and `m > 0`. For each target choose its finite exclusions, actual correction `H_eta`, actual probe `J_eta`, exact source signal `f_eta`, and finite orders `A_eta ≥ 0`, `B_eta`, `tau0_eta > 0` **before** the tail order `N`.

The missing analytic bounds on continuous real scales must imply, with character-dependent constants and thresholds:

```text
‖J_eta(Z)‖ ≤ C_eta Z^(signal(sigma0)+omega)
‖J_eta(Z)-f_eta(Z)‖ ≤ C_eta,N,tau [
    Z^(signal(beta)-m) (1+Z^tau)^A_eta + Z^(B_eta-N*tau)]
```

The second estimate is required for every natural `N` and every fixed `0 < tau ≤ min(dmin/100,tau0_eta)`. The actual signal is the source vertical integral on `Re s = 2` of `Z^(s-11/16) exp((s-5/6)^2) H_eta(s)/L_eta^S(s)`, with the `1/(2*pi*i)` factor. The probe and signal must not depend on the later height or tail choices.

`exists_late_height` and `exists_late_tail` verify the numerical choices. `absorb_height_and_tail` now proves the analytic absorption step from the fully quantified high estimate, and `nonzero_of_height_controlled_signal` combines it with Mellin continuation. Neither establishes the missing Hecke probe estimates themselves. Likewise `exists_above_sentinel` verifies the order-theoretic witness extraction, without assuming the supremum is attained; it has not been instantiated here with an improved continuation theorem about the actual Hecke zero set.

No assumption `Delta ≥ gammaSave` is permitted. After height absorption the continuation saving is `min(Delta-omega,m/2)>0`. The least-upper-bound witness then gives the contradiction; only afterwards can the Dirichlet/zeta transfer establish the stated target.
