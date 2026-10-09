import OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
import OAI.NumberTheory.DirichletL.Detector.ImprovedCorrection
import QRHParameterAudit.BaselineImprovement

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter Asymptotics
namespace SevenEighths.ImprovedProbe
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual QRHParameterAudit
local notation "O" => HeckeFamily.O

/-- The actual compensated physical probe with the audited length exponents.
The principal scalar uses the audited total slot length. Bounds for this function
are separate mathematical obligations. -/
def normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀ P ∈ S, P.IsMaximal)
    [NeZero (∏ P ∈ S, P)] (d : Fin K → ℝ) (a b : ℝ) (W : Fin K → ℝ → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j => Z^(d j)
  let T := fun j => pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j => canonicalSlotSupport (T j)) (fun j y => (W j y : ℂ)) Yp
    (Z^lx) (Z^ly) Z /
    (sourceResidueConstant W0 W1 (∏ P ∈ S, P) *
      (Probe.principalScalar Finset.univ Z ell (slotMass T (residueWeights W Yp)) : ℂ))

/-- An actual-Hecke endpoint for the smaller first improvement. The two unresolved
bounds are on the explicitly defined physical probe above. Regularization, finite
prime deletion, Mellin inversion, local integrability, and decay at zero are all
discharged here using the existing Hecke theory.

This theorem is conditional on `hlow` and the absorbed error estimate `herror`;
it does not prove either estimate. -/
theorem LFunction_ne_zero_of_probe_error {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    [NeZero (∏ P ∈ S, P)] (d : Fin K → ℝ) (a b : ℝ) (W : Fin K → ℝ → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character)
    (saving : ℝ) (hsaving : 0 < saving)
    (hH : AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ | 3/4 < s.re})
    (hbound : ∀ s : ℂ, 3/4 < s.re → ‖sourceCorrection η S s-1‖ ≤ 1/2)
    (hlow : normalizedProbe M H S hmax d a b W W0 W1 η =O[atTop]
      (fun Z : ℝ => Z^(QRHParameterAudit.signal sigma0+baselineLoss)))
    (herror : (fun Z => normalizedProbe M H S hmax d a b W W0 W1 η Z -
      HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z)
      =O[atTop] (fun Z : ℝ => Z^(QRHParameterAudit.signal (7/8)-saving/2)))
    {rho : ℂ} (hrho : baselineBoundary saving < rho.re)
    (hpole : rho ≠ 1 ∨ η.residue ≠ 1) : LFunction η rho ≠ 0 := by
  let χ := η.excludePrimes S hS.prime
  let J := normalizedProbe M H S hmax d a b W W0 W1 η
  let f := HeckeSignal.signal χ (sourceCorrection η S) (-11/16)
  have hmask := excludePrimes_mask η S hS.prime
  have hpoleχ : rho ≠ 1 ∨ χ.residue ≠ 1 := by
    rcases hpole with h1 | hη
    · exact Or.inl h1
    · exact Or.inr (fun hχ => hη ((HeckeFiniteDeletion.principal_iff_of_mask χ η hmask).mp hχ))
  have hsig : (3/4:ℝ) < sigma0 := by norm_num [sigma0]
  have hHσ : AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ | sigma0 < s.re} :=
    hH.mono (fun _ hs => hsig.trans hs)
  have hHd : DifferentiableOn ℂ (sourceCorrection η S) {s : ℂ | 7/8 < s.re} :=
    (hH.mono (fun _ hs => lt_trans (by norm_num : (3/4:ℝ) < 7/8) hs)).differentiableOn
  have hb : ∀ s : ℂ, 7/8 < s.re → ‖sourceCorrection η S s-1‖ ≤ 1/2 :=
    fun s hs => hbound s (lt_trans (by norm_num : (3/4:ℝ) < 7/8) hs)
  have herr : (fun Z => J Z-f Z) =O[atTop]
      (fun Z : ℝ => Z^((7/8:ℝ)+(-11/16)-saving/2)) := by
    simpa only [signal_eq, sub_eq_add_neg, neg_div] using herror
  have htop : f =O[atTop]
      (fun Z : ℝ => Z^(baselineBoundary saving+(-11/16))) := by
    have hh := AnalyticContinuation.common_signal_bound_with_margin J f
      sigma0 (7/8) baselineLoss (saving/2) (-11/16)
      (by simpa only [signal_eq, sub_eq_add_neg, neg_div] using hlow) herr
    convert hh using 1
    rw [baselineBoundary_eq]
    ring_nf
  have ha2 : baselineBoundary saving < 2 :=
    (baselineBoundary_improves hsaving).2.trans (by norm_num)
  have hrho0 : 0 < rho.re :=
    (lt_trans (by norm_num [sigma0] : (0:ℝ) < sigma0)
      (baselineBoundary_improves hsaving).1).trans hrho
  have hnonzero : LFunction χ rho ≠ 0 := by
    apply nonzero_of_fixed_baseline_error saving hsaving
      (LFunction χ) (HeckeSignal.regularL χ) (HeckeSignal.targetRegularizer χ)
      (sourceCorrection η S) J f
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (HeckeSignal.regularL_entire χ)).mono (Set.subset_univ _))
      ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
        (HeckeSignal.targetRegularizer_entire χ)).mono (Set.subset_univ _))
      hHσ (fun s hs => hbound s (hsig.trans hs))
      (HeckeSignal.signal_locallyIntegrable χ _ hHd hb _)
      (HeckeSignal.signal_rapidDecayAtZero χ _ hHd hb _)
      hlow herror ?_ hrho ?_ (HeckeSignal.targetRegularizer_ne_zero χ hpoleχ)
    · intro s hs
      have h0 : s ≠ 0 := by intro hh; norm_num [hh] at hs
      have h1 : s ≠ 1 := by intro hh; norm_num [hh] at hs
      change HeckeSignal.regularL χ s *
        Continuation.signalMellin (HeckeSignal.signal χ (sourceCorrection η S) (-11/16))
          (-11/16) s = HeckeSignal.targetRegularizer χ s *
            Continuation.gaussianMultiplier (sourceCorrection η S) s
      rw [HeckeSignal.regularL_eq χ h0 (Or.inl h1),
        HeckeSignal.signalMellin_eq_amplitude χ _ hHd hb (-11/16)
          (baselineBoundary saving) ha2 htop
          (max_lt ((baselineBoundary_improves hsaving).2.trans
            (lt_trans (by norm_num : (7/8:ℝ) < 1) hs)) hs)]
      unfold HeckeSignal.amplitude HeckeSignal.quotient Continuation.gaussianMultiplier
      rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
      have hn := LFunction_ne_zero_of_one_lt_re χ hs
      field_simp
    · exact HeckeSignal.regularL_eq χ
        (by intro hh; simp [hh] at hrho0) hpoleχ
  intro hz
  apply hnonzero
  rw [HeckeFiniteDeletion.LFunction_eq_of_mask_nonpole χ η hmask hrho0 hpoleχ, hz, zero_mul]

/-- The height-controlled form follows by absorption. The probe and signal
remain the same functions for every height and tail order. -/
theorem LFunction_ne_zero_of_probe_bounds {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O))
    (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    [NeZero (∏ P ∈ S, P)] (d : Fin K → ℝ) (a b : ℝ) (W : Fin K → ℝ → ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character)
    (saving A B dmin tau0 : ℝ) (hsaving : 0 < saving)
    (hA : 0 ≤ A) (hd : 0 < dmin) (ht0 : 0 < tau0)
    (hH : AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ | 3/4 < s.re})
    (hbound : ∀ s : ℂ, 3/4 < s.re → ‖sourceCorrection η S s-1‖ ≤ 1/2)
    (hlow : normalizedProbe M H S hmax d a b W W0 W1 η =O[atTop]
      (fun Z : ℝ => Z^(QRHParameterAudit.signal sigma0+baselineLoss)))
    (hhigh : ∀ N : ℕ, ∀ tau : ℝ, 0 < tau → tau ≤ dmin/100 → tau ≤ tau0 →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        ‖normalizedProbe M H S hmax d a b W W0 W1 η Z -
          HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖ ≤
        C*(Z^(QRHParameterAudit.signal (7/8)-saving)*(1+Z^tau)^A +
          Z^(B-(N:ℝ)*tau)))
    {rho : ℂ} (hrho : baselineBoundary saving < rho.re)
    (hpole : rho ≠ 1 ∨ η.residue ≠ 1) : LFunction η rho ≠ 0 := by
  apply LFunction_ne_zero_of_probe_error M H S hS hmax d a b W W0 W1 η
    saving hsaving hH hbound hlow ?_ hrho hpole
  exact absorbed_error_isBigO hsaving hA hd ht0 hhigh

end SevenEighths.ImprovedProbe
end
end OAI
