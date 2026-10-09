import QRHParameterAudit.AnalyticAssembly

namespace OAI.QRHParameterAudit
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology
open AnalyticContinuation

/-- An illustrative first target if the full high estimate retains `gammaSave`. -/
def firstBoundary : ℝ := 3499999 / 4000000

/-- Spend half the gap in the low estimate; the high saving is the smaller constraint. -/
def baselineLoss : ℝ := 21 / 1000000

/-- Every positive all-regime saving gives a strict improvement, however small. -/
def baselineBoundary (saving : ℝ) : ℝ :=
  max (sigma0+baselineLoss) (7/8-saving/2)

theorem baselineBoundary_improves {saving : ℝ} (hsaving : 0 < saving) :
    sigma0 < baselineBoundary saving ∧ baselineBoundary saving < 7/8 := by
  constructor
  · exact (show sigma0 < sigma0+baselineLoss by norm_num [baselineLoss]).trans_le
      (le_max_left _ _)
  · apply max_lt
    · norm_num [sigma0,baselineLoss]
    · linarith

theorem baselineBoundary_eq (saving : ℝ) :
    baselineBoundary saving =
      7/8-continuationMargin sigma0 (7/8) baselineLoss (saving/2) := by
  have h := max_signal_exponents sigma0 (7/8) baselineLoss (saving/2) 0
  simpa only [add_zero,baselineBoundary] using h

theorem firstBoundary_improves :
    sigma0 < firstBoundary ∧ firstBoundary < 7/8 ∧
    7/8-firstBoundary = 1/4000000 := by
  norm_num [sigma0,firstBoundary]

theorem baseline_margin_eq :
    continuationMargin sigma0 (7/8) baselineLoss (gammaSave/2) = gammaSave/2 := by
  norm_num [continuationMargin,sigma0,baselineLoss,gammaSave]

theorem baseline_continuation_below_firstBoundary :
    7/8-continuationMargin sigma0 (7/8) baselineLoss (gammaSave/2) < firstBoundary := by
  rw [baseline_margin_eq]
  norm_num [gammaSave,firstBoundary]

/-- Direct continuation once the actual height and tail estimates have already
been absorbed. This uses the same boundary as the height-controlled version;
its error hypothesis retains half the original saving. -/
theorem nonzero_of_fixed_baseline_error
    (saving : ℝ) (hsaving : 0 < saving)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | sigma0 < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | sigma0 < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | sigma0 < s.re})
    (hcontract : ∀ s : ℂ, sigma0 < s.re → ‖H s-1‖ ≤ (1/2:ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0)) (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun Z : ℝ => Z^(signal sigma0+baselineLoss)))
    (herror : (fun Z => J Z-f Z) =O[atTop]
      (fun Z : ℝ => Z^(signal (7/8)-saving/2)))
    (heq : ∀ s : ℂ, 1 < s.re →
      Lregular s*signalMellin f (-11/16) s = R s*gaussianMultiplier H s)
    {rho : ℂ} (hrho : baselineBoundary saving < rho.re)
    (hregular : Lregular rho = R rho*L rho) (hRrho : R rho ≠ 0) : L rho ≠ 0 := by
  have hloss : 0 < baselineLoss := by norm_num [baselineLoss]
  have hboundary := continuation_boundary_gt sigma0 (7/8) baselineLoss (saving/2) hloss
  apply nonzero_of_common_signal sigma0 (7/8) baselineLoss (saving/2) (-11/16)
    hloss L Lregular R H J f
    (hL.mono (fun s hs => hboundary.trans hs))
    (hR.mono (fun s hs => hboundary.trans hs)) hH hcontract hlocal hzero
  · simpa only [signal_eq,sub_eq_add_neg,neg_div] using hJ
  · simpa only [signal_eq,sub_eq_add_neg,neg_div] using herror
  · intro s hs
    exact heq s ((le_max_right _ _).trans_lt hs)
  · simpa only [baselineBoundary_eq] using hrho
  · exact hregular
  · exact hRrho

/-- A direct consequence of the two fixed-baseline probe estimates.

This does not assert those estimates for the actual Hecke probe. All missing analytic inputs
are arguments. In particular, `hhigh` uses the known upper envelope 7/8, not an unknown zero
supremum, so no supremum bootstrap is needed for this smaller first improvement. -/
theorem nonzero_of_fixed_baseline_bounds
    (saving A B dmin tau0 : ℝ) (hsaving : 0 < saving)
    (hA : 0 ≤ A) (hd : 0 < dmin) (ht0 : 0 < tau0)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular {s : ℂ | sigma0 < s.re})
    (hR : AnalyticOnNhd ℂ R {s : ℂ | sigma0 < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | sigma0 < s.re})
    (hcontract : ∀ s : ℂ, sigma0 < s.re → ‖H s-1‖ ≤ (1/2:ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0)) (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun Z : ℝ => Z^(signal sigma0+baselineLoss)))
    (hhigh : ∀ N : ℕ, ∀ tau : ℝ, 0 < tau → tau ≤ dmin/100 → tau ≤ tau0 →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        ‖J Z-f Z‖ ≤ C*(Z^(signal (7/8)-saving)*(1+Z^tau)^A+Z^(B-(N:ℝ)*tau)))
    (heq : ∀ s : ℂ, 1 < s.re →
      Lregular s*signalMellin f (-11/16) s = R s*gaussianMultiplier H s)
    {rho : ℂ} (hrho : baselineBoundary saving < rho.re)
    (hregular : Lregular rho = R rho*L rho) (hRrho : R rho ≠ 0) : L rho ≠ 0 := by
  apply nonzero_of_fixed_baseline_error saving hsaving L Lregular R H J f
    hL hR hH hcontract hlocal hzero hJ ?_ heq hrho hregular hRrho
  exact absorbed_error_isBigO hsaving hA hd ht0 hhigh

end
end OAI.QRHParameterAudit
