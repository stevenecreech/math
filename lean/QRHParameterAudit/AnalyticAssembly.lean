import QRHParameterAudit.Continuation
import QRHParameterAudit.HeightAbsorption

namespace OAI.QRHParameterAudit.AnalyticContinuation
noncomputable section
open Filter Asymptotics MeasureTheory
open scoped Topology

/-- Height absorption followed by actual Mellin continuation and the analytic identity theorem.
Every missing probe/Euler/signal estimate is an explicit argument. This is a general analytic
lemma, not an assertion that those arguments have been constructed for the Hecke family. -/
theorem nonzero_of_height_controlled_signal (boundary beta omega m c A B dmin tau0 : ℝ)
    (homega : 0 < omega) (hm : 0 < m) (hA : 0 ≤ A) (hd : 0 < dmin) (ht0 : 0 < tau0)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : AnalyticOnNhd ℂ Lregular
      {s : ℂ | beta-continuationMargin boundary beta omega (m/2) < s.re})
    (hR : AnalyticOnNhd ℂ R
      {s : ℂ | beta-continuationMargin boundary beta omega (m/2) < s.re})
    (hH : AnalyticOnNhd ℂ H {s : ℂ | boundary < s.re})
    (hcontract : ∀ s : ℂ, boundary < s.re → ‖H s-1‖ ≤ (1/2:ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0)) (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun Z : ℝ => Z^(boundary+c+omega)))
    (hhigh : ∀ N : ℕ, ∀ tau : ℝ, 0 < tau → tau ≤ dmin/100 → tau ≤ tau0 →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        ‖J Z-f Z‖ ≤ C*(Z^(beta+c-m)*(1+Z^tau)^A+Z^(B-(N:ℝ)*tau)))
    (heq : ∀ s : ℂ, max (beta-continuationMargin boundary beta omega (m/2)) 1 < s.re →
      Lregular s*signalMellin f c s = R s*gaussianMultiplier H s)
    {rho : ℂ} (hrho : beta-continuationMargin boundary beta omega (m/2) < rho.re)
    (hregular : Lregular rho = R rho*L rho) (hRrho : R rho ≠ 0) : L rho ≠ 0 := by
  have herror : (fun Z => J Z-f Z) =O[atTop] (fun Z : ℝ => Z^(beta+c-m/2)) :=
    absorbed_error_isBigO hm hA hd ht0 hhigh
  exact nonzero_of_common_signal boundary beta omega (m/2) c homega L Lregular R H J f
    hL hR hH hcontract hlocal hzero hJ herror heq hrho hregular hRrho

end
end OAI.QRHParameterAudit.AnalyticContinuation
