import OAI.NumberTheory.DirichletL.Improved.LowNormalized
import OAI.NumberTheory.DirichletL.Improved.Probe

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter Asymptotics
namespace SevenEighths.ImprovedProbe
open HeckeFamily ProbePhysical QRHParameterAudit
local notation "O" => HeckeFamily.O

/-- The low hypothesis in the fixed-baseline continuation theorem, now obtained
for the actual modified probe from its reflected-row estimate. -/
theorem normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀ P ∈ S, P.IsMaximal)
    (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (d : Fin K → ℝ) (hd : ∀ j, 0 < d j) (hinj : Function.Injective d)
    (hsum : ∑ j, d j = ell)
    (W : Fin K → ℝ → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hcompact : ∀ j, HasCompactSupport (W j))
    (hsupp : ∀ j, Function.support (W j) ⊆ Set.Ioo a b)
    (hWB : ∀ j y, 0 ≤ W j y ∧ W j y ≤ B) (hne : ∀ j, W j ≠ 0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0)
    (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re)
    (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0) :
    letI : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀ η : Character, normalizedProbe M H S hmax d a b W W0 W1 η =O[atTop]
      (fun Z : ℝ => Z^(QRHParameterAudit.signal sigma0+baselineLoss)) := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C, hC, hbound⟩ := improved_normalized_compensatedPhysicalProbe_low
    M H hH S hS hmax a b B baselineLoss ha hab (by norm_num [baselineLoss])
    d hd hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  have hexp : lx/2+(ly-lx)/12 = QRHParameterAudit.signal sigma0 := by
    rw [slot_difference]
    exact low_signal
  apply ProbeFinalAssembly.isBigO_rpow_of_eventual_norm_bound
  refine ⟨C, hC, hbound.mono ?_⟩
  intro Z hZ
  simpa only [normalizedProbe, hexp] using hZ.2

end SevenEighths.ImprovedProbe
end
end OAI
