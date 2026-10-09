import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyBaseline
open HeckeFamily CenteredMomentEnergyCertifiedExistence
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

/-- The actual terminal energy certificate is valid at the endpoint capacity
`3/4` under the fixed `7/8` envelope. No positive supremum gap is required. -/
theorem terminal_certificate_at_baseline
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    CertifiedBand (α := α) M H hH W bslot a b radial Bmask L lo hi Mcap
      (3/4) ε (count Mcap ε) := by
  exact terminal_certificate (α := α) M H hH W aslot bslot a b radial Bmask
    L lo hi Mcap (3/4) ε haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap
    le_rfl hε hβlo (by linarith)

/-- Endpoint capacity bounds for the actual zero-slot and positive-slot
energy families, with seminorms and height degree fixed before the character. -/
theorem actual_energy_at_baseline
    (W : ℝ → ℂ) (aslot bslot a b radial Bmask L lo hi Mcap ε : ℝ)
    (haslot : 0 < aslot) (hWs : Function.support W ⊆ Set.Icc aslot bslot)
    (hW : ContDiff ℝ ∞ W) (hbslot : 0 ≤ bslot)
    (ha : 0 < a) (haUpper : a ≤ 1/4) (hb : 1 ≤ b) (hrad : 0 < radial)
    (hmask : 0 ≤ Bmask) (hMcap : 0 < Mcap) (hε : 0 < ε)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∀ η₀ : Character, ∀ Q : Ideal O,
      Q ≤ M → internalQ Q η₀ ≠ 0 → internalQ Q η₀ ≠ ⊤ →
      internalQ Q η₀ ≤ Ideal.span {(72 : O)} →
      ∃ Czero Cpositive : ℝ, 0 < Czero ∧ 0 < Cpositive ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧
        ZeroAt (internalQ Q η₀) a b radial Bmask L Mcap ε Z degree S Czero ∧
        PositiveAt (α := α) M H hH W bslot a b radial Bmask L
          (fineMesh Mcap Bmask L (3/4) ε) lo hi Mcap ε (3/4) Z η₀ Q
          degree S Cpositive := by
  apply certified_terminal (α := α) M H hH W bslot a b radial Bmask L lo hi
    Mcap (3/4) ε hmask hMcap.le (by norm_num) hε
  exact terminal_certificate_at_baseline (α := α) M H hH W aslot bslot a b radial
    Bmask L lo hi Mcap ε haslot hWs hW hbslot ha haUpper hb hrad hmask hMcap hε
    hβlo hβhi

end SevenEighths.CenteredMomentEnergyBaseline

end

end OAI
