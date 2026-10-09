import Mathlib.Basic.Real.Basic

/-! Scalar exponents of the actual reflected terminal estimate. These definitions
were moved from `TerminalWidths` without changing their formulas or names. -/
namespace OAI.SevenEighths.InverseTerminalWidths
noncomputable section

def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))

def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2

end
end OAI.SevenEighths.InverseTerminalWidths
