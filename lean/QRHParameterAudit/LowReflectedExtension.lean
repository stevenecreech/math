import OAI.NumberTheory.DirichletL.Detector.LowReflectedExponent
import QRHParameterAudit.LowArithmetic

/-! The reflected terminal exponent with a variable total slot length.

This is the repository's original reflected exponent, with its original hybrid
saving and retained-kernel term. The extra cost is tracked explicitly. It is a
scalar step in the actual low-energy proof, not an estimate for the physical
probe or an unconditional improved nonvanishing theorem. -/
namespace OAI.QRHParameterAudit
noncomputable section
open SevenEighths.InverseTerminalWidths SevenEighths.ProbeLowReflected

/-- Generalization of `compensated_reflected_exponent_with_length` to physical
row length `1 - total - 2*d` and surviving slot length at most `total - d`.
The bound includes the extra reflected cost that appears when `total > 1/6`. -/
theorem compensated_reflected_exponent_variable
    (total d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hO : -ε ≤ O₀) (hH : H ≤ (1-total-2*d)-O₀+ε)
    (hA : 2*A₀ ≤ O₀+ε) (hN : 0 ≤ N₀) (hNA : N₀ ≤ A₀)
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀) (hell : ell₀ ≤ total-d+ε) (hz : za ≤ ell₀+ε)
    (hv : -ε ≤ v) (hl : -ε ≤ ell) (he : -ε ≤ el) (hθ : |θ| ≤ ε)
    (hret : v+3*ell+el ≤ 2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀+ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀) ≤
        1-total-2*d + max 0 (5*total-1+d)/4 + 40*ε := by
  let Td := 2*H+2*A₀+2*za-1-ell₀-θ-N₀-3*B₀
  have hθlo : -ε ≤ θ := (abs_le.mp hθ).1
  have hθhi : θ ≤ ε := (abs_le.mp hθ).2
  have hTd : Td ≤ H-3*d+6*ε := by dsimp [Td]; linarith
  have hcol : v+ell ≤ H+10*ε := by dsimp [Td] at hTd; linarith
  have hmax : max H (v+ell) ≤ H+10*ε := max_le (by linarith) hcol
  have hk := le_max_left 0 (Td-v-3*ell-el)
  have hcost0 := le_max_left 0 (5*total-1+d)
  have hcost := le_max_right 0 (5*total-1+d)
  by_cases hu : hybridSaving v za = za
  · unfold reflectedExponent
    rw [hu]
    change O₀/2+max H (v+ell)-S₀-B₀+za-za-ell-2*el/3-
      max 0 (Td-v-3*ell-el)/2 ≤ _
    linarith
  · have hhalf := hybrid_half_with_error hv hε hu
    have hquarter := retained_kernel_quarter Td (v+3*ell+el)
    have hcharge : Td/4-17*ε/12 ≤
        hybridSaving v za+ell+2*el/3+max 0 (Td-v-3*ell-el)/2 := by
      have heq : Td-(v+3*ell+el) = Td-v-3*ell-el := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤
        O₀/2+H-S₀-B₀+za-Td/4+(10+17/12)*ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el Td ≤ _
    apply hbound.trans
    dsimp [Td]
    linarith

/-- The reflected cost is absorbed after the square root and the compensated
unselected-tuple factor, for every total slot length at most `1/5`. -/
theorem compensated_reflected_cost (total d : ℝ) (htotal : total ≤ 1/5) (hd : 0 ≤ d) :
    -d + max 0 (5*total-1+d)/8 ≤ -(7/8)*d := by
  have hcost : max 0 (5*total-1+d) ≤ d := max_le hd (by linarith)
  linarith

/-- In particular, the candidate's reflected correction loses no power of `Z`
after the unselected-tuple compensation. -/
theorem candidate_compensated_reflected_cost (d : ℝ) (hd : 0 ≤ d) :
    -d + max 0 (5*OAI.QRHParameterAudit.ell-1+d)/8 ≤ -(7/8)*d :=
  compensated_reflected_cost _ _ parameter_bounds.2.2.2.1.le hd

end
end OAI.QRHParameterAudit
