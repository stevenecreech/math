import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Exact parameters from `preprints/quasi_riemann_parameter_audit.pdf`.
These arithmetic lemmas make no claim about analytic continuation or zeta zeros. -/
namespace OAI.QRHParameterAudit
noncomputable section

def sigma0 : ℝ := 437479 / 500000
def ell : ℝ := 62563 / 375000
def b : ℝ := 1 / 8
def lx : ℝ := 132781 / 375000
def ly : ℝ := 22457 / 46875
def geomH : ℝ := 50797 / 62500
def gammaSave : ℝ := 35774263 / 48612247200000
def signal (s : ℝ) : ℝ := s + lx / 2 - 1 + geomH / 6

theorem exact_improvement : (7 : ℝ) / 8 - sigma0 = 21 / 500000 := by
  norm_num [sigma0]
theorem slot_sum : lx + ly + ell = 1 := by norm_num [lx, ly, ell]
theorem slot_difference : ly - lx = b := by norm_num [lx, ly, b]
theorem height_geometry : geomH = 1 - lx + ell := by norm_num [geomH, lx, ell]
theorem boundary_geometry : sigma0 = 11 / 12 - ell / 4 := by norm_num [sigma0, ell]
theorem signal_eq (s : ℝ) : signal s = s - 11 / 16 := by
  unfold signal lx geomH
  ring
theorem low_signal : lx / 2 + b / 12 = signal sigma0 := by
  norm_num [signal, lx, b, sigma0, geomH]
theorem signal_at_boundary : signal sigma0 = 93729 / 500000 := by
  rw [signal_eq]; norm_num [sigma0]
theorem geometry_margins :
    lx - ell = 11703 / 62500 ∧ ly - ell = 39031 / 125000 ∧
    ly - ell - 11 * b / 6 = 62311 / 750000 := by
  norm_num [lx, ly, ell, b]
theorem parameter_bounds :
    1 / 2 < sigma0 ∧ sigma0 < 7 / 8 ∧ 0 < ell ∧ ell < 1 / 5 ∧
    0 < lx ∧ 0 < ly ∧ 0 < geomH ∧ 0 < gammaSave := by
  norm_num [sigma0, ell, lx, ly, geomH, gammaSave]
theorem inverse_supply : ell / geomH - 7 / 37 = 181357 / 11276934 := by
  norm_num [ell, geomH]
theorem extension_supply : 5 * ell - geomH = 8033 / 375000 := by
  norm_num [ell, geomH]
theorem gamma_lower : (735 : ℝ) / 10^9 < gammaSave := by norm_num [gammaSave]

end
end OAI.QRHParameterAudit
