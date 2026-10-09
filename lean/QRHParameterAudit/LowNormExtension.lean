import QRHParameterAudit.LowReflectedExtension
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr

/-! Variable-geometry normalization of the low reflected energy.

The energy estimate is an explicit hypothesis. Theorems here do not assert that
the actual compensated probe satisfies that estimate. -/
namespace OAI.QRHParameterAudit
noncomputable section

theorem low_inverse_power_cancel_variable (Z M d α : ℝ) (hZ : 0 < Z) :
    Z^(M-2*d+α)*(Z^d)^2/Z^M = Z^α := by
  have hp : (Z^d)^2 = Z^(2*d) := by
    rw [←Real.rpow_natCast, ←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp, ←Real.rpow_add hZ, ←Real.rpow_sub hZ]
  congr 1
  ring

/-- The original low-energy square-root normalization, with arbitrary physical
scale exponent `M`. -/
theorem low_inverse_sqrt_normalized_variable (q C B Z L M d α H E : ℝ) (n : ℕ)
    (hq : 0 < q) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hZ : 0 < Z) (hL : 0 < L) (hH : 1 ≤ H)
    (hE : 0 ≤ E) (hEL : E ≤ C*H^n*Z^(M-2*d+α)) (hLB : L ≤ B*Z^d) :
    Real.sqrt E / Real.sqrt (q*Z^M/L^2) ≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^M/L^2) ≤ (C*B^2/q)*H^n*Z^α := by
    calc
      _ ≤ (C*H^n*Z^(M-2*d+α))/(q*Z^M/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _ = (C*H^n*Z^(M-2*d+α))*L^2/(q*Z^M) := by field_simp
      _ ≤ (C*H^n*Z^(M-2*d+α))*(B*Z^d)^2/(q*Z^M) := by gcongr
      _ = (C*B^2/q)*H^n*(Z^(M-2*d+α)*(Z^d)^2/Z^M) := by ring
      _ = _ := by rw [low_inverse_power_cancel_variable Z M d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α) = Z^(α/2) := by
    rw [Real.sqrt_eq_rpow, ←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)

/-- The variable reflected cost is harmless in the normalized compensated low
bound. The gain `-7*d/8` remains explicit instead of being discarded. -/
theorem low_compensated_sqrt_bound (q C B Z L total d α H E : ℝ) (n : ℕ)
    (hq : 0 < q) (hC : 0 ≤ C) (hB : 0 ≤ B) (hZ : 1 ≤ Z) (hL : 0 < L) (hH : 1 ≤ H)
    (htotal : total ≤ 1/5) (hd : 0 ≤ d)
    (hE : 0 ≤ E)
    (hEL : E ≤ C*H^n*Z^(1-total-2*d+max 0 (5*total-1+d)/4+α))
    (hLB : L ≤ B*Z^d) :
    Z^(-d)*(Real.sqrt E / Real.sqrt (q*Z^(1-total)/L^2)) ≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2-(7/8)*d) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have he : E ≤ C*H^n*Z^((1-total)-2*d+(max 0 (5*total-1+d)/4+α)) := by
    simpa only [add_assoc] using hEL
  have hb := low_inverse_sqrt_normalized_variable q C B Z L (1-total) d
    (max 0 (5*total-1+d)/4+α) H E n hq hC hB hz hL hH hE he hLB
  have hcost := compensated_reflected_cost total d htotal hd
  calc
    _ ≤ Z^(-d)*(Real.sqrt (C*B^2/q)*H^n*Z^((max 0 (5*total-1+d)/4+α)/2)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (Real.sqrt (C*B^2/q)*H^n)*Z^(-d+(max 0 (5*total-1+d)/4+α)/2) := by
      rw [Real.rpow_add hz]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) (by positivity)

/-- The Gram square-root exponent is `lx/2 + (ly-lx)/12` for arbitrary
positive real scale `Z`; this specializes to the candidate signal exponent. -/
theorem low_gram_sqrt_power_variable (Z x y δ : ℝ) (hZ : 0 < Z) :
    Real.sqrt (Z^x*(Z^(y-x))^(1/6:ℝ)*(Z^y)^δ) =
      Z^(x/2+(y-x)/12+y*δ/2) := by
  rw [←Real.rpow_mul hZ.le, ←Real.rpow_mul hZ.le,
    ←Real.rpow_add hZ, ←Real.rpow_add hZ,
    Real.sqrt_eq_rpow, ←Real.rpow_mul hZ.le]
  congr 1
  ring

theorem low_gram_sqrt_power_candidate (Z δ : ℝ) (hZ : 0 < Z) :
    Real.sqrt (Z^lx*(Z^(ly-lx))^(1/6:ℝ)*(Z^ly)^δ) =
      Z^(signal sigma0+ly*δ/2) := by
  rw [low_gram_sqrt_power_variable Z lx ly δ hZ, slot_difference, low_signal]

end
end OAI.QRHParameterAudit
