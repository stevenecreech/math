import QRHParameterAudit.LateHeight
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs

namespace OAI.QRHParameterAudit
noncomputable section
open Filter

/-- The polynomial height factor on continuous real scales. -/
theorem polynomial_height_bound {Z tau A : ℝ} (hZ : 1 ≤ Z)
    (ht : 0 ≤ tau) (hA : 0 ≤ A) : (1+Z^tau)^A ≤ 2^A*Z^(tau*A) := by
  have hzpow : 1 ≤ Z^tau := Real.one_le_rpow hZ ht
  calc
    (1+Z^tau)^A ≤ (2*Z^tau)^A := Real.rpow_le_rpow (by positivity) (by linarith) hA
    _ = 2^A*Z^(tau*A) := by
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (by linarith) tau),
        ← Real.rpow_mul (by linarith : 0 ≤ Z)]

/-- Absorb the height factor and tail after their orders have been fixed. -/
theorem absorb_height_and_tail {error : ℝ → ℂ} {target m A B dmin tau0 : ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hd : 0 < dmin) (ht0 : 0 < tau0)
    (hbound : ∀ N : ℕ, ∀ tau : ℝ, 0 < tau → tau ≤ dmin/100 → tau ≤ tau0 →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        ‖error Z‖ ≤ C*(Z^(target-m)*(1+Z^tau)^A+Z^(B-(N:ℝ)*tau))) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop, ‖error Z‖ ≤ C*Z^(target-m/2) := by
  obtain ⟨tau,ht,htd,htt,hAt⟩ := exists_late_height hd ht0 hm hA
  obtain ⟨N,hN⟩ := exists_late_tail (B := B) (target := target-m/2) ht
  obtain ⟨C,hC,hbound⟩ := hbound N tau ht htd htt
  refine ⟨C*(2^A+1),by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have hZ0 : 0 < Z := by linarith
  have hpoly := polynomial_height_bound hZ ht.le hA
  have hfirst : Z^(target-m)*(1+Z^tau)^A ≤ 2^A*Z^(target-m/2) := by
    calc
      _ ≤ Z^(target-m)*(2^A*Z^(tau*A)) :=
        mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hZ0.le _)
      _ = 2^A*Z^(target-m+tau*A) := by rw [mul_left_comm,← Real.rpow_add hZ0]
      _ ≤ 2^A*Z^(target-m/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith only [hAt,hm])) (by positivity)
  have htail : Z^(B-(N:ℝ)*tau) ≤ Z^(target-m/2) :=
    Real.rpow_le_rpow_of_exponent_le hZ hN.le
  calc
    ‖error Z‖ ≤ C*(Z^(target-m)*(1+Z^tau)^A+Z^(B-(N:ℝ)*tau)) := hb
    _ ≤ C*(2^A*Z^(target-m/2)+Z^(target-m/2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hfirst htail) hC.le
    _ = (C*(2^A+1))*Z^(target-m/2) := by ring

/-- The resulting saving is independent of the target's finite height orders. -/
theorem absorbed_error_isBigO {error : ℝ → ℂ} {target m A B dmin tau0 : ℝ}
    (hm : 0 < m) (hA : 0 ≤ A) (hd : 0 < dmin) (ht0 : 0 < tau0)
    (hbound : ∀ N : ℕ, ∀ tau : ℝ, 0 < tau → tau ≤ dmin/100 → tau ≤ tau0 →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
        ‖error Z‖ ≤ C*(Z^(target-m)*(1+Z^tau)^A+Z^(B-(N:ℝ)*tau))) :
    error =O[atTop] (fun Z : ℝ => Z^(target-m/2)) := by
  obtain ⟨C,_,hb⟩ := absorb_height_and_tail hm hA hd ht0 hbound
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z h hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ _)] using h

end
end OAI.QRHParameterAudit
