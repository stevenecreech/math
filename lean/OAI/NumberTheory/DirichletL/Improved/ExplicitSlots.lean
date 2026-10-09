import QRHParameterAudit.Parameters
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.ImprovedExplicitSlots

/-- Distinct weights on a prescribed, rather than existential, finite dimension. -/
def weight (N : ℕ) (j : Fin N) : ℝ := 1 + (j.val : ℝ)/(N : ℝ)

def weightSum (N : ℕ) : ℝ := ∑j : Fin N, weight N j

/-- Explicit old-source slots, whose total length is `1/6`. -/
def ell (N : ℕ) (j : Fin N) : ℝ := weight N j/(6*weightSum N)

theorem weight_bounds {N : ℕ} (hN : 0 < N) (j : Fin N) :
    1 ≤ weight N j ∧ weight N j < 2 := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj : (j.val : ℝ) < N := by exact_mod_cast j.isLt
  have hdiv := (div_lt_one hNp).mpr hj
  dsimp only [weight]
  constructor
  · linarith [div_nonneg (Nat.cast_nonneg j.val) hNp.le]
  · linarith

theorem weightSum_bounds {N : ℕ} (hN : 0 < N) :
    (N : ℝ) ≤ weightSum N ∧ weightSum N ≤ 2*(N : ℝ) := by
  constructor
  · calc
      (N : ℝ) = ∑_j : Fin N, (1 : ℝ) := by simp
      _ ≤ weightSum N := Finset.sum_le_sum fun j _ => (weight_bounds hN j).1
  · calc
      weightSum N ≤ ∑_j : Fin N, (2 : ℝ) :=
        Finset.sum_le_sum fun j _ => (weight_bounds hN j).2.le
      _ = 2*(N : ℝ) := by simp [mul_comm]

theorem weightSum_pos {N : ℕ} (hN : 0 < N) : 0 < weightSum N :=
  (show (0 : ℝ) < N by exact_mod_cast hN).trans_le (weightSum_bounds hN).1

theorem ell_pos {N : ℕ} (hN : 0 < N) (j : Fin N) : 0 < ell N j := by
  have hw := (weight_bounds hN j).1
  have hA := weightSum_pos hN
  exact div_pos (by linarith) (by positivity)

theorem ell_injective {N : ℕ} (hN : 0 < N) : Function.Injective (ell N) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hA := weightSum_pos hN
  intro j k he
  have hden : 6*weightSum N ≠ 0 := by positivity
  have hwjk : weight N j = weight N k := (div_left_inj' hden).mp he
  have hjk : (j.val : ℝ)/(N : ℝ) = (k.val : ℝ)/(N : ℝ) := by
    dsimp [weight] at hwjk
    linarith
  have he' : (j.val : ℝ) = (k.val : ℝ) := (div_left_inj' hNp.ne').mp hjk
  apply Fin.ext
  exact_mod_cast he'

theorem ell_sum {N : ℕ} (hN : 0 < N) : (∑j, ell N j) = 1/6 := by
  have hA := (weightSum_pos hN).ne'
  dsimp only [ell]
  rw [← Finset.sum_div]
  change weightSum N/(6*weightSum N) = 1/6
  field_simp

theorem ell_lower {N : ℕ} (hN : 0 < N) (j : Fin N) :
    1/(12*(N : ℝ)) ≤ ell N j := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hA := weightSum_pos hN
  have hAu := (weightSum_bounds hN).2
  calc
    1/(12*(N : ℝ)) ≤ 1/(6*weightSum N) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    _ ≤ ell N j := (div_le_div_iff_of_pos_right (by positivity)).mpr
      (weight_bounds hN j).1

theorem ell_upper {N : ℕ} (hN : 0 < N) (j : Fin N) :
    ell N j ≤ 1/(3*(N : ℝ)) := by
  have hNp : 0 < (N : ℝ) := by exact_mod_cast hN
  have hA := weightSum_pos hN
  have hAl := (weightSum_bounds hN).1
  calc
    ell N j ≤ 2/(6*weightSum N) :=
      (div_le_div_iff_of_pos_right (by positivity)).mpr (weight_bounds hN j).2.le
    _ ≤ 2/(6*(N : ℝ)) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    _ = 1/(3*(N : ℝ)) := by ring

end SevenEighths.ImprovedExplicitSlots

end
end OAI
