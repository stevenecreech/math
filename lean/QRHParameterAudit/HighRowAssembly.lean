import OAI.NumberTheory.DirichletL.Endpoint
import QRHParameterAudit.OtherRegimes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm

namespace OAI.QRHParameterAudit
noncomputable section
open scoped BigOperators

/-! The audit's balanced row exponent agrees exactly with the exponent in the
existing row-count theorem.  At moment parameter `Delta = 0`, that theorem has
plain capacity `3/4` and no `Delta/4` loss.  The estimates below assemble finite
complex row sums from explicit cardinality and pointwise bounds.  They do not
assert those two inputs for the modified physical probe. -/

theorem rowD_eq_existing (x : ℝ) :
    rowD x = SevenEighths.Endpoint.denominator (1/2-x) := by
  unfold rowD SevenEighths.Endpoint.denominator
  ring

theorem rowP_eq_existing (x : ℝ) :
    rowP x = SevenEighths.Endpoint.primeWeight (1/2-x) := by
  unfold rowP SevenEighths.Endpoint.primeWeight
  ring

theorem rowJ_eq_existing (d x : ℝ) :
    rowJ d x = SevenEighths.Endpoint.balanceDenominator d (1/2-x) := by
  unfold rowJ SevenEighths.Endpoint.balanceDenominator
  rw [rowD_eq_existing, rowP_eq_existing]

theorem witnessT_eq_existing (d x : ℝ) :
    witnessT d x = SevenEighths.Endpoint.balancedCutoff d (1/2-x) := by
  unfold witnessT SevenEighths.Endpoint.balancedCutoff
  rw [rowP_eq_existing, rowJ_eq_existing]

theorem rowR_eq_existing (d x : ℝ) :
    rowR d x = SevenEighths.Endpoint.balancedRowCount d (1/2-x) := by
  rw [rowR_long, witnessT_eq_existing]
  unfold SevenEighths.Endpoint.balancedRowCount
  ring

theorem fixed_capacity_of_baseline {beta : ℝ} (hbeta : beta ≤ 7/8) :
    2*beta-1 ≤ (3/4:ℝ) := by linarith

theorem fixed_capacity_identity (m width : ℝ) :
    2*m+6*((3:ℝ)/4+2*0)*width = 2*m+(9/2)*width := by ring

/-- Extend the endpoint saving to every selected row height. -/
theorem selected_row_margin {r d x : ℝ}
    (hr : r ≤ geomH+extension)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 3/4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    generalE r d (x*d) (rowR d x) ≤ -(7/8)*gammaSave := by
  have hs := (selected_slope hd0 hd1 hx0 hx1).1.le
  have hm := mul_le_mul_of_nonneg_right hr hs
  have he := extended_high_margin hd0 hd1 hx0 hx1
  unfold generalE at he ⊢
  linarith

/-- A cardinality estimate and a per-row norm estimate yield a bound for the
actual finite complex sum, including both count and pointwise losses. -/
theorem selected_row_sum_bound {ι : Type*} (rows : Finset ι) (term : ι → ℂ)
    {Z r d x Ccount Cterm countLoss termLoss : ℝ}
    (hZ : 1 ≤ Z) (_hr0 : 0 ≤ r) (hr1 : r ≤ geomH+extension)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 3/4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (hCc : 0 ≤ Ccount) (hCt : 0 ≤ Cterm) (hcountLoss : 0 ≤ countLoss)
    (hbudget : (geomH+extension)*countLoss+termLoss ≤ (3/8)*gammaSave)
    (hcard : (rows.card : ℝ) ≤ Ccount*Z^(r*(rowR d x+countLoss)))
    (hterm : ∀u∈rows, ‖term u‖ ≤
      Cterm*Z^(signal sigma0+generalE r d (x*d) 0+termLoss)) :
    ‖∑u∈rows, term u‖ ≤ Ccount*Cterm*Z^(signal sigma0-gammaSave/2) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hbase := selected_row_margin hr1 hd0 hd1 hx0 hx1
  have hcountCost := mul_le_mul_of_nonneg_right hr1 hcountLoss
  have hexponent :
      r*(rowR d x+countLoss)+
          (signal sigma0+generalE r d (x*d) 0+termLoss) ≤
        signal sigma0-gammaSave/2 := by
    unfold generalE at hbase ⊢
    nlinarith only [hbase, hcountCost, hbudget]
  calc
    ‖∑u∈rows, term u‖ ≤ ∑u∈rows, ‖term u‖ := norm_sum_le _ _
    _ ≤ ∑_u∈rows, Cterm*Z^(signal sigma0+generalE r d (x*d) 0+termLoss) :=
      Finset.sum_le_sum hterm
    _ = (rows.card : ℝ)*(Cterm*Z^(signal sigma0+generalE r d (x*d) 0+termLoss)) := by simp
    _ ≤ (Ccount*Z^(r*(rowR d x+countLoss)))*
        (Cterm*Z^(signal sigma0+generalE r d (x*d) 0+termLoss)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = Ccount*Cterm*Z^(r*(rowR d x+countLoss)+
        (signal sigma0+generalE r d (x*d) 0+termLoss)) := by
      conv_rhs => rw [Real.rpow_add hZp]
      ring
    _ ≤ Ccount*Cterm*Z^(signal sigma0-gammaSave/2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hexponent)
        (mul_nonneg hCc hCt)

/-- A fixed finite collection of bins preserves the selected-row power saving. -/
theorem selected_bins_sum_bound {ι : Type*} (bins : Finset ι) (term : ι → ℂ)
    {Z C : ℝ} (hterm : ∀i∈bins, ‖term i‖ ≤ C*Z^(signal sigma0-gammaSave/2)) :
    ‖∑i∈bins, term i‖ ≤ (bins.card : ℝ)*C*Z^(signal sigma0-gammaSave/2) := by
  calc
    ‖∑i∈bins, term i‖ ≤ ∑i∈bins, ‖term i‖ := norm_sum_le _ _
    _ ≤ ∑_i∈bins, C*Z^(signal sigma0-gammaSave/2) := Finset.sum_le_sum hterm
    _ = _ := by simp [mul_assoc]

end
end OAI.QRHParameterAudit
