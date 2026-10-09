import QRHParameterAudit.RowArithmetic
namespace OAI.QRHParameterAudit
noncomputable section

def highE (d x : ℝ) : ℝ :=
  binA d - sigma0 + geomH * (rowR d x + d / 2 - 1 / 6)
    - binA d * ly - ell / 2 + x * d * ell

def polyA (y : ℝ) : ℝ :=
  38265876 + 98256048*y + 70521168*y^2 + 24024192*y^3
def polyB (y : ℝ) : ℝ := -29594760 - 47116180*y - 3252520*y^2
def polyC (y : ℝ) : ℝ := 5722975 + 5258950*y
def endpointPoly (d y : ℝ) : ℝ := polyA y*d^2 + polyB y*d + polyC y
def discPoly (y : ℝ) : ℝ := 4*polyA y*polyC y - (polyB y)^2

theorem endpoint_identity {d x : ℝ} (hJ : rowJ d x ≠ 0) :
    81000000 * (-2 * rowJ d x * highE d x) = endpointPoly d (1/2-x) := by
  unfold highE binA rowR endpointPoly polyA polyB polyC sigma0 geomH ly ell
  field_simp
  unfold rowJ rowD rowP
  ring

theorem discriminant_identity (y : ℝ) :
    discPoly y = 128787346800 + 265436861138400*y + 1268808584874800*y^2
      + 1726935951112000*y^3 + 494789211723200*y^4 := by
  unfold discPoly polyA polyB polyC
  ring

theorem square_identity (d y : ℝ) :
    4*polyA y*endpointPoly d y = (2*polyA y*d + polyB y)^2 + discPoly y := by
  unfold endpointPoly discPoly
  ring

theorem polyA_pos {y : ℝ} (hy : 0 ≤ y) : 0 < polyA y := by
  unfold polyA
  positivity

theorem polyA_upper {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) : polyA y ≤ 108027216 := by
  have hy2 : y^2 ≤ 1/4 := by nlinarith
  have hy3 : y^3 ≤ 1/8 := by
    have h := mul_le_mul_of_nonneg_right hy2 hy0
    nlinarith
  unfold polyA
  nlinarith only [hy1, hy2, hy3]

theorem discriminant_lower {y : ℝ} (hy : 0 ≤ y) : 128787346800 ≤ discPoly y := by
  rw [discriminant_identity]
  have h1 : 0 ≤ 265436861138400*y := by positivity
  have h2 : 0 ≤ 1268808584874800*y^2 := by positivity
  have h3 : 0 ≤ 1726935951112000*y^3 := by positivity
  have h4 : 0 ≤ 494789211723200*y^4 := by positivity
  linarith only [h1,h2,h3,h4]

theorem endpoint_positive {d y : ℝ} (hy : 0 ≤ y) : 0 < endpointPoly d y := by
  have hA := polyA_pos hy
  have hdisc := discriminant_lower hy
  have hid := square_identity d y
  have hsq := sq_nonneg (2*polyA y*d + polyB y)
  nlinarith only [hA,hdisc,hid,hsq]

theorem endpoint_lower {d y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) :
    128787346800 ≤ 4*108027216*endpointPoly d y := by
  have hP := endpoint_positive (d := d) hy0
  have hA := polyA_upper hy0 hy1
  have hdisc := discriminant_lower hy0
  have hid := square_identity d y
  have hsq := sq_nonneg (2*polyA y*d + polyB y)
  have hmul := mul_nonneg (show 0 ≤ 108027216-polyA y by linarith) hP.le
  nlinarith only [hdisc,hid,hsq,hmul]

/-- Uniform on the full real rectangle, with an exact rational saving. -/
theorem high_margin {d x : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 3/4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : highE d x ≤ -gammaSave := by
  have hy0 : 0 ≤ 1/2-x := by linarith
  have hy1 : 1/2-x ≤ 1/2 := by linarith
  have hJ := rowJ_pos hd0 hd1 hx0 hx1
  have hJu := (rowJ_bounds hd0 hd1 hx0 hx1).2
  have hid := endpoint_identity (ne_of_gt hJ)
  have hP := endpoint_positive (d := d) hy0
  have hPl := endpoint_lower (d := d) hy0 hy1
  have hE : highE d x < 0 := by nlinarith only [hJ,hid,hP]
  have hmul := mul_nonneg (show 0 ≤ 5-2*rowJ d x by linarith) (neg_nonneg.mpr hE.le)
  unfold gammaSave
  nlinarith only [hid,hPl,hmul]

end
end OAI.QRHParameterAudit
