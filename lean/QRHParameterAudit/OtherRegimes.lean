import QRHParameterAudit.HighCertificate
namespace OAI.QRHParameterAudit
noncomputable section

def generalE (r d q R : ℝ) : ℝ :=
  binA d - sigma0 + geomH*(17/50-1/6) - binA d*ly - ell/2 + q*ell
    + r*(R+d/2-17/50)
def extension : ℝ := gammaSave / 16

theorem highE_eq_generalE (d x : ℝ) : highE d x = generalE geomH d (x*d) (rowR d x) := by
  unfold highE generalE
  ring

theorem floor_endpoint : generalE geomH (1/50) (1/100) 1 = -105343/18750000 := by
  norm_num [generalE, binA, geomH, sigma0, ly, ell]

theorem floor_margin {r q : ℝ} (hr : r ≤ geomH) (hq : q ≤ 1/100) :
    generalE r (1/50) q 1 ≤ -105343/18750000 := by
  norm_num [generalE, binA, geomH, sigma0, ly, ell] at *
  linarith

theorem unselected_endpoint (d : ℝ) :
    generalE (1/2) d (d/2) (76/75-2*d/3) = -8263987/37500000 + 195407/750000*d := by
  unfold generalE binA geomH sigma0 ly ell
  ring

theorem unselected_margin {r d q : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 3/4)
    (hq : q ≤ d/2) (hr : r ≤ 1/2) :
    generalE r d q (76/75-2*d/3) ≤ -1872449/75000000 := by
  have hslope : 0 ≤ 101/150-d/6 := by linarith
  have hrow := mul_nonneg (show 0 ≤ 1/2-r by linarith) hslope
  have hq' := mul_nonneg (show 0 ≤ d/2-q by linarith) parameter_bounds.2.2.1.le
  have hend := unselected_endpoint d
  unfold generalE binA geomH sigma0 ly ell at *
  nlinarith only [hd1,hrow,hq',hend]

/-- This tiny-row saving is relative to C(beta), not C(sigma0). -/
theorem tiny_margin : geomH*(17/50-1/6)-ly/2+2/100 = -122913/1562500 := by
  norm_num [geomH, ly]

theorem extension_bounds :
    0 < extension ∧ extension < gammaSave/8 ∧ extension < 5*ell-geomH ∧
    1/5 < ell/(geomH+extension) ∧ (7:ℝ)/37 < 1/5 := by
  norm_num [extension, gammaSave, ell, geomH]

theorem selected_slope {d x : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 3/4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    0 < rowR d x+d/2-17/50 ∧ rowR d x+d/2-17/50 < 2 := by
  obtain ⟨hR0,hR1⟩ := rowR_bounds hd0 hd1 hx0 hx1
  constructor <;> linarith

theorem generalE_extension (z d q R : ℝ) :
    generalE (geomH+z) d q R = generalE geomH d q R + z*(R+d/2-17/50) := by
  unfold generalE
  ring

theorem extended_high_margin {d x : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 3/4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    generalE (geomH+extension) d (x*d) (rowR d x) ≤ -(7/8)*gammaSave := by
  have hE := high_margin hd0 hd1 hx0 hx1
  have hs := (selected_slope hd0 hd1 hx0 hx1).2
  have hmul := mul_le_mul_of_nonneg_left hs.le extension_bounds.1.le
  rw [generalE_extension, ← highE_eq_generalE]
  unfold extension at hmul ⊢
  nlinarith only [hE,hmul]

def eulerC (s : ℝ) : ℝ := min (6*s-301/100) (min (s+47/50) (97/50))
def slotDecay (s : ℝ) : ℝ := min s (min (99/100) (min (5*s-301/100) (47/50)))

theorem euler_exponents {s : ℝ} (hs : 3/4 ≤ s) :
    149/100 ≤ eulerC s ∧ (1:ℝ) < 149/100 ∧ 37/50 ≤ slotDecay s := by
  unfold eulerC slotDecay
  refine ⟨le_min (by linarith) (le_min (by linarith) (by norm_num)), by norm_num,
    le_min (by linarith) (le_min (by norm_num) (le_min (by linarith) (by norm_num)))⟩

end
end OAI.QRHParameterAudit
