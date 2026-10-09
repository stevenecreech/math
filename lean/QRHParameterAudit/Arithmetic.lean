import QRHParameterAudit.LowArithmetic
import QRHParameterAudit.OtherRegimes
import QRHParameterAudit.LateHeight

namespace OAI.QRHParameterAudit
noncomputable section

/-- A certificate of parameter arithmetic, with no analytic hypotheses.
Its fields do not assert a zero-free region for any L-function. -/
structure ArithmeticParameterCertificate : Prop where
  improvement : (7:ℝ)/8-sigma0 = 21/500000
  geometry : lx+ly+ell = 1 ∧ ly-lx = b ∧ geomH = 1-lx+ell
  margins : lx-ell = 11703/62500 ∧ ly-ell = 39031/125000 ∧
    ly-ell-11*b/6 = 62311/750000
  gamma_lower : (735:ℝ)/10^9 < gammaSave
  base_rows : ∀ x : ℝ, 0 ≤ x → x ≤ 1/2 →
    37/18 ≤ rowD x ∧ rowD x ≤ 3 ∧ 7/9 ≤ rowP x ∧ rowP x ≤ 2 ∧ 0 ≤ rowD x-rowP x
  boundary : sigma0 = 11/12-ell/4
  bounds : 1/2 < sigma0 ∧ sigma0 < 7/8 ∧ 0 < ell ∧ ell < 1/5 ∧
    0 < lx ∧ 0 < ly ∧ 0 < geomH ∧ 0 < gammaSave
  signal_identity : ∀ s, signal s = s-11/16
  low_signal_identity : lx/2+b/12 = signal sigma0
  low : ∀ u : ℝ, 0 ≤ u → max 0 (5*ell-1+u) ≤ u ∧ lowExtra u ≤ -(7/8)*u ∧ lowExtra u ≤ 0
  row_bounds : ∀ d x : ℝ, 0 ≤ d → d ≤ 3/4 → 0 ≤ x → x ≤ 1/2 →
    35/54 ≤ rowJ d x ∧ rowJ d x ≤ 5/2 ∧
    1 ≤ witnessT d x ∧ witnessT d x ≤ 3/2 ∧
    1-d ≤ rowR d x ∧ rowR d x ≤ 1-d+(5/6-d)/2
  balancing : ∀ d x : ℝ, 0 ≤ d → d ≤ 3/4 → 0 ≤ x → x ≤ 1/2 →
    1-d+d*rowP x/rowD x*(3/2-witnessT d x) = rowR d x
  high : ∀ d x : ℝ, 0 ≤ d → d ≤ 3/4 → 0 ≤ x → x ≤ 1/2 → highE d x ≤ -gammaSave
  floor : ∀ r q : ℝ, r ≤ geomH → q ≤ 1/100 → generalE r (1/50) q 1 ≤ -105343/18750000
  unselected : ∀ r d q : ℝ, 0 ≤ d → d ≤ 3/4 → q ≤ d/2 → r ≤ 1/2 →
    generalE r d q (76/75-2*d/3) ≤ -1872449/75000000
  tiny : geomH*(17/50-1/6)-ly/2+2/100 = -122913/1562500
  supply : ell/geomH-7/37 = 181357/11276934 ∧ 5*ell-geomH = 8033/375000
  extension_supply : 0 < extension ∧ extension < gammaSave/8 ∧
    extension < 5*ell-geomH ∧ 1/5 < ell/(geomH+extension) ∧ (7:ℝ)/37 < 1/5
  extended_high : ∀ d x : ℝ, 0 ≤ d → d ≤ 3/4 → 0 ≤ x → x ≤ 1/2 →
    generalE (geomH+extension) d (x*d) (rowR d x) ≤ -(7/8)*gammaSave
  euler : ∀ s : ℝ, 3/4 ≤ s → 149/100 ≤ eulerC s ∧ (1:ℝ) < 149/100 ∧ 37/50 ≤ slotDecay s

theorem arithmetic_parameter_certificate : ArithmeticParameterCertificate where
  improvement := exact_improvement
  geometry := ⟨slot_sum,slot_difference,height_geometry⟩
  margins := geometry_margins
  gamma_lower := OAI.QRHParameterAudit.gamma_lower
  base_rows := fun _ => row_base_bounds
  boundary := boundary_geometry
  bounds := parameter_bounds
  signal_identity := signal_eq
  low_signal_identity := low_signal
  low := fun _ hu => ⟨positive_part_le hu,low_extra_bound hu,low_extra_nonpos hu⟩
  row_bounds := by
    intro d x hd0 hd1 hx0 hx1
    exact ⟨(rowJ_bounds hd0 hd1 hx0 hx1).1,(rowJ_bounds hd0 hd1 hx0 hx1).2,
      (witness_bounds hd0 hd1 hx0 hx1).1,(witness_bounds hd0 hd1 hx0 hx1).2,
      rowR_bounds hd0 hd1 hx0 hx1⟩
  balancing := fun _ _ hd0 hd1 hx0 hx1 => row_balancing
    (ne_of_gt (rowD_pos hx0 hx1)) (ne_of_gt (rowJ_pos hd0 hd1 hx0 hx1))
  high := fun _ _ => high_margin
  floor := fun _ _ => floor_margin
  unselected := fun _ _ _ => unselected_margin
  tiny := tiny_margin
  supply := ⟨inverse_supply,extension_supply⟩
  extension_supply := extension_bounds
  extended_high := fun _ _ => extended_high_margin
  euler := fun _ => euler_exponents

end
end OAI.QRHParameterAudit
