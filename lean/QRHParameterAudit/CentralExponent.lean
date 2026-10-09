import QRHParameterAudit.HighRowAssembly

namespace OAI.QRHParameterAudit
noncomputable section

def centralPhysicalScale (a e : ℝ) : ℝ :=
  lx*(4/25)+a+16*e-33/50+ly*(-a-6*e)

theorem central_physical_scale_identity {Z : ℝ} (hZ : 0 < Z) (a e : ℝ) :
    (Z^lx)^(4/25 : ℝ)*Z^(a+16*e-33/50)*(Z^ly)^(-a-6*e) =
      Z^(centralPhysicalScale a e) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ, ←Real.rpow_add hZ]
  congr 1
  unfold centralPhysicalScale
  ring

theorem central_class_exponent_identity (N : ℕ) (a v d R q L e eps loss mesh overhead : ℝ) :
    centralPhysicalScale a e+overhead+d*(R+L)+
        v*(a-1/2+12*e+eps*(N+8)-17/50)+loss+ell*(-4/25+q+mesh) =
      signal sigma0+generalE v (2*a-1) q R+(d-v)*R+d*L+
        (16-6*ly)*e+v*(12*e+(N+8)*eps)+loss+ell*mesh+overhead := by
  unfold centralPhysicalScale signal generalE binA lx ly ell geomH
  ring

/-- The actual class exponent, including count losses and the mismatch
between the physical row dyad and the conductor dyad, retains a strict saving
through the audited extra row-height interval. -/
theorem central_class_saving (N : ℕ) (a v d q L μ e eps loss mesh overhead saving : ℝ)
    (ha : (1/2 : ℝ) < a) (ha' : a ≤ 7/8)
    (hq : 0 ≤ q) (hq' : q ≤ (2*a-1)/2)
    (hv : v ≤ geomH+extension) (hd : d ≤ 1) (hdv : d-v ≤ μ)
    (hL : 0 ≤ L) (hμ : 0 ≤ μ) (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hbudget : L+(3/2)*μ+28*e+(N+8)*eps+loss+ell*mesh+overhead+saving ≤
      (7/8)*gammaSave) :
    centralPhysicalScale a e+overhead+
        d*(SevenEighths.Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+L)+
        v*(a-1/2+12*e+eps*(N+8)-17/50)+loss+ell*(-4/25+q+mesh) ≤
      signal sigma0-saving := by
  have hδ : 0 < 2*a-1 := by linarith
  have hδ' : 2*a-1 ≤ (3/4 : ℝ) := by linarith
  have hx : 0 ≤ q/(2*a-1) := div_nonneg hq hδ.le
  have hx' : q/(2*a-1) ≤ 1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hqeq : q/(2*a-1)*(2*a-1) = q := div_mul_cancel₀ _ hδ.ne'
  have hsave := selected_row_margin hv hδ.le hδ' hx hx'
  rw [hqeq] at hsave
  obtain ⟨hRlo, hRhi⟩ := rowR_bounds hδ.le hδ' hx hx'
  have hRpos : 0 ≤ rowR (2*a-1) (q/(2*a-1)) := by linarith
  have hRmax : rowR (2*a-1) (q/(2*a-1)) ≤ 3/2 := by linarith
  have hμR := mul_le_mul_of_nonneg_right hdv hRpos
  have hμR' := mul_le_mul_of_nonneg_left hRmax hμ
  have hdL := mul_le_mul_of_nonneg_right hd hL
  have hv1 : v ≤ 1 := hv.trans (by norm_num [geomH, extension, gammaSave])
  have hvLoss := mul_le_mul_of_nonneg_right hv1
    (show 0 ≤ 12*e+(N+8)*eps by positivity)
  have heLoss : (16-6*ly)*e ≤ 16*e := by
    have hly : 0 ≤ ly := by norm_num [ly]
    nlinarith
  rw [←rowR_eq_existing]
  rw [central_class_exponent_identity]
  linarith

end
end OAI.QRHParameterAudit
