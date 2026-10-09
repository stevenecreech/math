import QRHParameterAudit.CentralExponent

namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open QRHParameterAudit

/-- The detector floor has a larger margin than the nonfloor endpoint. -/
def auditedFloorExponent (v : ℝ) : ℝ :=
  centralPhysicalScale (51/100) 0+(67/100)*v-(3/20)*ell

def auditedFloorLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (16-6*ly)*e+12*v*e+v*eps*(N+8)+loss+ell*mesh

lemma audited_floor_source_margin {v ζ : ℝ} (hζ : 0≤ζ) (hv : v≤geomH+ζ) :
    auditedFloorExponent v≤3/16-1/200+2*ζ := by
  unfold auditedFloorExponent centralPhysicalScale
  norm_num [lx,ly,ell,geomH] at hv ⊢
  linarith

lemma audited_floor_loss_bound (N : ℕ) {v e eps loss mesh : ℝ}
    (hv : v≤1) (he : 0≤e) (heps : 0≤eps) :
    auditedFloorLoss N v e eps loss mesh≤28*e+(N+8)*eps+loss+ell*mesh := by
  have h1 := mul_le_mul_of_nonneg_right hv he
  have h2 := mul_le_mul_of_nonneg_right hv (show 0≤eps*(N+8) by positivity)
  have hly : 0≤ly := by norm_num [ly]
  unfold auditedFloorLoss
  nlinarith

lemma audited_floor_exponent_identity (N : ℕ) (v e eps loss mesh : ℝ) :
    centralPhysicalScale (51/100) e+
      (v*(67/100+12*e+eps*(N+8))+loss+ell*(-3/20+mesh)) =
    auditedFloorExponent v+auditedFloorLoss N v e eps loss mesh := by
  unfold auditedFloorExponent auditedFloorLoss centralPhysicalScale
  ring

end SevenEighths.ProbeHighRowFamily
end
end OAI
