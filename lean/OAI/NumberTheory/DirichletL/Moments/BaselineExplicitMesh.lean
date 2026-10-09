import OAI.NumberTheory.DirichletL.Moments.BaselineGeometry
import QRHParameterAudit.ExplicitMeshArithmetic

namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentBaselineGeometry
open QRHParameterAudit CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentFirstSecondLossParameters

theorem explicit_amplification :
    amplification (explicitT/4)=1/(64000000000000000:ℝ) := by
  norm_num [amplification, explicitT]

theorem explicit_depth : count 2 (explicitT/4)=explicitDepth := by
  norm_num [count, depth, explicit_amplification, explicitDepth]

private theorem endpoint_mesh_lower_of_count (n : ℕ)
    (hcount : count 2 (explicitT/4)=n) :
    1/((10:ℝ)^22*(8:ℝ)^n)≤mesh explicitT := by
  have hq : 1≤(8:ℝ)^n := one_le_pow₀ (by norm_num)
  have hr := range_envelope 2 0 1 (by norm_num) (by norm_num) n
  have hB : finalSourceCap 2 0 1 (explicitT/4)≤100*(8:ℝ)^n := by
    unfold finalSourceCap sourceCap
    rw [hcount]
    norm_num at hr
    nlinarith
  have hB0 : 0≤finalSourceCap 2 0 1 (explicitT/4) :=
    sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _
  have h := explicit_mesh_formula_lower n (finalSourceCap 2 0 1 (explicitT/4)) hB0 hB
  simpa only [mesh, fineMesh, CenteredMomentEnergyWidthSchedule.mesh,
    reserve, scale, hcount, explicit_amplification] using h

/-- Quantitative lower bound for the exact mesh used by the actual endpoint
energy certificate, with no unknown analytic constants. -/
theorem explicit_mesh_lower : explicitMeshLower≤mesh explicitT := by
  exact endpoint_mesh_lower_of_count explicitDepth explicit_depth

theorem explicit_slot_mesh :
    1/(explicitSlotCount:ℝ)≤mesh explicitT/200 :=
  explicit_inverse_le_mesh_lower.trans
    (div_le_div_of_nonneg_right explicit_mesh_lower (by norm_num))

theorem explicit_slot_cap :
    1/(explicitSlotCount:ℝ)≤(1/200)*explicitT := by
  simpa only [div_eq_mul_inv, mul_comm] using explicit_inverse_le_t

/-- The explicit old slots have size at most `1/(3*N)`. Rescaling their total
from `1/6` to the audit's `ell` multiplies this bound by `6*ell`. -/
theorem explicit_scaled_slot_mesh :
    2*QRHParameterAudit.ell/(explicitSlotCount:ℝ)≤mesh explicitT/200 := by
  apply le_trans _ explicit_slot_mesh
  exact div_le_div_of_nonneg_right (by norm_num [QRHParameterAudit.ell])
    explicitSlotCount_cast_pos.le

theorem explicit_scaled_slot_cap :
    2*QRHParameterAudit.ell/(explicitSlotCount:ℝ)≤(1/200)*explicitT := by
  apply le_trans _ explicit_slot_cap
  exact div_le_div_of_nonneg_right (by norm_num [QRHParameterAudit.ell])
    explicitSlotCount_cast_pos.le

end SevenEighths.CenteredMomentBaselineGeometry

end

end OAI
