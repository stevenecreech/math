import QRHParameterAudit.Parameters
namespace OAI.QRHParameterAudit
noncomputable section

def lowExtra (u : ℝ) : ℝ := -u + max 0 (5 * ell - 1 + u) / 8

theorem positive_part_le {u : ℝ} (hu : 0 ≤ u) : max 0 (5 * ell - 1 + u) ≤ u := by
  apply max_le hu
  norm_num [ell] at *

theorem low_extra_bound {u : ℝ} (hu : 0 ≤ u) : lowExtra u ≤ -(7 / 8) * u := by
  have h := positive_part_le hu
  unfold lowExtra
  linarith

theorem low_extra_nonpos {u : ℝ} (hu : 0 ≤ u) : lowExtra u ≤ 0 := by
  have h := low_extra_bound hu
  linarith

end
end OAI.QRHParameterAudit
