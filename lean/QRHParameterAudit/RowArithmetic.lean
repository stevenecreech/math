import QRHParameterAudit.Parameters
namespace OAI.QRHParameterAudit
noncomputable section

def rowD (x : ℝ) : ℝ := 3 - 17 * x / 9
def rowP (x : ℝ) : ℝ := (2 - 8 * x / 9) * (1 - x)
def rowJ (d x : ℝ) : ℝ := (5 / 6 - d) * rowD x + d * rowP x
def witnessT (d x : ℝ) : ℝ := 1 + d * rowP x / (2 * rowJ d x)
def rowR (d x : ℝ) : ℝ :=
  1 - d + (5 / 6 - d) * d * rowP x / (2 * rowJ d x)
def binA (d : ℝ) : ℝ := (1 + d) / 2

theorem row_difference (x : ℝ) : rowD x - rowP x = 1 + x - 8 * x^2 / 9 := by
  unfold rowD rowP; ring

theorem row_base_bounds {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    37 / 18 ≤ rowD x ∧ rowD x ≤ 3 ∧ 7 / 9 ≤ rowP x ∧
    rowP x ≤ 2 ∧ 0 ≤ rowD x - rowP x := by
  have hx2 : x^2 ≤ x / 2 := by nlinarith
  unfold rowD rowP
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

theorem rowJ_bounds {d x : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 35 / 54 ≤ rowJ d x ∧ rowJ d x ≤ 5 / 2 := by
  obtain ⟨_, hD, hP, _, hDP⟩ := row_base_bounds hx0 hx1
  have hpos : 0 ≤ (5 / 6 - d) * (rowD x - rowP x) := mul_nonneg (by linarith) hDP
  have hsub : 0 ≤ d * (rowD x - rowP x) := mul_nonneg hd0 hDP
  unfold rowJ
  constructor <;> nlinarith

theorem rowJ_pos {d x : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 0 < rowJ d x := by
  have h := (rowJ_bounds hd0 hd1 hx0 hx1).1
  linarith

theorem rowD_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 0 < rowD x := by
  have h := (row_base_bounds hx0 hx1).1
  linarith

theorem witness_bounds {d x : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) : 1 ≤ witnessT d x ∧ witnessT d x ≤ 3 / 2 := by
  have hJ := rowJ_pos hd0 hd1 hx0 hx1
  obtain ⟨hD, _, hP, _, _⟩ := row_base_bounds hx0 hx1
  have hn : 0 ≤ d * rowP x := mul_nonneg hd0 (by linarith)
  have hle : d * rowP x ≤ rowJ d x := by
    have hh : 0 ≤ (5 / 6 - d) * rowD x := mul_nonneg (by linarith) (by linarith)
    unfold rowJ
    linarith
  have hratio : d * rowP x / (2 * rowJ d x) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * rowJ d x)).mpr
    linarith
  have hnonneg : 0 ≤ d * rowP x / (2 * rowJ d x) := div_nonneg hn (by positivity)
  unfold witnessT
  constructor <;> linarith

theorem rowR_long (d x : ℝ) :
    rowR d x = 1 - d + (5 / 6 - d) * (witnessT d x - 1) := by
  unfold rowR witnessT
  ring

theorem row_balancing {d x : ℝ} (hD : rowD x ≠ 0) (hJ : rowJ d x ≠ 0) :
    1 - d + d * rowP x / rowD x * (3 / 2 - witnessT d x) = rowR d x := by
  unfold witnessT rowR
  field_simp
  unfold rowJ
  ring

theorem rowR_bounds {d x : ℝ} (hd0 : 0 ≤ d) (hd1 : d ≤ 3 / 4)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    1 - d ≤ rowR d x ∧ rowR d x ≤ 1 - d + (5 / 6 - d) / 2 := by
  obtain ⟨ht0, ht1⟩ := witness_bounds hd0 hd1 hx0 hx1
  have hh : 0 ≤ 5 / 6 - d := by linarith
  have h0 := mul_nonneg hh (show 0 ≤ witnessT d x - 1 by linarith)
  have h1 := mul_le_mul_of_nonneg_left (show witnessT d x - 1 ≤ 1 / 2 by linarith) hh
  rw [rowR_long]
  constructor <;> linarith

end
end OAI.QRHParameterAudit
