import QRHParameterAudit.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IrreducibleDef

namespace OAI.QRHParameterAudit

noncomputable section

/-- Fixed common moment loss. -/
def explicitT : ℝ := 1/1000000000000

/-- The exact depth used by `fineMesh 2 0 1 (3/4) (explicitT/4)`. -/
def explicitDepth : ℕ := 256000000000000001

irreducible_def explicitSlotExponent : ℕ := 999999999999999990
def explicitSavingExponent : ℕ := 1000000000000000000

/-- Keep this power symbolic: expanding its decimal representation is neither
needed for the proof nor computationally practical. -/
def explicitSlotCount : ℕ := 2^explicitSlotExponent

/-- A concrete rational improvement, written as the reciprocal of a power. -/
def explicitSaving : ℝ := 1/(2:ℝ)^explicitSavingExponent

/-- A deliberately coarse lower bound for the actual endpoint moment mesh. -/
def explicitMeshLower : ℝ := 1/((10:ℝ)^22*(8:ℝ)^explicitDepth)

theorem explicitT_pos : 0<explicitT := by norm_num [explicitT]

theorem explicitSlotCount_pos : 0<explicitSlotCount := by
  exact pow_pos (by norm_num) _

theorem explicitSlotCount_cast :
    (explicitSlotCount:ℝ)=(2:ℝ)^explicitSlotExponent := by
  simp only [explicitSlotCount, Nat.cast_pow, Nat.cast_ofNat]

theorem explicitSlotCount_cast_pos : 0<(explicitSlotCount:ℝ) := by
  exact_mod_cast explicitSlotCount_pos

theorem explicitSlotCount_large : (10^15:ℝ)≤(explicitSlotCount:ℝ) := by
  rw [explicitSlotCount_cast]
  have hsmall : (10^15:ℝ)≤(2:ℝ)^50 := by norm_num
  exact hsmall.trans (pow_le_pow_right₀ (by norm_num)
    (by norm_num [explicitSlotExponent_def]))

theorem explicitSaving_pos : 0<explicitSaving := by
  unfold explicitSaving
  positivity

theorem explicitSaving_eq :
    explicitSaving=1/(1024*(explicitSlotCount:ℝ)) := by
  rw [explicitSlotCount_cast]
  have he : explicitSavingExponent=explicitSlotExponent+10 := by
    norm_num [explicitSavingExponent, explicitSlotExponent_def]
  unfold explicitSaving
  rw [he, pow_add]
  norm_num only [show (2:ℝ)^10=1024 from by norm_num]
  congr 1
  ring

theorem nat_add_one_le_eight_pow (n : ℕ) : (n:ℝ)+1≤(8:ℝ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 1≤(8:ℝ)^n := one_le_pow₀ (by norm_num)
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

theorem explicitSlotCount_dominates_mesh :
    (10:ℝ)^30*(8:ℝ)^explicitDepth≤(explicitSlotCount:ℝ) := by
  rw [explicitSlotCount_cast]
  have hnum : (10:ℝ)^30≤(2:ℝ)^100 := by norm_num
  have hexp : 100+3*explicitDepth≤explicitSlotExponent := by
    norm_num [explicitDepth, explicitSlotExponent_def]
  have hid : (2:ℝ)^100*(8:ℝ)^explicitDepth=(2:ℝ)^(100+3*explicitDepth) := by
    rw [pow_add, pow_mul]
    norm_num only [show (2:ℝ)^3=8 from by norm_num]
  calc
    _ ≤ (2:ℝ)^100*(8:ℝ)^explicitDepth :=
      mul_le_mul_of_nonneg_right hnum (by positivity)
    _ = _ := hid
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp

theorem explicitMeshLower_pos : 0<explicitMeshLower := by
  unfold explicitMeshLower
  positivity

theorem explicit_inverse_le_mesh_lower :
    1/(explicitSlotCount:ℝ)≤explicitMeshLower/200 := by
  unfold explicitMeshLower
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity)
  calc
    (10:ℝ)^22*(8:ℝ)^explicitDepth*200 =
        ((10:ℝ)^22*200)*(8:ℝ)^explicitDepth := by ring
    _ ≤ (10:ℝ)^30*(8:ℝ)^explicitDepth :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ _ := explicitSlotCount_dominates_mesh

theorem explicit_inverse_le_t :
    1/(explicitSlotCount:ℝ)≤explicitT/200 := by
  have hN : (200000000000000:ℝ)≤(explicitSlotCount:ℝ) :=
    (by norm_num : (200000000000000:ℝ)≤10^15).trans explicitSlotCount_large
  have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<200000000000000) hN
  convert h using 1 <;> norm_num [explicitT]

theorem explicitSlotCount_large_nat : (1000000000000000:ℕ)≤explicitSlotCount := by
  exact_mod_cast explicitSlotCount_large

theorem explicitSaving_le_halfT : explicitSaving≤explicitT/2 := by
  rw [explicitSaving_eq]
  have hN := explicitSlotCount_cast_pos
  have h := (one_div_le_one_div_of_le hN
    (show (explicitSlotCount:ℝ)≤1024*(explicitSlotCount:ℝ) by linarith)).trans
      explicit_inverse_le_t
  exact h.trans (by norm_num [explicitT])

/-- Scalar lower bound for the exact reserve formula. The input `B` is the
final source cap; its bound comes from the existing width recurrence. -/
theorem explicit_mesh_formula_lower (n : ℕ) (B : ℝ)
    (hB : 0≤B) (hBupper : B≤100*(8:ℝ)^n) :
    1/((10:ℝ)^22*(8:ℝ)^n) ≤
      (min ((1/(64000000000000000:ℝ))/100)
        ((explicitT/4)/(1000000*((n:ℝ)+2+10*B+30))))/((3/4:ℝ)+1) := by
  let q : ℝ := (8:ℝ)^n
  have hq : 1≤q := one_le_pow₀ (by norm_num)
  have hqp : 0<q := zero_lt_one.trans_le hq
  have hn : (n:ℝ)≤q := by
    have h := nat_add_one_le_eight_pow n
    dsimp [q]
    linarith
  let L : ℝ := (n:ℝ)+2+10*B+30
  have hL : 0<L := by dsimp [L]; positivity
  have hLupper : L≤1033*q := by dsimp [L]; nlinarith
  have hfirst : 1/(5*(10:ℝ)^21*q)≤(1/(64000000000000000:ℝ))/100 := by
    apply (div_le_iff₀ (by positivity)).mpr
    norm_num
    nlinarith
  have hsecond : 1/(5*(10:ℝ)^21*q)≤(explicitT/4)/(1000000*L) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    norm_num [explicitT]
    nlinarith
  have hbase : 1/((10:ℝ)^22*q)≤(1/(5*(10:ℝ)^21*q))/((3/4:ℝ)+1) := by
    rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact hbase.trans (div_le_div_of_nonneg_right (le_min hfirst hsecond) (by norm_num))

end

end OAI.QRHParameterAudit
