import OAI.NumberTheory.DirichletL.Moments.DetectorPlainMarkedState
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainUnmarkedState
import OAI.NumberTheory.DirichletL.Energy.WidthRanges

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentBaselineGeometry
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch
open CenteredMomentDetectorPlainMarkedState CenteredMomentEnergyBands
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
local notation "O" => HeckeFamily.O

def mesh (t : ℝ) : ℝ := fineMesh 2 0 1 (3/4) (t/4)

theorem mesh_pos {t : ℝ} (ht : 0 < t) : 0 < mesh t := by
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) (3/4) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by norm_num) (by positivity)).2.2.2.2.1

/-- Moment geometry independent of the old positive supremum gap and slot
total. The slot lengths may therefore be chosen for the improved probe. -/
structure Geometry (N : ℕ) where
  t : ℝ
  ε : ℝ
  ell : Fin N → ℝ
  t_pos : 0 < t
  t_le_one : t ≤ 1
  epsilon_nonneg : 0 ≤ ε
  epsilon_small : ε ≤ 1/1000
  ell_pos : ∀ j, 0 < ell j
  ell_injective : Function.Injective ell
  ell_fine : ∀ j, ell j ≤ mesh t / 200

variable {N : ℕ}

theorem allowance_parameters (G : Geometry N) :
    0 < G.t/4 ∧ G.t/4 ≤ 1/4 ∧ G.t/4+G.t/4 ≤ G.t := by
  constructor
  · exact div_pos G.t_pos (by norm_num)
  constructor <;> linarith [G.t_le_one, G.t_pos]

theorem fine_slot_widths (G : Geometry N) {d : ℝ} (hd : (1/200 : ℝ) ≤ d)
    (s : Fin N) : 0 < G.ell s/d ∧ G.ell s/d ≤ mesh G.t := by
  have hdpos : 0 < d := by linarith
  refine ⟨div_pos (G.ell_pos s) hdpos, (div_le_iff₀ hdpos).mpr ?_⟩
  have hmesh := mesh_pos G.t_pos
  nlinarith [G.ell_fine s]

variable {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
variable {U a tstar T heightAllowance : ℝ} {i : ℕ}

theorem fiber_lengths (G : Geometry N)
    (F : Fiber M H Label Slot U a G.ε tstar T heightAllowance i) (hU : 1 < U) :
    0 ≤ F.m ∧ F.m ≤ 23/40 ∧ 1 ≤ U^F.m ∧ U^F.m ≤ U ∧
      length U (U^F.m) = F.m := by
  have hm := F.lengths hU
  have hcap : F.m ≤ 23/40 := by linarith [hm.2.2.1, G.epsilon_small]
  refine ⟨hm.2.2.2.2, hcap, Real.one_le_rpow hU.le hm.2.2.2.2, ?_, ?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m ≤ 1 by linarith)
  · exact plain_length_eq F hU

theorem width_bands (G : Geometry N) {m : ℝ} (hm : m ≤ 23/40) :
    1 ≤ 1+G.t/4 ∧ 1+G.t/4 ≤ 2 ∧
    1 ≤ max 1 (2*m)+G.t/4 ∧ max 1 (2*m)+G.t/4 ≤ 2 := by
  have hp := allowance_parameters G
  have hmax : max 1 (2*m) ≤ 23/20 := max_le (by norm_num) (by linarith)
  have hlo := le_max_left (1 : ℝ) (2*m)
  constructor
  · linarith [hp.1]
  constructor
  · linarith [hp.2.1]
  constructor <;> linarith [hp.1, hp.2.1]

end SevenEighths.CenteredMomentBaselineGeometry

end

end OAI
