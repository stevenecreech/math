import OAI.NumberTheory.DirichletL.Hecke.Nonvanishing
import QRHParameterAudit.BaselineImprovement

namespace OAI

noncomputable section
namespace SevenEighths.ImprovedBaseline
open HeckeFamily HeckeZeroSupremum QRHParameterAudit

/-- The previously established Hecke theorem supplies the fixed envelope used
by the new endpoint energy and contour arguments. -/
theorem beta_le_baseline : HeckeZeroSupremum.beta ≤ (7/8 : ℝ) := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  obtain ⟨η, s, _, hpole, hz, rfl⟩ := hx
  by_contra h
  apply LFunction_ne_zero_of_seven_eighths_lt_re η (lt_of_not_ge h) ?_ hz
  rintro ⟨hη, hs⟩
  exact hpole.elim (fun h => h hs) (fun h => h hη)

/-- The lower gate in the endpoint energy theorem causes no gap: if the common
zero supremum is already below `51/100`, the proposed first region follows
directly from the definition of that supremum. -/
theorem nonzero_of_small_supremum (hβ : HeckeZeroSupremum.beta < (51/100 : ℝ))
    (saving : ℝ) (hsaving : 0 < saving) (η : Character) {s : ℂ}
    (hs : baselineBoundary saving < s.re) (hpole : s ≠ 1 ∨ η.residue ≠ 1) :
    LFunction η s ≠ 0 := by
  apply LFunction_ne_zero_of_beta_lt η ?_ hpole
  exact hβ.trans ((show (51/100 : ℝ) < sigma0 by norm_num [sigma0]).trans
    ((baselineBoundary_improves hsaving).1.trans hs))

end SevenEighths.ImprovedBaseline
end
end OAI
