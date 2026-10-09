import OAI.NumberTheory.DirichletL.PrimeRows.DetectorZeros
import OAI.NumberTheory.DirichletL.Hecke.ZeroSupremum

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily
variable {ι : Type*} [Fintype ι]

/-- The physical detector has only the fixed sentinel and actual Hecke zero
real parts; its maximum therefore respects any envelope for that family. -/
theorem detectorMaximum_le_envelope (χ : ι → Character) (T B : ℝ)
    (hB : (51/100 : ℝ) ≤ B) (hβ : HeckeZeroSupremum.beta ≤ B) :
    detectorMaximum χ T ≤ B := by
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hB
  · obtain ⟨⟨i, s⟩, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hlo, _, _, hz, hpole⟩ := (mem_detectorFamilyZeros χ T i s).mp hs
    exact (HeckeZeroSupremum.zero_re_le_beta (χ i) (by linarith)
      (by tauto) hz).trans hβ

/-- At the fixed baseline, all physical nonfloor bins have `2*a-1 ≤ 3/4`.
There is no loss involving the bin width in this upper bound. -/
theorem detector_bin_le_baseline (χ : ι → Character) (T a : ℝ)
    (hβ : HeckeZeroSupremum.beta ≤ (7/8 : ℝ))
    (ha : a ≤ detectorMaximum χ T) :
    a ≤ (7/8 : ℝ) ∧ 2*a-1 ≤ (3/4 : ℝ) := by
  have h := ha.trans (detectorMaximum_le_envelope χ T (7/8) (by norm_num) hβ)
  exact ⟨h, by linarith⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
