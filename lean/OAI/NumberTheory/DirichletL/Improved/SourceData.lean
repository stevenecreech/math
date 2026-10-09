import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
import OAI.NumberTheory.DirichletL.Detector.ImprovedCorrection

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ImprovedSourceData
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeFinalAssembly Parameters
open PrincipalSignalComparison
local notation "O" => HeckeFamily.O

/-- Choose the actual fixed source data, the first-region tail for an independent
detector width, and the extended principal correction at once. All choices occur
before the target character. The old source carrier's own tail is retained too.

This supplies the correction and exclusion hypotheses, not a high-probe bound. -/
theorem exists_extended_source_data {Δ : ℝ} (D : HighData Δ) (e : ℝ) (he : 0 < e) :
    ∃ F : SourceData D, FirstTail (4*e) F.S ∧
      ∀ η : Character,
        AnalyticOnNhd ℂ (sourceCorrection η F.S) {s : ℂ | 3/4 < s.re} ∧
        ∀ s : ℂ, 3/4 < s.re → ‖sourceCorrection η F.S s-1‖ ≤ 1/2 := by
  obtain ⟨N₁, _, hcut₁⟩ := exists_uniform_extended_global_cutoff
  obtain ⟨N₂, _, hcut₂⟩ := exists_first_cutoff (4*e) (by positivity)
  let N := max N₁ N₂
  have hprime : ∀ P ∈ smallPrimeSet N, Prime P := by
    intro P hP
    exact (Finset.mem_filter.mp hP).2
  obtain ⟨S, hsub, hS, hfirst, hmax⟩ :=
    exists_fixed_source D.e D.e_pos (smallPrimeSet N) hprime
  have hcut : ∀ P : PrimeIdeal, P.val.absNorm ≤ N → P.val ∈ S := by
    intro P hP
    exact hsub ((mem_smallPrimeSet N P).mpr hP)
  obtain ⟨w, W, hw, hc, hs, hp, hb, hn, heq, hWn, hWs, hr, hWpos⟩ :=
    exists_fixed_probe_window
  let F : SourceData D :=
    ⟨S, hS, hmax, hfirst, w, W, hw, hc, hs, hp, hb, hn, heq, hWn, hWs, hr, hWpos⟩
  refine ⟨F, hcut₂ S (fun P hP => hcut P (hP.trans (le_max_right _ _))), ?_⟩
  intro η
  exact hcut₁ S (fun P hP => hcut P (hP.trans (le_max_left _ _)))
    η 1 (1/6) (by norm_num) (by norm_num)

end SevenEighths.ImprovedSourceData
end
end OAI
