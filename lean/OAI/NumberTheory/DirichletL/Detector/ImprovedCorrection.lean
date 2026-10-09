import OAI.NumberTheory.DirichletL.Detector.SourceExclusions
import QRHParameterAudit.IdealEulerProduct

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalQuadraticSieve CompletedGauss ProbeEuler
open QRHParameterAudit.EulerExtension
local notation "Id" => Ideal HeckeFamily.O

/-- The actual correction in the physical probe is the ideal product already bounded
in the parameter audit; in particular its phases are the actual Hecke phases. -/
theorem globalClosedCorrection_eq_idealCorrection
    (η : HeckeFamily.Character) (S : Finset Id) (x w z : ℂ) :
    globalClosedCorrection η S x w z =
      idealCorrection HeckeFamily.K
        (fun P => actualAPhase η (primaryGenerator P.val))
        (fun P => HeckeFamily.idealCoeff η P.val) (fun _ => 1) S x w z := rfl

/-- One cutoff works for the actual Hecke correction in the larger half-plane,
uniformly before the character and the two other contour variables are chosen. -/
theorem exists_uniform_extended_global_cutoff :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ S : Finset Id,
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ η : HeckeFamily.Character, ∀ w z : ℂ,
        (19/20:ℝ) ≤ w.re → (33/200:ℝ) ≤ z.re →
        AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z)
          {x : ℂ | 3/4 < x.re} ∧
        ∀ x : ℂ, 3/4 < x.re → ‖globalClosedCorrection η S x w z-1‖ ≤ 1/2 := by
  obtain ⟨N, hN, hcut⟩ := exists_uniform_ideal_cutoff HeckeFamily.K
  refine ⟨N, hN, ?_⟩
  intro S hS η w z hw hz
  exact hcut S hS
    (fun P => actualAPhase η (primaryGenerator P.val))
    (fun P => HeckeFamily.idealCoeff η P.val) (fun _ => 1)
    (fun _ => actualAPhase_norm_le_one η _)
    (fun _ => HeckeFamily.idealCoeff_norm_le_one η _) (fun _ => by simp) w z hw hz

/-- The source exclusions required by all existing physical-probe identities can
be chosen simultaneously with the extended correction bound. -/
theorem exists_extended_source_exclusions (S₀ : Finset Id)
    (hp : ∀ P ∈ S₀, Prime P) (hbad : fixedBadPrimes ⊆ S₀) :
    ∃ S : Finset Id, S₀ ⊆ S ∧ SourceExclusions S ∧
      ∀ η : HeckeFamily.Character, ∀ w z : ℂ,
        (19/20:ℝ) ≤ w.re → (33/200:ℝ) ≤ z.re →
        AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z)
          {x : ℂ | 3/4 < x.re} ∧
        ∀ x : ℂ, 3/4 < x.re → ‖globalClosedCorrection η S x w z-1‖ ≤ 1/2 := by
  obtain ⟨N, _, hcut⟩ := exists_uniform_extended_global_cutoff
  have hp' : ∀ P ∈ S₀ ∪ smallPrimeSet N, Prime P := by
    intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hp P hP
    · exact (Finset.mem_filter.mp hP).2
  obtain ⟨S, hS, hsource⟩ := exists_source_exclusions
    (S₀ ∪ smallPrimeSet N) hp' (hbad.trans Finset.subset_union_left)
  refine ⟨S, Finset.subset_union_left.trans hS, hsource, hcut S ?_⟩
  intro P hP
  exact hS (Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP))

/-- In particular the actual principal correction extends with the same exclusions. -/
theorem exists_extended_principal_source (S₀ : Finset Id)
    (hp : ∀ P ∈ S₀, Prime P) (hbad : fixedBadPrimes ⊆ S₀) :
    ∃ S : Finset Id, S₀ ⊆ S ∧ SourceExclusions S ∧
      ∀ η : HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection η S) {x : ℂ | 3/4 < x.re} ∧
        ∀ x : ℂ, 3/4 < x.re → ‖principalCorrection η S x-1‖ ≤ 1/2 := by
  obtain ⟨S, hS, hsource, hext⟩ := exists_extended_source_exclusions S₀ hp hbad
  refine ⟨S, hS, hsource, ?_⟩
  intro η
  simpa only [source_globalCorrection_principal S hsource η] using
    hext η 1 (1/6) (by norm_num) (by norm_num)

end SevenEighths.ProbePhysical
end
end OAI
