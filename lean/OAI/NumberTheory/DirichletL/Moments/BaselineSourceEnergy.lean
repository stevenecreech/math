import OAI.NumberTheory.DirichletL.Energy.BaselineCertificate
import OAI.NumberTheory.DirichletL.Moments.BaselineGeometry

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.CenteredMomentBaselineSourceEnergy
open HeckeFamily CenteredMomentEnergyBaseline CenteredMomentEnergyBands
open CenteredMomentDetectorPlainMarkedState CenteredMomentDetectorPlainSlotProfile
open CenteredMomentDetectorEnergyInitialState
open CenteredMomentNaturalFixedRaySource CenteredMomentBaselineGeometry
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

/-- Actual endpoint energy estimates for the source's fixed modulus and
window. The new moment geometry is independent of the old `HighData` values.
The estimates themselves are supplied by the terminal energy theorem. -/
theorem source_energy_at_baseline (S : ProbeFinalAssembly.SourceData D)
    (G : Geometry D.N) (bΦ : ℝ) (hbΦ : 0 < bΦ)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ degree : ℕ, ∃ control : Finset (ℕ × ℕ), ∀ η₀ : Character,
      ∃ Czero Cpositive : ℝ, 0 < Czero ∧ 0 < Cpositive ∧
      ∀ᶠ U : ℝ in atTop, 1 < U ∧
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) bΦ
          0 1 2 (G.t/4) U degree control Czero ∧
        PositiveAt (α := Fin D.N) S.modulus ⊤ le_top (fun x => conj (S.W x))
          2 (1/4) (9/4) bΦ 0 1 (mesh G.t) (33/50) (33/50) 2
          (G.t/4) (3/4) U η₀ (sourceFixedIdeal S) degree control Cpositive := by
  obtain ⟨degree, control, hbound⟩ := actual_energy_at_baseline
    (α := Fin D.N) S.modulus ⊤ le_top (fun x => conj (S.W x))
    1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (G.t/4)
    (by norm_num) (conjugate_source_support S)
    (Complex.conjCLE.contDiff.comp (S.W.smooth ⊤))
    (by norm_num) (by norm_num) le_rfl (by norm_num) hbΦ
    (by norm_num) (by norm_num) (allowance_parameters G).1 hβlo hβhi
  refine ⟨degree, control, ?_⟩
  intro η₀
  exact hbound η₀ (sourceFixedIdeal S) (sourceFixedIdeal_le_modulus S)
    (source_fixed_gates S η₀).1
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top S) η₀)
    (source_fixed_gates S η₀).2.2.2

end SevenEighths.CenteredMomentBaselineSourceEnergy

end

end OAI
