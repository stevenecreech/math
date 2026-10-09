import OAI.NumberTheory.DirichletL.Improved.HighError
import OAI.NumberTheory.DirichletL.Improved.ProbeLow
import OAI.NumberTheory.DirichletL.Improved.SourceData
import OAI.NumberTheory.DirichletL.Improved.Baseline
import OAI.NumberTheory.DirichletL.Improved.Transfer
import OAI.NumberTheory.DirichletL.Improved.ExplicitHighData

/-! Assembly of the fixed-baseline route.

Verification status: this new source and its actual analytic dependency chain
must pass the full targeted build before these declarations can be reported as
verified results. The main `OAI` entry point does not yet import this module.
There are no analytic estimate hypotheses in the statements below. -/

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ImprovedNonvanishing
open HeckeFamily ProbePhysical ProbeFinalAssembly PrincipalSignalComparison
open QRHParameterAudit

/-- The actual Hecke estimate for any admissible common parameter system.
The saving is exposed so a numerical parameter certificate can instantiate it. -/
theorem hecke_nonzero_of_data (D : ImprovedParameters.HighData) :
      ∀ (η : Character) (s : ℂ), baselineBoundary (2*D.sigma) < s.re →
        (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0 := by
  have hsave : 0 < 2*D.sigma := mul_pos (by norm_num) D.sigma_pos
  by_cases hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta
  · obtain ⟨F, hfirst, hcorrection⟩ :=
      ImprovedSourceData.exists_extended_source_data D.carrier D.e D.e_pos
    letI : NeZero (∏ P ∈ F.S, P) :=
      ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
    have hhigh := ImprovedProbe.actual_probe_error D F hfirst hβlo ImprovedBaseline.beta_le_baseline
    have hlow := ImprovedProbe.normalizedProbe_low F.modulus ⊤ le_top
      F.S F.exclusions F.maximal 1 2 1 (by norm_num) (by norm_num)
      D.G.ell D.G.ell_pos D.G.ell_injective D.slots_sum
      (fun _ => F.w) (fun _ => F.smooth) (fun _ => F.compact) (fun _ => F.support)
      (fun _ => F.bounded) (fun _ => F.nonzero)
      F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
      F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative
      F.complex_nonzero F.complex_nonzero
    intro η s hs hpole
    apply ImprovedProbe.LFunction_ne_zero_of_probe_error F.modulus ⊤
      F.S F.exclusions F.maximal D.G.ell 1 2 (fun _ => F.w) F.W F.W η
      (2*D.sigma) hsave (hcorrection η).1 (hcorrection η).2 (hlow η) ?_ hs hpole
    have hexp : QRHParameterAudit.signal (7/8)-(2*D.sigma)/2 = 3/16-D.sigma := by
      rw [signal_eq]
      ring
    simpa only [hexp] using hhigh η
  · intro η s hs hpole
    exact ImprovedBaseline.nonzero_of_small_supremum (lt_of_not_ge hβlo)
      (2*D.sigma) hsave η hs hpole

/-- The low-bound cutoff is inactive for these deliberately small savings. -/
theorem boundary_eq (D : ImprovedParameters.HighData) :
    baselineBoundary (2*D.sigma) = 7/8-D.sigma := by
  have hmax : sigma0+baselineLoss ≤ 7/8-D.sigma := by
    norm_num [sigma0, baselineLoss]
    linarith only [D.t_small, D.high_saving]
  unfold baselineBoundary
  rw [show (2*D.sigma)/2 = D.sigma by ring, max_eq_right hmax]

/-- An admissible parameter system gives precisely the saving stored in it. -/
theorem zeta_nonzero_of_data (D : ImprovedParameters.HighData) (s : ℂ)
    (hs : (7/8 : ℝ)-D.sigma < s.re) : riemannZeta s ≠ 0 := by
  have hb := baselineBoundary_improves
    (mul_pos (show (0 : ℝ) < 2 by norm_num) D.sigma_pos)
  have hb0 : 0 < baselineBoundary (2*D.sigma) :=
    (show (0 : ℝ) < sigma0 by norm_num [sigma0]).trans hb.1
  apply ImprovedTransfer.zeta_nonzero_of_hecke (baselineBoundary (2*D.sigma))
    hb0.le (hecke_nonzero_of_data D) s
  simpa only [boundary_eq D] using hs

/-- A common positive improvement, with the geometry and saving fixed before
every Hecke character. -/
theorem exists_hecke_boundary :
    ∃ boundary : ℝ, 0 < boundary ∧ boundary < 7/8 ∧
      ∀ (η : Character) (s : ℂ), boundary < s.re →
        (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0 := by
  obtain ⟨D⟩ := ImprovedParameters.exists_high_data
  have hb := baselineBoundary_improves
    (mul_pos (show (0 : ℝ) < 2 by norm_num) D.sigma_pos)
  exact ⟨baselineBoundary (2*D.sigma),
    (show (0 : ℝ) < sigma0 by norm_num [sigma0]).trans hb.1, hb.2,
    hecke_nonzero_of_data D⟩

/-- Transfer the same fixed boundary to every Dirichlet character. -/
theorem exists_dirichlet_boundary :
    ∃ boundary : ℝ, 0 < boundary ∧ boundary < 7/8 ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        boundary < s.re → ¬ (χ = 1 ∧ s = 1) → χ.LFunction s ≠ 0 := by
  obtain ⟨boundary, hb0, hb, hH⟩ := exists_hecke_boundary
  refine ⟨boundary, hb0, hb, ?_⟩
  intro q _ χ s hs hpole
  exact ImprovedTransfer.dirichlet_nonzero_of_hecke boundary hb0.le hH χ s hs hpole

/-- A numerical version of the improvement, with the common parameters
constructed for the exact rational margin `2^(-10^18)`.

The enormous exponent is kept symbolic. This draft has the same pending
full-build verification status as the rest of this module. -/
theorem explicit_zeta_nonvanishing (s : ℂ)
    (hs : (7/8 : ℝ) - 1/(2:ℝ)^(1000000000000000000 : ℕ) < s.re) :
    riemannZeta s ≠ 0 := by
  obtain ⟨D, hD⟩ := ImprovedParameters.exists_explicit_high_data
  apply zeta_nonzero_of_data D s
  simpa only [hD, explicitSaving, explicitSavingExponent] using hs

/-- The requested strict improvement for mathlib's actual Riemann zeta
function. The positive margin is allowed to depend on the fixed slot system. -/
theorem exists_strictly_improved_zeta_region :
    ∃ δ : ℝ, 0 < δ ∧ δ < 7/8 ∧
      ∀ s : ℂ, (7/8 : ℝ)-δ < s.re → riemannZeta s ≠ 0 := by
  obtain ⟨boundary, hb0, hb, hH⟩ := exists_hecke_boundary
  refine ⟨7/8-boundary, sub_pos.mpr hb, by linarith, ?_⟩
  intro s hs
  exact ImprovedTransfer.zeta_nonzero_of_hecke boundary hb0.le hH s (by linarith)

end SevenEighths.ImprovedNonvanishing
end
end OAI
