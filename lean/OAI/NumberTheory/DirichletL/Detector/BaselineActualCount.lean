import OAI.NumberTheory.DirichletL.Detector.BaselineMomentAssembly
import OAI.NumberTheory.DirichletL.PrimeRows.BaselineCount

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.ProbeBaselineActualCount
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeFinalAssembly ProbeHighRowFamily CenteredMomentBaselineGeometry ProbeBaselineMomentAssembly
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

/-- Actual balanced row counts for the moving source family at the fixed
baseline. All four required moment estimates are supplied by
`source_moments_at_baseline`; there is no moment-bound premise. -/
theorem actual_balanced_rows_at_baseline (S : SourceData D) (G : Geometry D.N)
    (counts : CountParameters S.modulus ⊤ G.t)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ J : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ᶠ Z : ℝ in atTop, 1 < Z ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
      ∀ d : ℝ, (1/200 : ℝ) ≤ d →
      ∀ (a τ dmax slotMesh binWidth height ν q : ℝ) (i : ℕ) (z : ℂ),
      51/100 < a → a ≤ 7/8 → 0 ≤ height → 0 < ν →
      z.re = 17/50 → |z.im| ≤ height →
      2*Real.pi*((Z^d)^(τ/(2*dmax)))+(3*i : ℕ)*Z^τ ≤ height →
      ∀ B : Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a G.ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows ⊆ rows → B.data = sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η →
      B.reverse = sourceMomentReverse S.modulus ⊤ → B.slots = Finset.univ →
      B.widths = (fun j => G.ell j/d) → B.profile = (fun _ y => (S.w y : ℂ)) →
      B.upper = (fun _ => 2) → B.external = (fun _ => z) →
      B.mesh = slotMesh → B.binWidth = binWidth →
      (∀ u ∈ B.rows, ∀ j, B.family u j = sourceDetectorFamily S.S S.exclusions.prime η u
        (rayCubeFamily S.modulus ⊤ le_top u) j) →
      B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical S.modulus ⊤ (fun u : FreeRow => u.val) B.profile B.upper B.widths
          B.external (Z^d)) u = q) →
      (B.rows.card : ℝ) ≤
        (Fintype.card (Sum Bool (RayQuotient.Characters S.modulus ⊤)) : ℝ)*
        (dyadicLength (Z^d) : ℝ)^2*fiberConstant (C*(1+height)^J) height K*
        (Fintype.card B.Bin : ℝ)*
        (Z^d)^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          159*G.ε+G.t+B.mesh+7*ν) := by
  obtain ⟨J, hmom⟩ := source_moments_at_baseline S G counts hβlo hβhi
  obtain ⟨K, hK, hcount⟩ := counts.balanced
  refine ⟨J, K, hK, ?_⟩
  intro η
  obtain ⟨C, hC, hmom⟩ := hmom η
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmom, eventually_all_rpow_ge hcount (1/200) (by norm_num)]
    with Z hmom hcount
  refine ⟨hmom.1, ?_⟩
  intro rows hrows d hd a τ dmax slotMesh binWidth height ν q i z
    ha ha' hheight hν hz him hfrequency B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hmesh hbinWidth hfamily hne hq
  have hU : 1 < Z^d := Real.one_lt_rpow hmom.1 (by linarith)
  have hδ : 2*a-1 ≤ (5/6 : ℝ) := by linarith
  have hactual := hmom.2 rows hrows d hd a τ dmax slotMesh binWidth height i z
    hheight hz him q B hB hdata hreverse hslots hwidth hprofile hupper hexternal
    hmesh hbinWidth hfamily
  simp only [if_pos hδ] at hactual
  simpa only [zero_div, add_zero] using
    hcount d hd a G.ε (Z^τ) ((Z^d)^(τ/(2*dmax))) 0 ν
      (C*(1+height)^J) height q i hU ha hδ G.epsilon_nonneg G.epsilon_small
      le_rfl (by norm_num) hν (by positivity) hheight hfrequency B hne hq hactual

end SevenEighths.ProbeBaselineActualCount

end

end OAI
