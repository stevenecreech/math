import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter

namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst
open HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

/-- Cardinalities of actual source batches at endpoint moment capacity. The
moment hypothesis is at `Delta = 0`, so the exponent has no `Delta/4` loss.
The fixed baseline places every nonfloor detector bin in the balanced range. -/
theorem balanced_source_count_at_baseline
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M ≤ H) (S : Finset (Ideal O))
    (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ ⊆ Ioi 0) (hφ0 : ∀ y, 0 ≤ φ y) (hφne : φ ≠ 0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ ≤ b₀) (hB₀ : 0 < B₀)
    (hφs : Function.support φ ⊆ Ioo a₀ b₀) (hφB : ∀ y, φ y ≤ B₀)
    (εm : ℝ) (hεm : 0 < εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0 < dmin) (hdmax : 0 < dmax) (hτ : 0 < τ)
    (hl : 0 < logCost) (hh : τ < heightCost) (hb : 0 < binWidth) :
    ∃ c κ K : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < κ ∧ 0 < K ∧ ∀ᶠ Z : ℝ in atTop,
      ∀ d : ℝ, dmin ≤ d → d ≤ dmax →
      ∀ (a ε ν C q : ℝ) (i : ℕ), i ≤ n →
      51/100 < a → a ≤ 7/8 → 0 ≤ ε → ε ≤ 1/1000 → 0 < ν → 0 ≤ C →
      ∀ {Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card ≤ N → B.binWidth = binWidth → B.rows.Nonempty →
      (∀ u ∈ B.rows, rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths
          B.external (Z^d)) u = q) →
      (∀ bin j J K, ∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) 0 c κ (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card : ℝ) ≤ K*C*Z^(logCost+heightCost+momentCost)*
        (Z^d)^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c, κ, K, hc, hc1, hκ, hK, hcount⟩ :=
    balanced_source_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm Label N n
      dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb
  refine ⟨c, κ, K, hc, hc1, hκ, hK, ?_⟩
  filter_upwards [hcount] with Z hcount
  intro d hd hd' a ε ν C q i hi ha ha' hε hε' hν hC Slot B hslots hbin hne hq hmom
  simpa only [zero_div, add_zero] using
    hcount d hd hd' a ε 0 ν C q i hi ha (by linarith) (by linarith)
      hε hε' le_rfl (by norm_num) hν hC B hslots hbin hne hq hmom

end SevenEighths.ProbeHighRowFamily

end

end OAI
