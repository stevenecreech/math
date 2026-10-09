import OAI.NumberTheory.DirichletL.Detector.BaselineInverseFields
import OAI.NumberTheory.DirichletL.Detector.BaselineMarkedMoment
import OAI.NumberTheory.DirichletL.Detector.BaselineUnmarkedMoment
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.ProbeBaselineMomentAssembly
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily CenteredMomentBaselineGeometry
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

theorem exists_count_parameters_at_baseline (S : SourceData D) (G : Geometry D.N) :
    Nonempty (CountParameters S.modulus ⊤ G.t) := by
  exact exists_count_parameters S.modulus ⊤ le_top S.S S.w S.smooth S.compact
    S.positive_support (fun x => (S.bounded x).1) S.nonzero 1 2 1
    (by norm_num) (by norm_num) (by norm_num) S.support
    (fun x => (S.bounded x).2) G.t G.t_pos

/-- The four actual source moment estimates at `Delta = 0`, including the
endpoint marked capacity `3/4`. The moment input is proved from the energy
certificate, with a polynomial height degree fixed before the target.

`S` supplies the fixed source window and exclusions, while all moving slot
lengths and losses are the independent `G`. -/
theorem source_moments_at_baseline (S : SourceData D) (G : Geometry D.N)
    (counts : CountParameters S.modulus ⊤ G.t)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ J : ℕ, ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      1 < Z ∧ ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
      ∀ d : ℝ, (1/200 : ℝ) ≤ d →
      ∀ (a τ dmax slotMesh binWidth height : ℝ) (i : ℕ) (z : ℂ),
      0 ≤ height → z.re = 17/50 → |z.im| ≤ height →
      SourceMomentsAt S.modulus ⊤ le_top S.S S.exclusions.prime η rows G.ell
        (fun _ y => (S.w y : ℂ)) Z d a G.ε τ dmax 2 slotMesh binWidth i z 0
        (if 2*a-1 ≤ 5/6 then counts.cB else counts.cH)
        (if 2*a-1 ≤ 5/6 then counts.kB else counts.kH)
        (C*(1+height)^J) height G.t := by
  obtain ⟨Ji, hi⟩ := ProbeBaselineInverseFields.source_batch_inverse_fields_at_baseline
    S.modulus ⊤ le_top S G counts
  obtain ⟨Jm, hm⟩ := ProbeBaselineMarkedMoment.source_batch_plain_marked_at_baseline
    S G hβlo hβhi
  obtain ⟨Ju, hu⟩ := ProbeBaselineUnmarkedMoment.source_batch_plain_unmarked_at_baseline
    S G hβlo hβhi
  refine ⟨Ji+Jm+Ju, ?_⟩
  intro η
  obtain ⟨Ci, hCi, hi⟩ := hi η
  obtain ⟨Cm, hCm, hm⟩ := hm η
  obtain ⟨Cu, hCu, hu⟩ := hu η
  refine ⟨Ci+Cm+Cu, by positivity, ?_⟩
  filter_upwards [hi, hm, hu] with Z hi hm hu
  refine ⟨hi.1, ?_⟩
  intro rows hrows d hd a τ dmax slotMesh binWidth height i z hheight hz hzim
  have hZ : 0 < Z := zero_lt_one.trans hi.1
  have hbase : 1 ≤ 1+height := by linarith
  have hCi' : Ci*(1+height)^Ji ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega))
      (by positivity) (by positivity)
  have hCm' : Cm*(1+height)^Jm ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega))
      (by positivity) (by positivity)
  have hCu' : Cu*(1+height)^Ju ≤ (Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega))
      (by positivity) (by positivity)
  intro q B hB hdata hreverse hslots hwidth hprofile hupper hexternal
    hslotMesh hbinWidth hfamily bin label left right hne
  have hext : ∀ s, (B.external s).re = 17/50 := by
    intro s
    rw [hexternal]
    exact hz
  have hheight' : ∀ s, |(B.external s).im| ≤ height := by
    intro s
    rw [hexternal]
    exact hzim
  have hinv := hi.2 d hd a G.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hheight
  have hmarked := hm.2 rows hrows d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s => by rw [hupper]) hext bin label left right hne height hheight hheight'
  have hunmarked := hu.2 rows hrows d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hheight
  have hU : 0 ≤ Z^d := Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    have hcap' : 2*(B.fiber bin label left right hne).m+
        6*(3/4)*(∑s∈selected, (B.fiber bin label left right hne).widths s) ≤ 1 := by
      simpa only [mul_zero, add_zero] using hcap
    exact (hmarked selected hselected hcap' j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))

end SevenEighths.ProbeBaselineMomentAssembly

end

end OAI
