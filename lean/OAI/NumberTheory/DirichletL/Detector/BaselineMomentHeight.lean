import OAI.NumberTheory.DirichletL.Detector.BaselineMomentAssembly

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.ProbeBaselineMomentAssembly
open HeckeFamily HeckeInverseAmplification ProbeFinalAssembly ProbeHighRowFamily
open CenteredMomentBaselineGeometry
variable {Δ : ℝ} {D : Parameters.HighData Δ}

/-- Actual endpoint moments at a power height. The finite degree is chosen
before the height exponent, and before the target character. Consequently
the height exponent can be made small enough for any positive loss budget. -/
theorem source_moments_at_power_height (S : SourceData D) (G : Geometry D.N)
    (counts : CountParameters S.modulus ⊤ G.t)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ J : ℕ, ∀ η : Character, ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      1 < Z ∧ ∀ heightCost momentCost : ℝ, 0 ≤ heightCost →
      heightCost*J ≤ momentCost →
      ∀ rows : Finset FreeRow,
      (∀ u ∈ rows, Z^(1/100 : ℝ) ≤ rowNorm u) →
      ∀ d : ℝ, (1/200 : ℝ) ≤ d →
      ∀ (a τ dmax slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ),
      z.re = 17/50 → |z.im| ≤ Z^heightCost →
      SourceMomentsAt S.modulus ⊤ le_top S.S S.exclusions.prime η rows G.ell
        (fun _ y => (S.w y : ℂ)) Z d a G.ε τ dmax 2 slotMesh binWidth i z 0
        (if 2*a-1 ≤ 5/6 then counts.cB else counts.cH)
        (if 2*a-1 ≤ 5/6 then counts.kB else counts.kH)
        (C*Z^momentCost) (Z^heightCost) G.t := by
  obtain ⟨J, hbound⟩ := source_moments_at_baseline S G counts hβlo hβhi
  refine ⟨J, ?_⟩
  intro η
  obtain ⟨C, hC, hbound⟩ := hbound η
  refine ⟨C*2^J, by positivity, ?_⟩
  filter_upwards [hbound] with Z hZ
  refine ⟨hZ.1, ?_⟩
  intro heightCost momentCost hh hbudget rows hrows d hd a τ dmax slotMesh binWidth i z hz hzim
  have hZp : 0 < Z := zero_lt_one.trans hZ.1
  have hscale : 1 ≤ Z^heightCost := Real.one_le_rpow hZ.1.le hh
  have hconstant : C*(1+Z^heightCost)^J ≤ (C*2^J)*Z^momentCost := by
    calc
      _ ≤ C*(2*Z^heightCost)^J := by gcongr; linarith
      _ = (C*2^J)*Z^(heightCost*J) := by
        rw [mul_pow, ←Real.rpow_natCast (Z^heightCost) J,
          ←Real.rpow_mul hZp.le]
        ring
      _ ≤ (C*2^J)*Z^momentCost :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hZ.1.le hbudget) (by positivity)
  exact sourceMomentsAt_mono_constant S.modulus ⊤ le_top S.S S.exclusions.prime η rows G.ell
    (fun _ y => (S.w y : ℂ)) Z d a G.ε τ dmax 2 slotMesh binWidth i z 0 _ _
    (C*(1+Z^heightCost)^J) ((C*2^J)*Z^momentCost) (Z^heightCost) G.t
    hZp.le hconstant
    (hZ.2 rows hrows d hd a τ dmax slotMesh binWidth (Z^heightCost) i z
      (Real.rpow_nonneg hZp.le _) hz hzim)

end SevenEighths.ProbeBaselineMomentAssembly

end

end OAI
