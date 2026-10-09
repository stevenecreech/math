import OAI.NumberTheory.DirichletL.Detector.PrincipalPhysicalRemainder
import QRHParameterAudit.Parameters

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex Set MeasureTheory
namespace SevenEighths.ImprovedPrincipalRemainder
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
open ProbePrincipalRemainderBounds ProbePrincipalPhysical QRHParameterAudit
local notation "Id" => Ideal HeckeFamily.O

/-- A convenient saving left by both genuine principal contour remainders. -/
def contourSaving : ℝ := 1/4000

theorem contourSaving_pos : 0 < contourSaving := by norm_num [contourSaving]

lemma source_scale_identity {ι : Type*} (J : Finset ι) (d : ι → ℝ)
    (hd : ∑ j ∈ J, d j = ell) (Z a ξ υ : ℝ) (hZ : 0 < Z) :
    scalePower (Z^lx) (Z^ly) Z a ξ υ * (∏ j ∈ J, (Z^(d j))^ξ) =
      Z^(a-11/16+geomH*(ξ-1/6)+ly*(υ-1)) := by
  have hp : (∏ j ∈ J, (Z^(d j))^ξ) = Z^(ell*ξ) := by
    simp only [← Real.rpow_mul hZ.le]
    rw [← Real.rpow_sum_of_pos hZ, ← Finset.sum_mul, hd]
  rw [hp, scalePower, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  norm_num [lx, ly, ell, geomH]
  ring

lemma source_w_scale_identity {ι : Type*} (J : Finset ι) (d : ι → ℝ)
    (hd : ∑ j ∈ J, d j = ell) (Z a e : ℝ) (hZ : 0 < Z) :
    scalePower (Z^lx) (Z^ly) Z a (1/6+e) (19/20) *
      (∏ j ∈ J, (Z^(d j))^(1/6+e)) = Z^(a-11/16+geomH*e-ly/20) := by
  rw [source_scale_identity J d hd Z a (1/6+e) (19/20) hZ]
  congr 1
  ring

lemma source_z_scale_identity {ι : Type*} (J : Finset ι) (d : ι → ℝ)
    (hd : ∑ j ∈ J, d j = ell) (Z a : ℝ) (hZ : 0 < Z) :
    scalePower (Z^lx) (Z^ly) Z a (33/200) 1 *
      (∏ j ∈ J, (Z^(d j))^(33/200:ℝ)) = Z^(a-11/16-geomH/600) := by
  rw [source_scale_identity J d hd Z a (33/200) 1 hZ]
  congr 1
  ring

/-- Both ordered contour integrals for the actual Hecke source have a uniform
positive saving at the fixed baseline, with the audited physical lengths.
The premise `hbeta` is the original seven-eighths theorem expressed as a supremum bound. -/
theorem source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c b B : ℝ) (hc : 0 < c) (hcb : c ≤ b) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (hbeta : HeckeZeroSupremum.beta ≤ 7/8)
    (e : ℝ) (he : 0 < e) (hehi : e ≤ 1/1000) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ι → ℝ, (∑ j ∈ J, d j = ell) → ∀ W : ι → ℝ → ℝ,
      (∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B) →
      (∀ j ∈ J, Function.support (W j) ⊆ Icc c b) → ∀ T : ι → Finset PrimeIdeal,
      (∀ j ∈ J, ∀ p ∈ T j, p.val ∉ S) → ∀ Z : ℝ, 1 ≤ Z →
      (∀ j ∈ J, 480 ≤ c*Z^(d j)) →
      (∀ j ∈ J, (Ideal.absNorm η.modulus:ℝ) < c*Z^(d j)) →
      let K0 := fun s => sourceMultiplier W0 W1 (Z^lx) (Z^ly) Z
        (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
        (windowMultiplier η J T (fun j x => (W j x:ℂ)) (fun j => Z^(d j)) s)
      let π := fixedSourcePrincipal S hS.prime
      (‖verticalIntegral (7/8+e) (fun s => verticalIntegral (1/6+e)
        (fun z => verticalIntegral (19/20)
          (fun w => K0 s w z*LFunction π (6*z)*LFunction π w)))‖ ≤
        C/e*Z^(7/8-11/16-contourSaving)) ∧
      (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (7/8+e)
        (fun s => verticalIntegral (33/200) (fun z => K0 s 1 z*LFunction π (6*z)))‖ ≤
        C*Z^(7/8-11/16-contourSaving)) := by
  obtain ⟨C, hC, hbound⟩ := ordered_remainders_scale_bound η S hS J c b B hc hcb hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (7/8+e) e
    ⟨by linarith, by linarith⟩ (by linarith) he (by linarith)
  refine ⟨C, hC, ?_⟩
  intro d hd W hW hsupp T hT Z hZ hthreshold hmod
  have hZ0 : 0 < Z := by linarith
  have hh := hbound W hW hsupp (fun j => Z^(d j))
    (fun _ _ => Real.rpow_pos_of_pos hZ0 _) hthreshold hmod T hT
    (Z^lx) (Z^ly) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  dsimp only at hh ⊢
  rw [source_w_scale_identity J d hd Z (7/8+e) e hZ0,
    source_z_scale_identity J d hd Z (7/8+e) hZ0] at hh
  have hw : (7/8+e)-11/16+geomH*e-ly/20 ≤ 7/8-11/16-contourSaving := by
    norm_num [geomH, ly, contourSaving]
    linarith only [hehi]
  have hz : (7/8+e)-11/16-geomH/600 ≤ 7/8-11/16-contourSaving := by
    norm_num [geomH, contourSaving]
    linarith only [hehi]
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hw) (div_nonneg hC.le he.le)),
    hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ hz) hC.le)⟩

/-- A bound for the actual finite principal-row contribution minus its residue,
using the audited lengths and the original ordered-contour identity. -/
theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c b B : ℝ) (hc : 0 < c) (hcb : c ≤ b) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (hbeta : HeckeZeroSupremum.beta ≤ 7/8)
    (e : ℝ) (he : 0 < e) (hehi : e ≤ 1/1000) :
    letI : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧ ∀ d : Fin K → ℝ, (∑ j, d j) = ell → ∀ W : Fin K → ℝ → ℝ,
      (∀ j x, 0 ≤ W j x ∧ W j x ≤ B) → (∀ j, Function.support (W j) ⊆ Icc c b) →
      ∀ T : Fin K → Finset PrimeIdeal, (∀ j p, p ∈ T j → p.val ∉ S) →
      (∀ P : (∀ j, T j), Function.Injective (fun j => (P j).val)) →
      ∀ Z : ℝ, 1 ≤ Z → (∀ j, 480 ≤ c*Z^(d j)) →
      (∀ j, (Ideal.absNorm η.modulus:ℝ) < c*Z^(d j)) →
      ‖(∑ P : (∀ j, T j), (∏ j, (W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(d j)):ℂ))*
          principalRowIntegral η S (fun j => primaryGenerator (P j).val.val)
            W0 W1 (Z^lx) (Z^ly) Z) -
        sourceResidueIntegral W0 W1 (∏ p ∈ S, p) (η.excludePrimes S hS.prime)
          (7/8+e) (Z^lx) (Z^ly) Z (globalClosedCorrection η S)
          (windowMultiplier η Finset.univ T (fun j x => (W j x:ℂ)) (fun j => Z^(d j)))‖ ≤
        C/e*Z^(7/8-11/16-contourSaving) := by
  let : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hbound⟩ := source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c b B hc hcb hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hbeta e he hehi
  refine ⟨2*C, by positivity, ?_⟩
  intro d hd W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0 < Z := by linarith
  have hb := hbound d hd W (fun j _ => hW j) (fun j _ => hsupp j)
    T (fun j _ p hp => hT j p hp) Z hZ (fun j _ => hthreshold j) (fun j _ => hmod j)
  dsimp only at hb
  have heq := principal_physical_pool_ordered η S hS T hT hdis
    (fun j p => (W j ((Ideal.absNorm p.val:ℝ)/Z^(d j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^lx) (Z^ly) Z (7/8+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (by linarith) (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ → ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6 *
        verticalIntegral (7/8+e) F =
      verticalIntegral (7/8+e) (fun s => fixedPrincipalResidue (∏ p ∈ S, p)^2/6*F s) := by
    rw [verticalIntegral, verticalIntegral, integral_const_mul]
    dsimp only [fixedPrincipalResidue, fixedPrincipal, fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres, add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _ ≤ (2*C)/e*Z^(7/8-11/16-contourSaving)
  apply hn.trans
  have hCe : C ≤ C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0 ≤ Z^(7/8-11/16-contourSaving) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e = 2*(C/e) := by ring
  rw [htwo]
  nlinarith

end SevenEighths.ImprovedPrincipalRemainder
end
end OAI
