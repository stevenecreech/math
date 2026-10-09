import OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized
import OAI.NumberTheory.DirichletL.Improved.PrincipalResidue
import OAI.NumberTheory.DirichletL.Improved.PrincipalRemainder
import OAI.NumberTheory.DirichletL.Improved.Normalizer

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace SevenEighths.ImprovedPrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
open ProbePrincipalNormalized QRHParameterAudit
local notation "Id" => Ideal HeckeFamily.O
local notation "O" => HeckeFamily.O

/-! Normalization of the actual principal contribution at the audited probe lengths.
The only nonvanishing input is the previously established seven-eighths baseline. -/

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hmin : 0<ellMin)
    (slotLength : Fin K→ℝ) (hell : ∀j,ellMin≤slotLength j) (hdis : Function.Injective slotLength)
    (hsum : (∑j,slotLength j)=ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e≤1/1000) (hnu : 0<nu)
    (hbeta : HeckeZeroSupremum.beta ≤ 7/8) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(slotLength j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z ell
          (slotMass T (residueWeights W (fun j=>Z^(slotLength j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(slotLength j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^lx) (Z^ly) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
      C*(Z^((7/8:ℝ)-11/16-ImprovedPrincipalRemainder.contourSaving+nu)+
        Z^((7/8:ℝ)-11/16+e-(7/8)*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := ImprovedPrincipalRemainder.physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hbeta e he hehi (K:=K)
  obtain ⟨D,hD,hres⟩ := ImprovedPrincipalResidue.normalized_actual_window_residue S hS η
    (by linarith : (7/8:ℝ) < 7/8+e) (by linarith) (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(7/8:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin slotLength hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne slotLength (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) slotLength (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0<Z := by linarith
  let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(slotLength j))
  let normer := cs*(Probe.principalScalar Finset.univ Z ell
    (slotMass T (residueWeights W (fun j=>Z^(slotLength j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=>Z^(slotLength j)) (c*Z^ellMin) (Z^ly) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=>hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem slotLength hsum W hWbounds (fun j=>Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(7/8:ℝ))=c^(-(7/8:ℝ))*Z^(-(7/8:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^((7/8:ℝ)-11/16-ImprovedPrincipalRemainder.contourSaving))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^((7/8:ℝ)-11/16-ImprovedPrincipalRemainder.contourSaving+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^((7/8:ℝ)+e-11/16)*(c*Z^ellMin)^(-(7/8:ℝ))=
      (D*c^(-(7/8:ℝ)))*Z^((7/8:ℝ)-11/16+e-(7/8)*ellMin) := by
    rw [hpw]
    rw [show (7/8:ℝ)-11/16+e-(7/8)*ellMin=
      ((7/8:ℝ)+e-11/16)+(-(7/8:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤C := by
    dsimp [C]
    have : 0≤D*c^(-(7/8:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(7/8:ℝ))≤C := by
    dsimp [C]
    have : 0≤C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^((7/8:ℝ)-11/16-ImprovedPrincipalRemainder.contourSaving+nu)+
        C*Z^((7/8:ℝ)-11/16+e-(7/8)*ellMin) := by gcongr
    _ = _ := by ring

/-- A positive principal saving for every positive minimum slot length. -/
def principalSaving (ellMin : ℝ) : ℝ :=
  min (ImprovedPrincipalRemainder.contourSaving/2) ((7/16)*ellMin)

theorem principalSaving_pos {ellMin : ℝ} (hmin : 0 < ellMin) :
    0 < principalSaving ellMin :=
  lt_min (half_pos ImprovedPrincipalRemainder.contourSaving_pos) (by positivity)

/-- The normalized actual principal row already has the strictly positive saving
needed by the fixed-baseline route. The remaining high bound concerns nonprincipal rows. -/
theorem actual_ray_principal_saving {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hmin : 0<ellMin)
    (slotLength : Fin K→ℝ) (hell : ∀j,ellMin≤slotLength j) (hdis : Function.Injective slotLength)
    (hsum : (∑j,slotLength j)=ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (hbeta : HeckeZeroSupremum.beta ≤ 7/8) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(slotLength j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z ell
          (slotMass T (residueWeights W (fun j=>Z^(slotLength j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(slotLength j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^lx) (Z^ly) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
      C*Z^(3/16-principalSaving ellMin) := by
  let e : ℝ := min (1/1000) ((7/16)*ellMin)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have hehi : e ≤ 1/1000 := min_le_left _ _
  have henu : e ≤ (7/16)*ellMin := min_le_right _ _
  have hnu : 0 < ImprovedPrincipalRemainder.contourSaving/2 :=
    half_pos ImprovedPrincipalRemainder.contourSaving_pos
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hbound⟩ := actual_ray_principal_comparison M H hH η S hS c d B ellMin
    hc hd hB hmin slotLength hell hdis hsum W hW hcompact hsupp hWbounds hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    e (ImprovedPrincipalRemainder.contourSaving/2) he hehi hnu hbeta
  refine ⟨2*C, by positivity, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1:ℝ)] with Z hz hZ
  dsimp only at hz ⊢
  refine ⟨hz.1, hz.2.trans ?_⟩
  have hs1 : principalSaving ellMin ≤ ImprovedPrincipalRemainder.contourSaving/2 :=
    min_le_left _ _
  have hs2 : principalSaving ellMin ≤ (7/16)*ellMin := min_le_right _ _
  have hp1 : Z^((7/8:ℝ)-11/16-ImprovedPrincipalRemainder.contourSaving+
      ImprovedPrincipalRemainder.contourSaving/2) ≤ Z^(3/16-principalSaving ellMin) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hp2 : Z^((7/8:ℝ)-11/16+e-(7/8)*ellMin) ≤ Z^(3/16-principalSaving ellMin) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ C*(Z^(3/16-principalSaving ellMin)+Z^(3/16-principalSaving ellMin)) :=
      mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) hC.le
    _ = _ := by ring

end SevenEighths.ImprovedPrincipalNormalized
end
end OAI
