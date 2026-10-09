import OAI.NumberTheory.DirichletL.Improved.HighData
import OAI.NumberTheory.DirichletL.Improved.NonfloorTransport
import OAI.NumberTheory.DirichletL.Improved.Probe
import OAI.NumberTheory.DirichletL.Detector.ImprovedCentralActual

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Asymptotics

namespace SevenEighths.ImprovedProbe
open HeckeFamily ProbePhysical ProbeHighRowFamily ProbeFinalAssembly
open HeckeInverseAmplification ProbeMellinBoundary PrincipalSignalComparison QRHParameterAudit
local notation "O" => HeckeFamily.O

/-- The actual probe error at the fixed seven-eighths baseline. The saving and
all physical parameters precede the target character. Source moments, floor
bins, the principal residue, and contour tails are discharged internally. -/
theorem actual_probe_error (D : ImprovedParameters.HighData)
    (F : SourceData D.carrier) (hfirst : FirstTail (4*D.e) F.S)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
    ∀η : Character,
      (fun Z => normalizedProbe F.modulus ⊤ F.S F.maximal D.G.ell 1 2
        (fun _=>F.w) F.W F.W η Z-
        HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
          (sourceCorrection η F.S) (-11/16) Z)
      =O[atTop] (fun Z : ℝ => Z^(3/16-D.sigma)) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  obtain ⟨J,hcentral⟩ := improved_nonfloor_rows_actual F D.G hβlo hβhi
  obtain ⟨heightCost,τ,hhc,hhct,hhcJ,hτ,hτd,hτcost,hτheight,hτloss⟩ :=
    D.height_choice J (Nat.cast_nonneg _)
  have ht := D.t_pos
  have hmin : 0<(7/8:ℝ)*D.rmin := mul_pos (by norm_num) D.rmin_pos
  have hnu : 0<D.t/8 := by positivity
  have hζ : 0<extension := by norm_num [extension,gammaSave]
  have hζ1 : extension≤1/48 := by norm_num [extension,gammaSave]
  have hsmallheight : 2*τ<(1/200:ℝ)*D.cost := by linarith
  have hcap : geomH+extension≤(7/8:ℝ)-D.t := by linarith [D.conductor_budget]
  obtain ⟨n,hn,htransport⟩ := audited_actual_nonfloor_probe_transport F.modulus ⊤ le_top D.carrier.N
    D.e (1/4) 1 2 1 extension 1 τ ((7/8)*D.rmin) (D.t/8)
    D.e_pos D.e_small (by norm_num) (by norm_num) hζ hζ1 hτ
    (by norm_num) (by norm_num) (by norm_num) hmin hnu hβhi
    F.S F.exclusions F.maximal hfirst D.G.ell (fun j=>(D.slots_bounds j).1)
    D.G.ell_injective D.slots_sum (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact)
    (fun _=>F.support) (fun _=>F.bounded) (fun _=>F.nonzero)
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    D.sigma D.sigma_pos (by simpa only [auditedTinySaving] using D.geometric_budget)
    (by simpa only [ImprovedPrincipalRemainder.contourSaving] using D.principal_budget)
    D.window_budget (by linarith [D.principal_budget])
    D.eps D.t (1/200) (7/8) D.rmin D.ε D.κ D.cost D.t D.t D.t
    D.eps_pos ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos
    D.epsilon_pos D.kappa_pos D.cost_pos.le ht ht D.phase_budget D.epsilon_gap
    hsmallheight hτloss hcap (fun j=>(D.slots_bounds j).1) (fun j=>(D.slots_bounds j).2)
    D.floor_budget
  have hcentral' := hcentral n ⌊(49/100:ℝ)/D.e⌋₊
    D.e D.eps D.t (1/200) (7/8) D.rmin τ D.κ D.cost D.t D.t D.t
    D.t D.t heightCost D.t (2*D.t) D.t (D.t/8) (D.t/8)
    D.e_pos D.e_small D.eps_pos ht.le (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D.rmin_pos hτ
    (by simpa only [D.geometry_epsilon] using D.epsilon_pos)
    D.kappa_pos D.cost_pos.le ht
    (by simpa only [D.geometry_epsilon] using D.phase_budget)
    (by simpa only [D.geometry_epsilon] using D.epsilon_gap) ht hsmallheight hτloss hfirst
    (fun j=>(D.slots_bounds j).1) (fun j=>(D.slots_bounds j).2) D.slots_sum
    (by norm_num) D.kappa_small hτd hτcost
    (by simpa only [D.geometry_epsilon] using D.detector_budget)
    ht ht hhc.le hτheight hhcJ (by positivity)
    (by rw [D.geometry_epsilon,D.geometry_t]; linarith [D.central_budget])
    hnu hnu D.conductor_budget le_rfl
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  obtain ⟨Cc,hCc,hcentral⟩ := hcentral' η
  apply ProbeFinalAssembly.isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+Cc,by positivity,?_⟩
  filter_upwards [htransport,hcentral,eventually_ge_atTop (1:ℝ)] with Z ht hc hZ
  dsimp only at ht
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  let rows := supportedNonfloorRows F.S F.maximal
    (rowBand (Z^(1/100:ℝ)) (Z^(geomH+extension))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(geomH+extension) := by
    intro u hu
    rcases (mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/D.e⌋₊ ∧ grid u≠0 := by
    intro u hu
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).2.2⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily F.S F.exclusions.prime η u
      (rayCubeFamily F.modulus ⊤ le_top u)) (3*(idx u+1:ℕ)*Z^τ)<51/100+D.e*grid u+2*D.e :=
    fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+D.e*grid u≤detectorMaximum
      (sourceDetectorFamily F.S F.exclusions.prime η u (rayCubeFamily F.modulus ⊤ le_top u))
      ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hc rows hrows idx grid hlabel hnext hcurrent).2
  have hexp : Z^(QRHParameterAudit.signal sigma0-D.t+D.t/8+D.t/8)≤
      Z^((7/8:ℝ)-11/16-D.sigma) := by
    apply Real.rpow_le_rpow_of_exponent_le hZ
    have hs := D.high_saving
    rw [signal_eq]
    norm_num [sigma0]
    linarith
  have hcentralBound := hglobal.trans (mul_le_mul_of_nonneg_left hexp hCc.le)
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentralBound)
  have heq : (7/8:ℝ)-11/16=3/16 := by norm_num
  simpa only [normalizedProbe,rows,sub_add_cancel,add_mul,heq] using hsum

end SevenEighths.ImprovedProbe
end
end OAI
