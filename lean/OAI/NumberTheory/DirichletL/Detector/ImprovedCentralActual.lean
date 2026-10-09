import OAI.NumberTheory.DirichletL.Detector.ImprovedCentralCollected
import OAI.NumberTheory.DirichletL.Detector.BaselineMomentHeight
import OAI.NumberTheory.DirichletL.PrimeRows.BaselineMaximum

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set

namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open CenteredMomentBaselineGeometry ProbeBaselineMomentAssembly
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

/-- The audited central nonfloor estimate for the actual source. All four
source moments and the detector's fixed `7/8` envelope are proved internally.
The finite moment degree precedes every choice of height and every target. -/
theorem improved_nonfloor_rows_actual (S : SourceData D) (G : Geometry D.N)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃ J : ℕ, ∀ (n m : ℕ)
      (e eps R dmin dmax rmin τ κ cost mesh margin loss ν logCost heightCost momentCost μ saving nu dyadCost : ℝ),
    0<e → e<1/1000 → 0<eps → 0≤R → (1/200:ℝ)≤dmin → dmin<1/100 →
    0≤dmax → dmin≤dmax → 0<rmin → 0<τ → 0<G.ε → 0<κ → 0≤cost → 0<mesh →
    8*e*R+κ≤G.ε → G.ε<rmin*mesh → 0<margin →
    2*τ<dmin*cost → τ*(2+4*eps)<loss →
    FirstTail (4*e) S.S →
    (∀j,dmax*rmin≤G.ell j) → (∀j,G.ell j≤dmin*R) →
    (∑j,G.ell j)=QRHParameterAudit.ell →
    dmax≤37/42 → κ≤1 → τ<dmin/2 → 4*τ<dmin*cost →
    12*e*((22:ℝ)+2)+8*κ+2*cost≤G.ε/2 →
    0<ν → 0<logCost → 0≤heightCost → τ<heightCost → heightCost*J≤momentCost →
    0≤μ →
    (159*G.ε+G.t+R+7*ν)+(3/2)*μ+28*e+(D.N+8)*eps+loss+
      QRHParameterAudit.ell*mesh+(logCost+heightCost+momentCost)+saving≤(7/8)*QRHParameterAudit.gammaSave →
    0<nu → 0<dyadCost →
    QRHParameterAudit.geomH+QRHParameterAudit.extension+2*margin≤dmax → 2*margin≤μ →
    letI : NeZero (∏P∈S.S,P) := ⟨fixedPrimeProduct_ne_zero S.S S.exclusions.prime⟩
    ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S.S S.maximal).residueMonoid u.val≠0 ∧
        rowNorm u≤Z^(QRHParameterAudit.geomH+QRHParameterAudit.extension)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u≤n ∧ grid u≤m ∧ grid u≠0) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S.S S.exclusions.prime η u
        (rayCubeFamily S.modulus ⊤ le_top u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u≤detectorMaximum
        (sourceDetectorFamily S.S S.exclusions.prime η u (rayCubeFamily S.modulus ⊤ le_top u))
        ((3*idx u:ℕ)*Z^τ)) →
      let Y : Fin D.N→ℝ := fun j=>Z^(G.ell j)
      let T : Fin D.N→Finset ProbePhysical.PrimeIdeal := fun j=>
        pool (RayQuotient.identityClass S.modulus ⊤) S.S 1 2 (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant S.W S.W (∏P∈S.S,P)*
        (Probe.principalScalar Finset.univ Z QRHParameterAudit.ell
          (PrincipalSignalComparison.slotMass T
            (ProbePrincipalResidueActual.residueWeights (fun _=>S.w) Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S.S S.exclusions S.maximal η rows T
        (nonfloorPoolOutside S.modulus ⊤ S.S D.N 1 2 Y)
        (fun _ y=>(S.w y:ℂ)) Y S.W S.W (Z^QRHParameterAudit.lx) (Z^QRHParameterAudit.ly) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*Z^(QRHParameterAudit.signal QRHParameterAudit.sigma0-saving+nu+dyadCost) := by
  obtain ⟨counts⟩ := exists_count_parameters_at_baseline S G
  obtain ⟨J, hmom⟩ := source_moments_at_power_height S G counts hβlo hβhi
  refine ⟨J, ?_⟩
  intro n m e eps R dmin dmax rmin τ κ cost mesh margin loss ν logCost heightCost momentCost
    μ saving nu dyadCost he he1 heps hR hdmin200 hdmin1 hdmax hdRange hrmin hτ hε hκ hcost hmesh
    hbudget hgap hmargin hheight hloss hfirst hello hellhi hellsum hdtop hκ1 hτzero hτheight hwbudget
    hν hlog hhc hMomentHeight hdegree hμ hfinal hnu hdyadCost hconductor hmuMargin
  let : NeZero (∏P∈S.S,P) := ⟨fixedPrimeProduct_ne_zero S.S S.exclusions.prime⟩
  have hdmin : 0<dmin := lt_of_lt_of_le (by norm_num) hdmin200
  obtain ⟨C,hC,hbound⟩ := improved_nonfloor_rows_saving S.modulus ⊤ le_top D.N n
    e eps 1 2 1 R dmin dmax rmin τ G.ε κ cost mesh margin loss
    he he1 heps (by norm_num) (by norm_num) (by norm_num) hR hdmin hdmax hdRange hrmin
    hτ hε hκ hcost hmesh hbudget hgap hmargin hheight hloss S.S S.exclusions hfirst S.maximal
    G.ell G.ell_injective hello hellhi (fun _=>S.w) (fun _=>S.support) (fun _=>S.smooth)
    (fun _=>S.bounded) (fun _=>S.compact) (fun _=>S.nonzero) hellsum hdtop G.epsilon_small hκ1
    hτzero hτheight hwbudget S.w S.smooth S.compact S.positive_support
    (fun y=>(S.bounded y).1) S.nonzero 1 2 1 (by norm_num) (by norm_num) (by norm_num)
    S.support (fun y=>(S.bounded y).2) G.t ν logCost heightCost momentCost G.t_pos hν hlog hMomentHeight
    μ saving hμ hfinal S.W S.W 1 2 1 2 (by norm_num) (by norm_num)
    S.complex_support S.complex_support S.real S.real S.nonnegative S.nonnegative
    S.complex_nonzero S.complex_nonzero nu hnu m dyadCost hdyadCost hdmin1 hconductor hmuMargin counts
  intro η
  obtain ⟨Cm,hCm,hmom⟩ := hmom η
  have hηnorm : 0<(η.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  refine ⟨C*Cm*(η.modulus.absNorm:ℝ)^(2*eps),by positivity,?_⟩
  filter_upwards [hbound η,hmom,
    sourceDyad_geometry_eventually dmin dmax margin
      (QRHParameterAudit.geomH+QRHParameterAudit.extension) hdmin hdmin1 hmargin hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) (heightCost-τ) (by linarith)]
    with Z hb hm hg hheightZ
  intro rows hrows idx grid hlabels hnext hcurrent
  have hZ : 1<Z := hm.1
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hlabels' : ∀u∈rows,idx u≤n ∧ grid u≤m ∧ grid u≠0 ∧ 51/100+e*grid u≤7/8 := by
    intro u hu
    exact ⟨(hlabels u hu).1,(hlabels u hu).2.1,(hlabels u hu).2.2,
      (detector_bin_le_baseline _ _ _ hβhi (hcurrent u hu)).1⟩
  have hb' := hb Cm hCm.le rows hrows idx grid hlabels' hnext hcurrent
  apply hb'
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hgeo := hg rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩)
    k (hne.mono hsub)
  have hi' : (i:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight' : (3*i+1:ℕ)*Z^τ≤Z^heightCost := by
    calc
      _ ≤ (3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _ ≤ Z^(heightCost-τ)*Z^τ := mul_le_mul_of_nonneg_right hheightZ (by positivity)
      _ = Z^heightCost := by rw [←Real.rpow_add hZp];congr 1;ring
  exact hm.2 heightCost momentCost hhc hdegree rows'
    (fun u hu=>(hrows u (hsubr hu)).2.1) (sourceDyadConductor Z margin k)
    (hdmin200.trans hgeo.2.2.1) (51/100+e*j) τ dmax R mesh i
    ((17/50:ℂ)+t.1.2*Complex.I) (by simp) (by simpa using htheight.2.trans hheight')

end SevenEighths.ProbeFinalAssembly

end

end OAI
