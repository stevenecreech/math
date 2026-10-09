import OAI.NumberTheory.DirichletL.Moments.BaselineMarkedState
import OAI.NumberTheory.DirichletL.Moments.BaselineSourceEnergy
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainRelativeClass
import OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl
import OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicGeometry

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.ProbeBaselineMarkedMoment
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly
open QuadraticInitialBound CenteredMomentDetectorDictionary
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentInductionEnergy
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentBaselineGeometry CenteredMomentBaselineMarkedState CenteredMomentBaselineSourceEnergy
local notation "O" => HeckeFamily.O

/-! Actual marked moments at endpoint capacity `3/4`, obtained from the
terminal energy theorem. `G` supplies all moving widths and losses; `S` only
supplies the pre-existing fixed source window and exclusion data. -/

theorem source_batch_plain_marked_at_baseline {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(G:Geometry D.N)
    (hβlo:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hβhi:HeckeZeroSupremum.beta≤(7/8:ℝ)):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a G.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>G.ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→(∀s,|(B.external s).im|≤height)→
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots→
      2*F.m+6*(3/4)*(∑s∈selected,F.widths s)≤1→
    ∀j k:ℕ,j+k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+G.t):=by
  obtain ⟨bΦ,hbΦ,hsource⟩:=source_batch_marked_initial_at_baseline S G
  obtain ⟨degree,seminorms,he⟩ := source_energy_at_baseline S G bΦ hbΦ hβlo hβhi
  have henergy : ∀η₀:Character,∃C:ℝ,0<C ∧ ∀ᶠU:ℝ in atTop,
      PositiveAt (α:=Fin D.N) S.modulus ⊤ le_top (fun x=>conj (S.W x))
        2 (1/4) (9/4) bΦ 0 1 (mesh G.t) (33/50) (33/50) 2
        (G.t/4) (3/4) U η₀ (sourceFixedIdeal S) degree seminorms C := by
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩ := he η₀
    exact ⟨Cp,hCp,h.mono (fun U h=>h.2.2)⟩
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩:=
    CenteredMomentDetectorPlainProfileControl.source_height_factor seminorms
  refine ⟨J+degree,?_⟩
  intro η
  let data:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η
  choose C hC hbound using fun label=>henergy (data label)
  choose U₀ hU₀ using fun label=>Filter.eventually_atTop.mp (hbound label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0<Csum:=by
    have h:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤Csum:=by
    have h:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le)
      (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤d→U₀ label≤Z^d:=by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  let Cfinal:=Csum*(1+diagonalControl radialMajorant)*Cprofile
  have hdiag:0≤diagonalControl radialMajorant:=diagonalControl_nonneg _
  refine ⟨Cfinal,by dsimp [Cfinal];positivity,?_⟩
  filter_upwards [hsource η (G.t/4) (allowance_parameters G).1,hscale] with Z hs hscale
  refine ⟨hs.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal F selected hselected hcap j k hjk σ hσ t ht
  have hU:1<Z^d:=Real.one_lt_rpow hs.1 (by linarith : 0<d)
  obtain ⟨state,hchar,hQ,hpuncture,hΦ,hK,hkeep,hwidthstate,hcapacity,hwidths,hrow⟩:=
    hs.2 rows hrows d hd a G.ε tstar T allowance i B hB hdata hprof hwidth hupper hreal
      bin label left right hne selected hselected hcap
  have hf:=fiber_lengths G F hU
  have hstate:state.width≤2:=by rw [hwidthstate];exact (width_bands G hf.2.1).2.1
  have hw (s:selected):0≤F.widths s.val:=(hwidths s).1.le
  have hwcap (s:selected):F.widths s.val≤mesh G.t:=by
    change B.widths s.val≤mesh G.t
    rw [hwidth]
    exact (fine_slot_widths G hd s.val).2
  have hpos:=hU₀ label (Z^d) (hscale label d hd) selected (fun _=>1)
    (fun s=>F.widths s.val) (fun _=>(33/50:ℝ)) (fun s=>-(F.external s.val).im)
    0 height hw hwcap (fun _=>le_rfl) (fun _=>le_rfl) hheight
    (fun s=>by change |-(B.external s.val).im|≤height; simpa only [abs_neg] using hexternal s.val)
    state hQ hstate (detectorProfiles F.reverse j k σ t) ((Z^d)^F.m) ((Z^d)^F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by simpa only [Real.rpow_one] using hf.2.2.2.1)
    (by simpa only [Real.rpow_one] using hf.2.2.2.1) hcapacity
  have heq:=CenteredMomentDetectorPlainRelativeClass.energy_eq S.modulus ⊤ le_top
    state.character (data label) (fun (_:selected)=>1) state.mask 1
    ((detectorProfiles F.reverse j k σ t).profile 0)
    ((detectorProfiles F.reverse j k σ t).profile 1)
    (fun _=>2) (fun s:selected=>(Z^d)^(F.widths s.val))
    (fun s I=>HeckePrimeAnnular.annularWeight (fun x=>conj (S.W x))
      ((Z^d)^(F.widths s.val)) (33/50) (-(F.external s.val).im) I)
    0 ((Z^d)^F.m) ((Z^d)^F.m) state.radial.keep state.radial.profile state.radial.scale
  have hnorm:=hprofile degree F.reverse j k hjk σ hσ height t hheight (abs_le.mpr ht)
  have hp:0≤(detectorProfiles F.reverse j k σ t).control seminorms ^2:=sq_nonneg _
  have hexp:state.width+(G.t/4)≤1+G.t:=by
    rw [hwidthstate];linarith [(allowance_parameters G).2.2]
  calc
    _≤_:=hrow j k σ t
    _≤C label*diagonalControl state.radial.profile*
        (detectorProfiles F.reverse j k σ t).control seminorms ^2*
        (1+|(0:ℝ)|+height)^degree*(Z^d)^(state.width+(G.t/4)):=by
      exact heq.le.trans hpos
    _≤(Cfinal*(1+height)^(J+degree))*(Z^d)^(1+G.t):=by
      rw [hΦ]
      have hpow:=Real.rpow_le_rpow_of_exponent_le hU.le hexp
      calc
        _=(C label*diagonalControl radialMajorant)*
          ((detectorProfiles F.reverse j k σ t).control seminorms ^2*
            (1+|(0:ℝ)|+height)^degree)*(Z^d)^(state.width+(G.t/4)):=by ring
        _≤(Csum*(1+diagonalControl radialMajorant))*
          (Cprofile*(1+height)^(J+degree))*(Z^d)^(1+G.t):=by
          apply mul_le_mul _ hpow (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
          apply mul_le_mul _ hnorm (by positivity) (by positivity)
          exact mul_le_mul (hClabel label) (by linarith) hdiag hCsum.le
        _=_:=by dsimp [Cfinal];ring

end SevenEighths.ProbeBaselineMarkedMoment

end

end OAI
