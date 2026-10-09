import OAI.NumberTheory.DirichletL.Moments.BaselineMarkedState
import OAI.NumberTheory.DirichletL.Moments.BaselineSourceEnergy
import OAI.NumberTheory.DirichletL.Detector.DetectorPlainUnmarkedField

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.ProbeBaselineUnmarkedMoment
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentNaturalFixedRaySource
open CenteredMomentBaselineGeometry CenteredMomentBaselineMarkedState CenteredMomentBaselineSourceEnergy
open ProbeDetectorPlainUnmarkedField QuadraticInitialBound
local notation "O" => HeckeFamily.O

theorem retained_unmarked_bound_at_baseline {N : ℕ} (G : Geometry N)
    {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {Label : Type*}
    {U a tstar T heightAllowance : ℝ} {i : ℕ}
    (F : Fiber M H Label (Fin N) U a G.ε tstar T heightAllowance i)
    (η : Character) (Q : Ideal O) (hU : 1 < U)
    (hη : (η.modulus.absNorm : ℝ) ≤ U^(G.t/4))
    (degree : ℕ) (control : Finset (ℕ × ℕ)) (A : ℝ)
    (hzero : ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (G.t/4)
      U degree control A) (j k : ℕ) (σ t : ℝ) :
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t radialMajorant ≤
      A*diagonalControl radialMajorant*(detectorProfiles F.reverse j k σ t).control control ^2*
        U^(max 1 (2*F.m)+G.t/4+G.t/4) := by
  let s := state F η Q radialMajorant radialSupportUpper (G.t/4) hU.le
    (allowance_parameters G).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hf := fiber_lengths G F hU
  have hwidth : s.width = max 1 (2*F.m)+G.t/4 := padded_width _ _
  have hband : s.width ≤ 2 := by
    rw [hwidth]
    exact (width_bands G hf.2.1).2.2.2
  have hz := hzero s rfl hband (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m)
    (zero_lt_one.trans_le hf.2.2.1) (zero_lt_one.trans_le hf.2.2.1)
    (by simpa only [Real.rpow_one] using hf.2.2.2.1)
    (by simpa only [Real.rpow_one] using hf.2.2.2.1)
  rw [actual_source_eq F η Q radialMajorant radialSupportUpper (G.t/4) hU.le
    (allowance_parameters G).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t]
  have hrad : s.radial.profile = radialMajorant := rfl
  simpa only [hwidth, hrad, norm_zero, add_zero, one_pow, mul_one] using hz


theorem source_batch_plain_unmarked_at_baseline {Δ : ℝ} {D : Parameters.HighData Δ}
    (S : ProbeFinalAssembly.SourceData D) (G : Geometry D.N)
    (hβlo : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ (7/8 : ℝ)) :
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a G.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>G.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+G.t) ∧
      value≤C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^G.t := by
  obtain ⟨degree,control,he⟩ := source_energy_at_baseline S G radialSupportUpper
    radialSupportUpper_spec.1 hβlo hβhi
  have henergy : ∀η₀ : Character, ∃A : ℝ, 0<A ∧ ∀ᶠU : ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (G.t/4) U degree control A := by
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩ := he η₀
    exact ⟨Cz,hCz,h.mono (fun U h=>h.2.1)⟩
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=>sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=>internalQ (sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=>henergy (η₀ label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0≤∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0<Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label≤Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0≤diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0<C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp≤C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤d→
      ZeroAt (Q label) (1/4) (9/4) radialSupportUpper 0 1 2 ((G.t/4))
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [source_batch_plain_retained_at_baseline S G η,
    source_label_modulus_eventually S η (G.t/4) (allowance_parameters G).1,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1<Z^d:=Real.one_lt_rpow hret.1 (by linarith : 0<d)
  have hnorm:‖t‖≤height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(detectorProfiles F.reverse j k σ t).control control ^2≤Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value≤retainedSourceEnergy (initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
      hret.2 rows hrows d (by linarith) a G.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=retained_unmarked_bound_at_baseline G F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+(G.t/4)+(G.t/4))≤
      (Z^d)^(max 1 (2*F.m)+G.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (by linarith [(allowance_parameters G).2.2])
  have hfinal:value≤C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+G.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _≤(A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+G.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+G.t):=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.ProbeBaselineUnmarkedMoment

end

end OAI
