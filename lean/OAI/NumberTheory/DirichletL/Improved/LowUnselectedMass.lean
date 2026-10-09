import OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
import OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry
import OAI.NumberTheory.DirichletL.Detector.GramIdealSummation

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma canonical_slot_inverse_three_halves : ∃C : ℝ,0<C ∧
    ∀(T : Finset PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))≤C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-(3/2)) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=>I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-(3/2:ℝ)))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-(3/2:ℝ)) := by
    rw [Finset.sum_image (fun P _ Q _ h=>hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=>elementNorm a.val^(-(3/2:ℝ)))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

/-- The actual unselected tuples retain a power saving from their lower norm
bounds. The summation is over the original prime-ideal slots and weights. -/
theorem lowUnselectedMass_nominal_decay {K : ℕ} (ell : Fin K→ℝ)
    (a M : ℝ) (ha : 0<a) (hM : 0≤M) :
    ∃C : ℝ,0<C ∧ ∀(Z : ℝ),0<Z→
    ∀(T : Fin K→Finset PrimeIdeal)(hT : ∀i P,P∈T i→Supported P.val),
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤M)→
      (∑p : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P p‖*
          elementNorm (∏i : J,(p i).val)^(-(1/2:ℝ)))≤
        C*Z^(-lowUnselectedLength ell J/2) := by
  obtain ⟨C,hC,hbound⟩ := canonical_slot_inverse_three_halves
  let D := a^(-(1/2:ℝ))*C*M
  have hD : 0≤D := by dsimp [D]; positivity
  refine ⟨(max 1 D)^K,by positivity,?_⟩
  intro Z hZ T hT hnorm J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=>canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (p : canonicalSlotSupport (T i.val))=>
    elementNorm p.val^(-2:ℝ)*‖W i.val (elementNorm p.val/P i.val)‖)]
  have hslot (i : J) :
      (∑p : canonicalSlotSupport (T i.val),
        elementNorm p.val^(-2:ℝ)*‖W i.val (elementNorm p.val/P i.val)‖)≤
      D*Z^(-ell i.val/2) := by
    have hterm (p : canonicalSlotSupport (T i.val)) :
        elementNorm p.val^(-2:ℝ)*‖W i.val (elementNorm p.val/P i.val)‖≤
        (a^(-(1/2:ℝ))*Z^(-ell i.val/2)*M)*elementNorm p.val^(-(3/2:ℝ)) := by
      have hp : 0<elementNorm p.val := elementNorm_pos _
        (canonicalSlotSupport_nonzero _ (hT i.val) p.val p.property)
      have hlo : a*Z^(ell i.val)≤elementNorm p.val := by
        obtain ⟨q,hq,heq⟩ := Finset.mem_image.mp p.property
        rw [←heq,primaryTuple_norm q (hT i.val q hq)]
        exact hnorm i.val q hq
      have hhalf : elementNorm p.val^(-(1/2:ℝ))≤a^(-(1/2:ℝ))*Z^(-ell i.val/2) := by
        apply (Real.rpow_le_rpow_of_nonpos (by positivity) hlo (by norm_num)).trans_eq
        rw [Real.mul_rpow ha.le (by positivity),←Real.rpow_mul hZ.le]
        congr 2
        ring
      have he : elementNorm p.val^(-2:ℝ)=
          elementNorm p.val^(-(1/2:ℝ))*elementNorm p.val^(-(3/2:ℝ)) := by
        rw [←Real.rpow_add hp]
        norm_num
      rw [he]
      calc
        _≤(a^(-(1/2:ℝ))*Z^(-ell i.val/2)*elementNorm p.val^(-(3/2:ℝ)))*M :=
          mul_le_mul (mul_le_mul_of_nonneg_right hhalf (by positivity))
            (hW i.val _) (norm_nonneg _) (by positivity)
        _=_ := by ring
    calc
      _≤∑p : canonicalSlotSupport (T i.val),
          (a^(-(1/2:ℝ))*Z^(-ell i.val/2)*M)*elementNorm p.val^(-(3/2:ℝ)) :=
        Finset.sum_le_sum (fun p _=>hterm p)
      _=(a^(-(1/2:ℝ))*Z^(-ell i.val/2)*M)*
          ∑p : canonicalSlotSupport (T i.val),elementNorm p.val^(-(3/2:ℝ)) :=
        (Finset.mul_sum ..).symm
      _≤(a^(-(1/2:ℝ))*Z^(-ell i.val/2)*M)*C :=
        mul_le_mul_of_nonneg_left (hbound _ (hT i.val)) (by positivity)
      _=_ := by dsimp [D];ring
  have hp : (∏i : J,Z^(-ell i.val/2))=Z^(-lowUnselectedLength ell J/2) := by
    rw [←Real.rpow_sum_of_pos hZ,Finset.sum_div,Finset.sum_neg_distrib,Finset.sum_coe_sort]
    rfl
  calc
    _≤∏i : J,D*Z^(-ell i.val/2) := Finset.prod_le_prod₀
      (fun _ _=>Finset.sum_nonneg (fun _ _=>by unfold elementNorm;positivity)) (fun i _=>hslot i)
    _=D^J.card*Z^(-lowUnselectedLength ell J/2) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,hp]
    _≤(max 1 D)^J.card*Z^(-lowUnselectedLength ell J/2) := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ hD (le_max_right _ _) _) (by positivity)
    _≤_ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J)))
      (by positivity)

end SevenEighths.ProbePhysical
end

end OAI
