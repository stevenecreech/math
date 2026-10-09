import OAI.NumberTheory.DirichletL.Detector.LowGramScale
import QRHParameterAudit.LowNormExtension
import OAI.NumberTheory.DirichletL.Detector.LowTupleGram
import OAI.NumberTheory.DirichletL.Detector.PhysicalCrudeMass

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma variable_source_scale_ratio (x y : ℝ) (Z : ℝ) (hZ : 0<Z) :
    Z^(y)/Z^(x)=Z^(y-x) := by
  rw [←Real.rpow_sub hZ]

lemma variable_source_scale_square (x y : ℝ) (Z : ℝ) (hZ : 0<Z) :
    Z^(2*x-y)*Z^(y)=(Z^(x))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  congr 1
  ring

lemma variable_source_compensated_scale_admissible (x y : ℝ) (hxy : x ≤ y) (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(y-x)) (hLl : L≤Z^(2*x-y)) :
    1≤Z^(y)/L ∧
    q*Z^(x)≤Z^(y) ∧
    L*Z^(y)≤q^2*(Z^(x))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show 2*x-y≤y by linarith))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz x)).mp
    rwa [variable_source_scale_ratio x y Z hz]
  · calc
      _≤Z^(2*x-y)*Z^(y) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(x))^2 := variable_source_scale_square x y Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma variable_source_compensated_gram_scale (x y : ℝ) (hxy : x ≤ y) (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(y-x)) (hLl : L≤Z^(2*x-y)) (hδ : 0≤δ) :
    (q*(Z^(x)/L)*(Z^(y)/L)/(Z^(y)/L))*
      (1+((Z^(y)/L)^2/(q*(Z^(x)/L)*(Z^(y)/L)))^(1/6:ℝ)+
        ((Z^(y)/L)^2/(q*(Z^(x)/L)*(Z^(y)/L)))^2/(Z^(y)/L))*
      (Z^(y)/L)^δ ≤
        (3*q/L)*Z^(x+(y-x)/6+y*δ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := variable_source_compensated_scale_admissible x y hxy q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(x)) (Z^(y)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(y)/(q*Z^(x))≤Z^(y-x) := by
    rw [←variable_source_scale_ratio x y Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(y)/(q*Z^(x))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(x)/L)*(Z^(y-x))^(1/6:ℝ)*(Z^(y))^δ := by gcongr
    _=(3*q/L)*(Z^(x)*(Z^(y-x))^(1/6:ℝ)*(Z^(y))^δ) := by ring
    _=_ := by
      rw [←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring

lemma variable_source_compensated_gram_sqrt (x y : ℝ) (hxy : x ≤ y) (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(y-x)) (hLl : L≤Z^(2*x-y)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(x)/L)*(Z^(y)/L)/(Z^(y)/L))*
      (1+((Z^(y)/L)^2/(q*(Z^(x)/L)*(Z^(y)/L)))^(1/6:ℝ)+
        ((Z^(y)/L)^2/(q*(Z^(x)/L)*(Z^(y)/L)))^2/(Z^(y)/L))*
      (Z^(y)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(x/2+(y-x)/12+y*δ/2) := by
  apply (Real.sqrt_le_sqrt (variable_source_compensated_gram_scale x y hxy q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  have hp : Real.sqrt (Z^(x+(y-x)/6+y*δ))=Z^(x/2+(y-x)/12+y*δ/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul (lt_of_lt_of_le zero_lt_one hZ).le]
    congr 1
    ring
  rw [Real.sqrt_mul (by positivity),hp]

lemma variable_lowGramFactor_source_bound (x y : ℝ) (hxy : x ≤ y) (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^(y-x))
    (hLl : L≤Z^(2*x-y)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(x)/L) (Z^(y)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(x/2+(y-x)/12+y*δ/2) :=
  variable_source_compensated_gram_sqrt x y hxy _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma variable_eventually_compensated_source_scales
    (x y total : ℝ) (hxy : x < y) (hgap : total < 2*x-y) (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^(y-x) ∧
      ∀L : ℝ,1≤L→L≤B*Z^total→
        1≤Z^(y)/L ∧
        1≤(Z^(y)/L)^2/lowPhysicalScale C (Z^(x)/L) (Z^(y)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(x)/L) (Z^(y)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(x/2+(y-x)/12+y*δ/2) := by
  have hq := (tendsto_rpow_atTop (show 0<y-x by linarith)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<2*x-y-total by linarith)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^(2*x-y) := calc
    L≤B*Z^total := hLB
    _≤Z^(2*x-y-total)*Z^total := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^(2*x-y) := by rw [←Real.rpow_add hz];congr 1;ring
  obtain ⟨hy,hp,_⟩ := variable_source_compensated_scale_admissible x y hxy.le _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>variable_lowGramFactor_source_bound x y hxy.le C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI
