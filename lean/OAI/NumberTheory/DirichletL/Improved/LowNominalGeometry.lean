import OAI.NumberTheory.DirichletL.Detector.LowNominalGeometry

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRaySlots
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma variable_lowLength_bounds (total : ℝ) {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ell i)
    (hsum : ∑i,ell i≤total) (J : Finset (Fin K)) :
    0≤lowUnselectedLength ell J ∧ lowUnselectedLength ell J≤total ∧
    0≤lowSelectedLength ell J ∧ lowSelectedLength ell J≤total-lowUnselectedLength ell J := by
  have hu : 0≤lowUnselectedLength ell J := Finset.sum_nonneg (fun i _=>hell i)
  have hs : 0≤lowSelectedLength ell J := Finset.sum_nonneg (fun i _=>hell i.val)
  have he := lowLength_sum ell J
  exact ⟨hu,by linarith,hs,by linarith⟩

lemma variable_lowPhysicalScale_source (x y total : ℝ) (hsum : x+y=1-total) (C : CalibrationData) (Z L : ℝ) (hZ : 0<Z) :
    lowPhysicalScale C (Z^(x)/L) (Z^(y)/L)=
      elementNorm C.generator*Z^(1-total)/L^2 := by
  unfold lowPhysicalScale
  have he : Z^(x)*Z^(y)=Z^(1-total) := by rw [←Real.rpow_add hZ,hsum]
  rw [←he]
  ring

lemma variable_lowPhysicalScale_nominal_bound (x y total : ℝ) (hsum : x+y=1-total) (C : CalibrationData) (Z L c d : ℝ)
    (hZ : 0<Z) (hc : 0<c) (hL : c*Z^d≤L) :
    lowPhysicalScale C (Z^(x)/L) (Z^(y)/L)≤
      (elementNorm C.generator/c^2)*Z^(1-total-2*d) := by
  have hl : 0<L := lt_of_lt_of_le (by positivity) hL
  rw [variable_lowPhysicalScale_source x y total hsum C Z L hZ]
  calc
    _≤elementNorm C.generator*Z^(1-total)/(c*Z^d)^2 :=
      div_le_div_of_nonneg_left (by unfold elementNorm;positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) hL 2)
    _=_ := by
      have hp : (Z^d)^2=Z^(2*d) := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
        congr 1
        push_cast
        ring
      rw [mul_pow,hp,Real.rpow_sub hZ]
      ring

end SevenEighths.ProbePhysical
end

end OAI
