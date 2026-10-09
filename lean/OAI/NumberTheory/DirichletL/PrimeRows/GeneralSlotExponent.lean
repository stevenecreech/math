import OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum_general {Slot : Type*} (slots : Finset Slot)
    (ell : Slot → ℝ) (d total : ℝ) (hell : ∑j∈slots, ell j = total) :
    (∑j∈slots, ell j/d) = total/d := by
  rw [←Finset.sum_div, hell]

lemma source_slot_weightedMean_general {Slot : Type*} (slots : Finset Slot)
    (ell g : Slot → ℝ) (d total : ℝ) (hd : d ≠ 0) (htotal : total ≠ 0)
    (hell : ∑j∈slots, ell j = total) :
    weightedMean slots (fun j => ell j/d) g = (∑j∈slots, ell j*g j)/total := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div, ←Finset.sum_div, hell]
  field_simp [hd, htotal]

lemma source_slot_product_general {Slot : Type*} (slots : Finset Slot)
    (ell g : Slot → ℝ) (Z d mesh total : ℝ) (hZ : 0 < Z) (hd : d ≠ 0)
    (htotal : total ≠ 0) (hell : ∑j∈slots, ell j = total) :
    (∏j∈slots, (Z^(ell j))^(-(4/25 : ℝ)+g j+mesh)) =
      Z^(total*(-4/25+weightedMean slots (fun j => ell j/d) g+mesh)) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean_general slots ell g d total hd htotal hell]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [←Finset.sum_mul, ←Finset.sum_mul, hell]
  field_simp [htotal]
  <;> ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
