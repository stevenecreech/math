import QRHParameterAudit.SlotExtension

namespace OAI.QRHParameterAudit.EulerExtension
noncomputable section
open scoped BigOperators Classical
open SevenEighths.PrincipalSlotEstimate

/-- The local extended-region error survives a nonnegative weighted prime-window sum. -/
theorem weighted_region_slot_error {ι : Type*} (S : Finset ι) (weight Q : ι → ℝ)
    (A eta : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hweight : ∀ i ∈ S, 0 ≤ weight i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (he : ∀ i ∈ S, ‖eta i‖ = 1)
    (hs : (3/4:ℝ) ≤ s.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    ‖(∑ i ∈ S, (weight i:ℂ)*regionSlot (Q i) (A i) (eta i) s w z)+
      (∑ i ∈ S, weight i:ℝ)‖ ≤
      (1440*P^(-(37/50:ℝ)))*(∑ i ∈ S, weight i) := by
  apply weighted_slot_error S weight _ _ hweight
  intro i hi
  apply (region_slot_error (hP.trans (hQ i hi)) (hA i hi) (he i hi) hs hw hz).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)

/-- The same principal scalar as the original proof; positive window masses make it nonzero.
The error is uniform in imaginary height and in the finite prime-window supports. -/
theorem weighted_region_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (weight Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hsmall : 1440*P^(-(37/50:ℝ)) ≤ 1)
    (hweight : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ weight j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (he : ∀ j ∈ S, ∀ i ∈ T j, ‖eta j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, weight j i)
    (hs : (3/4:ℝ) ≤ s.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    principalScalar S (fun j => ∑ i ∈ T j, weight j i) ≠ 0 ∧
    ‖(∏ j ∈ S, ∑ i ∈ T j, (weight j i:ℂ)*regionSlot (Q j i) (A j i) (eta j i) s w z)/
      principalScalar S (fun j => ∑ i ∈ T j, weight j i)-1‖ ≤
      (S.card*2^S.card*1440)*P^(-(37/50:ℝ)) := by
  constructor
  · exact principalScalar_ne_zero S _ hM
  · have h := fixed_product_relative_error_linear S
      (fun j => ∑ i ∈ T j, weight j i)
      (fun j => ∑ i ∈ T j, (weight j i:ℂ)*regionSlot (Q j i) (A j i) (eta j i) s w z)
      (1440*P^(-(37/50:ℝ))) (by positivity) hsmall hM
      (fun j hj => weighted_region_slot_error (T j) (weight j) (Q j) (A j) (eta j)
        s w z P hP (hweight j hj) (hQ j hj) (hA j hj) (he j hj) hs hw hz)
    simpa only [mul_assoc] using h

/-- Principal specialization, using the original `principalSlot` and `principalScalar`. -/
theorem weighted_principal_product_error_extended {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (weight Q : κ → ι → ℝ) (A eta : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hsmall : 1440*P^(-(37/50:ℝ)) ≤ 1)
    (hweight : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ weight j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (he : ∀ j ∈ S, ∀ i ∈ T j, ‖eta j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, weight j i)
    (hs : (3/4:ℝ) ≤ s.re) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (weight j i:ℂ)*principalSlot (Q j i) (A j i) (eta j i) s)/
      principalScalar S (fun j => ∑ i ∈ T j, weight j i)-1‖ ≤
      (S.card*2^S.card*1440)*P^(-(37/50:ℝ)) := by
  have h := (weighted_region_product_error_linear S T weight Q A eta s 1 (1/6) P hP hsmall
    hweight hQ hA he hM hs (by norm_num) (by norm_num)).2
  simpa only [regionSlot,regionReplacement,regionMarked,principalSlot,principalReplacement,
    principalMarked] using h

end
end OAI.QRHParameterAudit.EulerExtension
