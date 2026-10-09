import QRHParameterAudit.Parameters
import OAI.NumberTheory.DirichletL.ParametersSlotLengths

/-! The finite slot system for the modified physical probe.

These existence results choose the slots and their positive minimum before any
Hecke character or height orders. No estimate for the resulting probe is assumed
or proved here. -/
namespace OAI.QRHParameterAudit
noncomputable section
open scoped BigOperators

theorem exists_distinct_slots (total L : ℝ) (htotal : 0 < total) (hL : 0 < L) :
    ∃ N : ℕ, 0 < N ∧ ∃ d : Fin N → ℝ, Function.Injective d ∧
      (∀ j, 0 < d j ∧ d j < L) ∧ (∑ j, d j) = total := by
  obtain ⟨N, hN, d, hi, hd, hs⟩ :=
    SevenEighths.Parameters.exists_distinct_slot_lengths (L / (6*total)) (by positivity)
  refine ⟨N, hN, fun j => (6*total)*d j, ?_, ?_, ?_⟩
  · intro j k he
    exact hi (mul_left_cancel₀ (by positivity : (6*total) ≠ 0) he)
  · intro j
    refine ⟨mul_pos (by positivity) (hd j).1, ?_⟩
    have hh := (lt_div_iff₀ (by positivity : 0 < 6*total)).mp (hd j).2
    simpa only [mul_comm] using hh
  · rw [←Finset.mul_sum, hs]
    ring

/-- Positive, distinct physical slots with any prescribed total length, with
the same uniform capacity conditions as the original slot construction. -/
theorem exists_physical_slots (total dmin dmax mesh R : ℝ)
    (htotal : 0 < total) (hdmin : 0 < dmin) (hd : dmin ≤ dmax)
    (hm : 0 < mesh) (hR : 0 < R) :
    ∃ N : ℕ, 0 < N ∧ ∃ d : Fin N → ℝ, ∃ rmin : ℝ, 0 < rmin ∧
      Function.Injective d ∧ (∑ j, d j) = total ∧
      (∀ j, 0 < d j ∧ dmax*rmin ≤ d j ∧ d j ≤ dmin*mesh ∧ d j ≤ dmin*R) ∧
      (∀ u : ℝ, dmin ≤ u → u ≤ dmax → ∀ j,
        rmin ≤ d j/u ∧ d j/u ≤ mesh ∧ d j/u ≤ R) := by
  obtain ⟨N, hN, d, hi, he, hS⟩ := exists_distinct_slots total (dmin*min mesh R)
    htotal (mul_pos hdmin (lt_min hm hR))
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  obtain ⟨j, _, hjmin⟩ := Finset.exists_min_image Finset.univ d hne
  have hmax : 0 < dmax := hdmin.trans_le hd
  let rmin := d j/(2*dmax)
  have hr : 0 < rmin := div_pos (he j).1 (by positivity)
  have hlo (k : Fin N) : dmax*rmin ≤ d k := by
    have hk := hjmin k (Finset.mem_univ k)
    have hiden : dmax*rmin = d j/2 := by dsimp [rmin]; field_simp
    rw [hiden]
    linarith [(he j).1]
  have hup (k : Fin N) : d k ≤ dmin*mesh ∧ d k ≤ dmin*R := by
    constructor
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hdmin.le)
    · exact (he k).2.le.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hdmin.le)
  refine ⟨N, hN, d, rmin, hr, hi, hS,
    fun k => ⟨(he k).1, hlo k, (hup k).1, (hup k).2⟩, ?_⟩
  intro u hu hu' k
  have hu0 : 0 < u := hdmin.trans_le hu
  refine ⟨(le_div_iff₀ hu0).mpr ?_, (div_le_iff₀ hu0).mpr ?_,
    (div_le_iff₀ hu0).mpr ?_⟩
  · exact (by nlinarith : rmin*u ≤ dmax*rmin).trans (hlo k)
  · exact (hup k).1.trans (by nlinarith)
  · exact (hup k).2.trans (by nlinarith)

/-- The audited geometry has an actual finite slot system for every positive
mesh and capacity allowance. -/
theorem exists_audit_slots (mesh R : ℝ) (hm : 0 < mesh) (hR : 0 < R) :
    ∃ N : ℕ, 0 < N ∧ ∃ d : Fin N → ℝ, ∃ rmin : ℝ, 0 < rmin ∧
      Function.Injective d ∧ (∑ j, d j) = ell ∧
      (∀ j, 0 < d j ∧ (7/8)*rmin ≤ d j ∧ d j ≤ (1/100)*mesh ∧ d j ≤ (1/100)*R) ∧
      (∀ u : ℝ, 1/100 ≤ u → u ≤ 7/8 → ∀ j,
        rmin ≤ d j/u ∧ d j/u ≤ mesh ∧ d j/u ≤ R) :=
  exists_physical_slots ell (1/100) (7/8) mesh R
    (by norm_num [ell]) (by norm_num) (by norm_num) hm hR

end
end OAI.QRHParameterAudit
