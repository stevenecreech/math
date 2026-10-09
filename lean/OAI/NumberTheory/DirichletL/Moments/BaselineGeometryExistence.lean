import OAI.NumberTheory.DirichletL.Moments.BaselineGeometry
import OAI.NumberTheory.DirichletL.ParametersHighDataFine

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentBaselineGeometry

/-- The independent endpoint geometry is inhabited for every positive total
slot length and every prescribed admissible moment loss. The old `HighData`
is used only to supply a finite dimension and a source-window carrier. -/
theorem exists_geometry_with_total (total t ε : ℝ)
    (htotal : 0 < total) (ht : 0 < t) (ht1 : t ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/1000) :
    ∃ D : Parameters.HighData 1, ∃ G : Geometry D.N,
      G.t = t ∧ G.ε = ε ∧ (∑j, G.ell j) = total ∧
      ∃ rmin : ℝ, 0 < rmin ∧ ∀j, (7/8)*rmin ≤ G.ell j := by
  have hfactor : 0 < 6*total := by positivity
  obtain ⟨D, hfine⟩ := Parameters.exists_high_data_fine 1 (by norm_num)
    (fun _ => mesh t / (6*total))
    (fun _ _ => div_pos (mesh_pos ht) hfactor)
  let G : Geometry D.N := {
    t := t
    ε := ε
    ell := fun j => (6*total)*D.ell j
    t_pos := ht
    t_le_one := ht1
    epsilon_nonneg := hε
    epsilon_small := hε1
    ell_pos := fun j => mul_pos hfactor (D.slots_bounds j).1
    ell_injective := by
      intro j k he
      exact D.slots_injective (mul_left_cancel₀ hfactor.ne' he)
    ell_fine := by
      intro j
      have h := mul_le_mul_of_nonneg_left (hfine j) hfactor.le
      have he : (6*total)*(mesh t/(6*total)/200) = mesh t/200 := by
        field_simp [htotal.ne']
      exact h.trans_eq he }
  refine ⟨D, G, rfl, rfl, ?_, (6*total)*D.rmin,
    mul_pos hfactor D.rmin_pos, ?_⟩
  · change (∑j, (6*total)*D.ell j) = total
    rw [←Finset.mul_sum, D.slots_sum]
    ring
  · intro j
    have h := mul_le_mul_of_nonneg_left (D.slots_bounds j).2.1 hfactor.le
    change (7/8)*((6*total)*D.rmin) ≤ (6*total)*D.ell j
    nlinarith only [h]

/-- Fixing the moment loss does not impose a lower bound on the slot mesh.
The physical slots can simultaneously have any prescribed positive upper
bound and a positive lower bound scaled by the conductor cutoff. -/
theorem exists_geometry_with_capacity (total t ε cap dmax : ℝ)
    (htotal : 0 < total) (ht : 0 < t) (ht1 : t ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/1000) (hcap : 0 < cap)
    (hdmax : 0 < dmax) :
    ∃ D : Parameters.HighData 1, ∃ G : Geometry D.N,
      G.t = t ∧ G.ε = ε ∧ (∑j, G.ell j) = total ∧
      (∀j, G.ell j ≤ cap) ∧
      ∃ rmin : ℝ, 0 < rmin ∧ ∀j, dmax*rmin ≤ G.ell j := by
  have hfactor : 0 < 6*total := by positivity
  let fine := min (mesh t) (200*cap)
  have hfinepos : 0 < fine := lt_min (mesh_pos ht) (by positivity)
  obtain ⟨D, hfine⟩ := Parameters.exists_high_data_fine 1 (by norm_num)
    (fun _ => fine / (6*total)) (fun _ _ => div_pos hfinepos hfactor)
  have hscaled (j : Fin D.N) : (6*total)*D.ell j ≤ fine/200 := by
    have h := mul_le_mul_of_nonneg_left (hfine j) hfactor.le
    have he : (6*total)*(fine/(6*total)/200) = fine/200 := by
      field_simp [htotal.ne']
    exact h.trans_eq he
  let G : Geometry D.N := {
    t := t
    ε := ε
    ell := fun j => (6*total)*D.ell j
    t_pos := ht
    t_le_one := ht1
    epsilon_nonneg := hε
    epsilon_small := hε1
    ell_pos := fun j => mul_pos hfactor (D.slots_bounds j).1
    ell_injective := by
      intro j k he
      exact D.slots_injective (mul_left_cancel₀ hfactor.ne' he)
    ell_fine := fun j => (hscaled j).trans
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) }
  refine ⟨D, G, rfl, rfl, ?_, ?_, (6*total)*(7/8)*D.rmin/dmax,
    div_pos (mul_pos (mul_pos hfactor (by norm_num)) D.rmin_pos) hdmax, ?_⟩
  · change (∑j, (6*total)*D.ell j) = total
    rw [←Finset.mul_sum, D.slots_sum]
    ring
  · intro j
    have h := (hscaled j).trans
      (div_le_div_of_nonneg_right (min_le_right (mesh t) (200*cap)) (by norm_num))
    dsimp [G]
    convert h using 1 <;> ring
  · intro j
    have h := mul_le_mul_of_nonneg_left (D.slots_bounds j).2.1 hfactor.le
    change dmax*((6*total)*(7/8)*D.rmin/dmax) ≤ (6*total)*D.ell j
    have he : dmax*((6*total)*(7/8)*D.rmin/dmax) = (6*total)*((7/8)*D.rmin) := by
      field_simp [hdmax.ne']
      <;> ring
    rw [he]
    exact h

end SevenEighths.CenteredMomentBaselineGeometry

end

end OAI
