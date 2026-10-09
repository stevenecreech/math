import OAI.NumberTheory.DirichletL.ParametersHighData
import OAI.NumberTheory.DirichletL.Improved.ExplicitSlots
import QRHParameterAudit.ExplicitMeshArithmetic

namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.ImprovedExplicitCarrier

/-- The old source carrier can use a prescribed finite dimension and the
explicit distinct slots. Its auxiliary detector scales do not change them. -/
theorem exists_carrier_on_slots (N : ℕ) (hNlarge : 1000000000000000 ≤ N) :
    ∃D : Parameters.HighData 1, D.N = N ∧
      (∀j, 1/(12*(D.N : ℝ)) ≤ D.ell j) ∧
      (∀j, D.ell j ≤ 1/(3*(D.N : ℝ))) := by
  have hNreal : (1000000000000000 : ℝ) ≤ N := by exact_mod_cast hNlarge
  have hNp : 0 < (N : ℝ) := by linarith
  have hN : 0 < N := by exact_mod_cast hNp
  let t : ℝ := 1/100000000
  have ht : 0 < t := by norm_num [t]
  have ht1 : t ≤ 1/100000000 := le_rfl
  let ell := ImprovedExplicitSlots.ell N
  let rmin : ℝ := 1/(32*(N : ℝ))
  have hr : 0 < rmin := by dsimp [rmin]; positivity
  have hlower (j : Fin N) : (7/8)*rmin ≤ ell j := by
    calc
      (7/8)*rmin = (7/256)*(1/(N : ℝ)) := by dsimp [rmin]; ring
      _ ≤ (1/12)*(1/(N : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = 1/(12*(N : ℝ)) := by ring
      _ ≤ ell j := ImprovedExplicitSlots.ell_lower hN j
  have hupper (j : Fin N) : ell j ≤ (1/200)*t := by
    apply (ImprovedExplicitSlots.ell_upper hN j).trans
    apply (div_le_iff₀ (show 0 < 3*(N : ℝ) by positivity)).mpr
    norm_num only [t]
    nlinarith only [hNreal]
  let allowance := t/((N : ℝ)+2000)
  have hden : 0 < (N : ℝ)+2000 := by positivity
  have ha : 0 < allowance := div_pos ht hden
  have ha0 : allowance ≤ t/2000 := div_le_div_of_nonneg_left ht.le
    (by norm_num) (by linarith only [hNp])
  let ellMin := (7/8 : ℝ)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    Parameters.exists_detector_scales t rmin t (1/200) t ellMin allowance 0
      ht.le hr ht (by norm_num) ht hmin ha (by norm_num)
  let eps := allowance/2
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hepsa : eps ≤ allowance := by dsimp [eps]; linarith only [ha]
  have heps1 : eps ≤ 1 := by linarith only [hepsa, ha0, ht1]
  have hεt : 2000*ε ≤ t := by
    have h := (le_div_iff₀ (show (0 : ℝ) < 2000 by norm_num)).mp (hεa.trans ha0)
    simpa only [mul_comm] using h
  have het : 2000*e ≤ t := by
    have h := (le_div_iff₀ (show (0 : ℝ) < 2000 by norm_num)).mp (hea.trans ha0)
    simpa only [mul_comm] using h
  have heN : ((N : ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ hden).mp hepsa
    simpa only [mul_comm] using h
  have he8 : ((N : ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst : sigma ≤ t/2 := min_le_left _ _
  have hsel : sigma ≤ ellMin/4 := min_le_right _ _
  refine ⟨{
    t := t, N := N, ell := ell, rmin := rmin,
    ε := ε, e := e, κ := κ, cost := cost, eps := eps, sigma := sigma,
    t_pos := ht
    t_delta := by norm_num [t]
    t_small := ht1
    slots_pos := hN
    slots_injective := ImprovedExplicitSlots.ell_injective hN
    slots_sum := ImprovedExplicitSlots.ell_sum hN
    slots_bounds := fun j => ⟨ImprovedExplicitSlots.ell_pos hN j, hlower j, hupper j⟩
    rmin_pos := hr
    epsilon_pos := hε
    epsilon_small := hε1
    epsilon_gap := hεgap
    e_pos := he
    e_small := he1
    kappa_pos := hκ
    kappa_small := hκ1
    cost_pos := hcost
    eps_pos := heps
    eps_small := heps1
    sigma_pos := hs
    detector_budget := by linarith only [hdet]
    phase_budget := hphase
    count_budget := by
      dsimp only [t] at hεt ⊢
      linarith only [hεt]
    central_budget := by
      dsimp only [t] at hεt het he8 ⊢
      linarith only [hεt, het, he8]
    geometric_budget := by
      dsimp only [t] at hst het ⊢
      linarith only [hst, het]
    principal_budget := by linarith only [hst, ht1]
    window_budget := by
      change sigma+e ≤ (7/8)*ellMin
      linarith only [hsel, heell, hmin]
    floor_budget := by
      dsimp only [t] at hst het he8 ⊢
      linarith only [hst, het, he8]
    high_saving := by linarith only [hst, ht]
    height_choice := ?_ }, rfl,
      ImprovedExplicitSlots.ell_lower hN, ImprovedExplicitSlots.ell_upper hN⟩
  intro J hJ
  let τ := min ((1/200 : ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
  have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hτc : τ ≤ (1/200 : ℝ)*cost/16 := min_le_left _ _
  have hτd : τ ≤ 1/800 := (min_le_right _ _).trans (min_le_left _ _)
  have hτt : τ ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
  have hτJ : τ*(4*(J+7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
  have hprod : 0 ≤ τ*J := mul_nonneg htau.le hJ
  have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
  refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc,hcost],
    by nlinarith only [hτJ,hprod,htau],by nlinarith only [hτJ,hprod,htau],
    by nlinarith only [hτJ,hprod,hprodeps,htau]⟩

/-- Explicit finite dimension and uniform slot bounds for the final geometry. -/
theorem exists_carrier :
    ∃D : Parameters.HighData 1, D.N = QRHParameterAudit.explicitSlotCount ∧
      (∀j, 1/(12*(D.N : ℝ)) ≤ D.ell j) ∧
      (∀j, D.ell j ≤ 1/(3*(D.N : ℝ))) :=
  exists_carrier_on_slots QRHParameterAudit.explicitSlotCount
    (by exact_mod_cast QRHParameterAudit.explicitSlotCount_large)

end SevenEighths.ImprovedExplicitCarrier

end
end OAI
