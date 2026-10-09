import OAI.NumberTheory.DirichletL.Moments.BaselineGeometryExistence
import QRHParameterAudit.OtherRegimes

namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.ImprovedParameters
open CenteredMomentBaselineGeometry
open QRHParameterAudit

/-- Common physical, moment, and detector parameters for the fixed-baseline
route. The old carrier supplies only the finite dimension and source window;
its gap and its physical slot lengths are not used by this geometry. -/
structure HighData where
  carrier : Parameters.HighData 1
  G : Geometry carrier.N
  t rmin ε e κ cost eps sigma : ℝ
  geometry_t : G.t = t
  geometry_epsilon : G.ε = ε
  t_pos : 0 < t
  t_small : t ≤ 1/1000000000000
  slots_sum : (∑j, G.ell j) = QRHParameterAudit.ell
  slots_bounds : ∀j, (7/8)*rmin ≤ G.ell j ∧ G.ell j ≤ (1/200)*t
  rmin_pos : 0 < rmin
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1/1000
  epsilon_gap : ε < rmin*t
  e_pos : 0 < e
  e_small : e < 1/1000
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  sigma_pos : 0 < sigma
  detector_budget : 12*e*((22:ℝ)+2)+8*κ+2*cost ≤ ε/2
  phase_budget : 8*e*t+κ ≤ ε
  conductor_budget : geomH+extension+2*t ≤ 7/8
  count_budget : 159*ε+t+t+7*t ≤ 1/32
  central_budget : (159*ε+t+t+7*t)+(3/2)*(2*t)+28*e+
    (carrier.N+8)*eps+t+QRHParameterAudit.ell*t+(t+t+t)+t ≤ (7/8)*gammaSave
  geometric_budget : sigma+8*e+t/8 ≤ 122913/1562500
  principal_budget : sigma+t/8 ≤ 1/4000
  window_budget : sigma+e ≤ (7/8)*((7/8)*rmin)
  floor_budget : 2*extension+28*e+(carrier.N+8)*eps+t+
    QRHParameterAudit.ell*t+t/8+sigma ≤ 1/200
  high_saving : sigma+t/8+t/8 ≤ t
  height_choice : ∀J : ℝ, 0 ≤ J → ∃heightCost τ : ℝ,
    0 < heightCost ∧ heightCost ≤ t ∧ heightCost*J ≤ t ∧
    0 < τ ∧ τ < (1/200)/2 ∧ 4*τ < (1/200)*cost ∧
    τ < heightCost ∧ τ*(2+4*eps) < t

/-- All common parameters exist before a target character is chosen. In
particular the saving remains strictly positive even when the required slot
mesh makes the minimum slot length very small. -/
theorem exists_high_data : Nonempty HighData := by
  let t : ℝ := 1/1000000000000
  have ht : 0 < t := by norm_num [t]
  have ht1 : t ≤ 1/1000000000000 := le_rfl
  obtain ⟨D, G₀, hGt, _, hsum, hupper, rmin, hrmin, hlower⟩ :=
    exists_geometry_with_capacity QRHParameterAudit.ell t 0 ((1/200)*t) (7/8)
      (by norm_num [QRHParameterAudit.ell]) ht (by norm_num [t])
      le_rfl (by norm_num) (by positivity) (by norm_num)
  let allowance := t/((D.N:ℝ)+2000)
  have hden : 0 < (D.N:ℝ)+2000 := by positivity
  have ha : 0 < allowance := div_pos ht hden
  have ha0 : allowance ≤ t/2000 :=
    div_le_div_of_nonneg_left ht.le (by norm_num)
      (by linarith [Nat.cast_nonneg (α:=ℝ) D.N])
  let ellMin : ℝ := (7/8)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hrmin
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    Parameters.exists_detector_scales t rmin t (1/200) t ellMin allowance 0
      ht.le hrmin ht (by norm_num) ht hmin ha (by norm_num)
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
  have heN : ((D.N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ hden).mp hepsa
    simpa only [mul_comm] using h
  have he8 : ((D.N:ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst : sigma ≤ t/2 := min_le_left _ _
  have hsel : sigma ≤ ellMin/4 := min_le_right _ _
  let G : Geometry D.N := {
    G₀ with
    ε := ε
    epsilon_nonneg := hε.le
    epsilon_small := hε1 }
  refine ⟨{
    carrier := D
    G := G
    t := t
    rmin := rmin
    ε := ε
    e := e
    κ := κ
    cost := cost
    eps := eps
    sigma := sigma
    geometry_t := hGt
    geometry_epsilon := rfl
    t_pos := ht
    t_small := ht1
    slots_sum := hsum
    slots_bounds := fun j => ⟨hlower j, hupper j⟩
    rmin_pos := hrmin
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
    detector_budget := hdet
    phase_budget := hphase
    conductor_budget := by norm_num [geomH, extension, gammaSave, t]
    count_budget := by
      dsimp only [t] at hεt ⊢
      linarith only [hεt]
    central_budget := ?_
    geometric_budget := by
      dsimp only [t] at hst het ⊢
      linarith only [hst, het]
    principal_budget := by linarith only [hst, ht1]
    window_budget := by
      change sigma+e ≤ (7/8)*ellMin
      linarith only [hsel, heell, hmin]
    floor_budget := ?_
    high_saving := by linarith only [hst, ht]
    height_choice := ?_ }⟩
  · norm_num only [QRHParameterAudit.ell, gammaSave]
    dsimp only [t] at hεt het he8 ⊢
    linarith only [hεt, het, he8]
  · norm_num only [extension, gammaSave, QRHParameterAudit.ell]
    dsimp only [t] at het he8 hst ⊢
    linarith only [het, he8, hst]
  · intro J hJ
    let heightCost := t/(J+1)
    have hheight : 0 < heightCost := div_pos ht (by positivity)
    have hheight1 : heightCost ≤ t := by
      apply (div_le_iff₀ (show 0 < J+1 by positivity)).mpr
      nlinarith only [mul_nonneg ht.le hJ]
    have hheightJ : heightCost*J ≤ t := by
      have heq : heightCost*(J+1) = t := div_mul_cancel₀ _ (by positivity)
      nlinarith only [heq, hheight.le]
    let τ := min ((1/200:ℝ)*cost/16)
      (min (1/800) (min (heightCost/2) (t/28)))
    have htau : 0 < τ := lt_min (by positivity)
      (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
    have hτc : τ ≤ (1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ ≤ 1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτh : τ ≤ heightCost/2 := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
    have hτt : τ ≤ t/28 := (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))
    have hprod := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨heightCost, τ, hheight, hheight1, hheightJ, htau, ?_, ?_, ?_, ?_⟩
    · linarith only [hτd]
    · linarith only [hτc, hcost]
    · linarith only [hτh, hheight]
    · nlinarith only [hτt, hprod, ht]

end SevenEighths.ImprovedParameters

end
end OAI
