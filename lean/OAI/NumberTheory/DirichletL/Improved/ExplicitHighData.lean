import OAI.NumberTheory.DirichletL.Improved.HighData
import OAI.NumberTheory.DirichletL.Improved.ExplicitCarrier
import OAI.NumberTheory.DirichletL.Moments.BaselineExplicitMesh

/-! A prescribed numerical saving for the actual fixed-baseline parameter
package. This module remains subject to the full actual-source build. -/

namespace OAI

noncomputable section
open scoped BigOperators

namespace SevenEighths.ImprovedParameters
open CenteredMomentBaselineGeometry QRHParameterAudit

private theorem exists_with_prescribed_saving
    (carrier : Parameters.HighData 1) (G₀ : Geometry carrier.N)
    (rmin sigma : ℝ)
    (hGt : G₀.t = explicitT)
    (hsum : (∑j, G₀.ell j) = QRHParameterAudit.ell)
    (hbounds : ∀j, (7/8)*rmin ≤ G₀.ell j ∧ G₀.ell j ≤ (1/200)*explicitT)
    (hrmin : 0 < rmin) (hs : 0 < sigma)
    (hst : sigma ≤ explicitT/2)
    (hsel : sigma ≤ ((7/8)*rmin)/4) :
    ∃ D : HighData, D.sigma = sigma := by
  let t : ℝ := explicitT
  have ht : 0 < t := by norm_num [t, explicitT]
  have ht1 : t ≤ 1/1000000000000 := by norm_num [t, explicitT]
  let allowance := t/((carrier.N:ℝ)+2000)
  have hden : 0 < (carrier.N:ℝ)+2000 := by positivity
  have ha : 0 < allowance := div_pos ht hden
  have ha0 : allowance ≤ t/2000 :=
    div_le_div_of_nonneg_left ht.le (by norm_num)
      (by linarith [Nat.cast_nonneg (α:=ℝ) carrier.N])
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
    have h := (le_div_iff₀ (show (0:ℝ) < 2000 by norm_num)).mp (hεa.trans ha0)
    simpa only [mul_comm] using h
  have het : 2000*e ≤ t := by
    have h := (le_div_iff₀ (show (0:ℝ) < 2000 by norm_num)).mp (hea.trans ha0)
    simpa only [mul_comm] using h
  have heN : ((carrier.N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ hden).mp hepsa
    simpa only [mul_comm] using h
  have he8 : ((carrier.N:ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  let G : Geometry carrier.N := {
    G₀ with
    ε := ε
    epsilon_nonneg := hε.le
    epsilon_small := hε1 }
  refine ⟨{
    carrier := carrier
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
    slots_bounds := hbounds
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
    conductor_budget := by norm_num [geomH, extension, gammaSave, t, explicitT]
    count_budget := by
      dsimp only [t, explicitT] at hεt ⊢
      linarith only [hεt]
    central_budget := ?_
    geometric_budget := by
      dsimp only [t, explicitT] at hst het ⊢
      linarith only [hst, het]
    principal_budget := by
      dsimp only [t, explicitT] at hst ⊢
      linarith only [hst]
    window_budget := by
      change sigma+e ≤ (7/8)*ellMin
      linarith only [hsel, heell, hmin]
    floor_budget := ?_
    high_saving := by
      dsimp only [t, explicitT] at hst ⊢
      linarith only [hst]
    height_choice := ?_ }, rfl⟩
  · dsimp only [t, explicitT] at hεt het he8 ⊢
    norm_num only [QRHParameterAudit.ell, gammaSave]
    linarith only [hεt, het, he8]
  · dsimp only [t, explicitT] at het he8 hst ⊢
    norm_num only [extension, gammaSave, QRHParameterAudit.ell]
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

private theorem explicit_scaled_lower (n x : ℝ) (hn : 0 < n)
    (hx : 1/(12*n) ≤ x) :
    (7/8)*(1/(32*n)) ≤ (6*QRHParameterAudit.ell)*x := by
  calc
    (7/8)*(1/(32*n)) = (7/256)*(1/n) := by ring
    _ ≤ (QRHParameterAudit.ell/2)*(1/n) :=
      mul_le_mul_of_nonneg_right (by norm_num [QRHParameterAudit.ell])
        (one_div_pos.mpr hn).le
    _ = (6*QRHParameterAudit.ell)*(1/(12*n)) := by ring
    _ ≤ (6*QRHParameterAudit.ell)*x :=
      mul_le_mul_of_nonneg_left hx (by norm_num [QRHParameterAudit.ell])

private theorem explicit_scaled_upper (n x : ℝ)
    (hx : x ≤ 1/(3*n)) :
    (6*QRHParameterAudit.ell)*x ≤ 2*QRHParameterAudit.ell/n := by
  calc
    (6*QRHParameterAudit.ell)*x ≤ (6*QRHParameterAudit.ell)*(1/(3*n)) :=
      mul_le_mul_of_nonneg_left hx (by norm_num [QRHParameterAudit.ell])
    _ = 2*QRHParameterAudit.ell/n := by ring

/-- The actual parameter package can retain the specified numerical saving
`2^(-1000000000000000000)`, rather than merely an unnamed positive margin.
The power is kept symbolic throughout the proof. -/
theorem exists_explicit_high_data :
    ∃ D : HighData, D.sigma = explicitSaving := by
  obtain ⟨carrier, hN, hlower, hupper⟩ := ImprovedExplicitCarrier.exists_carrier
  have hNpos : 0 < (carrier.N:ℝ) := by exact_mod_cast carrier.slots_pos
  have hfactor : 0 < 6*QRHParameterAudit.ell := by norm_num [QRHParameterAudit.ell]
  let G : Geometry carrier.N := {
    t := explicitT
    ε := 0
    ell := fun j => (6*QRHParameterAudit.ell)*carrier.ell j
    t_pos := explicitT_pos
    t_le_one := by norm_num [explicitT]
    epsilon_nonneg := le_rfl
    epsilon_small := by norm_num
    ell_pos := fun j => mul_pos hfactor (carrier.slots_bounds j).1
    ell_injective := by
      intro j k hjk
      exact carrier.slots_injective (mul_left_cancel₀ hfactor.ne' hjk)
    ell_fine := by
      intro j
      have h := explicit_scaled_upper (carrier.N:ℝ) (carrier.ell j) (hupper j)
      exact h.trans (by simpa only [hN] using explicit_scaled_slot_mesh) }
  let rmin : ℝ := 1/(32*(carrier.N:ℝ))
  have hrmin : 0 < rmin := by dsimp [rmin]; positivity
  have hsum : (∑j, G.ell j) = QRHParameterAudit.ell := by
    change (∑j, (6*QRHParameterAudit.ell)*carrier.ell j) = QRHParameterAudit.ell
    rw [← Finset.mul_sum, carrier.slots_sum]
    ring
  have hbounds : ∀j, (7/8)*rmin ≤ G.ell j ∧ G.ell j ≤ (1/200)*explicitT := by
    intro j
    constructor
    · exact explicit_scaled_lower (carrier.N:ℝ) (carrier.ell j) hNpos (hlower j)
    · exact (explicit_scaled_upper (carrier.N:ℝ) (carrier.ell j) (hupper j)).trans
        (by simpa only [hN] using explicit_scaled_slot_cap)
  have hsmin : explicitSaving ≤ ((7/8)*rmin)/4 := by
    rw [explicitSaving_eq, ← hN]
    dsimp [rmin]
    have h := div_le_div_of_nonneg_right (by norm_num : (1:ℝ) ≤ 7)
      (show 0 ≤ 1024*(carrier.N:ℝ) by positivity)
    convert h using 1
    ring
  exact exists_with_prescribed_saving carrier G rmin explicitSaving rfl hsum hbounds
    hrmin explicitSaving_pos explicitSaving_le_halfT hsmin

end SevenEighths.ImprovedParameters

end
end OAI
