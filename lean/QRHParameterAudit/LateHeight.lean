import QRHParameterAudit.Parameters
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace OAI.QRHParameterAudit
noncomputable section

/-- Height is chosen after the fixed seminorm order A, for every positive saving m. -/
theorem exists_late_height {dmin tau0 m A : ℝ}
    (hd : 0 < dmin) (ht0 : 0 < tau0) (hm : 0 < m) (hA : 0 ≤ A) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ dmin/100 ∧ tau ≤ tau0 ∧ tau*A < m/4 := by
  let tau := min (dmin/200) (min (tau0/2) (m/(8*(A+1))))
  have ht : 0 < tau := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have h1 : tau ≤ dmin/200 := min_le_left _ _
  have h2 : tau ≤ tau0/2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : tau ≤ m/(8*(A+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hprod : tau*(8*(A+1)) ≤ m := (le_div_iff₀ (by positivity)).mp h3
  refine ⟨tau,ht,by linarith,by linarith,?_⟩
  nlinarith only [ht,hprod,hm]

/-- The tail order is chosen after the positive height exponent. -/
theorem exists_late_tail {tau B target : ℝ} (ht : 0 < tau) :
    ∃ N : ℕ, B-(N:ℝ)*tau < target := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((B-target)/tau)
  have h := (div_lt_iff₀ ht).mp hN
  exact ⟨N,by linarith⟩

/-- No positive lower bound on beta-sigma0 is required for these choices. -/
theorem exists_common_losses {beta : ℝ} (hb : sigma0 < beta) :
    ∃ omega margin : ℝ, 0 < omega ∧ omega < beta-sigma0 ∧
      0 < margin ∧ margin ≤ gammaSave/2 ∧ margin ≤ (beta-sigma0)/2 := by
  refine ⟨(beta-sigma0)/2, min (gammaSave/2) ((beta-sigma0)/2),
    by linarith,by linarith,?_,min_le_left _ _,min_le_right _ _⟩
  exact lt_min (by have := parameter_bounds.2.2.2.2.2.2.2; positivity) (by linarith)

/-- A supremum need not be attained; every strictly lower level has a witness. -/
theorem exists_above_level {S : Set ℝ} (hne : S.Nonempty) (hbd : BddAbove S)
    {c : ℝ} (hc : c < sSup S) : ∃ x ∈ S, c < x :=
  (lt_csSup_iff hbd hne).mp hc

/-- Exclude the adjoined sentinel without assuming a rightmost zero. -/
theorem exists_above_sentinel {S : Set ℝ} {sentinel c : ℝ}
    (hbd : BddAbove (insert sentinel S)) (hs : sentinel ≤ c)
    (hc : c < sSup (insert sentinel S)) : ∃ x ∈ S, c < x := by
  obtain ⟨x,hx,hxc⟩ := exists_above_level (Set.insert_nonempty sentinel S) hbd hc
  rcases Set.mem_insert_iff.mp hx with h | h
  · subst x
    exact False.elim ((not_lt_of_ge hs) hxc)
  · exact ⟨x,h,hxc⟩

end
end OAI.QRHParameterAudit
