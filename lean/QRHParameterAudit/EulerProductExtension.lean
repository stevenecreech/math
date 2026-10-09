import QRHParameterAudit.EulerExtension
import OAI.NumberTheory.DirichletL.Detector.NormalProduct

namespace OAI.QRHParameterAudit.EulerExtension
noncomputable section
open scoped BigOperators Classical
open SevenEighths.ProbeEuler

/-- The same rational Euler correction as in the repository, after finite exclusions. -/
def extendedCorrection {ι : Type*} (Q : ι → ℝ) (A eta v : ι → ℂ)
    (excluded : Finset ι) (x w z : ℂ) : ℂ :=
  ∏' i : {i : ι // i ∉ excluded}, unramifiedClosed (Q i.val) (A i.val) (eta i.val) (v i.val) x w z

def extendedDefect {ι : Type*} (Q : ι → ℝ) (i : ι) : ℝ := 240*(Q i)^(-(149/100:ℝ))

theorem extendedDefect_nonneg {ι : Type*} (Q : ι → ℝ) (i : ι) (hQ : 0 ≤ Q i) : 0 ≤ extendedDefect Q i := by
  unfold extendedDefect
  positivity

/-- Uniform convergence gives holomorphy and a nonvanishing correction on the extended region.
Summability of the norm weight and its small tail are explicit analytic hypotheses. -/
theorem extendedCorrection_analytic_and_close {ι : Type*}
    (Q : ι → ℝ) (A eta v : ι → ℂ) (excluded : Finset ι)
    (hQ : ∀ i, 4 ≤ Q i) (hA : ∀ i, ‖A i‖ ≤ 1)
    (he : ∀ i, ‖eta i‖ ≤ 1) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hsum : Summable (fun i : {i : ι // i ∉ excluded} => extendedDefect Q i.val))
    (hsmall : (∑' i : {i : ι // i ∉ excluded}, extendedDefect Q i.val) ≤ 1/6)
    (w z : ℂ) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => extendedCorrection Q A eta v excluded x w z)
      {x : ℂ | 3/4 < x.re} ∧
    ∀ x : ℂ, 3/4 < x.re → ‖extendedCorrection Q A eta v excluded x w z-1‖ ≤ 1/2 := by
  have hhalf (i : {i : ι // i ∉ excluded}) : extendedDefect Q i.val ≤ 1/2 := by
    have h := Summable.le_tsum hsum i (fun j _ => extendedDefect_nonneg Q j.val (by linarith [hQ j.val]))
    linarith
  have hbound (i : {i : ι // i ∉ excluded}) (x : ℂ) (hx : 3/4 < x.re) :
      ‖unramifiedClosed (Q i.val) (A i.val) (eta i.val) (v i.val) x w z-1‖ ≤
        extendedDefect Q i.val :=
    unramifiedClosed_extended_second_region_bound _ _ _ _ _ _ _
      (hQ i.val) (hA i.val) (he i.val) (hv i.val) hx.le hw hz
  constructor
  · exact normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hsum
      (fun i => unramifiedClosed_extended_analytic_x _ _ _ _ _ _
        (hQ i.val) (hA i.val) (he i.val) (hv i.val) hz) hbound hhalf
  · intro x hx
    exact product_defect_le _ _ hsum (fun i => hbound i x hx) hhalf hsmall

/-- The cutoff is chosen before all target phases and external parameters. -/
theorem exists_uniform_extended_cutoff {ι : Type*} (Q : ι → ℝ)
    (hQ : ∀ i, 4 ≤ Q i) (hsum : Summable (extendedDefect Q)) :
    ∃ excluded : Finset ι, ∀ A eta v : ι → ℂ,
      (∀ i, ‖A i‖ ≤ 1) → (∀ i, ‖eta i‖ ≤ 1) → (∀ i, ‖v i‖ ≤ 1) →
      ∀ w z : ℂ, (19/20:ℝ) ≤ w.re → (33/200:ℝ) ≤ z.re →
      AnalyticOnNhd ℂ (fun x => extendedCorrection Q A eta v excluded x w z)
        {x : ℂ | 3/4 < x.re} ∧
      ∀ x : ℂ, 3/4 < x.re → ‖extendedCorrection Q A eta v excluded x w z-1‖ ≤ 1/2 := by
  obtain ⟨excluded,hsmall⟩ := ((tendsto_order.1
    (tendsto_tsum_compl_atTop_zero (extendedDefect Q))).2 (1/6) (by norm_num)).exists
  refine ⟨excluded,?_⟩
  intro A eta v hA he hv w z hw hz
  exact extendedCorrection_analytic_and_close Q A eta v excluded hQ hA he hv
    (hsum.subtype _) hsmall.le w z hw hz

end
end OAI.QRHParameterAudit.EulerExtension
