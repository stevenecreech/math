import QRHParameterAudit.IdealSummability
import QRHParameterAudit.EulerProductExtension

namespace OAI.QRHParameterAudit.EulerExtension
noncomputable section
open scoped BigOperators Classical
open SevenEighths.ProbeEuler

/-- The same prime-ideal index used by the physical probe, for any number field. -/
abbrev NormPrime (K : Type*) [Field K] [NumberField K] :=
  {P : Ideal (NumberField.RingOfIntegers K) // Prime P}

variable (K : Type*) [Field K] [NumberField K]

def idealDefect (P : NormPrime K) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ)^(-(149/100:ℝ))

/-- No character estimates or nonvanishing assumptions are needed for convergence. -/
theorem idealDefect_summable : Summable (idealDefect K) := by
  exact ((ideal_norm_rpow_summable K (149/100) (by norm_num)).comp_injective
    Subtype.val_injective).mul_left 240

theorem idealDefect_nonneg (P : NormPrime K) : 0 ≤ idealDefect K P := by
  unfold idealDefect
  positivity

/-- Original rational local factors indexed by actual prime ideals and their absolute norms.
The phases remain arguments, so the result holds uniformly for the Hecke phases once identified. -/
def idealCorrection (A eta v : NormPrime K → ℂ)
    (S : Finset (Ideal (NumberField.RingOfIntegers K))) (x w z : ℂ) : ℂ :=
  ∏' P : {P : NormPrime K // P.val ∉ S},
    unramifiedClosed (Ideal.absNorm P.val.val) (A P.val) (eta P.val) (v P.val) x w z

/-- A single norm cutoff works before choosing phases, external parameters, or exclusions.
This is unconditional holomorphy of the correction product, not L-function nonvanishing. -/
theorem exists_uniform_ideal_cutoff :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ S : Finset (Ideal (NumberField.RingOfIntegers K)),
      (∀ P : NormPrime K, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ A eta v : NormPrime K → ℂ,
      (∀ P, ‖A P‖ ≤ 1) → (∀ P, ‖eta P‖ ≤ 1) → (∀ P, ‖v P‖ ≤ 1) →
      ∀ w z : ℂ, (19/20:ℝ) ≤ w.re → (33/200:ℝ) ≤ z.re →
      AnalyticOnNhd ℂ (fun x => idealCorrection K A eta v S x w z)
        {x : ℂ | 3/4 < x.re} ∧
      ∀ x : ℂ, 3/4 < x.re → ‖idealCorrection K A eta v S x w z-1‖ ≤ 1/2 := by
  obtain ⟨F,hF⟩ := ((tendsto_order.1
    (tendsto_tsum_compl_atTop_zero (idealDefect K))).2 (1/6) (by norm_num)).exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N,le_max_left _ _,?_⟩
  intro S hS A eta v hA he hv w z hw hz
  let T := {P : NormPrime K // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    exact P.property (hS P.val
      ((Finset.le_sup (f := fun Q : NormPrime K => Ideal.absNorm Q.val) hm).trans
        (le_max_right _ _)))
  let inc : T → {P : NormPrime K // P ∉ F} := fun P => ⟨P.val,hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    exact Subtype.ext (congrArg (fun t : {P : NormPrime K // P ∉ F} => t.val) h)
  have hnorm (P : T) : 4 ≤ (Ideal.absNorm P.val.val:ℝ) := by
    have hh : ¬ Ideal.absNorm P.val.val ≤ N := fun h => P.property (hS P.val h)
    exact_mod_cast (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T => idealDefect K P.val) :=
    (idealDefect_summable K).subtype _
  have hsmall : (∑' P : T, idealDefect K P.val) ≤ 1/6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi (fun P _ => idealDefect_nonneg K P.val)
      (fun _ => le_rfl) hsum ((idealDefect_summable K).subtype _)
  have hhalf (P : T) : idealDefect K P.val ≤ 1/2 := by
    have hh := Summable.le_tsum hsum P (fun Q _ => idealDefect_nonneg K Q.val)
    linarith
  have hbound (P : T) (x : ℂ) (hx : (3/4:ℝ) < x.re) :
      ‖unramifiedClosed (Ideal.absNorm P.val.val) (A P.val) (eta P.val) (v P.val) x w z-1‖ ≤
        idealDefect K P.val :=
    unramifiedClosed_extended_second_region_bound _ _ _ _ _ _ _
      (hnorm P) (hA P.val) (he P.val) (hv P.val) hx.le hw hz
  constructor
  · exact normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hsum
      (fun P => unramifiedClosed_extended_analytic_x _ _ _ _ _ _
        (hnorm P) (hA P.val) (he P.val) (hv P.val) hz) hbound hhalf
  · intro x hx
    exact product_defect_le _ _ hsum (fun P => hbound P x hx) hhalf hsmall

def idealSmallPrimeSet (N : ℕ) : Finset (Ideal (NumberField.RingOfIntegers K)) :=
  (Ideal.finite_setOfPred_absNorm_le N).toFinset.filter Prime

theorem mem_idealSmallPrimeSet (N : ℕ) (P : NormPrime K) :
    P.val ∈ idealSmallPrimeSet K N ↔ Ideal.absNorm P.val ≤ N := by
  simp [idealSmallPrimeSet,P.property]

/-- Finite prime exclusions can always be enlarged to obtain the extended correction. -/
theorem exists_ideal_correction (S₀ : Finset (Ideal (NumberField.RingOfIntegers K))) :
    ∃ S : Finset (Ideal (NumberField.RingOfIntegers K)), S₀ ⊆ S ∧
      (∀ P ∈ S, Prime P ∨ P ∈ S₀) ∧
      ∀ A eta v : NormPrime K → ℂ,
      (∀ P, ‖A P‖ ≤ 1) → (∀ P, ‖eta P‖ ≤ 1) → (∀ P, ‖v P‖ ≤ 1) →
      ∀ w z : ℂ, (19/20:ℝ) ≤ w.re → (33/200:ℝ) ≤ z.re →
      AnalyticOnNhd ℂ (fun x => idealCorrection K A eta v S x w z)
        {x : ℂ | 3/4 < x.re} ∧
      ∀ x : ℂ, 3/4 < x.re → ‖idealCorrection K A eta v S x w z-1‖ ≤ 1/2 := by
  obtain ⟨N,hN,hcut⟩ := exists_uniform_ideal_cutoff K
  refine ⟨S₀ ∪ idealSmallPrimeSet K N,Finset.subset_union_left,?_,?_⟩
  · intro P hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact Or.inr hP
    · exact Or.inl (Finset.mem_filter.mp hP).2
  · apply hcut
    intro P hP
    exact Finset.mem_union_right _ ((mem_idealSmallPrimeSet K N P).mpr hP)

end
end OAI.QRHParameterAudit.EulerExtension
