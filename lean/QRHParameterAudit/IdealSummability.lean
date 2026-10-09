import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI.QRHParameterAudit
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators Classical

/-- Absolute convergence of the ideal norm weight, without a zero-free hypothesis.
The input is mathlib's unconditional ideal-counting asymptotic. -/
theorem ideal_norm_rpow_summable (K : Type*) [Field K] [NumberField K]
    (r : ℝ) (hr : 1 < r) :
    Summable (fun I : Ideal (NumberField.RingOfIntegers K) =>
      (Ideal.absNorm I : ℝ)^(-r)) := by
  let a : ℕ → ℝ := fun n => Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n}
  have hlim : Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, a k)/(n:ℝ)) atTop
      (𝓝 (NumberField.dedekindZeta_residue K)) := by
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
      tendsto_natCast_atTop_atTop).congr fun n => ?_
    dsimp only [Function.comp_apply, a]
    simp only [Nat.cast_le, ← Nat.cast_sum]
    congr 1
    norm_cast
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = 0} by
        simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq
        (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have hs : LSeriesSummable (fun n => (a n:ℂ)) (r:ℂ) :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim))
      (fun n => Nat.cast_nonneg _) zero_le_one (by simpa using hr)
  have hweight : Summable (fun n : ℕ => a n*(n:ℝ)^(-r)) := by
    convert hs.norm using 1
    funext n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      simp [Real.zero_rpow (by linarith : -r ≠ 0)]
    · simp only [hn, ite_false, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ a n from Nat.cast_nonneg _), Complex.ofReal_re]
      rw [div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
  apply (summable_partition (s := fun n : ℕ =>
    {I : Ideal (NumberField.RingOfIntegers K) | Ideal.absNorm I = n})
    (fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _) (fun I => ⟨Ideal.absNorm I,rfl,
      fun _ h => h.symm⟩)).mpr
  constructor
  · intro n
    let := (Ideal.finite_setOfPred_absNorm_eq (S := NumberField.RingOfIntegers K) n).fintype
    exact Summable.of_finite
  · convert hweight using 1
    funext n
    let := (Ideal.finite_setOfPred_absNorm_eq (S := NumberField.RingOfIntegers K) n).fintype
    calc
      _ = ∑' _ : {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n},
          (n:ℝ)^(-r) := tsum_congr (fun I => by rw [I.property])
      _ = _ := by simp [a]

end
end OAI.QRHParameterAudit
