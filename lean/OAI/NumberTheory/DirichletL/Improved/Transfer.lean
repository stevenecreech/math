import OAI.NumberTheory.DirichletL.Hecke.Dirichlet

namespace OAI

noncomputable section
namespace SevenEighths.ImprovedTransfer
open HeckeFamily HeckeDirichlet

/-- The existing actual base-change product transfers any positive Hecke
zero-free boundary, including a boundary below seven eighths. -/
theorem dirichlet_nonzero_of_hecke (boundary : ℝ) (hboundary : 0 ≤ boundary)
    (hH : ∀ (η : Character) (s : ℂ), boundary < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : boundary < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) : χ.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hexc) hge
  have hs1 : s ≠ 1 := by intro h; simp [h] at hge
  have hs0 : s ≠ 0 := by
    intro h
    have hpos := hboundary.trans_lt hs
    simp [h] at hpos
  have h := hH (character χ) s hs (Or.inl hs1)
  rw [LFunction_eq_dirichlet_product χ hs0 hs1] at h
  exact (mul_ne_zero_iff.mp h).1

/-- The transfer is to mathlib's actual `riemannZeta` function. The improved
Hecke estimate is an explicit premise, not supplied by this theorem. -/
theorem zeta_nonzero_of_hecke (boundary : ℝ) (hboundary : 0 ≤ boundary)
    (hH : ∀ (η : Character) (s : ℂ), boundary < s.re →
      (s ≠ 1 ∨ η.residue ≠ 1) → LFunction η s ≠ 0)
    (s : ℂ) (hs : boundary < s.re) : riemannZeta s ≠ 0 := by
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  have h := dirichlet_nonzero_of_hecke boundary hboundary hH
    (1 : DirichletCharacter ℂ 1) s hs (by simp [h1])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end SevenEighths.ImprovedTransfer
end
end OAI
