import OAI.NumberTheory.DirichletL.Detector.EulerCoordinatesScalar
import OAI.NumberTheory.DirichletL.Detector.Row

namespace OAI
noncomputable section
namespace SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

def actualAPhase (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p) ^ 6 * HeckeFamily.elementCoeff eta p ^ 6

def actualUnramifiedClosed (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedClosed (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

lemma actualAPhase_norm_le_one (eta : HeckeFamily.Character) (p : O) :
    ‖actualAPhase eta p‖ ≤ 1 := by
  simp only [actualAPhase, norm_mul, norm_pow, norm_star]
  exact (mul_le_of_le_one_left (by positivity)
    (pow_le_one₀ (norm_nonneg _) (CompletedGauss.angularFactor_norm_le_one p))).trans
    (pow_le_one₀ (norm_nonneg _) (ProbeRow.targetMonoid_norm_le_one eta p))

end SevenEighths.ProbeEuler
end
end OAI
