import OAI.NumberTheory.DirichletL.PrimeRows.TailScales
import QRHParameterAudit.Parameters
import OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily
open QRHParameterAudit

def auditedTinySaving : ℝ := 122913/1562500

def auditedSmallRawSaving : ℝ := auditedTinySaving+1/50

def auditedLargeBase : ℝ := 1+QRHParameterAudit.lx/2+QRHParameterAudit.ly

lemma audited_small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(ell:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(lx:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(ly:ℝ))^((1/2:ℝ)-1))=Z^(β-11/16-auditedSmallRawSaving+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  norm_num [lx,ly,ell,geomH,auditedTinySaving,auditedSmallRawSaving,auditedLargeBase]
  ring

lemma audited_small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤Z) (hU : 1≤U)
    (hUsmall : U≤Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=(ell:ℝ)) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(lx:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(ly:ℝ))^((1/2:ℝ)-1))≤Z^(β-11/16-auditedTinySaving+8*e) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,audited_small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(β-11/16-auditedSmallRawSaving+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1;unfold auditedSmallRawSaving;ring

lemma audited_large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(ell:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(lx:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(ly:ℝ))^((2:ℝ)-1))=
      Z^((auditedLargeBase:ℝ)+(geomH:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  norm_num [lx,ly,ell,geomH,auditedTinySaving,auditedSmallRawSaving,auditedLargeBase]

end SevenEighths.ProbeHighRowFamily
end

end OAI
