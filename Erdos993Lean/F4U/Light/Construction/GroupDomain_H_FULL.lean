module

public import Erdos993Lean.F4U.Light.Construction.ActivityCharts
public import Erdos993Lean.F4U.Light.Linking.Generated.DAG_H_FULL_01.Program
public import Mathlib.Tactic.FinCases

/-! Exact original semantic setup and retained AST divisor obligations for H_FULL.
The original activity/chart/source functions remain in every identity. -/

@[expose] public section

namespace F4Unified.LightConstruction.GroupDomain_H_FULL
noncomputable section
open F4U.Light.Linking.Generated.DAG_H_FULL_01

def input (lam : ℝ) : ℝ := q lam
def chart (lam t : ℝ) : ℝ := guardParentChart lam t

 theorem lam_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00008_expression (input lam) t=lam := by
  simpa only [n00008_expression,n00000_expression,n00007_expression,n00006_expression,input,div_one] using lambda_from_q lam (inRow_lambda_bounds hlam).1

 theorem q_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00010_expression (input lam) t=q lam := by
  simp only [n00010_expression,n00009_expression,n00006_expression,lam_eq hlam,div_one]
  <;> norm_num [input,chart,q]
  <;> ring
  <;> simp

 theorem intercept_second_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00025_expression (input lam) t=intercept .H .second lam := by
  simp only [n00025_expression,n00024_expression,n00021_expression,n00019_expression,n00006_expression,n00017_expression,n00015_expression,n00012_expression,n00002_expression,n00011_expression,n00016_expression,n00014_expression,n00003_expression,n00013_expression,n00020_expression,n00023_expression,n00022_expression,n00018_expression,lam_eq hlam,q_eq hlam,div_one]
  <;> norm_num [input,chart,intercept,interceptError,endpointInterceptLo,endpointInterceptHi,rowData,q]
  <;> ring
  <;> simp

 theorem H_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00029_expression (input lam) t=chart lam t := by
  simp only [n00029_expression,n00026_expression,n00004_expression,n00028_expression,n00027_expression,n00001_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,div_one]
  <;> norm_num [input,chart,guardParentChart]
  <;> ring
  <;> simp

 theorem p_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00033_expression (input lam) t=pH lam (chart lam t) := by
  simp only [n00033_expression,n00031_expression,n00030_expression,n00006_expression,n00032_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,div_one]
  <;> norm_num [input,chart,pH]
  <;> ring
  <;> simp

 theorem r0_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00037_expression (input lam) t=vacancyLo lam (chart lam t) := by
  simp only [n00037_expression,n00006_expression,n00036_expression,n00035_expression,n00034_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,div_one]
  <;> norm_num [input,chart,vacancyLo]
  <;> ring
  <;> simp

 theorem alpha_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00044_expression (input lam) t=alpha .H lam := by
  simp only [n00044_expression,n00042_expression,n00038_expression,n00041_expression,n00040_expression,n00039_expression,n00005_expression,n00043_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,div_one]
  <;> norm_num [input,chart,alpha,field,rowData]
  <;> ring
  <;> simp

 theorem beta_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00049_expression (input lam) t=beta .H lam := by
  simp only [n00049_expression,n00048_expression,n00045_expression,n00047_expression,n00046_expression,n00039_expression,n00005_expression,n00043_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,div_one]
  <;> norm_num [input,chart,beta,field,rowData]
  <;> ring
  <;> simp

 theorem gamma_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00054_expression (input lam) t=gamma .H lam := by
  simp only [n00054_expression,n00053_expression,n00050_expression,n00052_expression,n00051_expression,n00039_expression,n00005_expression,n00043_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,div_one]
  <;> norm_num [input,chart,gamma,field,rowData]
  <;> ring
  <;> simp

 theorem delta_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00059_expression (input lam) t=delta .H lam := by
  simp only [n00059_expression,n00058_expression,n00055_expression,n00057_expression,n00056_expression,n00039_expression,n00005_expression,n00043_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,div_one]
  <;> norm_num [input,chart,delta,field,rowData]
  <;> ring
  <;> simp

 theorem e_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00034_expression (input lam) t=1-pH lam (chart lam t) := by
  simp only [n00034_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,div_one]
  <;> norm_num [input,chart]
  <;> ring
  <;> simp

 theorem P0_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00076_expression (input lam) t=gamma .H lam*parentHBound (pH lam (chart lam t)) := by
  simp only [n00076_expression,n00075_expression,n00072_expression,n00006_expression,n00071_expression,n00004_expression,n00074_expression,n00073_expression,n00063_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,div_one]
  <;> norm_num [input,chart,parentHBound]
  <;> ring
  <;> simp

 theorem zPlus_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00070_expression (input lam) t=zPlus (chart lam t) := by
  simp only [n00070_expression,n00067_expression,n00066_expression,n00065_expression,n00060_expression,n00064_expression,n00063_expression,n00069_expression,n00068_expression,n00062_expression,n00030_expression,n00006_expression,n00061_expression,n00004_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,div_one]
  <;> norm_num [input,chart,zPlus]
  <;> ring
  <;> simp

 theorem n00007_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00007_expression (input lam) t=(1-q lam:ℝ) := by
  simp only [n00007_expression,n00006_expression,n00000_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00009_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00009_expression (input lam) t=(1+lam:ℝ) := by
  simp only [n00009_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00011_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00011_expression (input lam) t=(11/4:ℝ) := by
  norm_num [n00011_expression,n00006_expression,n00002_expression]

 theorem n00013_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00013_expression (input lam) t=(10/3:ℝ) := by
  norm_num [n00013_expression,n00006_expression,n00003_expression]

 theorem n00016_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00016_expression (input lam) t=(7/110:ℝ) := by
  norm_num [n00016_expression,n00014_expression,n00003_expression,n00013_expression,n00006_expression,n00012_expression,n00002_expression,n00011_expression]

 theorem n00004_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00004_expression (input lam) t=(2:ℝ) := by
  norm_num [n00004_expression]

 theorem n00032_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00032_expression (input lam) t=(1+lam*(1-chart lam t):ℝ) := by
  simp only [n00032_expression,n00006_expression,n00031_expression,n00030_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00036_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00036_expression (input lam) t=(1+lam*(1-pH lam (chart lam t)):ℝ) := by
  simp only [n00036_expression,n00006_expression,n00035_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00043_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00043_expression (input lam) t=(65536:ℝ) := by
  norm_num [n00043_expression]

 theorem n00069_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00069_expression (input lam) t=(6*(1-chart lam t)*(2-chart lam t):ℝ) := by
  simp only [n00069_expression,n00068_expression,n00062_expression,n00030_expression,n00006_expression,n00061_expression,n00004_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00063_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00063_expression (input lam) t=(12:ℝ) := by
  norm_num [n00063_expression]

 theorem original_DivisorsNonzero {lam t : ℝ} (hlam : InRow .H lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : DivisorsNonzero (input lam) t := by
  have fac : OriginalLightFactors .H lam (chart lam t) := by
    unfold chart
    exact guardChart_factors hlam ht0 ht1
  have hparentden : 0 < 1+lam*(1-chart lam t) := by
    have hl := fac.lambda_pos
    have hH := fac.one_sub_H_pos
    positivity
  have hvacancyden : 0 < 1+lam*(1-pH lam (chart lam t)) := by
    have hl := fac.lambda_pos
    have hp := fac.one_sub_p_pos
    positivity
  have hswitchden : 0 < (1+q lam)*pH lam (chart lam t) :=
    mul_pos fac.one_add_q_pos fac.p_pos
  have htwoq : 0 < 2*q lam := by have hq:=fac.q_pos; positivity
  have hfourq : 0 < 4*q lam := by have hq:=fac.q_pos; positivity
  have htwoqtwominus : 0 < 2*q lam*(2-q lam) := by
    have hq:=fac.q_pos
    have h2q:=fac.two_sub_q_pos
    positivity
  have htwoqsq : 0 < 2*q lam*q lam := by have hq:=fac.q_pos; positivity
  have hchordden : 0 < 4*q lam*(2-q lam)*(1-q lam*chart lam t) := by
    have hq:=fac.q_pos
    have h2q:=fac.two_sub_q_pos
    have hqH:=fac.one_sub_qH_pos
    positivity
  have hlogplusden : 0 < 6*(1-chart lam t)*(2-chart lam t) := by
    have hH1:=fac.one_sub_H_pos
    have hH2:=fac.two_sub_H_pos
    positivity
  have h_n00007 : n00007_expression (input lam) t ≠ 0 := by
    rw [n00007_factor hlam]
    exact (fac.one_sub_q_pos).ne'
  have h_n00009 : n00009_expression (input lam) t ≠ 0 := by
    rw [n00009_factor hlam]
    exact (fac.lambda_add_one_pos).ne'
  have h_n00011 : n00011_expression (input lam) t ≠ 0 := by
    rw [n00011_factor hlam]
    norm_num
  have h_n00013 : n00013_expression (input lam) t ≠ 0 := by
    rw [n00013_factor hlam]
    norm_num
  have h_n00016 : n00016_expression (input lam) t ≠ 0 := by
    rw [n00016_factor hlam]
    norm_num
  have h_n00004 : n00004_expression (input lam) t ≠ 0 := by
    rw [n00004_factor hlam]
    norm_num
  have h_n00032 : n00032_expression (input lam) t ≠ 0 := by
    rw [n00032_factor hlam]
    exact (hparentden).ne'
  have h_n00036 : n00036_expression (input lam) t ≠ 0 := by
    rw [n00036_factor hlam]
    exact (hvacancyden).ne'
  have h_n00043 : n00043_expression (input lam) t ≠ 0 := by
    rw [n00043_factor hlam]
    norm_num
  have h_n00069 : n00069_expression (input lam) t ≠ 0 := by
    rw [n00069_factor hlam]
    exact (hlogplusden).ne'
  have h_n00063 : n00063_expression (input lam) t ≠ 0 := by
    rw [n00063_factor hlam]
    norm_num
  intro i
  fin_cases i <;> simp only [divisorExpression] <;> assumption

#print axioms input
#print axioms chart
#print axioms lam_eq
#print axioms q_eq
#print axioms intercept_second_eq
#print axioms H_eq
#print axioms p_eq
#print axioms r0_eq
#print axioms alpha_eq
#print axioms beta_eq
#print axioms gamma_eq
#print axioms delta_eq
#print axioms e_eq
#print axioms P0_eq
#print axioms zPlus_eq
#print axioms n00007_factor
#print axioms n00009_factor
#print axioms n00011_factor
#print axioms n00013_factor
#print axioms n00016_factor
#print axioms n00004_factor
#print axioms n00032_factor
#print axioms n00036_factor
#print axioms n00043_factor
#print axioms n00069_factor
#print axioms n00063_factor
#print axioms original_DivisorsNonzero

end
end F4Unified.LightConstruction.GroupDomain_H_FULL
