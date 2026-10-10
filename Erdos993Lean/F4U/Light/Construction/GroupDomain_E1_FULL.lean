module

public import Erdos993Lean.F4U.Light.Construction.ActivityCharts
public import Erdos993Lean.F4U.Light.Linking.Generated.DAG_E1_FULL_01.Program
public import Mathlib.Tactic.FinCases

/-! Exact original semantic setup and retained AST divisor obligations for E1_FULL.
The original activity/chart/source functions remain in every identity. -/

@[expose] public section

namespace F4Unified.LightConstruction.GroupDomain_E1_FULL
noncomputable section
open F4U.Light.Linking.Generated.DAG_E1_FULL_01

def input (lam : ℝ) : ℝ := lam
def chart (lam t : ℝ) : ℝ := guardParentChart lam t

 theorem lam_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00000_expression (input lam) t=lam := by
  rfl

 theorem q_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00007_expression (input lam) t=q lam := by
  simp only [n00007_expression,n00006_expression,n00005_expression,lam_eq hlam,div_one]
  <;> norm_num [input,chart,q]
  <;> ring
  <;> simp

 theorem intercept_second_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00030_expression (input lam) t=intercept .E1 .second lam := by
  simp only [n00030_expression,n00029_expression,n00026_expression,n00022_expression,n00021_expression,n00003_expression,n00014_expression,n00002_expression,n00025_expression,n00028_expression,n00024_expression,n00023_expression,n00027_expression,n00020_expression,n00016_expression,n00013_expression,n00009_expression,n00008_expression,n00005_expression,n00012_expression,n00011_expression,n00010_expression,n00015_expression,n00019_expression,n00018_expression,n00017_expression,lam_eq hlam,q_eq hlam,div_one]
  <;> norm_num [input,chart,intercept,interceptError,endpointInterceptLo,endpointInterceptHi,rowData,q]
  <;> ring
  <;> simp

 theorem H_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00034_expression (input lam) t=chart lam t := by
  simp only [n00034_expression,n00031_expression,n00010_expression,n00033_expression,n00032_expression,n00001_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,div_one]
  <;> norm_num [input,chart,guardParentChart]
  <;> ring
  <;> simp

 theorem p_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00038_expression (input lam) t=pH lam (chart lam t) := by
  simp only [n00038_expression,n00036_expression,n00035_expression,n00005_expression,n00037_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,div_one]
  <;> norm_num [input,chart,pH]
  <;> ring
  <;> simp

 theorem r0_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00042_expression (input lam) t=vacancyLo lam (chart lam t) := by
  simp only [n00042_expression,n00005_expression,n00041_expression,n00040_expression,n00039_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,div_one]
  <;> norm_num [input,chart,vacancyLo]
  <;> ring
  <;> simp

 theorem alpha_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00049_expression (input lam) t=alpha .E1 lam := by
  simp only [n00049_expression,n00047_expression,n00043_expression,n00046_expression,n00045_expression,n00044_expression,n00004_expression,n00048_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,div_one]
  <;> norm_num [input,chart,alpha,field,rowData]
  <;> ring
  <;> simp

 theorem beta_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00054_expression (input lam) t=beta .E1 lam := by
  simp only [n00054_expression,n00053_expression,n00050_expression,n00052_expression,n00051_expression,n00044_expression,n00004_expression,n00048_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,div_one]
  <;> norm_num [input,chart,beta,field,rowData]
  <;> ring
  <;> simp

 theorem gamma_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00059_expression (input lam) t=gamma .E1 lam := by
  simp only [n00059_expression,n00058_expression,n00055_expression,n00057_expression,n00056_expression,n00044_expression,n00004_expression,n00048_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,div_one]
  <;> norm_num [input,chart,gamma,field,rowData]
  <;> ring
  <;> simp

 theorem delta_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00064_expression (input lam) t=delta .E1 lam := by
  simp only [n00064_expression,n00063_expression,n00060_expression,n00062_expression,n00061_expression,n00044_expression,n00004_expression,n00048_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,div_one]
  <;> norm_num [input,chart,delta,field,rowData]
  <;> ring
  <;> simp

 theorem e_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00039_expression (input lam) t=1-pH lam (chart lam t) := by
  simp only [n00039_expression,n00005_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,div_one]
  <;> norm_num [input,chart]
  <;> ring
  <;> simp

 theorem P0_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00081_expression (input lam) t=gamma .E1 lam*parentHBound (pH lam (chart lam t)) := by
  simp only [n00081_expression,n00080_expression,n00077_expression,n00005_expression,n00076_expression,n00010_expression,n00079_expression,n00078_expression,n00068_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,div_one]
  <;> norm_num [input,chart,parentHBound]
  <;> ring
  <;> simp

 theorem zPlus_eq {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00075_expression (input lam) t=zPlus (chart lam t) := by
  simp only [n00075_expression,n00072_expression,n00071_expression,n00070_expression,n00065_expression,n00069_expression,n00068_expression,n00074_expression,n00073_expression,n00067_expression,n00035_expression,n00005_expression,n00066_expression,n00010_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,div_one]
  <;> norm_num [input,chart,zPlus]
  <;> ring
  <;> simp

 theorem n00006_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00006_expression (input lam) t=(1+lam:ℝ) := by
  simp only [n00006_expression,n00005_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00008_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00008_expression (input lam) t=(49/20:ℝ) := by
  norm_num [n00008_expression,n00005_expression,n00003_expression]

 theorem n00010_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00010_expression (input lam) t=(2:ℝ) := by
  norm_num [n00010_expression]

 theorem n00019_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00019_expression (input lam) t=(338/25:ℝ) := by
  norm_num [n00019_expression,n00018_expression,n00017_expression,n00002_expression]

 theorem n00014_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00014_expression (input lam) t=(3/20:ℝ) := by
  norm_num [n00014_expression,n00003_expression,n00002_expression]

 theorem n00037_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00037_expression (input lam) t=(1+lam*(1-chart lam t):ℝ) := by
  simp only [n00037_expression,n00005_expression,n00036_expression,n00035_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00041_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00041_expression (input lam) t=(1+lam*(1-pH lam (chart lam t)):ℝ) := by
  simp only [n00041_expression,n00005_expression,n00040_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00048_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00048_expression (input lam) t=(65536:ℝ) := by
  norm_num [n00048_expression]

 theorem n00074_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00074_expression (input lam) t=(6*(1-chart lam t)*(2-chart lam t):ℝ) := by
  simp only [n00074_expression,n00073_expression,n00067_expression,n00035_expression,n00005_expression,n00066_expression,n00010_expression,lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00068_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00068_expression (input lam) t=(12:ℝ) := by
  norm_num [n00068_expression]

 theorem n00038_factor {lam t : ℝ} (hlam : InRow .E1 lam) :
    n00038_expression (input lam) t=(pH lam (chart lam t):ℝ) := by
  simp only [lam_eq hlam,q_eq hlam,intercept_second_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,e_eq hlam,P0_eq hlam,zPlus_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem original_DivisorsNonzero {lam t : ℝ} (hlam : InRow .E1 lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : DivisorsNonzero (input lam) t := by
  have fac : OriginalLightFactors .E1 lam (chart lam t) := by
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
  have h_n00006 : n00006_expression (input lam) t ≠ 0 := by
    rw [n00006_factor hlam]
    exact (fac.lambda_add_one_pos).ne'
  have h_n00008 : n00008_expression (input lam) t ≠ 0 := by
    rw [n00008_factor hlam]
    norm_num
  have h_n00010 : n00010_expression (input lam) t ≠ 0 := by
    rw [n00010_factor hlam]
    norm_num
  have h_n00019 : n00019_expression (input lam) t ≠ 0 := by
    rw [n00019_factor hlam]
    norm_num
  have h_n00014 : n00014_expression (input lam) t ≠ 0 := by
    rw [n00014_factor hlam]
    norm_num
  have h_n00037 : n00037_expression (input lam) t ≠ 0 := by
    rw [n00037_factor hlam]
    exact (hparentden).ne'
  have h_n00041 : n00041_expression (input lam) t ≠ 0 := by
    rw [n00041_factor hlam]
    exact (hvacancyden).ne'
  have h_n00048 : n00048_expression (input lam) t ≠ 0 := by
    rw [n00048_factor hlam]
    norm_num
  have h_n00074 : n00074_expression (input lam) t ≠ 0 := by
    rw [n00074_factor hlam]
    exact (hlogplusden).ne'
  have h_n00068 : n00068_expression (input lam) t ≠ 0 := by
    rw [n00068_factor hlam]
    norm_num
  have h_n00038 : n00038_expression (input lam) t ≠ 0 := by
    rw [n00038_factor hlam]
    exact (fac.p_pos).ne'
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
#print axioms n00006_factor
#print axioms n00008_factor
#print axioms n00010_factor
#print axioms n00019_factor
#print axioms n00014_factor
#print axioms n00037_factor
#print axioms n00041_factor
#print axioms n00048_factor
#print axioms n00074_factor
#print axioms n00068_factor
#print axioms n00038_factor
#print axioms original_DivisorsNonzero

end
end F4Unified.LightConstruction.GroupDomain_E1_FULL
