module

public import Erdos993Lean.F4U.Light.Construction.ActivityCharts
public import Erdos993Lean.F4U.Light.Linking.Generated.DAG_H_A_01.Expressions
public import Mathlib.Tactic.FinCases

/-! Exact original semantic setup and retained AST divisor obligations for H_A.
The original activity/chart/source functions remain in every identity. -/

@[expose] public section

namespace F4Unified.LightConstruction.GroupDomain_H_A
noncomputable section
open F4U.Light.Linking.Generated.DAG_H_A_01

def input (lam : ℝ) : ℝ := q lam
def chart (lam t : ℝ) : ℝ := parentChart .H .A lam t

 theorem lam_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00008_expression (input lam) t=lam := by
  simpa only [n00008_expression,n00000_expression,n00007_expression,n00006_expression,input,div_one] using lambda_from_q lam (inRow_lambda_bounds hlam).1

 theorem q_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00010_expression (input lam) t=q lam := by
  simp only [n00010_expression,n00009_expression,n00006_expression,lam_eq hlam,div_one]
  <;> norm_num [input,chart,q]
  <;> ring
  <;> simp

 theorem intercept_first_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00025_expression (input lam) t=intercept .H .first lam := by
  simp only [n00025_expression,n00024_expression,n00021_expression,n00019_expression,n00006_expression,n00017_expression,n00015_expression,n00012_expression,n00002_expression,n00011_expression,n00016_expression,n00014_expression,n00003_expression,n00013_expression,n00020_expression,n00023_expression,n00022_expression,n00018_expression,lam_eq hlam,q_eq hlam,div_one]
  <;> norm_num [input,chart,intercept,interceptError,endpointInterceptLo,endpointInterceptHi,rowData,q]
  <;> ring
  <;> simp

 theorem intercept_second_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00031_expression (input lam) t=intercept .H .second lam := by
  simp only [n00031_expression,n00030_expression,n00027_expression,n00019_expression,n00006_expression,n00017_expression,n00015_expression,n00012_expression,n00002_expression,n00011_expression,n00016_expression,n00014_expression,n00003_expression,n00013_expression,n00026_expression,n00029_expression,n00028_expression,n00018_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,div_one]
  <;> norm_num [input,chart,intercept,interceptError,endpointInterceptLo,endpointInterceptHi,rowData,q]
  <;> ring
  <;> simp

 theorem hCross_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00036_expression (input lam) t=hCross .H lam := by
  simp only [n00036_expression,n00034_expression,n00035_expression,n00032_expression,n00033_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,div_one]
  <;> norm_num [input,chart,hCross,slope]
  <;> ring
  <;> simp

 theorem HCross_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00039_expression (input lam) t=HCross .H lam := by
  simp only [n00039_expression,n00037_expression,n00006_expression,n00038_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,div_one]
  <;> norm_num [input,chart,HCross,sigma]
  <;> ring
  <;> simp

 theorem H_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00043_expression (input lam) t=chart lam t := by
  simp only [n00043_expression,n00040_expression,n00004_expression,n00042_expression,n00041_expression,n00001_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,div_one]
  <;> norm_num [input,chart,parentChart]
  <;> ring
  <;> simp

 theorem p_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00047_expression (input lam) t=pH lam (chart lam t) := by
  simp only [n00047_expression,n00045_expression,n00044_expression,n00006_expression,n00046_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,div_one]
  <;> norm_num [input,chart,pH]
  <;> ring
  <;> simp

 theorem r0_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00051_expression (input lam) t=vacancyLo lam (chart lam t) := by
  simp only [n00051_expression,n00006_expression,n00050_expression,n00049_expression,n00048_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,div_one]
  <;> norm_num [input,chart,vacancyLo]
  <;> ring
  <;> simp

 theorem rs_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00054_expression (input lam) t=vacancySwitch lam (chart lam t) := by
  simp only [n00054_expression,n00053_expression,n00052_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,div_one]
  <;> norm_num [input,chart,vacancySwitch]
  <;> ring
  <;> simp

 theorem alpha_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00061_expression (input lam) t=alpha .H lam := by
  simp only [n00061_expression,n00059_expression,n00055_expression,n00058_expression,n00057_expression,n00056_expression,n00005_expression,n00060_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,div_one]
  <;> norm_num [input,chart,alpha,field,rowData]
  <;> ring
  <;> simp

 theorem beta_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00066_expression (input lam) t=beta .H lam := by
  simp only [n00066_expression,n00065_expression,n00062_expression,n00064_expression,n00063_expression,n00056_expression,n00005_expression,n00060_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,div_one]
  <;> norm_num [input,chart,beta,field,rowData]
  <;> ring
  <;> simp

 theorem gamma_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00071_expression (input lam) t=gamma .H lam := by
  simp only [n00071_expression,n00070_expression,n00067_expression,n00069_expression,n00068_expression,n00056_expression,n00005_expression,n00060_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,div_one]
  <;> norm_num [input,chart,gamma,field,rowData]
  <;> ring
  <;> simp

 theorem delta_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00076_expression (input lam) t=delta .H lam := by
  simp only [n00076_expression,n00075_expression,n00072_expression,n00074_expression,n00073_expression,n00056_expression,n00005_expression,n00060_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,div_one]
  <;> norm_num [input,chart,delta,field,rowData]
  <;> ring
  <;> simp

 theorem bar_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00077_expression (input lam) t=(rowData .H).price/(1+lam) := by
  simp only [n00077_expression,n00004_expression,n00009_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,div_one]
  <;> norm_num [input,chart,rowData]
  <;> ring
  <;> simp

 theorem e_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00048_expression (input lam) t=1-pH lam (chart lam t) := by
  simp only [n00048_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,div_one]
  <;> norm_num [input,chart]
  <;> ring
  <;> simp

 theorem P0_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00146_expression (input lam) t=gamma .H lam*parentHBound (pH lam (chart lam t)) := by
  simp only [n00146_expression,n00145_expression,n00142_expression,n00006_expression,n00141_expression,n00004_expression,n00144_expression,n00143_expression,n00133_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,div_one]
  <;> norm_num [input,chart,parentHBound]
  <;> ring
  <;> simp

 theorem sourceAtLo_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00081_expression (input lam) t=sourceAtLo lam (chart lam t) := by
  simp only [n00081_expression,n00080_expression,n00079_expression,n00052_expression,n00006_expression,n00078_expression,n00004_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,div_one]
  <;> norm_num [input,chart,sourceAtLo,sourceSlopeA]
  <;> ring
  <;> simp

 theorem sourceAtSwitchLower_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00093_expression (input lam) t=sourceAtSwitchLower lam (chart lam t) := by
  simp only [n00093_expression,n00087_expression,n00084_expression,n00083_expression,n00082_expression,n00086_expression,n00085_expression,n00092_expression,n00089_expression,n00088_expression,n00091_expression,n00078_expression,n00004_expression,n00090_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,div_one]
  <;> norm_num [input,chart,sourceAtSwitchLower]
  <;> ring
  <;> simp

 theorem sourceAtHi_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00099_expression (input lam) t=sourceAtHi lam (chart lam t) := by
  simp only [n00099_expression,n00096_expression,n00095_expression,n00052_expression,n00006_expression,n00094_expression,n00078_expression,n00004_expression,n00098_expression,n00097_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,div_one]
  <;> norm_num [input,chart,sourceAtHi,sourceSlopeB,sourceSlopeA,sourceIntercept]
  <;> ring
  <;> simp

 theorem chord_first_slope_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00102_expression (input lam) t=chordSlope .first lam (chart lam t) := by
  simp only [n00102_expression,n00100_expression,n00101_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,div_one]
  <;> norm_num [input,chart,chordSlope]
  <;> ring
  <;> simp

 theorem chord_first_intercept_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00124_expression (input lam) t=chordIntercept .first lam (chart lam t) := by
  simp only [n00124_expression,n00123_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,div_one]
  <;> norm_num [input,chart,chordIntercept]
  <;> ring
  <;> simp

 theorem chord_second_slope_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00122_expression (input lam) t=chordSlope .second lam (chart lam t) := by
  simp only [n00122_expression,n00117_expression,n00103_expression,n00044_expression,n00006_expression,n00052_expression,n00116_expression,n00115_expression,n00114_expression,n00113_expression,n00110_expression,n00106_expression,n00105_expression,n00004_expression,n00104_expression,n00109_expression,n00107_expression,n00082_expression,n00108_expression,n00112_expression,n00111_expression,n00121_expression,n00118_expression,n00086_expression,n00085_expression,n00090_expression,n00120_expression,n00119_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,div_one]
  <;> norm_num [input,chart,chordSlope]
  <;> ring
  <;> simp

 theorem chord_second_intercept_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00125_expression (input lam) t=chordIntercept .second lam (chart lam t) := by
  simp only [n00125_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,div_one]
  <;> norm_num [input,chart,chordIntercept]
  <;> ring
  <;> simp

 theorem zMinus_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00132_expression (input lam) t=zMinus (chart lam t) := by
  simp only [n00132_expression,n00127_expression,n00107_expression,n00082_expression,n00126_expression,n00004_expression,n00131_expression,n00130_expression,n00104_expression,n00129_expression,n00128_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,div_one]
  <;> norm_num [input,chart,zMinus]
  <;> ring
  <;> simp

 theorem zPlus_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00140_expression (input lam) t=zPlus (chart lam t) := by
  simp only [n00140_expression,n00137_expression,n00136_expression,n00135_expression,n00104_expression,n00134_expression,n00133_expression,n00139_expression,n00138_expression,n00128_expression,n00044_expression,n00006_expression,n00126_expression,n00004_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,div_one]
  <;> norm_num [input,chart,zPlus]
  <;> ring
  <;> simp

 theorem point0_h_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00148_expression (input lam) t=hMinus .H (chart lam t) := by
  simp only [n00148_expression,n00006_expression,n00147_expression,n00038_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,div_one]
  <;> norm_num [input,chart,hMinus,sigma]
  <;> ring
  <;> simp

 theorem point0_L_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00150_expression (input lam) t=supportLine .H .second lam (hMinus .H (chart lam t)) := by
  simp only [n00150_expression,n00149_expression,n00033_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,div_one]
  <;> norm_num [input,chart,supportLine,slope]
  <;> ring
  <;> simp

 theorem point1_h_eq {lam t : ℝ} (hlam : InRow .H lam) :
    n00036_expression (input lam) t=hCross .H lam := by
  simp only [lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> norm_num [input,chart]
  <;> ring
  <;> simp

 theorem n00007_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00007_expression (input lam) t=(1-q lam:ℝ) := by
  simp only [n00007_expression,n00006_expression,n00000_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00009_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00009_expression (input lam) t=(1+lam:ℝ) := by
  simp only [n00009_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
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

 theorem n00035_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00035_expression (input lam) t=(21/10:ℝ) := by
  norm_num [n00035_expression,n00032_expression,n00033_expression]

 theorem n00038_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00038_expression (input lam) t=(3/5:ℝ) := by
  norm_num [n00038_expression]

 theorem n00004_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00004_expression (input lam) t=(2:ℝ) := by
  norm_num [n00004_expression]

 theorem n00046_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00046_expression (input lam) t=(1+lam*(1-chart lam t):ℝ) := by
  simp only [n00046_expression,n00006_expression,n00045_expression,n00044_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00050_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00050_expression (input lam) t=(1+lam*(1-pH lam (chart lam t)):ℝ) := by
  simp only [n00050_expression,n00006_expression,n00049_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00053_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00053_expression (input lam) t=((1+q lam)*pH lam (chart lam t):ℝ) := by
  simp only [n00053_expression,n00052_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00060_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00060_expression (input lam) t=(65536:ℝ) := by
  norm_num [n00060_expression]

 theorem n00078_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00078_expression (input lam) t=(2*q lam:ℝ) := by
  simp only [n00078_expression,n00004_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00086_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00086_expression (input lam) t=(4*q lam:ℝ) := by
  simp only [n00086_expression,n00085_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00091_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00091_expression (input lam) t=(2*q lam*(2-q lam):ℝ) := by
  simp only [n00091_expression,n00078_expression,n00004_expression,n00090_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00094_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00094_expression (input lam) t=(2*q lam*q lam:ℝ) := by
  simp only [n00094_expression,n00078_expression,n00004_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00101_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00101_expression (input lam) t=(vacancySwitch lam (chart lam t)-vacancyLo lam (chart lam t):ℝ) := by
  simp only [n00101_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00121_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00121_expression (input lam) t=(4*q lam*(2-q lam)*(1-q lam*chart lam t):ℝ) := by
  simp only [n00121_expression,n00118_expression,n00086_expression,n00085_expression,n00090_expression,n00004_expression,n00120_expression,n00006_expression,n00119_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00131_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00131_expression (input lam) t=((chart lam t)^2-6*chart lam t+6:ℝ) := by
  simp only [n00131_expression,n00130_expression,n00104_expression,n00129_expression,n00128_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00139_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00139_expression (input lam) t=(6*(1-chart lam t)*(2-chart lam t):ℝ) := by
  simp only [n00139_expression,n00138_expression,n00128_expression,n00044_expression,n00006_expression,n00126_expression,n00004_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00133_factor {lam t : ℝ} (hlam : InRow .H lam) :
    n00133_expression (input lam) t=(12:ℝ) := by
  norm_num [n00133_expression]

 theorem original_DivisorsNonzero {lam t : ℝ} (hlam : InRow .H lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : DivisorsNonzero (input lam) t := by
  have fac : OriginalLightFactors .H lam (chart lam t) := by
    unfold chart
    exact parentChart_factors (reg:=.A) hlam ht0 ht1
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
  have h_n00035 : n00035_expression (input lam) t ≠ 0 := by
    rw [n00035_factor hlam]
    norm_num
  have h_n00038 : n00038_expression (input lam) t ≠ 0 := by
    rw [n00038_factor hlam]
    norm_num
  have h_n00004 : n00004_expression (input lam) t ≠ 0 := by
    rw [n00004_factor hlam]
    norm_num
  have h_n00046 : n00046_expression (input lam) t ≠ 0 := by
    rw [n00046_factor hlam]
    exact (hparentden).ne'
  have h_n00050 : n00050_expression (input lam) t ≠ 0 := by
    rw [n00050_factor hlam]
    exact (hvacancyden).ne'
  have h_n00053 : n00053_expression (input lam) t ≠ 0 := by
    rw [n00053_factor hlam]
    exact (hswitchden).ne'
  have h_n00060 : n00060_expression (input lam) t ≠ 0 := by
    rw [n00060_factor hlam]
    norm_num
  have h_n00078 : n00078_expression (input lam) t ≠ 0 := by
    rw [n00078_factor hlam]
    exact (htwoq).ne'
  have h_n00086 : n00086_expression (input lam) t ≠ 0 := by
    rw [n00086_factor hlam]
    exact (hfourq).ne'
  have h_n00091 : n00091_expression (input lam) t ≠ 0 := by
    rw [n00091_factor hlam]
    exact (htwoqtwominus).ne'
  have h_n00094 : n00094_expression (input lam) t ≠ 0 := by
    rw [n00094_factor hlam]
    exact (htwoqsq).ne'
  have h_n00101 : n00101_expression (input lam) t ≠ 0 := by
    rw [n00101_factor hlam]
    exact (fac.source_phase_width_pos).ne'
  have h_n00121 : n00121_expression (input lam) t ≠ 0 := by
    rw [n00121_factor hlam]
    exact (hchordden).ne'
  have h_n00131 : n00131_expression (input lam) t ≠ 0 := by
    rw [n00131_factor hlam]
    exact (fac.log_minus_denominator_pos).ne'
  have h_n00139 : n00139_expression (input lam) t ≠ 0 := by
    rw [n00139_factor hlam]
    exact (hlogplusden).ne'
  have h_n00133 : n00133_expression (input lam) t ≠ 0 := by
    rw [n00133_factor hlam]
    norm_num
  intro i
  fin_cases i <;> simp only [divisorExpression] <;> assumption

#print axioms input
#print axioms chart
#print axioms lam_eq
#print axioms q_eq
#print axioms intercept_first_eq
#print axioms intercept_second_eq
#print axioms hCross_eq
#print axioms HCross_eq
#print axioms H_eq
#print axioms p_eq
#print axioms r0_eq
#print axioms rs_eq
#print axioms alpha_eq
#print axioms beta_eq
#print axioms gamma_eq
#print axioms delta_eq
#print axioms bar_eq
#print axioms e_eq
#print axioms P0_eq
#print axioms sourceAtLo_eq
#print axioms sourceAtSwitchLower_eq
#print axioms sourceAtHi_eq
#print axioms chord_first_slope_eq
#print axioms chord_first_intercept_eq
#print axioms chord_second_slope_eq
#print axioms chord_second_intercept_eq
#print axioms zMinus_eq
#print axioms zPlus_eq
#print axioms point0_h_eq
#print axioms point0_L_eq
#print axioms point1_h_eq
#print axioms n00007_factor
#print axioms n00009_factor
#print axioms n00011_factor
#print axioms n00013_factor
#print axioms n00016_factor
#print axioms n00035_factor
#print axioms n00038_factor
#print axioms n00004_factor
#print axioms n00046_factor
#print axioms n00050_factor
#print axioms n00053_factor
#print axioms n00060_factor
#print axioms n00078_factor
#print axioms n00086_factor
#print axioms n00091_factor
#print axioms n00094_factor
#print axioms n00101_factor
#print axioms n00121_factor
#print axioms n00131_factor
#print axioms n00139_factor
#print axioms n00133_factor
#print axioms original_DivisorsNonzero

end
end F4Unified.LightConstruction.GroupDomain_H_A
