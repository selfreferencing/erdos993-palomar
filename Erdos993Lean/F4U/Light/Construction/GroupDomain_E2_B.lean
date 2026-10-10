module

public import Erdos993Lean.F4U.Light.Construction.ActivityCharts
public import Erdos993Lean.F4U.Light.Linking.Generated.DAG_E2_B_01.Expressions
public import Mathlib.Tactic.FinCases

/-! Exact original semantic setup and retained AST divisor obligations for E2_B.
The original activity/chart/source functions remain in every identity. -/

@[expose] public section

namespace F4Unified.LightConstruction.GroupDomain_E2_B
noncomputable section
open F4U.Light.Linking.Generated.DAG_E2_B_01

def input (lam : ℝ) : ℝ := lam
def chart (lam t : ℝ) : ℝ := parentChart .E2 .B lam t

 theorem lam_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00000_expression (input lam) t=lam := by
  rfl

 theorem q_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00008_expression (input lam) t=q lam := by
  simp only [n00008_expression,n00007_expression,n00006_expression,lam_eq hlam,div_one]
  <;> norm_num [input,chart,q]
  <;> ring
  <;> simp

 theorem intercept_first_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00031_expression (input lam) t=intercept .E2 .first lam := by
  simp only [n00031_expression,n00030_expression,n00025_expression,n00023_expression,n00022_expression,n00003_expression,n00015_expression,n00002_expression,n00024_expression,n00029_expression,n00027_expression,n00026_expression,n00028_expression,n00021_expression,n00017_expression,n00014_expression,n00010_expression,n00009_expression,n00006_expression,n00013_expression,n00012_expression,n00011_expression,n00016_expression,n00020_expression,n00019_expression,n00018_expression,lam_eq hlam,q_eq hlam,div_one]
  <;> norm_num [input,chart,intercept,interceptError,endpointInterceptLo,endpointInterceptHi,rowData,q]
  <;> ring
  <;> simp

 theorem intercept_second_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00037_expression (input lam) t=intercept .E2 .second lam := by
  simp only [n00037_expression,n00036_expression,n00033_expression,n00023_expression,n00022_expression,n00003_expression,n00015_expression,n00002_expression,n00032_expression,n00035_expression,n00027_expression,n00026_expression,n00034_expression,n00021_expression,n00017_expression,n00014_expression,n00010_expression,n00009_expression,n00006_expression,n00013_expression,n00012_expression,n00011_expression,n00016_expression,n00020_expression,n00019_expression,n00018_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,div_one]
  <;> norm_num [input,chart,intercept,interceptError,endpointInterceptLo,endpointInterceptHi,rowData,q]
  <;> ring
  <;> simp

 theorem hCross_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00042_expression (input lam) t=hCross .E2 lam := by
  simp only [n00042_expression,n00040_expression,n00041_expression,n00038_expression,n00039_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,div_one]
  <;> norm_num [input,chart,hCross,slope]
  <;> ring
  <;> simp

 theorem HCross_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00045_expression (input lam) t=HCross .E2 lam := by
  simp only [n00045_expression,n00043_expression,n00006_expression,n00044_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,div_one]
  <;> norm_num [input,chart,HCross,sigma]
  <;> ring
  <;> simp

 theorem H_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00048_expression (input lam) t=chart lam t := by
  simp only [n00048_expression,n00047_expression,n00046_expression,n00001_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,div_one]
  <;> norm_num [input,chart,parentChart]
  <;> ring
  <;> simp

 theorem p_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00052_expression (input lam) t=pH lam (chart lam t) := by
  simp only [n00052_expression,n00050_expression,n00049_expression,n00006_expression,n00051_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,div_one]
  <;> norm_num [input,chart,pH]
  <;> ring
  <;> simp

 theorem r0_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00056_expression (input lam) t=vacancyLo lam (chart lam t) := by
  simp only [n00056_expression,n00006_expression,n00055_expression,n00054_expression,n00053_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,div_one]
  <;> norm_num [input,chart,vacancyLo]
  <;> ring
  <;> simp

 theorem rs_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00059_expression (input lam) t=vacancySwitch lam (chart lam t) := by
  simp only [n00059_expression,n00058_expression,n00057_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,div_one]
  <;> norm_num [input,chart,vacancySwitch]
  <;> ring
  <;> simp

 theorem alpha_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00066_expression (input lam) t=alpha .E2 lam := by
  simp only [n00066_expression,n00064_expression,n00060_expression,n00063_expression,n00062_expression,n00061_expression,n00005_expression,n00065_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,div_one]
  <;> norm_num [input,chart,alpha,field,rowData]
  <;> ring
  <;> simp

 theorem beta_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00071_expression (input lam) t=beta .E2 lam := by
  simp only [n00071_expression,n00070_expression,n00067_expression,n00069_expression,n00068_expression,n00061_expression,n00005_expression,n00065_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,div_one]
  <;> norm_num [input,chart,beta,field,rowData]
  <;> ring
  <;> simp

 theorem gamma_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00076_expression (input lam) t=gamma .E2 lam := by
  simp only [n00076_expression,n00075_expression,n00072_expression,n00074_expression,n00073_expression,n00061_expression,n00005_expression,n00065_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,div_one]
  <;> norm_num [input,chart,gamma,field,rowData]
  <;> ring
  <;> simp

 theorem delta_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00081_expression (input lam) t=delta .E2 lam := by
  simp only [n00081_expression,n00080_expression,n00077_expression,n00079_expression,n00078_expression,n00061_expression,n00005_expression,n00065_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,div_one]
  <;> norm_num [input,chart,delta,field,rowData]
  <;> ring
  <;> simp

 theorem bar_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00082_expression (input lam) t=(rowData .E2).price/(1+lam) := by
  simp only [n00082_expression,n00004_expression,n00007_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,div_one]
  <;> norm_num [input,chart,rowData]
  <;> ring
  <;> simp

 theorem e_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00053_expression (input lam) t=1-pH lam (chart lam t) := by
  simp only [n00053_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,div_one]
  <;> norm_num [input,chart]
  <;> ring
  <;> simp

 theorem P0_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00151_expression (input lam) t=gamma .E2 lam*parentHBound (pH lam (chart lam t)) := by
  simp only [n00151_expression,n00150_expression,n00147_expression,n00006_expression,n00146_expression,n00011_expression,n00149_expression,n00148_expression,n00138_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,div_one]
  <;> norm_num [input,chart,parentHBound]
  <;> ring
  <;> simp

 theorem sourceAtLo_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00086_expression (input lam) t=sourceAtLo lam (chart lam t) := by
  simp only [n00086_expression,n00085_expression,n00084_expression,n00057_expression,n00006_expression,n00083_expression,n00011_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,div_one]
  <;> norm_num [input,chart,sourceAtLo,sourceSlopeA]
  <;> ring
  <;> simp

 theorem sourceAtSwitchLower_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00098_expression (input lam) t=sourceAtSwitchLower lam (chart lam t) := by
  simp only [n00098_expression,n00092_expression,n00089_expression,n00088_expression,n00087_expression,n00091_expression,n00090_expression,n00097_expression,n00094_expression,n00093_expression,n00096_expression,n00083_expression,n00011_expression,n00095_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,div_one]
  <;> norm_num [input,chart,sourceAtSwitchLower]
  <;> ring
  <;> simp

 theorem sourceAtHi_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00104_expression (input lam) t=sourceAtHi lam (chart lam t) := by
  simp only [n00104_expression,n00101_expression,n00100_expression,n00057_expression,n00006_expression,n00099_expression,n00083_expression,n00011_expression,n00103_expression,n00102_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,div_one]
  <;> norm_num [input,chart,sourceAtHi,sourceSlopeB,sourceSlopeA,sourceIntercept]
  <;> ring
  <;> simp

 theorem chord_first_slope_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00107_expression (input lam) t=chordSlope .first lam (chart lam t) := by
  simp only [n00107_expression,n00105_expression,n00106_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,div_one]
  <;> norm_num [input,chart,chordSlope]
  <;> ring
  <;> simp

 theorem chord_first_intercept_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00129_expression (input lam) t=chordIntercept .first lam (chart lam t) := by
  simp only [n00129_expression,n00128_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,div_one]
  <;> norm_num [input,chart,chordIntercept]
  <;> ring
  <;> simp

 theorem chord_second_slope_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00127_expression (input lam) t=chordSlope .second lam (chart lam t) := by
  simp only [n00127_expression,n00122_expression,n00108_expression,n00049_expression,n00006_expression,n00057_expression,n00121_expression,n00120_expression,n00119_expression,n00118_expression,n00115_expression,n00111_expression,n00110_expression,n00011_expression,n00109_expression,n00114_expression,n00112_expression,n00087_expression,n00113_expression,n00117_expression,n00116_expression,n00126_expression,n00123_expression,n00091_expression,n00090_expression,n00095_expression,n00125_expression,n00124_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,div_one]
  <;> norm_num [input,chart,chordSlope]
  <;> ring
  <;> simp

 theorem chord_second_intercept_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00130_expression (input lam) t=chordIntercept .second lam (chart lam t) := by
  simp only [n00130_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,div_one]
  <;> norm_num [input,chart,chordIntercept]
  <;> ring
  <;> simp

 theorem zMinus_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00137_expression (input lam) t=zMinus (chart lam t) := by
  simp only [n00137_expression,n00132_expression,n00112_expression,n00087_expression,n00131_expression,n00011_expression,n00136_expression,n00135_expression,n00109_expression,n00134_expression,n00133_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,div_one]
  <;> norm_num [input,chart,zMinus]
  <;> ring
  <;> simp

 theorem zPlus_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00145_expression (input lam) t=zPlus (chart lam t) := by
  simp only [n00145_expression,n00142_expression,n00141_expression,n00140_expression,n00109_expression,n00139_expression,n00138_expression,n00144_expression,n00143_expression,n00133_expression,n00049_expression,n00006_expression,n00131_expression,n00011_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,div_one]
  <;> norm_num [input,chart,zPlus]
  <;> ring
  <;> simp

 theorem point0_h_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00153_expression (input lam) t=hMinus .E2 (chart lam t) := by
  simp only [n00153_expression,n00006_expression,n00152_expression,n00044_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,div_one]
  <;> norm_num [input,chart,hMinus,sigma]
  <;> ring
  <;> simp

 theorem point0_L_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00155_expression (input lam) t=supportLine .E2 .first lam (hMinus .E2 (chart lam t)) := by
  simp only [n00155_expression,n00154_expression,n00038_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,div_one]
  <;> norm_num [input,chart,supportLine,slope]
  <;> ring
  <;> simp

 theorem point1_h_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00042_expression (input lam) t=hCross .E2 lam := by
  simp only [lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,hCross_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> norm_num [input,chart]
  <;> ring
  <;> simp

 theorem point1_L_eq {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00157_expression (input lam) t=supportLine .E2 .first lam (hCross .E2 lam) := by
  simp only [n00157_expression,n00156_expression,n00038_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,div_one]
  <;> norm_num [input,chart,supportLine,slope]
  <;> ring
  <;> simp

 theorem n00007_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00007_expression (input lam) t=(1+lam:ℝ) := by
  simp only [n00007_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00009_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00009_expression (input lam) t=(13/5:ℝ) := by
  norm_num [n00009_expression,n00006_expression,n00003_expression]

 theorem n00011_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00011_expression (input lam) t=(2:ℝ) := by
  norm_num [n00011_expression]

 theorem n00020_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00020_expression (input lam) t=(841/50:ℝ) := by
  norm_num [n00020_expression,n00019_expression,n00018_expression,n00002_expression]

 theorem n00015_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00015_expression (input lam) t=(3/20:ℝ) := by
  norm_num [n00015_expression,n00003_expression,n00002_expression]

 theorem n00041_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00041_expression (input lam) t=(61/30:ℝ) := by
  norm_num [n00041_expression,n00038_expression,n00039_expression]

 theorem n00044_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00044_expression (input lam) t=(7/12:ℝ) := by
  norm_num [n00044_expression]

 theorem n00051_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00051_expression (input lam) t=(1+lam*(1-chart lam t):ℝ) := by
  simp only [n00051_expression,n00006_expression,n00050_expression,n00049_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00055_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00055_expression (input lam) t=(1+lam*(1-pH lam (chart lam t)):ℝ) := by
  simp only [n00055_expression,n00006_expression,n00054_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00058_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00058_expression (input lam) t=((1+q lam)*pH lam (chart lam t):ℝ) := by
  simp only [n00058_expression,n00057_expression,n00006_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00065_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00065_expression (input lam) t=(65536:ℝ) := by
  norm_num [n00065_expression]

 theorem n00083_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00083_expression (input lam) t=(2*q lam:ℝ) := by
  simp only [n00083_expression,n00011_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00091_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00091_expression (input lam) t=(4*q lam:ℝ) := by
  simp only [n00091_expression,n00090_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00096_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00096_expression (input lam) t=(2*q lam*(2-q lam):ℝ) := by
  simp only [n00096_expression,n00083_expression,n00011_expression,n00095_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00099_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00099_expression (input lam) t=(2*q lam*q lam:ℝ) := by
  simp only [n00099_expression,n00083_expression,n00011_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00106_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00106_expression (input lam) t=(vacancySwitch lam (chart lam t)-vacancyLo lam (chart lam t):ℝ) := by
  simp only [n00106_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00126_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00126_expression (input lam) t=(4*q lam*(2-q lam)*(1-q lam*chart lam t):ℝ) := by
  simp only [n00126_expression,n00123_expression,n00091_expression,n00090_expression,n00095_expression,n00011_expression,n00125_expression,n00006_expression,n00124_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00136_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00136_expression (input lam) t=((chart lam t)^2-6*chart lam t+6:ℝ) := by
  simp only [n00136_expression,n00135_expression,n00109_expression,n00134_expression,n00133_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00144_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00144_expression (input lam) t=(6*(1-chart lam t)*(2-chart lam t):ℝ) := by
  simp only [n00144_expression,n00143_expression,n00133_expression,n00049_expression,n00006_expression,n00131_expression,n00011_expression,lam_eq hlam,q_eq hlam,intercept_first_eq hlam,intercept_second_eq hlam,point1_h_eq hlam,HCross_eq hlam,H_eq hlam,p_eq hlam,r0_eq hlam,rs_eq hlam,alpha_eq hlam,beta_eq hlam,gamma_eq hlam,delta_eq hlam,bar_eq hlam,e_eq hlam,P0_eq hlam,sourceAtLo_eq hlam,sourceAtSwitchLower_eq hlam,sourceAtHi_eq hlam,chord_first_slope_eq hlam,chord_first_intercept_eq hlam,chord_second_slope_eq hlam,chord_second_intercept_eq hlam,zMinus_eq hlam,zPlus_eq hlam,point0_h_eq hlam,point0_L_eq hlam,point1_L_eq hlam,div_one]
  <;> simp only [input]
  <;> ring

 theorem n00138_factor {lam t : ℝ} (hlam : InRow .E2 lam) :
    n00138_expression (input lam) t=(12:ℝ) := by
  norm_num [n00138_expression]

 theorem original_DivisorsNonzero {lam t : ℝ} (hlam : InRow .E2 lam)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : DivisorsNonzero (input lam) t := by
  have fac : OriginalLightFactors .E2 lam (chart lam t) := by
    unfold chart
    exact parentChart_factors (reg:=.B) hlam ht0 ht1
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
    exact (fac.lambda_add_one_pos).ne'
  have h_n00009 : n00009_expression (input lam) t ≠ 0 := by
    rw [n00009_factor hlam]
    norm_num
  have h_n00011 : n00011_expression (input lam) t ≠ 0 := by
    rw [n00011_factor hlam]
    norm_num
  have h_n00020 : n00020_expression (input lam) t ≠ 0 := by
    rw [n00020_factor hlam]
    norm_num
  have h_n00015 : n00015_expression (input lam) t ≠ 0 := by
    rw [n00015_factor hlam]
    norm_num
  have h_n00041 : n00041_expression (input lam) t ≠ 0 := by
    rw [n00041_factor hlam]
    norm_num
  have h_n00044 : n00044_expression (input lam) t ≠ 0 := by
    rw [n00044_factor hlam]
    norm_num
  have h_n00051 : n00051_expression (input lam) t ≠ 0 := by
    rw [n00051_factor hlam]
    exact (hparentden).ne'
  have h_n00055 : n00055_expression (input lam) t ≠ 0 := by
    rw [n00055_factor hlam]
    exact (hvacancyden).ne'
  have h_n00058 : n00058_expression (input lam) t ≠ 0 := by
    rw [n00058_factor hlam]
    exact (hswitchden).ne'
  have h_n00065 : n00065_expression (input lam) t ≠ 0 := by
    rw [n00065_factor hlam]
    norm_num
  have h_n00083 : n00083_expression (input lam) t ≠ 0 := by
    rw [n00083_factor hlam]
    exact (htwoq).ne'
  have h_n00091 : n00091_expression (input lam) t ≠ 0 := by
    rw [n00091_factor hlam]
    exact (hfourq).ne'
  have h_n00096 : n00096_expression (input lam) t ≠ 0 := by
    rw [n00096_factor hlam]
    exact (htwoqtwominus).ne'
  have h_n00099 : n00099_expression (input lam) t ≠ 0 := by
    rw [n00099_factor hlam]
    exact (htwoqsq).ne'
  have h_n00106 : n00106_expression (input lam) t ≠ 0 := by
    rw [n00106_factor hlam]
    exact (fac.source_phase_width_pos).ne'
  have h_n00126 : n00126_expression (input lam) t ≠ 0 := by
    rw [n00126_factor hlam]
    exact (hchordden).ne'
  have h_n00136 : n00136_expression (input lam) t ≠ 0 := by
    rw [n00136_factor hlam]
    exact (fac.log_minus_denominator_pos).ne'
  have h_n00144 : n00144_expression (input lam) t ≠ 0 := by
    rw [n00144_factor hlam]
    exact (hlogplusden).ne'
  have h_n00138 : n00138_expression (input lam) t ≠ 0 := by
    rw [n00138_factor hlam]
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
#print axioms point1_L_eq
#print axioms n00007_factor
#print axioms n00009_factor
#print axioms n00011_factor
#print axioms n00020_factor
#print axioms n00015_factor
#print axioms n00041_factor
#print axioms n00044_factor
#print axioms n00051_factor
#print axioms n00055_factor
#print axioms n00058_factor
#print axioms n00065_factor
#print axioms n00083_factor
#print axioms n00091_factor
#print axioms n00096_factor
#print axioms n00099_factor
#print axioms n00106_factor
#print axioms n00126_factor
#print axioms n00136_factor
#print axioms n00144_factor
#print axioms n00138_factor
#print axioms original_DivisorsNonzero

end
end F4Unified.LightConstruction.GroupDomain_E2_B
