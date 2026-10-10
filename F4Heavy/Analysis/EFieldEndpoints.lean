module

public import F4Heavy.Finite.Metadata
public import F4Heavy.Analysis.FractionSemantics
public import F4Heavy.Contract

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite F4Unified

-- Exact original field endpoint; premise metadata_0238_E1_a_alpha____3_5.
theorem e_field_E1_a_alpha_lower : (3/5 : ℝ) ≤ alpha .E1 (rowData .E1).lo := by
  have h := fraction_le_sound _ _ metadata_0238_E1_a_alpha____3_5
  convert h using 1 <;> norm_num [fractionValue, alpha, field, rowData]

-- Exact original field endpoint; premise metadata_0239_E1_a_alpha____3_4.
theorem e_field_E1_a_alpha_upper : alpha .E1 (rowData .E1).lo ≤ (3/4 : ℝ) := by
  have h := fraction_le_sound _ _ metadata_0239_E1_a_alpha____3_4
  convert h using 1 <;> norm_num [fractionValue, alpha, field, rowData]

-- Exact original field endpoint; premise metadata_0240_E1_a_gamma____6_25.
theorem e_field_E1_a_gamma_lower : (6/25 : ℝ) ≤ gamma .E1 (rowData .E1).lo := by
  have h := fraction_le_sound _ _ metadata_0240_E1_a_gamma____6_25
  convert h using 1 <;> norm_num [fractionValue, gamma, field, rowData]

-- Exact original field endpoint; premise metadata_0241_E1_a_gamma____1_3.
theorem e_field_E1_a_gamma_upper : gamma .E1 (rowData .E1).lo ≤ (1/3 : ℝ) := by
  have h := fraction_le_sound _ _ metadata_0241_E1_a_gamma____1_3
  convert h using 1 <;> norm_num [fractionValue, gamma, field, rowData]

-- Exact original field endpoint; premise metadata_0242_E1_b_alpha____3_5.
theorem e_field_E1_b_alpha_lower : (3/5 : ℝ) ≤ alpha .E1 (rowData .E1).hi := by
  have h := fraction_le_sound _ _ metadata_0242_E1_b_alpha____3_5
  convert h using 1 <;> norm_num [fractionValue, alpha, field, rowData]

-- Exact original field endpoint; premise metadata_0243_E1_b_alpha____3_4.
theorem e_field_E1_b_alpha_upper : alpha .E1 (rowData .E1).hi ≤ (3/4 : ℝ) := by
  have h := fraction_le_sound _ _ metadata_0243_E1_b_alpha____3_4
  convert h using 1 <;> norm_num [fractionValue, alpha, field, rowData]

-- Exact original field endpoint; premise metadata_0244_E1_b_gamma____6_25.
theorem e_field_E1_b_gamma_lower : (6/25 : ℝ) ≤ gamma .E1 (rowData .E1).hi := by
  have h := fraction_le_sound _ _ metadata_0244_E1_b_gamma____6_25
  convert h using 1 <;> norm_num [fractionValue, gamma, field, rowData]

-- Exact original field endpoint; premise metadata_0245_E1_b_gamma____1_3.
theorem e_field_E1_b_gamma_upper : gamma .E1 (rowData .E1).hi ≤ (1/3 : ℝ) := by
  have h := fraction_le_sound _ _ metadata_0245_E1_b_gamma____1_3
  convert h using 1 <;> norm_num [fractionValue, gamma, field, rowData]

-- Exact original field endpoint; premise metadata_0247_E2_a_alpha____3_5.
theorem e_field_E2_a_alpha_lower : (3/5 : ℝ) ≤ alpha .E2 (rowData .E2).lo := by
  have h := fraction_le_sound _ _ metadata_0247_E2_a_alpha____3_5
  convert h using 1 <;> norm_num [fractionValue, alpha, field, rowData]

-- Exact original field endpoint; premise metadata_0248_E2_a_alpha____3_4.
theorem e_field_E2_a_alpha_upper : alpha .E2 (rowData .E2).lo ≤ (3/4 : ℝ) := by
  have h := fraction_le_sound _ _ metadata_0248_E2_a_alpha____3_4
  convert h using 1 <;> norm_num [fractionValue, alpha, field, rowData]

-- Exact original field endpoint; premise metadata_0249_E2_a_gamma____6_25.
theorem e_field_E2_a_gamma_lower : (6/25 : ℝ) ≤ gamma .E2 (rowData .E2).lo := by
  have h := fraction_le_sound _ _ metadata_0249_E2_a_gamma____6_25
  convert h using 1 <;> norm_num [fractionValue, gamma, field, rowData]

-- Exact original field endpoint; premise metadata_0250_E2_a_gamma____1_3.
theorem e_field_E2_a_gamma_upper : gamma .E2 (rowData .E2).lo ≤ (1/3 : ℝ) := by
  have h := fraction_le_sound _ _ metadata_0250_E2_a_gamma____1_3
  convert h using 1 <;> norm_num [fractionValue, gamma, field, rowData]

-- Exact original field endpoint; premise metadata_0251_E2_b_alpha____3_5.
theorem e_field_E2_b_alpha_lower : (3/5 : ℝ) ≤ alpha .E2 (rowData .E2).hi := by
  have h := fraction_le_sound _ _ metadata_0251_E2_b_alpha____3_5
  convert h using 1 <;> norm_num [fractionValue, alpha, field, rowData]

-- Exact original field endpoint; premise metadata_0252_E2_b_alpha____3_4.
theorem e_field_E2_b_alpha_upper : alpha .E2 (rowData .E2).hi ≤ (3/4 : ℝ) := by
  have h := fraction_le_sound _ _ metadata_0252_E2_b_alpha____3_4
  convert h using 1 <;> norm_num [fractionValue, alpha, field, rowData]

-- Exact original field endpoint; premise metadata_0253_E2_b_gamma____6_25.
theorem e_field_E2_b_gamma_lower : (6/25 : ℝ) ≤ gamma .E2 (rowData .E2).hi := by
  have h := fraction_le_sound _ _ metadata_0253_E2_b_gamma____6_25
  convert h using 1 <;> norm_num [fractionValue, gamma, field, rowData]

-- Exact original field endpoint; premise metadata_0254_E2_b_gamma____1_3.
theorem e_field_E2_b_gamma_upper : gamma .E2 (rowData .E2).hi ≤ (1/3 : ℝ) := by
  have h := fraction_le_sound _ _ metadata_0254_E2_b_gamma____1_3
  convert h using 1 <;> norm_num [fractionValue, gamma, field, rowData]

end F4Heavy.Analysis
