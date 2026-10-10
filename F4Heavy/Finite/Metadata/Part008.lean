module

public import F4Heavy.Finite.Arithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite
open Fraction

-- e12_metadata.py:19: E1 a gamma >= 6/25
theorem metadata_0240_E1_a_gamma____6_25 :
    (((le ⟨6, 25⟩ ⟨651391, 2621440⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E1 a gamma <= 1/3
theorem metadata_0241_E1_a_gamma____1_3 :
    (((le ⟨651391, 2621440⟩ ⟨1, 3⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E1 b alpha >= 3/5
theorem metadata_0242_E1_b_alpha____3_5 :
    (((le ⟨3, 5⟩ ⟨943277, 1310720⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E1 b alpha <= 3/4
theorem metadata_0243_E1_b_alpha____3_4 :
    (((le ⟨943277, 1310720⟩ ⟨3, 4⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E1 b gamma >= 6/25
theorem metadata_0244_E1_b_gamma____6_25 :
    (((le ⟨6, 25⟩ ⟨774289, 2621440⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E1 b gamma <= 1/3
theorem metadata_0245_E1_b_gamma____1_3 :
    (((le ⟨774289, 2621440⟩ ⟨1, 3⟩))) = true := by
  decide +kernel

-- e12_metadata.py:12: E2 two positive slopes followed by a negative slope
theorem metadata_0246_E2_two_positive_slopes_followed_by_a_negative_slope :
    (((decide (3 = 3) && eq ⟨7, 3⟩ ⟨7, 3⟩ && eq ⟨3, 10⟩ ⟨3, 10⟩ && eq ⟨-8, 15⟩ ⟨-8, 15⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E2 a alpha >= 3/5
theorem metadata_0247_E2_a_alpha____3_5 :
    (((le ⟨3, 5⟩ ⟨14125407, 20971520⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E2 a alpha <= 3/4
theorem metadata_0248_E2_a_alpha____3_4 :
    (((le ⟨14125407, 20971520⟩ ⟨3, 4⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E2 a gamma >= 6/25
theorem metadata_0249_E2_a_gamma____6_25 :
    (((le ⟨6, 25⟩ ⟨6043677, 20971520⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E2 a gamma <= 1/3
theorem metadata_0250_E2_a_gamma____1_3 :
    (((le ⟨6043677, 20971520⟩ ⟨1, 3⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E2 b alpha >= 3/5
theorem metadata_0251_E2_b_alpha____3_5 :
    (((le ⟨3, 5⟩ ⟨15192831, 20971520⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E2 b alpha <= 3/4
theorem metadata_0252_E2_b_alpha____3_4 :
    (((le ⟨15192831, 20971520⟩ ⟨3, 4⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E2 b gamma >= 6/25
theorem metadata_0253_E2_b_gamma____6_25 :
    (((le ⟨6, 25⟩ ⟨6714621, 20971520⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E2 b gamma <= 1/3
theorem metadata_0254_E2_b_gamma____1_3 :
    (((le ⟨6714621, 20971520⟩ ⟨1, 3⟩))) = true := by
  decide +kernel

-- e12_metadata.py:26: p endpoint bound and coarser bound used for R
theorem metadata_0255_p_endpoint_bound_and_coarser_bound_used_for_R :
    (((lt ⟨8, 21⟩ ⟨2, 5⟩))) = true := by
  decide +kernel

-- e12_metadata.py:27: R endpoint bound
theorem metadata_0256_R_endpoint_bound :
    (((lt ⟨50, 89⟩ ⟨9, 16⟩))) = true := by
  decide +kernel

-- e12_metadata.py:28: K endpoint bound
theorem metadata_0257_K_endpoint_bound :
    (((lt ⟨17, 46⟩ ⟨3, 8⟩))) = true := by
  decide +kernel

-- e12_metadata.py:29: linear-parent lower bound
theorem metadata_0258_linear_parent_lower_bound :
    (((eq (mul ⟨6, 25⟩ (sub ⟨1, 1⟩ (div ⟨8, 21⟩ ⟨2, 1⟩))) ⟨34, 175⟩))) = true := by
  decide +kernel

-- e12_metadata.py:30: strict negative feasible lower-endpoint N
theorem metadata_0259_strict_negative_feasible_lower_endpoint_N :
    (((eq ⟨-1917, 1030400⟩ ⟨-1917, 1030400⟩) && (lt ⟨-1917, 1030400⟩ ⟨0, 1⟩))) = true := by
  decide +kernel

-- e12_metadata.py:31: strict negative upper-endpoint N
theorem metadata_0260_strict_negative_upper_endpoint_N :
    (((eq ⟨-4433, 9600⟩ ⟨-4433, 9600⟩) && (lt ⟨-4433, 9600⟩ ⟨0, 1⟩))) = true := by
  decide +kernel

-- e12_metadata.py:32: strict positive virtual-zero N
theorem metadata_0261_strict_positive_virtual_zero_N :
    (((eq ⟨107, 1920⟩ ⟨107, 1920⟩) && (lt ⟨0, 1⟩ ⟨107, 1920⟩))) = true := by
  decide +kernel

end F4Heavy.Finite
