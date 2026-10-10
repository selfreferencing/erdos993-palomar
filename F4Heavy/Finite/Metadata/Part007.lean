module

public import F4Heavy.Finite.Arithmetic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Finite
open Fraction

-- audit.py:100: E fixed exponential ratio
theorem metadata_0210_E_fixed_exponential_ratio :
    (((lt ⟨9, 8⟩ (add (add ⟨1, 1⟩ ⟨1, 8⟩) ⟨1, 128⟩)))) = true := by
  decide +kernel

-- audit.py:109: H curvature lower function decreasing
theorem metadata_0211_H_curvature_lower_function_decreasing :
    (((lt (sub (add (mul ⟨2, 1⟩ (pow ⟨7, 10⟩ 4)) (mul ⟨36, 1⟩ ⟨7, 10⟩)) ⟨36, 1⟩) ⟨0, 1⟩))) = true := by
  decide +kernel

-- audit.py:110: E curvature lower function decreasing
theorem metadata_0212_E_curvature_lower_function_decreasing :
    (((lt (sub (add (pow ⟨2, 3⟩ 4) ⟨32, 1⟩) ⟨48, 1⟩) ⟨0, 1⟩))) = true := by
  decide +kernel

-- metadata.py:25: one new rational upper bound for log 4
theorem metadata_0213_one_new_rational_upper_bound_for_log_4 :
    (((lt ⟨19540640549631085013602404472731818469789797150617764779, 14095592608373277291969041104040625296119343690556510450⟩ ⟨8664339757, 6250000000⟩))) = true := by
  decide +kernel

-- metadata.py:26: shared rational log upper is positive at x=1
theorem metadata_0214_shared_rational_log_upper_is_positive_at_x_1 :
    (((lt ⟨0, 1⟩ (sub (sub ⟨8664339757, 6250000000⟩ ⟨21, 73⟩) ⟨12, 11⟩)))) = true := by
  decide +kernel

-- metadata.py:57: D within log certificate domain
theorem metadata_0215_D_within_log_certificate_domain :
    (((le ⟨1, 4⟩ ⟨5, 16⟩))) = true := by
  decide +kernel

-- metadata.py:66: D original half-slope envelope geometry
theorem metadata_0216_D_original_half_slope_envelope_geometry :
    ((((lt ⟨0, 1⟩ ⟨7316730639, 11000000000⟩)) && ((lt ⟨-3326942783, 2000000000⟩ ⟨0, 1⟩)) && ((lt ⟨3, 10⟩ (div ⟨11, 5⟩ ⟨2, 1⟩))))) = true := by
  decide +kernel

-- metadata.py:66: D original half-slope envelope geometry
theorem metadata_0217_D_original_half_slope_envelope_geometry :
    ((((lt ⟨0, 1⟩ ⟨246537112593966747679369, 485993323596781000000000⟩)) && ((lt ⟨-395332357433134768176779, 265087267416426000000000⟩ ⟨0, 1⟩)) && ((lt ⟨3, 10⟩ (div ⟨11, 5⟩ ⟨2, 1⟩))))) = true := by
  decide +kernel

-- metadata.py:82: D new upper denominator anchor
theorem metadata_0218_D_new_upper_denominator_anchor :
    ((((lt ⟨1, 50⟩ ⟨117373, 4194304⟩)) && ((lt ⟨1, 50⟩ ⟨379318759949071244203881880048206054195821108094337, 15572997847702994716600943247360000000000000000000000⟩)))) = true := by
  decide +kernel

-- metadata.py:57: E1 within log certificate domain
theorem metadata_0219_E1_within_log_certificate_domain :
    (((le ⟨1, 4⟩ ⟨1, 4⟩))) = true := by
  decide +kernel

-- metadata.py:57: E2 within log certificate domain
theorem metadata_0220_E2_within_log_certificate_domain :
    (((le ⟨1, 4⟩ ⟨1, 4⟩))) = true := by
  decide +kernel

-- metadata.py:57: H within log certificate domain
theorem metadata_0221_H_within_log_certificate_domain :
    (((le ⟨1, 4⟩ ⟨1, 4⟩))) = true := by
  decide +kernel

-- metadata.py:66: H original half-slope envelope geometry
theorem metadata_0222_H_original_half_slope_envelope_geometry :
    ((((lt ⟨0, 1⟩ ⟨1481046707, 3200000000⟩)) && ((lt ⟨-15097571481, 10000000000⟩ ⟨0, 1⟩)) && ((lt ⟨3, 10⟩ (div ⟨12, 5⟩ ⟨2, 1⟩))))) = true := by
  decide +kernel

-- metadata.py:73: H coarser breaks ordered
theorem metadata_0223_H_coarser_breaks_ordered :
    (((lt ⟨5032523827, 8000000000⟩ ⟨16130889827, 21000000000⟩))) = true := by
  decide +kernel

-- metadata.py:73: H coarser breaks ordered
theorem metadata_0224_H_coarser_breaks_ordered :
    (((lt ⟨16130889827, 21000000000⟩ ⟨313509157, 360000000⟩))) = true := by
  decide +kernel

-- metadata.py:73: H coarser breaks ordered
theorem metadata_0225_H_coarser_breaks_ordered :
    (((lt ⟨313509157, 360000000⟩ ⟨6368671561, 6800000000⟩))) = true := by
  decide +kernel

-- metadata.py:73: H coarser breaks ordered
theorem metadata_0226_H_coarser_breaks_ordered :
    (((lt ⟨6368671561, 6800000000⟩ ⟨1, 1⟩))) = true := by
  decide +kernel

-- metadata.py:74: H coarser support positive
theorem metadata_0227_H_coarser_support_positive :
    ((((lt ⟨0, 1⟩ ⟨5032523827, 8000000000⟩)) && ((eq ⟨1, 1⟩ ⟨1, 1⟩)) && ((lt ⟨0, 1⟩ (minimum [⟨23364118249, 70000000000⟩, ⟨10937683963, 30000000000⟩, ⟨3454858137, 10625000000⟩, ⟨178601269, 2500000000⟩]))))) = true := by
  decide +kernel

-- metadata.py:75: H coarser maximum remains J2
theorem metadata_0228_H_coarser_maximum_remains_J2 :
    (((eq (maximum [⟨0, 1⟩, ⟨23364118249, 70000000000⟩, ⟨10937683963, 30000000000⟩, ⟨3454858137, 10625000000⟩, ⟨178601269, 2500000000⟩]) ⟨10937683963, 30000000000⟩))) = true := by
  decide +kernel

-- metadata.py:66: H original half-slope envelope geometry
theorem metadata_0229_H_original_half_slope_envelope_geometry :
    ((((lt ⟨0, 1⟩ ⟨20097899841913805037991, 57996705806121600000000⟩)) && ((lt ⟨-84214906818380060768551, 60413235214710000000000⟩ ⟨0, 1⟩)) && ((lt ⟨3, 10⟩ (div ⟨12, 5⟩ ⟨2, 1⟩))))) = true := by
  decide +kernel

-- metadata.py:73: H coarser breaks ordered
theorem metadata_0230_H_coarser_breaks_ordered :
    (((lt ⟨84214906818380060768551, 144991764515304000000000⟩ ⟨284580553619837109926551, 380603381852673000000000⟩))) = true := by
  decide +kernel

-- metadata.py:73: H coarser breaks ordered
theorem metadata_0231_H_coarser_breaks_ordered :
    (((lt ⟨284580553619837109926551, 380603381852673000000000⟩ ⟨795665454288133404263, 932089914741240000000⟩))) = true := by
  decide +kernel

-- metadata.py:73: H coarser breaks ordered
theorem metadata_0232_H_coarser_breaks_ordered :
    (((lt ⟨795665454288133404263, 932089914741240000000⟩ ⟨114035057263978191758693, 123242999838008400000000⟩))) = true := by
  decide +kernel

-- metadata.py:73: H coarser breaks ordered
theorem metadata_0233_H_coarser_breaks_ordered :
    (((lt ⟨114035057263978191758693, 123242999838008400000000⟩ ⟨1, 1⟩))) = true := by
  decide +kernel

-- metadata.py:74: H coarser support positive
theorem metadata_0234_H_coarser_support_positive :
    ((((lt ⟨0, 1⟩ ⟨84214906818380060768551, 144991764515304000000000⟩)) && ((eq ⟨1, 1⟩ ⟨1, 1⟩)) && ((lt ⟨0, 1⟩ (minimum [⟨508131385772715603272837, 1268677939508910000000000⟩, ⟨235048953994514128608719, 543719116932390000000000⟩, ⟨24989333986403578559527, 64189062415629375000000⟩, ⟨4098437852122808040097, 45309926411032500000000⟩]))))) = true := by
  decide +kernel

-- metadata.py:75: H coarser maximum remains J2
theorem metadata_0235_H_coarser_maximum_remains_J2 :
    (((eq (maximum [⟨0, 1⟩, ⟨508131385772715603272837, 1268677939508910000000000⟩, ⟨235048953994514128608719, 543719116932390000000000⟩, ⟨24989333986403578559527, 64189062415629375000000⟩, ⟨4098437852122808040097, 45309926411032500000000⟩]) ⟨235048953994514128608719, 543719116932390000000000⟩))) = true := by
  decide +kernel

-- metadata.py:82: H new upper denominator anchor
theorem metadata_0236_H_new_upper_denominator_anchor :
    ((((lt ⟨1, 50⟩ ⟨2328975, 16777216⟩)) && ((lt ⟨1, 50⟩ ⟨93848558789697075555049351475045906756177857583519, 1010378695824469457582193377280000000000000000000000⟩)))) = true := by
  decide +kernel

-- e12_metadata.py:12: E1 two positive slopes followed by a negative slope
theorem metadata_0237_E1_two_positive_slopes_followed_by_a_negative_slope :
    (((decide (3 = 3) && eq ⟨7, 3⟩ ⟨7, 3⟩ && eq ⟨3, 10⟩ ⟨3, 10⟩ && eq ⟨-8, 15⟩ ⟨-8, 15⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E1 a alpha >= 3/5
theorem metadata_0238_E1_a_alpha____3_5 :
    (((le ⟨3, 5⟩ ⟨853403, 1310720⟩))) = true := by
  decide +kernel

-- e12_metadata.py:19: E1 a alpha <= 3/4
theorem metadata_0239_E1_a_alpha____3_4 :
    (((le ⟨853403, 1310720⟩ ⟨3, 4⟩))) = true := by
  decide +kernel

end F4Heavy.Finite
