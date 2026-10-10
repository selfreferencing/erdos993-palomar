module

public import F4Heavy.Analysis.CapBernstein

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

/-- A printed positive projective coefficient gives a positive Bernstein
coefficient after positive normalization and division by its binomial weight. -/
theorem tail_scaled_ray_positive (scale ray : Fraction) (weight : Nat)
    (hs : Fraction.positive scale = true) (hr : Fraction.positive ray = true)
    (hw : 0 < weight) :
    0 < fractionValue (Fraction.mul scale (Fraction.mul ray ⟨1, weight⟩)) := by
  have hsden : 0 < scale.den := (show 0 < scale.den ∧ 0 < scale.num by
    simpa only [Fraction.positive, Bool.and_eq_true, decide_eq_true_eq] using hs).1
  have hrden : 0 < ray.den := (show 0 < ray.den ∧ 0 < ray.num by
    simpa only [Fraction.positive, Bool.and_eq_true, decide_eq_true_eq] using hr).1
  rw [fractionValue_mul _ _ hsden (fraction_mul_den_pos _ _ hrden hw),
    fractionValue_mul _ _ hrden hw]
  have hweight : 0 < fractionValue ⟨1, weight⟩ := by
    dsimp only [fractionValue]
    exact div_pos (by norm_num) (by exact_mod_cast hw)
  exact mul_pos (fraction_positive_sound _ hs) (mul_pos (fraction_positive_sound _ hr) hweight)

end F4Heavy.Analysis
