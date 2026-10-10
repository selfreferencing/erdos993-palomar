module

public import F4Heavy.Analysis.LeafCore
public import F4Heavy.Analysis.PolynomialIdentity

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def leafReflectV (t : ℝ) : ℝ :=
  1-t/2-t^2/12-t^3/24-19*t^4/720
noncomputable def leafReflectN (k t a g : ℝ) : ℝ :=
  4*(65536*k*(1-t^2)*(1-t))*(2*t*(a-g*leafReflectV t))-
    (-65536*k*(1-t)^3-2*t*a-131072*t*(1-t)^2)^2

theorem leaf_reflect_quotient (k t a g : ℝ) (ht : t ≠ 0) (h1 : 1-t ≠ 0) :
    4*(k*(1-t^2)/(2*t))*(a/(65536*(1-t))-g/(65536*(1-t))*leafReflectV t)-
      (-k*(1-t)^2/(2*t)-a/(65536*(1-t))-(1-t))^2 =
    leafReflectN k t a g/(131072*t*(1-t))^2 := by
  unfold leafReflectN leafReflectV
  field_simp [ht,h1]
  <;> ring

end F4Heavy.Analysis
