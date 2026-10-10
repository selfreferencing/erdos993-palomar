module
public import Erdos993Lean.F4U.Light.Construction.Definitions

@[expose] public section
namespace F4Unified.LightConstruction
noncomputable section

/-- The manuscript's derivative dJ/dh, evaluated at the actual child u. -/
def supportDerivative (lam u : ℝ) : ℝ :=
  u*(1+(childH u-2*(1-u))*Real.log (lam*(1-u)/u))/(childH u-1+u)

def supportW (u : ℝ) : ℝ := childH u-1+u

def supportA (u : ℝ) : ℝ := 2*(1-u)^2*phi u+3*u^2-2*u

def supportB (u : ℝ) : ℝ := 3*u-(3-2*u)*phi u

/-- The literal expression for the second derivative in the h coordinate. -/
def supportSecond (lam u : ℝ) : ℝ :=
  -(1-u)*(supportA u*Real.log (lam*(1-u)/u)+supportB u)/(supportW u)^3

/-- The table's contact comparison, preserving childJ and childH. -/
def supportContactValue (r : Row) (s : Support) (lam u : ℝ) : ℝ :=
  childJ lam u-slope r s*childH u+(supportDerivative lam u-slope r s)^2/(2*curvature r)

end
end F4Unified.LightConstruction
