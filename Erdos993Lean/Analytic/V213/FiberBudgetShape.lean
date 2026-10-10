module

public import Erdos993Lean.Analytic.V213.FiberBudgetData
public import Erdos993Lean.Analytic.V213.LowMeanIntegerOrder

/-!
Literal F17 budget and margin formulas, retaining the full canonical
operation tree before numerical comparisons.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

namespace FiberBudgetFormula

def sub (x y : LowMeanIntegerShape) : LowMeanIntegerShape := .add x (.neg y)

def budget (id : FiberBudgetIdentity) : LowMeanIntegerShape :=
  let r := fiberBudgetById id
  sub (sub (sub (.add (.atom (1,1)) (.atom r.b)) (.atom r.Theta))
    (.div (.mul (.atom (9,1)) (.atom r.D_star)) (.mul (.atom (2,1)) (.atom r.mu_star))))
    (.div (.pow (.atom r.R) 2) (.mul (sub (.atom (1,1)) (.pow (.atom r.R) 2)) (.atom r.mu_star)))

end FiberBudgetFormula

def fiberBudgetShape (id : FiberBudgetIdentity) : FiberBudgetRole → LowMeanIntegerShape
  | .budget => FiberBudgetFormula.budget id
  | .strictGap => FiberBudgetFormula.sub (FiberBudgetFormula.budget id) (.atom (fiberBudgetById id).B_star)
  | .margin => FiberBudgetFormula.sub (.atom (fiberBudgetById id).B_star) (.atom (fiberBudgetById id).Z)

noncomputable def fiberBlockBudget (id : FiberBudgetIdentity) : ℝ :=
  let r := fiberBudgetById id
  1+lowMeanFractionReal r.b-lowMeanFractionReal r.Theta-
    9*lowMeanFractionReal r.D_star/(2*lowMeanFractionReal r.mu_star)-
    (lowMeanFractionReal r.R)^2/((1-(lowMeanFractionReal r.R)^2)*lowMeanFractionReal r.mu_star)

noncomputable def fiberBudgetValue (id : FiberBudgetIdentity) : FiberBudgetRole → ℝ
  | .budget => fiberBlockBudget id
  | .strictGap => fiberBlockBudget id-lowMeanFractionReal (fiberBudgetById id).B_star
  | .margin => lowMeanFractionReal (fiberBudgetById id).B_star-lowMeanFractionReal (fiberBudgetById id).Z

theorem fiber_budget_shape_real (id : FiberBudgetIdentity) (role : FiberBudgetRole) :
    lowMeanIntegerShapeReal (fiberBudgetShape id role) = fiberBudgetValue id role := by
  cases role <;> simp [fiberBudgetShape,FiberBudgetFormula.budget,FiberBudgetFormula.sub,
    lowMeanIntegerShapeReal,fiberBudgetValue,fiberBlockBudget,lowMeanFractionReal] <;> ring

end Erdos993Lean.Analytic.V213
