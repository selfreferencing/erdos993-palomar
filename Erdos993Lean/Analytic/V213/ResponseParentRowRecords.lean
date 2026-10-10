module

public import Mathlib

/-! Literal current Table1 rows D,E1,E2,H. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

structure Row where
  low : ℚ
  high : ℚ
  gammaTheta : ℚ
  center : ℚ
  alpha0 : ℤ
  alpha1 : ℤ
  beta0 : ℤ
  beta1 : ℤ
  gamma0 : ℤ
  gamma1 : ℤ
  delta0 : ℤ
  delta1 : ℤ
  deriving DecidableEq

def rowData : Fin 4 → Row :=
  ![⟨(4:ℚ)/5, (13:ℚ)/10, (8:ℚ)/5, (269:ℚ)/256, 46809, 3327, 35136, 3086, 14520, 13694, 1835, 1340⟩,
    ⟨(13:ℚ)/10, (29:ℚ)/20, (17:ℚ)/10, (11:ℚ)/8, 44917, 29958, 28533, 57271, 17821, 20483, 3064, -4423⟩,
    ⟨(29:ℚ)/20, (8:ℚ)/5, (17:ℚ)/10, (195:ℚ)/128, 45775, 22238, 30825, 10297, 19913, 13978, 3161, 4340⟩,
    ⟨(7:ℚ)/4, (7:ℚ)/3, (2:ℚ)/1, (523:ℚ)/256, 51799, 8158, 20496, 41265, 29750, 4333, 9083, -11181⟩]

noncomputable def affineField (i : Fin 4) (a b : ℤ) (lam : ℝ) : ℝ :=
  ((a:ℝ)+(b:ℝ)*(lam-(rowData i).center))/65536

noncomputable def alpha (i : Fin 4) (lam : ℝ) : ℝ :=
  affineField i (rowData i).alpha0 (rowData i).alpha1 lam

noncomputable def beta (i : Fin 4) (lam : ℝ) : ℝ :=
  affineField i (rowData i).beta0 (rowData i).beta1 lam

noncomputable def gamma (i : Fin 4) (lam : ℝ) : ℝ :=
  affineField i (rowData i).gamma0 (rowData i).gamma1 lam

noncomputable def delta (i : Fin 4) (lam : ℝ) : ℝ :=
  affineField i (rowData i).delta0 (rowData i).delta1 lam

noncomputable def price (i : Fin 4) (lam : ℝ) : ℝ := (rowData i).gammaTheta/(1+lam)

def inRow (i : Fin 4) (lam : ℝ) : Prop :=
  (rowData i).low ≤ lam ∧ lam ≤ (rowData i).high

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.Row
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.Row
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.rowData
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.rowData
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.affineField
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.affineField
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.alpha
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.alpha
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.beta
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.beta
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.gamma
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.gamma
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.delta
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.delta
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.price
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.price
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.inRow
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.inRow
