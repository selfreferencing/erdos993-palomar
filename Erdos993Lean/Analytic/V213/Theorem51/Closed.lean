module

public import Erdos993Lean.Analytic.V213.Theorem51.Final
public import Erdos993Lean.F4U.Light.Construction.LightCoreComplete

/-! Theorem 5.1 on every row of Table 1 with no hypothesis left.

`Theorem51.Final` proves the variance-ratio bound for all nine rows from one premise, the frozen
contract's light core on its four heavy rows. `F4Unified.LightConstruction.lightCore_all_rows`
proves exactly that premise. This file applies the one to the other and contains no other
mathematics. -/

@[expose] public section

universe u

namespace Erdos993Lean.Analytic.V213.Theorem51

open Finset Erdos993Lean.Analytic Tail Reserve O2 VarianceResponse

/-- The light core on the four heavy rows, in the form `Theorem51.Final` asks for. -/
theorem lightCore_closed : ∀ r : F4Unified.Row, F4Unified.LightCore r :=
  fun r => F4Unified.LightConstruction.lightCore_all_rows r

/-- Theorem 5.1 for every row of Table 1, with no hypothesis. -/
theorem allRowsVarianceRatio_closed : AllRowsVarianceRatio.{u} :=
  allRowsVarianceRatio lightCore_closed

/-- Theorem 5.1 in the finite-forest vocabulary, with no hypothesis. -/
theorem finiteForest_variance_ratio_bound_closed
    (F : FiniteForest) {r : TableRow} {t : ℝ} (hrow : InTableRow r t)
    (B : Finset (Fin F.n)) (hB : IsMaxWeight F t B) :
    hardCoreVar F t ≤ (gammaTheta r/(1+t))*weightW F t B :=
  finiteForest_variance_ratio_bound lightCore_closed F hrow B hB

end Erdos993Lean.Analytic.V213.Theorem51
