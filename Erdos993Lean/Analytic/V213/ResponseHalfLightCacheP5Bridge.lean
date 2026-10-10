module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP5Chunk028
public import Erdos993Lean.Analytic.V213.ResponseHalfLightControlDefs

/-! Generated: the cached polynomial equals `determinantPolynomial`; trimmed form `trimmedNF`. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

theorem polynomial_cached : p0289 = determinantPolynomial (⟨5, by decide⟩ : Fin 8) := by
  exact p0289_encode.trans (congrArg
    (fun e => Expr.encode e [[0,1]] [[],[1]]) source_determinantExpression)

def trimmedNF : Bi := exact_poly_nf_compact% (Bi.trim p0289)

theorem trimmedNF_op : trimmedNF = Bi.trim p0289 := by decide +kernel

theorem trimmedNF_exact : trimmedNF = HalfLightGates.trimmedDeterminant (⟨5, by decide⟩ : Fin 8) := by
  exact trimmedNF_op.trans (congrArg Bi.trim polynomial_cached)

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.polynomial_cached
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.polynomial_cached
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.trimmedNF
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.trimmedNF
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.trimmedNF_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.trimmedNF_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.trimmedNF_exact
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.trimmedNF_exact
