module

public meta import Lean
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceExactBi

/-! Exact polynomial normal forms by an elaborator.

The elaborator returns a closed constructor expression, not a proof. Every
use must have a separate ordinary kernel equality to its source operation.
The intended unit is one operation over previously normalized children.
The root whitelist excludes Expr.encode and pow; it is not a security boundary
against a caller hiding a large expression inside an argument. Calls and their
children require source review. No options or evaluation-based axiom are used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ExactPolyNF

open Lean Meta Elab

private meta def intDataNF (e : Expr) : Bool :=
  (e.isAppOfArity ``Int.ofNat 1 || e.isAppOfArity ``Int.negSucc 1) &&
    e.getAppArgs[0]!.isRawNatLit

private meta def ratDataNF (e : Expr) : Bool :=
  e.isAppOfArity ``Rat.mk' 4 && intDataNF e.getAppArgs[0]! &&
    e.getAppArgs[1]!.isRawNatLit

private meta partial def listDataNF (entry : Expr → Bool) (e : Expr) : Bool :=
  if e.isAppOfArity ``List.nil 1 then true
  else if e.isAppOfArity ``List.cons 3 then
    entry e.getAppArgs[1]! && listDataNF entry e.getAppArgs[2]!
  else false

private meta def biDataNF (e : Expr) : Bool := listDataNF (listDataNF ratDataNF) e

private meta def supportedRoot (e : Expr) : Bool :=
  e.isAppOfArity ``List.nil 1 || e.isAppOfArity ``List.cons 3 ||
    e.isAppOfArity ``Erdos993Lean.BCFG.Bi.add 2 ||
    e.isAppOfArity ``Erdos993Lean.BCFG.Bi.trim 1 ||
    e.isAppOfArity ``Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.mul 2 ||
    e.isAppOfArity ``Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.neg 1

/-- Normalize one reviewed closed Bi operation with Lean's ordinary reducer.
Rat proof fields are preserved; only data fields must be constructor-normal.
The surrounding declaration and a separate equality remain kernel checked. -/
elab "exact_poly_nf% " t:term : term => do
  let expected := mkConst ``Erdos993Lean.BCFG.Bi
  let e ← Term.elabTermEnsuringType t expected
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    throwError "exact_poly_nf% requires a closed Bi term without metavariables"
  unless supportedRoot e do
    throwError "exact_poly_nf% accepts a literal Bi or one add/mul/neg/trim operation"
  let nf ← withTransparency .all <|
    Meta.reduce e (explicitOnly := false) (skipTypes := true) (skipProofs := true)
  if nf.hasMVar || nf.hasFVar || nf.hasLooseBVars then
    throwError "exact_poly_nf% produced a nonclosed expression"
  unless biDataNF nf do
    throwError "exact_poly_nf% did not reach literal List/List/Rat data constructors"
  unless (← isDefEq (← inferType nf) expected) do
    throwError "exact_poly_nf% produced an expression with the wrong type"
  return nf

end Erdos993Lean.Analytic.V213.VarianceResponse.ExactPolyNF

-- Imported type audit for this elaborator support module.
#check Erdos993Lean.BCFG.Bi
#print axioms Erdos993Lean.BCFG.Bi
