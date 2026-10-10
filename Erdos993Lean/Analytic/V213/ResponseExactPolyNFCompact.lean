module

public import Erdos993Lean.Analytic.V213.ResponseExactPolyNF

/-! Compact exact polynomial normal forms.

Reduce one reviewed closed Bi operation, then rebuild each rational from only
its literal numerator and denominator. The second reduction starts at mkRat;
it cannot retain an earlier convolution in a rational's proof fields. Both
reductions use Lean's ordinary reducer under the unchanged resource limits.

The literal data comparison below is a rejection guard, not a proof. Every
use still requires a separate ordinary kernel equality to its source
operation. List constructors, including empty rows and trailing zeroes, are
preserved exactly; this elaborator never trims or expands a whole Expr.encode.
The root whitelist is a reviewed-call discipline, not a security boundary
against a caller hiding a larger operation inside one of the arguments.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ExactPolyNFCompact

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

private abbrev CompactM := MonadCacheT Expr Expr MetaM

/-- The memoization key contains only mkRat and two literal data arguments.
No proof from the original rational is passed to the fresh reduction. -/
private meta def compactRat (e : Expr) : CompactM Expr := do
  unless ratDataNF e do
    throwError "exact_poly_nf_compact% expected a literal Rat constructor"
  let num := e.getAppArgs[0]!
  let den := e.getAppArgs[1]!
  if den == mkRawNatLit 0 then
    throwError "exact_poly_nf_compact% encountered a zero denominator"
  let seed := mkApp2 (mkConst ``mkRat) num den
  checkCache seed fun _ => do
    let fresh ← withTransparency .all <|
      Meta.reduce seed (explicitOnly := false) (skipTypes := true) (skipProofs := true)
    unless ratDataNF fresh do
      throwError "exact_poly_nf_compact% could not rebuild a literal Rat constructor"
    unless fresh.getAppArgs[0]! == num && fresh.getAppArgs[1]! == den do
      throwError "exact_poly_nf_compact% rebuilding changed literal rational data"
    if fresh.hasMVar || fresh.hasFVar || fresh.hasLooseBVars then
      throwError "exact_poly_nf_compact% rebuilt a nonclosed rational"
    return fresh

/-- Rebuild the original spine with the same constructor, universe levels and
element-type argument. No zero removal, reordering or arithmetic occurs here. -/
private meta partial def compactList (entry : Expr → CompactM Expr) (e : Expr) :
    CompactM Expr := do
  if e.isAppOfArity ``List.nil 1 then
    return e
  else if e.isAppOfArity ``List.cons 3 then
    let args := e.getAppArgs
    let head ← entry args[1]!
    let tail ← compactList entry args[2]!
    return mkAppN e.getAppFn #[args[0]!, head, tail]
  else
    throwError "exact_poly_nf_compact% expected a literal List constructor"

/-- Normalize one operation and replace only its rational proof provenance.
The caller must retain a separate kernel proof of equality to that operation. -/
elab "exact_poly_nf_compact% " t:term : term => do
  let expected := mkConst ``Erdos993Lean.BCFG.Bi
  let e ← Term.elabTermEnsuringType t expected
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar || e.hasFVar || e.hasLooseBVars then
    throwError "exact_poly_nf_compact% requires a closed Bi term without metavariables"
  unless supportedRoot e do
    throwError "exact_poly_nf_compact% accepts a literal Bi or one add/mul/neg/trim operation"
  let nf ← withTransparency .all <|
    Meta.reduce e (explicitOnly := false) (skipTypes := true) (skipProofs := true)
  unless biDataNF nf do
    throwError "exact_poly_nf_compact% did not reach literal List/List/Rat data constructors"
  if nf.hasMVar || nf.hasFVar || nf.hasLooseBVars then
    throwError "exact_poly_nf_compact% produced a nonclosed normal form"
  let compacted ← (compactList (compactList compactRat) nf).run
  unless biDataNF compacted do
    throwError "exact_poly_nf_compact% rebuilding changed the constructor shape"
  if compacted.hasMVar || compacted.hasFVar || compacted.hasLooseBVars then
    throwError "exact_poly_nf_compact% produced a nonclosed compact form"
  unless (← isDefEq (← inferType compacted) expected) do
    throwError "exact_poly_nf_compact% produced an expression with the wrong type"
  return compacted

end Erdos993Lean.Analytic.V213.VarianceResponse.ExactPolyNFCompact

-- Imported support declarations; this file contains no polynomial theorem.
#check Erdos993Lean.BCFG.Bi
#print axioms Erdos993Lean.BCFG.Bi
#check mkRat
#print axioms mkRat
