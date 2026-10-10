module

public meta import Mathlib.Tactic.Ring.RingNF

/-! The stock `ring_nf` conversion with an explicit initial atom order.
Independent normalizations can then produce the same raw expression. All
rewrites use Mathlib's proof-producing normalizer and are checked by Lean. -/

public meta section

open Lean Meta Elab Tactic Mathlib.Tactic

elab "bcfg_ring_nf" "[" xs:term,* "]" : conv => withMainContext do
  let atoms ← xs.getElems.mapM fun x => Term.elabTerm x none
  let cfg : RingNF.Config := { mode := .raw }
  let state ← IO.mkRef ({ atoms } : AtomM.State)
  Conv.applySimpResult
    (← AtomM.recurse state cfg.toConfig (wellBehavedDischarge := true)
      RingNF.evalExpr (RingNF.cleanup cfg)
      (← instantiateMVars (← Conv.getLhs)))
