module

public import F4Heavy.Analysis.EFormulaUCore

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def eUPiece (r : Row) (lam x h L : ℝ) (i : Fin 5) : ℝ :=
  let B := eBaseDen lam x
  let T := eLogDen x
  let pn := lam*x
  let u := eParentNumerator r lam x+B-pn
  let n := (15/16)*eKNumerator r lam x-(1+lam)*u
  let c := pn*(2*u-(alpha r lam+beta r lam)*B)
  let d := (gamma r lam-delta r lam)*B^2*T-pn*eUpperNumerator r lam x*u
  let G := delta r lam*B^2*T+d*L
  match i with
  | 0 => 4*G*pn*n*(1+x)
  | 1 => 4*G*eLowerNumerator r lam x*pn*beta r lam*h*(1+lam)*B
  | 2 => 4*delta r lam*eLowerNumerator r lam x*c*T*h*(1+lam)*B^2
  | 3 => 4*delta r lam*eLowerNumerator r lam x*d*h^2*(1+lam)*B^2
  | 4 => eLowerNumerator r lam x*L*c^2*(1+lam)*T

theorem eUNumerator_pieces (r : Row) (lam x h L : ℝ) :
    eUNumerator r lam x h L = eUPiece r lam x h L 0+eUPiece r lam x h L 1+
      eUPiece r lam x h L 2+eUPiece r lam x h L 3-eUPiece r lam x h L 4 := by
  unfold eUNumerator eUPiece
  ring

end F4Heavy.Analysis
