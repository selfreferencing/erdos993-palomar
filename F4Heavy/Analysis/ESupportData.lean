module

public import F4Heavy.Analysis.EFormulaUCore

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def eSupportIntercept0 (r : Row) (lam : ℝ) : ℝ :=
  match r with
  | .E1 => (-79166889/50000000 : ℝ)+((-154103887/100000000 : ℝ)-(-79166889/50000000 : ℝ))*(lam-(13/10 : ℝ))/((29/20 : ℝ)-(13/10 : ℝ))+(18009/25969216 : ℝ)
  | .E2 => (-154103887/100000000 : ℝ)+((-150225069/100000000 : ℝ)-(-154103887/100000000 : ℝ))*(lam-(29/20 : ℝ))/((8/5 : ℝ)-(29/20 : ℝ))+(81/142129 : ℝ)
  | _ => 0

noncomputable def eSupportIntercept1 (r : Row) (lam : ℝ) : ℝ :=
  match r with
  | .E1 => (3500567/100000000 : ℝ)+((5922933/100000000 : ℝ)-(3500567/100000000 : ℝ))*(lam-(13/10 : ℝ))/((29/20 : ℝ)-(13/10 : ℝ))+(18009/25969216 : ℝ)
  | .E2 => (5922933/100000000 : ℝ)+((1640021/20000000 : ℝ)-(5922933/100000000 : ℝ))*(lam-(29/20 : ℝ))/((8/5 : ℝ)-(29/20 : ℝ))+(81/142129 : ℝ)
  | _ => 0

noncomputable def eSupportIntercept2 (r : Row) (lam : ℝ) : ℝ :=
  match r with
  | .E1 => (38732233/50000000 : ℝ)+((19828959/25000000 : ℝ)-(38732233/50000000 : ℝ))*(lam-(13/10 : ℝ))/((29/20 : ℝ)-(13/10 : ℝ))+(18009/25969216 : ℝ)
  | .E2 => (19828959/25000000 : ℝ)+((81122983/100000000 : ℝ)-(19828959/25000000 : ℝ))*(lam-(29/20 : ℝ))/((8/5 : ℝ)-(29/20 : ℝ))+(81/142129 : ℝ)
  | _ => 0

noncomputable def eSupportVertex (r : Row) (lam : ℝ) : Fin 4 → ℝ
  | 0 => -eSupportIntercept0 r lam/(7/3)
  | 1 => (eSupportIntercept1 r lam-eSupportIntercept0 r lam)/(7/3-3/10)
  | 2 => (eSupportIntercept2 r lam-eSupportIntercept1 r lam)/(3/10-(-8/15))
  | 3 => 1

noncomputable def eSupportHeight (r : Row) (lam : ℝ) : Fin 4 → ℝ
  | 0 => 0
  | 1 => (7/3)*eSupportVertex r lam 1+eSupportIntercept0 r lam
  | 2 => (3/10)*eSupportVertex r lam 2+eSupportIntercept1 r lam
  | 3 => (-8/15)+eSupportIntercept2 r lam

end F4Heavy.Analysis
