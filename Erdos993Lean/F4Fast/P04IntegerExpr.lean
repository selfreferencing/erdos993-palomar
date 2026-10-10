module

public import Erdos993Lean.F4Fast.P04WholePolynomial

/-! The finite polynomial calculation takes only integer syntax. Rat constants
are introduced by erase solely in the structural soundness theorem; no Rat
value or Rat numerator/denominator projection occurs in IntExpr.encode.
-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.F4Fast.P04Int
open Erdos993Lean.BCFG

inductive IntExpr where
  | constant : Int → Int → IntExpr
  | first : IntExpr
  | second : IntExpr
  | add : IntExpr → IntExpr → IntExpr
  | neg : IntExpr → IntExpr
  | mul : IntExpr → IntExpr → IntExpr
  | pow : IntExpr → Nat → IntExpr
  deriving Repr

namespace IntExpr

def erase : IntExpr → Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr
  | .constant n d => .constant ((n : Rat)/(d : Rat))
  | .first => .first
  | .second => .second
  | .add a b => .add (erase a) (erase b)
  | .neg a => .neg (erase a)
  | .mul a b => .mul (erase a) (erase b)
  | .pow a n => .pow (erase a) n

def valid : IntExpr → Prop
  | .constant _ d => 0 < d
  | .first => True
  | .second => True
  | .add a b => valid a ∧ valid b
  | .neg a => valid a
  | .mul a b => valid a ∧ valid b
  | .pow a _ => valid a

def encode : IntExpr → WholeBi → WholeBi → WholeBi
  | .constant n d, _, _ => ⟨[[n]], d⟩
  | .first, x, _ => x
  | .second, _, y => y
  | .add a b, x, y => WholeBi.add (encode a x y) (encode b x y)
  | .neg a, x, y => WholeBi.neg (encode a x y)
  | .mul a b, x, y => WholeBi.mul (encode a x y) (encode b x y)
  | .pow a n, x, y => WholeBi.pow (encode a x y) n

theorem recover_constant (n d : Int) :
    WholeBi.recover ⟨[[n]], d⟩ = [[(n : Rat)/(d : Rat)]] := by
  simp only [WholeBi.recover, IBi.castRat, IUni.castRat, List.map_cons,
    List.map_nil, rscale, Uni.scale, div_eq_mul_inv, one_mul]
  rw [mul_comm]

theorem encode_valid (e : IntExpr) (x y : WholeBi)
    (he : valid e) (hx : WholeBi.valid x) (hy : WholeBi.valid y) :
    WholeBi.valid (encode e x y) := by
  induction e with
  | constant n d => exact he
  | first => exact hx
  | second => exact hy
  | add a b ha hb => exact WholeBi.valid_add _ _ (ha he.1) (hb he.2)
  | neg a ha => exact WholeBi.valid_neg _ (ha he)
  | mul a b ha hb => exact WholeBi.valid_mul _ _ (ha he.1) (hb he.2)
  | pow a n ha => exact WholeBi.valid_pow _ n (ha he)

theorem encode_recover (e : IntExpr) (x y : WholeBi)
    (he : valid e) (hx : WholeBi.valid x) (hy : WholeBi.valid y) :
    WholeBi.recover (encode e x y) =
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode
        (erase e) (WholeBi.recover x) (WholeBi.recover y) := by
  induction e with
  | constant n d => exact recover_constant n d
  | first => rfl
  | second => rfl
  | add a b ha hb =>
    rw [encode, WholeBi.recover_add _ _ (encode_valid a x y he.1 hx hy)
      (encode_valid b x y he.2 hx hy), ha he.1, hb he.2, erase,
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode]
  | neg a ha =>
    rw [encode, WholeBi.recover_neg, ha he, erase,
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode]
  | mul a b ha hb =>
    rw [encode, WholeBi.recover_mul, ha he.1, hb he.2, erase,
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode]
  | pow a n ha =>
    rw [encode, WholeBi.recover_pow, ha he, erase,
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode]

theorem chart_eq_recover (e : IntExpr)
    (source : Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr)
    (l h v w : Rat) (x y : WholeBi) (he : valid e)
    (hx : WholeBi.valid x) (hy : WholeBi.valid y)
    (herase : erase e = source)
    (hxr : WholeBi.recover x = [[l],[h-l]])
    (hyr : WholeBi.recover y = [[v,w-v]]) :
    Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.chart source l h v w =
      WholeBi.recover (encode e x y) := by
  rw [encode_recover e x y he hx hy, herase, hxr, hyr]
  rfl

end IntExpr
end Erdos993Lean.F4Fast.P04Int

#print axioms Erdos993Lean.F4Fast.P04Int.IntExpr.recover_constant
#print axioms Erdos993Lean.F4Fast.P04Int.IntExpr.encode_valid
#print axioms Erdos993Lean.F4Fast.P04Int.IntExpr.encode_recover
#print axioms Erdos993Lean.F4Fast.P04Int.IntExpr.chart_eq_recover
