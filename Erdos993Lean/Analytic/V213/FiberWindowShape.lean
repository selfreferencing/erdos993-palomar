module

public import Erdos993Lean.Analytic.V213.FiberWindowData
public import Erdos993Lean.Analytic.V213.FiberWindowDeficit

/-!
Full canonical shape/semantic binding for every accepted F13 window.
The source class supplies a,b,mu_D and the target; N0 is computed from
mu_D*l+2. Eq100, capped Eq102, and both Eq103 price branches are retained.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

namespace FiberWindowFormula

def sub (a b : LowMeanIntegerShape) : LowMeanIntegerShape := .add a (.neg b)

def gain (a b N : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let m := .add N (.atom (1,1))
  let o := sub (.atom (1,1)) (.pow b 2)
  let A := sub (sub (.atom (1,2)) (.div (.pow b 2) (.mul (.atom (3,1)) o)))
    (.div (.pow b 2) (.mul (.atom (12,1)) (.pow o 2)))
  .add (.add (sub (sub (.add (.mul (.pow a 2)
    (.add (sub (.mul m A) (.atom (4,1))) (.div (.atom (8,1)) m)))
    (.div (.atom (71,1)) (.mul (.atom (20,1)) m)))
    (.div (sub m (.atom (1,1))) (.mul m (sub m (.atom (2,1))))))
    (.div (.mul (.pow b 2) (sub m (.atom (1,1))))
      (.mul (.mul (.atom (6,1)) o) (sub m (.atom (2,1))))))
    (.div (.mul (.atom (4,1)) (.pow a 4)) (.atom (3,1))))
    (.div (.mul m (.pow a 6)) (.atom (18,1)))

def rate (b N : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let o := sub (.atom (1,1)) (.pow b 2)
  .add (.div (.mul o N) (.add N (.atom (1,1)))) (.neg
    (.mul (.add (.div (.atom (2,1)) (.add N (.atom (1,1))))
      (.div (.pow b 2) (.mul (.atom (3,1)) o)))
      (.div (sub (.mul (.atom (2,1)) N) (.atom (1,1)))
        (.mul (.atom (2,1)) (sub N (.atom (1,1)))))))

def bonus (a N : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .div (.mul (.pow a 2) (.add (sub (.pow N 2) N) (.atom (1,1))))
    (.mul (sub (.atom (1,1)) (.pow a 2)) N)

def taylor5 (z : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .add (.add (.add (.add (.add (.atom (1,1)) z) (.div (.pow z 2) (.atom (2,1))))
    (.div (.pow z 3) (.atom (6,1)))) (.div (.pow z 4) (.atom (24,1))))
    (.div (.pow z 5) (.atom (120,1)))

def anchor (l v phi : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .minimum (.atom (1,1)) (.mul
    (.div (.mul (.mul (.atom (2,1)) v) (.pow l 3)) (.add l (.pow v 2)))
    (taylor5 (.add (.atom (1,1)) phi)))

def inverse (x : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .div (.mul x (.add (.atom (2,1)) (.mul (.atom (3,1)) x)))
    (.add (.add (.atom (2,1)) (.mul (.atom (5,1)) x)) (.mul (.atom (2,1)) (.pow x 2)))

def minorant (delta rho w : LowMeanIntegerShape) : LowMeanIntegerShape :=
  sub (.add (.atom (1,1)) delta)
    (.div (.mul (.atom (2,1)) (.pow (sub (.atom (1,1)) w) 2)) (.mul rho w))

def price (b beta l h N X : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let psi := sub h (.mul (.atom (9,2)) (.pow (sub h (.atom (1,1))) 2))
  let target := .add b (.mul beta (sub h (.atom (1,1))))
  let base := .selectLE (.atom (0,1)) X (.mul l X)
    (.div (.mul (.mul h N) X) (sub N (.atom (2,1))))
  .maximum (.atom (0,1)) (sub (.add psi target) base)

end FiberWindowFormula

def fiberWindowShape (id : FiberWindowIdentity) (role : FiberWindowRole) : LowMeanIntegerShape :=
  let r := fiberWindowById id
  let c := fiberOuterClassById r.outerClass
  let a := LowMeanIntegerShape.atom c.skew_lower
  let b := LowMeanIntegerShape.atom c.skew_upper
  let l := LowMeanIntegerShape.atom r.l
  let N := LowMeanIntegerShape.add (.mul (.atom c.mu_D) l) (.atom (2,1))
  let phi := FiberWindowFormula.gain a b N
  let rho := FiberWindowFormula.rate b N
  let delta := FiberWindowFormula.bonus a N
  let x := FiberWindowFormula.anchor l (.atom r.v) phi
  let w := FiberWindowFormula.inverse x
  let X := FiberWindowFormula.minorant delta rho w
  match role with
  | .gain => phi
  | .rate => rho
  | .bonus => delta
  | .anchor => x
  | .inverse => w
  | .minorant => X
  | .gap => FiberWindowFormula.sub X (.atom r.X)
  | .price => FiberWindowFormula.price (.atom c.b) (.atom c.beta_prime) l (.atom r.h) N (.atom r.X)

noncomputable def fiberWindowN0 (id : FiberWindowIdentity) : ℝ :=
  lowMeanFractionReal (fiberOuterClassById (fiberWindowById id).outerClass).mu_D *
    lowMeanFractionReal (fiberWindowById id).l + 2

noncomputable def fiberWindowValue (id : FiberWindowIdentity) (role : FiberWindowRole) : ℝ :=
  let r := fiberWindowById id
  let c := fiberOuterClassById r.outerClass
  let a := lowMeanFractionReal c.skew_lower
  let b := lowMeanFractionReal c.skew_upper
  let N := fiberWindowN0 id
  let l := lowMeanFractionReal r.l
  let phi := fiberRationalGain a b N
  let rho := fiberWindowRho b N
  let delta := fiberWindowDelta a N
  let x := fiberWindowAnchor l (lowMeanFractionReal r.v) phi
  let w := fiberWindowInverse x
  match role with
  | .gain => phi
  | .rate => rho
  | .bonus => delta
  | .anchor => x
  | .inverse => w
  | .minorant => fiberWindowX a b N l (lowMeanFractionReal r.v)
  | .gap => fiberWindowX a b N l (lowMeanFractionReal r.v) - lowMeanFractionReal r.X
  | .price => fiberWindowPrice (lowMeanFractionReal c.b) (lowMeanFractionReal c.beta_prime)
      l (lowMeanFractionReal r.h) N (lowMeanFractionReal r.X)

theorem fiber_window_gain_shape_real (a b N : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (FiberWindowFormula.gain a b N) =
      fiberRationalGain (lowMeanIntegerShapeReal a) (lowMeanIntegerShapeReal b) (lowMeanIntegerShapeReal N) := by
  simp only [FiberWindowFormula.gain,FiberWindowFormula.sub,lowMeanIntegerShapeReal,
    fiberRationalGain,fiberRationalA,lowMeanFractionReal]
  norm_num
  ring

theorem fiber_window_rate_shape_real (b N : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (FiberWindowFormula.rate b N) =
      fiberWindowRho (lowMeanIntegerShapeReal b) (lowMeanIntegerShapeReal N) := by
  simp only [FiberWindowFormula.rate,FiberWindowFormula.sub,lowMeanIntegerShapeReal,
    fiberWindowRho,lowMeanFractionReal]
  norm_num
  ring

theorem fiber_window_bonus_shape_real (a N : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (FiberWindowFormula.bonus a N) =
      fiberWindowDelta (lowMeanIntegerShapeReal a) (lowMeanIntegerShapeReal N) := by
  simp only [FiberWindowFormula.bonus,FiberWindowFormula.sub,lowMeanIntegerShapeReal,
    fiberWindowDelta,lowMeanFractionReal]
  norm_num
  ring

theorem fiber_window_taylor_shape_real (z : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (FiberWindowFormula.taylor5 z) = fiberWindowTaylor5 (lowMeanIntegerShapeReal z) := by
  simp only [FiberWindowFormula.taylor5,lowMeanIntegerShapeReal,fiberWindowTaylor5,lowMeanFractionReal]
  norm_num

theorem fiber_window_anchor_shape_real (l v phi : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (FiberWindowFormula.anchor l v phi) =
      fiberWindowAnchor (lowMeanIntegerShapeReal l) (lowMeanIntegerShapeReal v) (lowMeanIntegerShapeReal phi) := by
  simp only [FiberWindowFormula.anchor,lowMeanIntegerShapeReal,fiber_window_taylor_shape_real,
    fiberWindowAnchor,lowMeanFractionReal]
  norm_num

theorem fiber_window_inverse_shape_real (x : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (FiberWindowFormula.inverse x) = fiberWindowInverse (lowMeanIntegerShapeReal x) := by
  simp only [FiberWindowFormula.inverse,lowMeanIntegerShapeReal,fiberWindowInverse,lowMeanFractionReal]
  norm_num

theorem fiber_window_shape_real (id : FiberWindowIdentity) (role : FiberWindowRole) :
    lowMeanIntegerShapeReal (fiberWindowShape id role) = fiberWindowValue id role := by
  cases role <;> simp only [fiberWindowShape,fiberWindowValue,
    fiber_window_gain_shape_real,fiber_window_rate_shape_real,fiber_window_bonus_shape_real,
    fiber_window_anchor_shape_real,fiber_window_inverse_shape_real,FiberWindowFormula.minorant,
    FiberWindowFormula.price,FiberWindowFormula.sub,lowMeanIntegerShapeReal,
    fiberWindowX,fiberWindowPrice,fiberWindowN0,lowMeanFractionReal,
    Int.cast_ofNat,Nat.cast_ofNat,Int.cast_one,Nat.cast_one,Int.cast_zero,div_one,zero_div]
  all_goals first | rfl | (congr 1 <;> simp only [fiberPsi] <;> ring)

end Erdos993Lean.Analytic.V213
