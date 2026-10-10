module

public import Erdos993Lean.ExactComparisons.Checker

/-! Exact rational worksheets of Appendix F of version 2.10 of the manuscript. No assertion here
identifies a rational log/exp envelope with the transcendental function.
Log envelopes are implemented on the checked use-domain 1 ≤ z < 8. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All

def rmin (a b : Rat) : Rat := if a ≤ b then a else b
def rmax (a b : Rat) : Rat := if a ≤ b then b else a
def rabs (a : Rat) : Rat := if 0 ≤ a then a else -a

def seriesS (w : Rat) : Rat := 2 * (w + w^3/3 + w^5/5)
def seriesT (w : Rat) : Rat := seriesS w + 2*w^7/(7*(1-w^2))
def polyP3 (x : Rat) : Rat := 120+60*x+12*x^2+x^3
def polyP4 (x : Rat) : Rat := 1680+840*x+180*x^2+20*x^3+x^4
def expLower (y : Rat) : Rat := (polyP4 (y/4) / polyP4 (-y/4))^4
def expUpper (y : Rat) : Rat := (polyP3 (y/4) / polyP3 (-y/4))^4
def expFive (x : Rat) : Rat := 1+x+x^2/2+x^3/6+x^4/24+x^5/120

/-- On [1,8), these branches are exactly the paper's dyadic reduction. -/
def logIndex (z : Rat) : Nat := if z < 2 then 0 else if z < 4 then 1 else 2
def logReduced (z : Rat) : Rat := z / (2^(logIndex z))
def logAnchor (z : Rat) : Rat :=
  if logReduced z < 5/4 then 1 else if logReduced z < 3/2 then 5/4 else 3/2
def logW (z : Rat) : Rat :=
  let v := logReduced z / logAnchor z
  (v-1)/(v+1)
def anchorLower (c : Rat) : Rat :=
  if c = 1 then 0 else if c = 5/4 then 2231434/10000000 else 4054650/10000000
def anchorUpper (c : Rat) : Rat :=
  if c = 1 then 0 else if c = 5/4 then 2231436/10000000 else 4054652/10000000
def logLower (z : Rat) : Rat :=
  (logIndex z : Rat)*(6931467/10000000) + anchorLower (logAnchor z) + seriesS (logW z)
def logUpper (z : Rat) : Rat :=
  (logIndex z : Rat)*(6931472/10000000) + anchorUpper (logAnchor z) + seriesT (logW z)
def logUseOK (z : Rat) : Bool := decide (1 ≤ z ∧ z < 8)
def expUseOK (y : Rat) : Bool := decide (0 ≤ y ∧ y ≤ 3)

def nFour (q D : Rat) : Rat :=
  D*(40+20*q-46*q^2-13*q^3-7*q^4)+48*q^2-96*q
def nFive (q D : Rat) : Rat :=
  D*(40-20*q-52*q^2+40*q^3-18*q^4-5*q^5)-48*q^3+144*q^2-96*q
def cubicC (z : Rat) : Rat := 4*z^3-8*z^2-12*z-3

structure EPoint where
  y : Rat
  lo : Rat
  hi : Rat
structure BPoint where
  lam : Rat
  lo : Rat
  hi : Rat
structure PPoint where
  lam : Rat
  y : Rat
  lo : Rat
  hi : Rat
structure Point where
  e : EPoint
  b : BPoint
  f : PPoint

def zeroParent (b : BPoint) : PPoint := ⟨b.lam,0,b.lo,b.hi⟩
def pointOK (p : Point) : Bool := decide (p.f.lam = p.b.lam ∧ p.f.y = p.e.y)
def qAt (lam : Rat) : Rat := lam/(1+lam)
def pMinus (p : Point) : Rat := p.b.lam/(p.e.hi+p.b.lam)
def pPlus (p : Point) : Rat := p.b.lam/(p.e.lo+p.b.lam)
def ellMinus (D : Rat) (p : Point) : Rat :=
  p.e.lo/p.b.lam - p.e.y*((1-pMinus p)/((5*D/12)*p.b.lo)+pMinus p/p.f.lo)
def jCap (D : Rat) : Rat := if D = 6/5 ∨ D = 7/5 then 1/3 else 1/2

def capRightOK (D u : Rat) : Bool := decide
  ((D = 6/5 ∧ u = 263/200) ∨ (D = 7/5 ∧ u = 3/2) ∨
   (D = 8/5 ∧ u = 7/4) ∨ (D = 9/5 ∧ u = 2) ∨ (D = 21/10 ∧ u = 7/3))

structure CRow where
  D : Rat
  left : Point
  right : Point

def cRowOK (r : CRow) : Bool :=
  pointOK r.left && pointOK r.right && capRightOK r.D r.left.b.lam &&
  decide (r.left.b.lam = r.right.b.lam ∧ 0 ≤ r.left.e.y ∧
    r.left.e.y < r.right.e.y ∧ r.right.e.y ≤ 5/4)
def faceEll (r : CRow) : Rat :=
  rmin (ellMinus r.D r.left) (ellMinus r.D r.right) - (9/16)*(r.right.e.y-r.left.e.y)^2
def faceL0 (r : CRow) : Rat := rmin 0 (faceEll r)
def faceDen (r : CRow) : Rat := 1+jCap r.D*faceL0 r
def faceS0 (r : CRow) : Rat := rmax 0 (1-1/r.left.e.lo-pPlus r.left)
def faceBalance (r : CRow) : Rat :=
  2*(faceS0 r)^2 + (5/7)*r.left.b.hi*pPlus r.left*faceL0 r/faceDen r

def rhoMinus (p : Point) : Rat := qAt p.b.lam*p.f.lo/(pMinus p*p.b.hi)
def rhoPlus (p : Point) : Rat := rmin 1 (qAt p.b.lam*p.f.hi/(pPlus p*p.b.lo))
def kPlus (D : Rat) (p : Point) : Rat := (1-pMinus p)/D+(5/12)*p.b.hi*pMinus p/p.f.lo
def omegaAt (rho : Rat) : Rat := 1-(7*rho+5/rho)/12

structure ARow where
  D : Rat
  ac : Point
  ad : Point
  bd : Point
  mid : EPoint
  m : Rat

def aRowOK (r : ARow) : Bool :=
  pointOK r.ac && pointOK r.ad && pointOK r.bd && decide
  (0 < r.D ∧ 1/3 ≤ r.ac.b.lam ∧ r.ac.b.lam < r.bd.b.lam ∧ r.bd.b.lam ≤ 7/3 ∧
   r.ad.b.lam = r.ac.b.lam ∧ r.ad.e.y = r.bd.e.y ∧
   0 ≤ r.ac.e.y ∧ r.ac.e.y < r.bd.e.y ∧ r.bd.e.y ≤ 3 ∧
   r.mid.y = (r.ac.e.y+r.bd.e.y)/2)
def cellWidth (r : ARow) : Rat := (r.bd.e.y-r.ac.e.y)/2
def cellK (r : ARow) : Rat :=
  rmax (kPlus r.D r.ad) (kPlus r.D r.bd)+(15/256)*(r.bd.b.lam-r.ac.b.lam)^2
def cellDelta (r : ARow) : Rat :=
  (5/12)*(r.bd.b.lo*r.ac.e.lo/r.bd.b.lam+
    2*(r.bd.b.lo/qAt r.bd.b.lam)^2/(1+r.bd.b.lam))-r.bd.e.y*cellK r
def cellT (r : ARow) : Rat :=
  ((1+r.bd.b.lam)/(r.mid.hi+r.bd.b.lam)-1)/r.D +
  (7/12)*r.mid.y*r.mid.lo/((1+r.bd.b.lam)*r.bd.b.hi)
def cellTMinus (r : ARow) : Rat :=
  -(1+r.bd.b.lam)*r.mid.hi/(r.D*(r.mid.lo+r.bd.b.lam)^2) +
  (7/12)*(1+r.mid.y)*r.mid.lo/((1+r.bd.b.lam)*r.bd.b.hi)
def cellTPlus (r : ARow) : Rat :=
  -(1+r.bd.b.lam)*r.mid.lo/(r.D*(r.mid.hi+r.bd.b.lam)^2) +
  (7/12)*(1+r.mid.y)*r.mid.hi/((1+r.bd.b.lam)*r.bd.b.lo)
def cellM0 (r : ARow) : Rat :=
  (7/12)*(2+r.ac.e.y)*r.ac.e.lo/((1+r.bd.b.lam)*r.bd.b.hi)-1/10
def cellJ0 (r : ARow) : Rat := rmax (rabs (cellTMinus r)) (rabs (cellTPlus r))
def cellPsi (r : ARow) : Rat :=
  if cellJ0 r ≤ cellM0 r*cellWidth r then (cellJ0 r)^2/(2*cellM0 r)
  else cellJ0 r*cellWidth r-cellM0 r*(cellWidth r)^2/2
def cellEpsilon (r : ARow) : Rat := 7/12-(12/5)*r.m^2
def cellBalance (r : ARow) : Rat :=
  rmin (omegaAt (rhoMinus r.bd)) (omegaAt (rhoPlus r.ac)) + cellT r-cellPsi r +
  cellEpsilon r*rmax 0 (1-r.bd.e.y/r.ac.b.lo) -
  (r.bd.e.y/qAt r.ac.b.lam)*(rmax 0 (cellK r-r.m))^2/cellDelta r

def coverFrom (hi : Rat) : Rat → List (Rat × Rat) → Bool
  | lo, [] => decide (lo = hi)
  | lo, (a,b)::rest => decide (a = lo ∧ a < b) && coverFrom hi b rest
def coverOK (lo hi : Rat) (rows : List (Rat × Rat)) : Bool :=
  !rows.isEmpty && coverFrom hi lo rows

end Erdos993Lean.ExactComparisons.F3All
