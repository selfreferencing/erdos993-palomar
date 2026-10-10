module

public import Erdos993Lean.Analytic.V213.SmallForestPrintedData
public import Erdos993Lean.Analytic.V213.SmallForestCatalanGraph
public import Erdos993Lean.Analytic.V213.SmallForestAffineSigned

/-! Exact current-paper rational operands, with generic real interpretation.
The descending-factorial implementation avoids exponential Pascal reduction.
No finite assertion is used in these interpretation proofs. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite

open Finset SmallForestPrinted

def fastChoose (m j : ℕ) : ℕ := m.descFactorial j / j.factorial

theorem fastChoose_eq_choose (m j : ℕ) : fastChoose m j = m.choose j := by
  exact (Nat.choose_eq_descFactorial_div_factorial m j).symm

def chooseQ (m j : ℕ) : ℚ := (fastChoose m j : ℚ)
def binomQ (m : ℕ) (j : ℤ) : ℚ := if 0 ≤ j then chooseQ m j.toNat else 0
def GQ (w : ℚ) (j : ℤ) (m : ℕ) : ℚ :=
  binomQ m j - w * binomQ m (j-1) - (1-w) * binomQ m (j+1)
def catQ (j : ℕ) : ℚ := chooseQ (2*j) j / ((j : ℚ)+1)
def risingQ (a c k : ℕ) : ℚ := chooseQ a k - chooseQ a (k-1) -
  ∑ h ∈ Icc 1 (k-1), chooseQ c h * catQ (k-h-1)
def adjustedQ (p : ℚ) (h : ℕ) : ℚ := if 0 ≤ p then p else p / chooseQ h 2
def affineAQ (a c k : ℕ) (w : ℚ) (β q : ℕ → ℚ) : ℚ :=
  GQ w (k : ℤ) a + ∑ h ∈ Icc 1 (k+1),
    (β h * chooseQ c h + q h * ((a : ℚ)-h) * chooseQ (c-1) h)
def affineBQ (a c k : ℕ) (β q : ℕ → ℚ) : ℚ :=
  q 1 + ∑ h ∈ Icc 2 (k+1),
    (q h * chooseQ (c-2) (h-1) - adjustedQ (β h + q h*((a : ℚ)-h)) h * chooseQ (c-2) (h-2))

theorem chooseQ_eq (m j : ℕ) : chooseQ m j = (m.choose j : ℚ) := by
  simp only [chooseQ, fastChoose_eq_choose]

theorem catQ_eq (j : ℕ) : catQ j = SmallForestCatalan.cat j := by
  simp only [catQ, chooseQ_eq, SmallForestCatalan.cat]

theorem risingQ_eq (a c k : ℕ) : risingQ a c k = SmallForestCatalan.rising a c k := by
  simp only [risingQ, chooseQ_eq, catQ_eq, SmallForestCatalan.rising]

theorem binomQ_cast (m : ℕ) (j : ℤ) : (binomQ m j : ℝ) = SmallForest.binom m j := by
  by_cases hj : 0 ≤ j <;> simp [binomQ, SmallForest.binom, hj, chooseQ_eq]

theorem GQ_cast (w : ℚ) (j : ℤ) (m : ℕ) :
    (GQ w j m : ℝ) = SmallForest.G (w : ℝ) j m := by
  simp only [GQ, SmallForest.G, Rat.cast_sub, Rat.cast_mul, Rat.cast_one, binomQ_cast]

theorem catQ_cast (j : ℕ) : (catQ j : ℝ) = SmallForestCatalan.realCatalan j := by
  rw [catQ_eq]
  rfl

theorem adjustedQ_cast (p : ℚ) (h : ℕ) :
    (adjustedQ p h : ℝ) = SmallForest.adjusted (p : ℝ) h := by
  by_cases hp : 0 ≤ p
  · have hr : (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    simp [adjustedQ, SmallForest.adjusted, hp, hr]
  · have hr : ¬ (0 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    simp [adjustedQ, SmallForest.adjusted, hp, hr, chooseQ_eq]

theorem affineAQ_cast (a c k : ℕ) (w : ℚ) (β q : ℕ → ℚ) :
    (affineAQ a c k w β q : ℝ) =
      SmallForest.affineA a c k (w : ℝ) (fun h => (β h : ℝ)) (fun h => (q h : ℝ)) := by
  simp only [affineAQ, SmallForest.affineA, Rat.cast_add, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, GQ_cast, chooseQ_eq]

theorem affineBQ_cast (a c k : ℕ) (β q : ℕ → ℚ) :
    (affineBQ a c k β q : ℝ) =
      SmallForest.affineB a c k (fun h => (β h : ℝ)) (fun h => (q h : ℝ)) := by
  simp only [affineBQ, SmallForest.affineB, Rat.cast_add, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_sub, Rat.cast_natCast, adjustedQ_cast, chooseQ_eq]

/-- The four-case cuts displayed before the current affine Catalan table. -/
def catalanLineQ (k s t h : ℕ) : ℚ × ℚ :=
  if h < k then
    if h ≤ s then (catQ (k-h) * (1-2*((k-h : ℕ) : ℚ)), catQ (k-h))
    else if h ≤ t then (catQ (k-h-1) * (1-2*((k-h : ℕ) : ℚ)), catQ (k-h-1))
    else (-catQ (k-h-1),0)
  else (0,0)

def catalanAQ (a c k s t : ℕ) : ℚ :=
  affineAQ a c k 1 (fun h => (catalanLineQ k s t h).1) (fun h => (catalanLineQ k s t h).2)
def catalanBQ (a c k s t : ℕ) : ℚ :=
  affineBQ a c k (fun h => (catalanLineQ k s t h).1) (fun h => (catalanLineQ k s t h).2)

def horizontalQ (j : ℕ) : ℚ := horizontalFloors[j-1]?.getD 0

/-- Exactly equation (118) and its printed horizontal/final-level conventions.
Only the fifteen actual records will be used; no other weight is certified. -/
def familyLineQ (r : FamilyInput) (h : ℕ) : ℚ × ℚ :=
  if h = 0 then (0,0)
  else if h ≤ r.tangents.length then
    let t := r.tangents[h-1]?.getD 0
    let j := (r.k : ℤ)-h
    let q := GQ r.w (j-1) (t-1)
    (GQ r.w j t-q*t,q)
  else if h < r.k then
    if r.w = (1/2 : ℚ) then
      (min (horizontalQ (r.k-h)) (GQ r.w ((r.k : ℤ)-h) (r.a-h)),0)
    else (-2/3,0)
  else if h = r.k then (1-(1-r.w)*((r.a : ℚ)-r.k),0)
  else if h = r.k+1 then (-(1-r.w),0)
  else (0,0)

def familyAQ (r : FamilyInput) (c : ℕ) : ℚ :=
  affineAQ r.a c r.k r.w (fun h => (familyLineQ r h).1) (fun h => (familyLineQ r h).2)
def familyBQ (r : FamilyInput) (c : ℕ) : ℚ :=
  affineBQ r.a c r.k (fun h => (familyLineQ r h).1) (fun h => (familyLineQ r h).2)

def differenceQ (f : ℕ → ℚ) : ℕ → ℕ → ℚ
  | 0,c => f c
  | d+1,c => differenceQ f d (c+1)-differenceQ f d c

def RisingFacts (r : RisingInput) : Prop :=
  risingQ (2*r.k+r.aOffset) r.c r.k = (r.margin : ℚ) ∧ 0 < r.margin ∧
  1 ≤ r.k ∧ 2*r.k-3 ≤ 2*r.k+r.aOffset

def CatalanFacts (r : CatalanInput) : Prop :=
  catalanAQ r.a r.c r.k r.s r.t = r.constant ∧
  catalanBQ r.a r.c r.k r.s r.t = r.slope ∧
  36 ≤ r.constant ∧ 0 < r.slope ∧ 2 ≤ r.c ∧ 1 ≤ r.k

def FamilyEndpointFacts (r : FamilyInput) : Prop :=
  familyAQ r r.lo = r.constantLo ∧ familyAQ r r.hi = r.constantHi ∧
  familyBQ r r.lo = r.slopeLo ∧
  26 ≤ min r.constantLo r.constantHi + ((r.hi : ℚ)-1)*min r.slopeLo 0 ∧
  2 ≤ r.lo ∧ r.lo ≤ r.hi ∧ 1 ≤ r.k ∧ 0 ≤ r.w ∧ r.w ≤ 1

/-- Direct verification on the printed integer interval, not a new input catalogue. -/
def FamilyMargins (r : FamilyInput) : Prop :=
  ∀ c ∈ Icc r.lo r.hi, 26 ≤ familyAQ r c + ((c : ℚ)-1)*min (familyBQ r c) 0

def DifferenceFacts (r : FamilyInput) (d : DifferenceInput) : Prop :=
  (List.range d.constantDifferences.length).map (fun i => differenceQ (familyAQ r) (i+2) r.lo) = d.constantDifferences ∧
  (List.range d.slopeDifferences.length).map (fun i => differenceQ (familyBQ r) (i+1) r.lo) = d.slopeDifferences ∧
  (∀ x ∈ d.constantDifferences, x ≤ 0) ∧ (∀ x ∈ d.slopeDifferences, 0 < x)

instance (r : RisingInput) : Decidable (RisingFacts r) := by unfold RisingFacts; infer_instance
instance (r : CatalanInput) : Decidable (CatalanFacts r) := by unfold CatalanFacts; infer_instance
instance (r : FamilyInput) : Decidable (FamilyEndpointFacts r) := by unfold FamilyEndpointFacts; infer_instance
instance (r : FamilyInput) : Decidable (FamilyMargins r) := by unfold FamilyMargins; infer_instance
instance (r : FamilyInput) (d : DifferenceInput) : Decidable (DifferenceFacts r d) := by
  unfold DifferenceFacts
  infer_instance

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.fastChoose_eq_choose
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.fastChoose_eq_choose
#check Erdos993Lean.Analytic.V213.SmallForestFinite.chooseQ_eq
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.chooseQ_eq
#check Erdos993Lean.Analytic.V213.SmallForestFinite.catQ_eq
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.catQ_eq
#check Erdos993Lean.Analytic.V213.SmallForestFinite.risingQ_eq
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.risingQ_eq
#check Erdos993Lean.Analytic.V213.SmallForestFinite.binomQ_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.binomQ_cast
#check Erdos993Lean.Analytic.V213.SmallForestFinite.GQ_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.GQ_cast
#check Erdos993Lean.Analytic.V213.SmallForestFinite.catQ_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.catQ_cast
#check Erdos993Lean.Analytic.V213.SmallForestFinite.adjustedQ_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.adjustedQ_cast
#check Erdos993Lean.Analytic.V213.SmallForestFinite.affineAQ_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.affineAQ_cast
#check Erdos993Lean.Analytic.V213.SmallForestFinite.affineBQ_cast
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.affineBQ_cast
