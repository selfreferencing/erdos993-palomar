module

public import Erdos993Lean.Analytic.V213.SmallForestClassification
public import Erdos993Lean.Analytic.V213.SmallForestPrintedData

/-!
This reads the existing accepted symbolic C2 catalogue;
it does not create an enumerated list of triples or use any old scalar checker.
The nine bounded rank obligations route to the current printed literal inputs.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestPrinted

abbrev OldTriple := Erdos993Lean.Section6V210.Triple

def currentRising (t : OldTriple) : Bool := risingInputs.any fun r =>
  decide (r.k = t.k ∧ 2*r.k+r.aOffset ≤ t.a ∧ t.n-t.a ≤ r.c)

def currentNamedCatalan (t : OldTriple) : Bool := namedCatalanInputs.any fun r =>
  decide (r.a = t.a ∧ r.c = t.n-t.a ∧ r.k = t.k)

def currentNewtonCatalan (t : OldTriple) : Bool := a14Indices.any fun x =>
  decide (t.a = 14 ∧ t.n-t.a = 7+x ∧ t.k = 7)

def currentFamily (t : OldTriple) : Bool := familyInputs.any fun r =>
  decide (r.a = t.a ∧ r.k = t.k ∧ r.lo ≤ t.n-t.a ∧ t.n-t.a ≤ r.hi)

def currentRouteBool (t : OldTriple) : Bool :=
  currentRising t || (currentNamedCatalan t || (currentNewtonCatalan t || currentFamily t))

def currentRouteBits (t : OldTriple) : List Bool :=
  [currentRising t, currentNamedCatalan t || currentNewtonCatalan t, currentFamily t]

def currentRouteCheck (t : OldTriple) : Bool := currentRouteBool t &&
  decide (((currentRouteBits t).filter (fun b => b)).length = 1)

/-- Natural complement subtraction is interpreted only after the domain proof
or on mkTriple a c k, where it reduces exactly to c. -/
def CurrentRoute (a c k : ℕ) : Prop :=
  (∃ r ∈ risingInputs, r.k = k ∧ 2*r.k+r.aOffset ≤ a ∧ c ≤ r.c) ∨
  (∃ r ∈ namedCatalanInputs, r.a = a ∧ r.c = c ∧ r.k = k) ∨
  (∃ x ∈ a14Indices, a = 14 ∧ c = 7+x ∧ k = 7) ∨
  (∃ r ∈ familyInputs, r.a = a ∧ r.k = k ∧ r.lo ≤ c ∧ c ≤ r.hi)

theorem currentRouteBool_iff (t : OldTriple) :
    currentRouteBool t = true ↔ CurrentRoute t.a (t.n-t.a) t.k := by
  simp only [currentRouteBool, currentRising, currentNamedCatalan,
    currentNewtonCatalan, currentFamily, CurrentRoute, Bool.or_eq_true,
    List.any_eq_true, decide_eq_true_eq]

-- Nine current-domain rank checks; no unprinted evaluated record catalogue.
theorem current_rank3 : (Erdos993Lean.Section6V210.atRank 3).all currentRouteCheck = true := by decide +kernel
theorem current_rank4 : (Erdos993Lean.Section6V210.atRank 4).all currentRouteCheck = true := by decide +kernel
theorem current_rank5 : (Erdos993Lean.Section6V210.atRank 5).all currentRouteCheck = true := by decide +kernel
theorem current_rank6 : (Erdos993Lean.Section6V210.atRank 6).all currentRouteCheck = true := by decide +kernel
theorem current_rank7 : (Erdos993Lean.Section6V210.atRank 7).all currentRouteCheck = true := by decide +kernel
theorem current_rank8 : (Erdos993Lean.Section6V210.atRank 8).all currentRouteCheck = true := by decide +kernel
theorem current_rank9 : (Erdos993Lean.Section6V210.atRank 9).all currentRouteCheck = true := by decide +kernel
theorem current_rank10 : (Erdos993Lean.Section6V210.atRank 10).all currentRouteCheck = true := by decide +kernel
theorem current_rank11 : (Erdos993Lean.Section6V210.atRank 11).all currentRouteCheck = true := by decide +kernel

theorem current_rank_checked (k : ℕ) (hk : 3 ≤ k ∧ k ≤ 11) :
    (Erdos993Lean.Section6V210.atRank k).all currentRouteCheck = true := by
  have h : k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact current_rank3
  · exact current_rank4
  · exact current_rank5
  · exact current_rank6
  · exact current_rank7
  · exact current_rank8
  · exact current_rank9
  · exact current_rank10
  · exact current_rank11

theorem accepted_member_current_check (t : OldTriple)
    (ht : t ∈ Erdos993Lean.Section6V210.allTriples) : currentRouteCheck t = true := by
  change t ∈ (Erdos993Lean.Section6V210.levels 3 11).flatMap
    Erdos993Lean.Section6V210.atRank at ht
  rcases List.mem_flatMap.mp ht with ⟨k, hk, ht⟩
  unfold Erdos993Lean.Section6V210.levels at hk
  rcases List.mem_map.mp hk with ⟨i, hi, rfl⟩
  have hi' := List.mem_range.mp hi
  exact List.all_eq_true.mp (current_rank_checked (3+i) (by omega)) t ht

/-- Literal coverage for every current triple, rather than a list-count surrogate. -/
theorem currentDomain_route (a c k : ℕ) (hd : CurrentDomain a c k) : CurrentRoute a c k := by
  have hm := (mem_accepted_catalogue_iff a c k).mpr hd
  have hc := accepted_member_current_check (Erdos993Lean.Section6V210.mkTriple a c k) hm
  simp only [currentRouteCheck, Bool.and_eq_true] at hc
  have hb := hc.1
  have hr := (currentRouteBool_iff _).mp hb
  simpa only [Erdos993Lean.Section6V210.mkTriple, Nat.add_sub_cancel_left] using hr

theorem currentDomain_unique_route (a c k : ℕ) (hd : CurrentDomain a c k) :
    ((currentRouteBits (Erdos993Lean.Section6V210.mkTriple a c k)).filter (fun b => b)).length = 1 := by
  have hm := (mem_accepted_catalogue_iff a c k).mpr hd
  have hc := accepted_member_current_check (Erdos993Lean.Section6V210.mkTriple a c k) hm
  simp only [currentRouteCheck, Bool.and_eq_true] at hc
  exact of_decide_eq_true hc.2

-- The three totals refer to current routes over the same accepted 203-element
-- symbolic catalogue; they do not import the old finite arithmetic arguments.
theorem current_rising_count :
    (Erdos993Lean.Section6V210.allTriples.filter currentRising).length = 160 := by decide +kernel
theorem current_catalan_count :
    (Erdos993Lean.Section6V210.allTriples.filter
      (fun t => currentNamedCatalan t || currentNewtonCatalan t)).length = 8 := by decide +kernel
theorem current_family_count :
    (Erdos993Lean.Section6V210.allTriples.filter currentFamily).length = 35 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestPrinted

#check Erdos993Lean.Analytic.V213.SmallForestPrinted.currentRouteBool_iff
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.currentRouteBool_iff
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank3
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank3
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank4
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank4
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank5
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank5
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank6
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank6
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank7
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank7
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank8
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank8
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank9
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank9
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank10
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank10
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank11
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank11
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank_checked
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rank_checked
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.accepted_member_current_check
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.accepted_member_current_check
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.currentDomain_route
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.currentDomain_route
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.currentDomain_unique_route
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.currentDomain_unique_route
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rising_count
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_rising_count
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_catalan_count
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_catalan_count
#check Erdos993Lean.Analytic.V213.SmallForestPrinted.current_family_count
#print axioms Erdos993Lean.Analytic.V213.SmallForestPrinted.current_family_count
