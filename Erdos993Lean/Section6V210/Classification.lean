module

public import Erdos993Lean.Section6V210.Base
public import Lean.Elab.Tactic.Omega

/-! Parameter classification of version 2.10 of the manuscript. Core/Std only; kernel `decide`.

No graph-to-window statement is asserted here. -/

@[expose] public section

namespace Erdos993Lean.Section6V210

def PaperDomain (n a k : Nat) : Prop :=
  1 ≤ n ∧ n ≤ 24 ∧ (n+1)/2 ≤ a ∧ a ≤ n-1 ∧
  (n+3)/4 < k ∧ k < min a ((n+2*a+3)/6)

def IntegerDomain (a c k : Nat) : Prop :=
  c ≤ a ∧ 1 ≤ c ∧ a+c ≤ 24 ∧ a+c+4 ≤ 4*k ∧ 6*k+3 ≤ 3*a+c

instance (a c k : Nat) : Decidable (IntegerDomain a c k) := by
  unfold IntegerDomain
  infer_instance

/-- Equation p1:eq:domain iff flx:eq:conds, with natural c=n-a. -/
theorem paperDomain_iff (n a k : Nat) :
    PaperDomain n a k ↔ IntegerDomain a (n-a) k := by
  unfold PaperDomain IntegerDomain
  omega

theorem integerDomain_bounds {a c k : Nat} (h : IntegerDomain a c k) :
    3 ≤ k ∧ k ≤ 11 ∧ a ≤ 23 ∧ c ≤ 12 := by
  unfold IntegerDomain at h
  omega

/-- The minimum in the paper's domain is always H on its n,a range. -/
theorem window_min_eq_H {n a : Nat}
    (hn : 1 ≤ n) (ha : (n+1)/2 ≤ a) :
    min a ((n+2*a+3)/6) = (n+2*a+3)/6 := by
  omega

def atRank (k : Nat) : List Triple := (List.range 25).flatMap fun a =>
  ((List.range 13).filter (fun c => decide (IntegerDomain a c k))).map
    (fun c => mkTriple a c k)

def allTriples : List Triple := (levels 3 11).flatMap atRank

/-- The finite generator includes exactly the original domain at a fixed rank. -/
theorem mem_atRank_iff (t : Triple) :
    t ∈ atRank t.k ↔ PaperDomain t.n t.a t.k := by
  constructor
  · intro ht
    rcases List.mem_flatMap.mp ht with ⟨a, _, ht⟩
    rcases List.mem_map.mp ht with ⟨c, hc, heq⟩
    have hd : IntegerDomain a c t.k := of_decide_eq_true (List.mem_filter.mp hc).2
    have hn := congrArg Triple.n heq
    have ha := congrArg Triple.a heq
    simp only [mkTriple] at hn ha
    apply (paperDomain_iff t.n t.a t.k).mpr
    unfold IntegerDomain at hd ⊢
    omega
  · intro hd
    have hi := (paperDomain_iff t.n t.a t.k).mp hd
    have hb := integerDomain_bounds hi
    apply List.mem_flatMap.mpr
    refine ⟨t.a, List.mem_range.mpr (by omega), ?_⟩
    apply List.mem_map.mpr
    refine ⟨t.n-t.a, ?_, ?_⟩
    · apply List.mem_filter.mpr
      exact ⟨List.mem_range.mpr (by omega), by simp [hi]⟩
    · have hn : t.a+(t.n-t.a) = t.n := by
        unfold PaperDomain at hd
        omega
      cases t
      simp_all [mkTriple]

theorem mem_levels_iff (lo hi x : Nat) :
    x ∈ levels lo hi ↔ lo ≤ x ∧ x ≤ hi := by
  simp only [levels, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · intro h
    exact ⟨x-lo, by omega, by omega⟩

theorem mem_atRank_rank {t : Triple} {k : Nat} (h : t ∈ atRank k) : t.k = k := by
  rcases List.mem_flatMap.mp h with ⟨a, _, h⟩
  rcases List.mem_map.mp h with ⟨c, _, heq⟩
  exact (congrArg Triple.k heq).symm

/-- Exact coverage, not just a count of a list satisfying some checks. -/
theorem mem_allTriples_iff (t : Triple) :
    t ∈ allTriples ↔ PaperDomain t.n t.a t.k := by
  constructor
  · intro ht
    rcases List.mem_flatMap.mp ht with ⟨k, _, h⟩
    have hk := mem_atRank_rank h
    rw [← hk] at h
    exact (mem_atRank_iff t).mp h
  · intro hd
    have hb := integerDomain_bounds ((paperDomain_iff t.n t.a t.k).mp hd)
    exact List.mem_flatMap.mpr ⟨t.k, (mem_levels_iff 3 11 t.k).mpr ⟨hb.1,hb.2.1⟩,
      (mem_atRank_iff t).mpr hd⟩

def c1 (k : Nat) : Nat := [0,0,0,1,3,5,7,8,8,7,5,3][k]?.getD 0
def c2 (k : Nat) : Nat := [0,0,0,2,3,4,4,5,5,5,5,4][k]?.getD 0
def isP1 (t : Triple) : Bool := decide (2*t.k+1 ≤ t.a)
def isP2 (t : Triple) : Bool := decide (t.a = 2*t.k ∧ t.n-t.a ≤ c2 t.k)
def isException (t : Triple) : Bool := t == ⟨24,15,7⟩
def isP3 (t : Triple) : Bool := !(isP1 t || isP2 t)
def isRising1 (t : Triple) : Bool := isP1 t && !isException t

def branches (t : Triple) : List Bool :=
  [isRising1 t, isP2 t, catalanTriples.contains t, familyTriples.contains t]

def classificationOK (k : Nat) : Bool := (atRank k).all fun t =>
  decide (((branches t).filter (fun b => b)).length = 1)

theorem classification_rank3 : classificationOK 3 = true := by decide +kernel
theorem classification_rank4 : classificationOK 4 = true := by decide +kernel
theorem classification_rank5 : classificationOK 5 = true := by decide +kernel
theorem classification_rank6 : classificationOK 6 = true := by decide +kernel
theorem classification_rank7 : classificationOK 7 = true := by decide +kernel
theorem classification_rank8 : classificationOK 8 = true := by decide +kernel
theorem classification_rank9 : classificationOK 9 = true := by decide +kernel
theorem classification_rank10 : classificationOK 10 = true := by decide +kernel
theorem classification_rank11 : classificationOK 11 = true := by decide +kernel

theorem classification_all_ranks {k : Nat} (hk : 3 ≤ k ∧ k ≤ 11) :
    classificationOK k = true := by
  have h : k=3 ∨ k=4 ∨ k=5 ∨ k=6 ∨ k=7 ∨ k=8 ∨ k=9 ∨ k=10 ∨ k=11 := by omega
  rcases h with h | h | h | h | h | h | h | h | h
  · subst k; exact classification_rank3
  · subst k; exact classification_rank4
  · subst k; exact classification_rank5
  · subst k; exact classification_rank6
  · subst k; exact classification_rank7
  · subst k; exact classification_rank8
  · subst k; exact classification_rank9
  · subst k; exact classification_rank10
  · subst k; exact classification_rank11

/-- Every original-domain triple has exactly one of the four finite routes.
This is a classification theorem, not yet an independent-set inequality. -/
theorem unique_route {t : Triple} (hd : PaperDomain t.n t.a t.k) :
    ((branches t).filter (fun b => b)).length = 1 := by
  have hb := integerDomain_bounds ((paperDomain_iff t.n t.a t.k).mp hd)
  have hc := classification_all_ranks ⟨hb.1, hb.2.1⟩
  unfold classificationOK at hc
  have hr := List.all_eq_true.mp hc t ((mem_atRank_iff t).mpr hd)
  exact of_decide_eq_true hr

theorem rank_sizes : (levels 3 11).map (fun k => (atRank k).length) =
    [1,8,21,40,63,40,21,8,1] := by decide +kernel
theorem domain_size : allTriples.length = 203 := by decide +kernel
theorem domain_nodup : allTriples.Nodup := by decide +kernel
theorem p1_size : (allTriples.filter isP1).length = 145 := by decide +kernel
theorem p2_size : (allTriples.filter isP2).length = 16 := by decide +kernel
theorem p3_size : (allTriples.filter isP3).length = 42 := by decide +kernel
theorem rising1_size : (allTriples.filter isRising1).length = 144 := by decide +kernel
theorem families_size : familyTriples.length = 35 := by decide +kernel
theorem catalan_size : catalanTriples.length = 8 := by decide +kernel
theorem families_nodup : familyTriples.Nodup := by decide +kernel
theorem catalan_nodup : catalanTriples.Nodup := by decide +kernel
theorem named_triples_are_in_domain :
    (familyTriples ++ catalanTriples).all (fun t =>
      decide (IntegerDomain t.a (t.n-t.a) t.k)) = true := by decide +kernel

/-- Exact r=0/1/2 classification, avoiding truncated subtraction at a>2k. -/
theorem non_p1_r_counts :
    [0,1,2].map (fun r => (allTriples.filter (fun t =>
      decide (t.a+r = 2*t.k))).length) = [32,18,8] := by decide +kernel

/-- The finite corner hypothesis used by Propositions class1 and class2. -/
theorem rising1_corner_routing :
    (allTriples.filter isRising1).all (fun t => decide (t.n-t.a ≤ c1 t.k)) = true := by decide +kernel

end Erdos993Lean.Section6V210
