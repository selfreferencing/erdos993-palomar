module

public import Erdos993Lean.BCFG.Bivariate

/-!
Optional resource fallback only. The accepted normalization computation and
certificate statements remain unchanged. Finite Uni checks may be proved in
separate modules, then assembled without a new full Bi equality reduction.

-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG.Bi

/-- Equal-length lists with equal trimmed rows have the same bivariate trim. -/
theorem trim_eq_of_row_checks (p q : Bi) (hlen : p.length = q.length)
    (hrows : ∀ i < p.length, Uni.checkEq (p.getD i []) (q.getD i []) = true) :
    trim p = trim q := by
  induction p generalizing q with
  | nil =>
      cases q with
      | nil => rfl
      | cons a q => simp at hlen
  | cons a p ih =>
      cases q with
      | nil => simp at hlen
      | cons b q =>
          have htailLength : p.length = q.length := Nat.succ.inj hlen
          have hhead : Uni.checkEq a b = true := by
            simpa using hrows 0 (by simp)
          have hheadTrim : Uni.trim a = Uni.trim b := of_decide_eq_true hhead
          have htail : ∀ i < p.length,
              Uni.checkEq (p.getD i []) (q.getD i []) = true := by
            intro i hi
            simpa using hrows (i+1) (by simpa using Nat.succ_lt_succ hi)
          have htailTrim : trim p = trim q := ih q htailLength htail
          simp only [trim, hheadTrim, htailTrim]

/-- Assemble the original Bi Boolean from independent row Boolean theorems. -/
theorem checkEq_of_row_checks (p q : Bi) (hlen : p.length = q.length)
    (hrows : ∀ i < p.length, Uni.checkEq (p.getD i []) (q.getD i []) = true) :
    checkEq p q = true := by
  have ht := trim_eq_of_row_checks p q hlen hrows
  simp [checkEq, ht]

/-- A fixed n avoids carrying a reducible list-length expression in each
concrete row theorem and its final finite case assembly. -/
theorem checkEq_of_bounded_row_checks (n : Nat) (p q : Bi)
    (hp : p.length = n) (hq : q.length = n)
    (hrows : ∀ i < n, Uni.checkEq (p.getD i []) (q.getD i []) = true) :
    checkEq p q = true := by
  apply checkEq_of_row_checks p q (hp.trans hq.symm)
  intro i hi
  exact hrows i (by simpa only [hp] using hi)

end Erdos993Lean.BCFG.Bi
