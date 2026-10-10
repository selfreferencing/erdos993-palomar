module

public import Erdos993Lean.Analytic.V213.SmallForestResidual

/-!
The actual supporting-line conclusion of current Lemma7.5.
The weak positive-superlevel theorem includes equality at the
chosen slope. Both zero residuals t-1,t and the last endpoint are proved.
The j=2 case uses the same signed increment identity and G0 hypothesis.
No finite table is used in this module.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

theorem supporting_line (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1)
    (j t M : ℕ) (hj : 2 ≤ j) (ht : 2 ≤ t) (hM : t ≤ M)
    (hq : 0 < G w ((j : ℤ) - 1) (t - 1))
    (hprevious : 0 < G w ((j : ℤ) - 2) (t - 2))
    (hend : G w (j : ℤ) t + G w ((j : ℤ) - 1) (t - 1) * ((M : ℝ) - t) ≤
      G w (j : ℤ) M) :
    ∀ m : ℕ, m ≤ M →
      G w (j : ℤ) t + G w ((j : ℤ) - 1) (t - 1) * ((m : ℝ) - t) ≤
        G w (j : ℤ) m := by
  let q : ℝ := G w ((j : ℤ) - 1) (t - 1)
  let f : ℕ → ℝ := fun n => G w ((j : ℤ) - 1) n
  let R : ℕ → ℝ := fun n => G w (j : ℤ) n - G w (j : ℤ) t - q * ((n : ℝ) - t)
  have hind : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  have hlevel : ∀ a b c : ℕ, a ≤ b → b ≤ c → q ≤ f a → q ≤ f c → q ≤ f b := by
    intro a b c hab hbc ha hc
    have ha' : q ≤ G w ((j - 1 : ℕ) : ℤ) a := by simpa only [f, hind] using ha
    have hc' : q ≤ G w ((j - 1 : ℕ) : ℤ) c := by simpa only [f, hind] using hc
    simpa only [f, hind] using
      G_positive_superlevel_interval w (le_of_lt hw0) (le_of_lt hw1) (j - 1)
        (by omega) (q := q) hq hab hbc ha' hc'
  have hprev : f (t - 2) < q := by
    have hi := G_increment w ((j : ℤ) - 1) (t - 2)
    have he : t - 2 + 1 = t - 1 := by omega
    have hjj : (j : ℤ) - 1 - 1 = (j : ℤ) - 2 := by omega
    rw [he, hjj] at hi
    dsimp [f, q]
    linarith only [hi, hprevious]
  have hstep : ∀ n : ℕ, R (n + 1) - R n = f n - q := by
    intro n
    have hi := G_increment w (j : ℤ) n
    dsimp [R, f]
    push_cast
    nlinarith only [hi]
  have hleft : R (t - 1) = 0 := by
    have hi := G_increment w (j : ℤ) (t - 1)
    have he : t - 1 + 1 = t := by omega
    rw [he] at hi
    dsimp [R, q]
    rw [Nat.cast_sub (by omega : 1 ≤ t)]
    norm_num only [Nat.cast_one]
    nlinarith only [hi]
  have hright : R t = 0 := by dsimp [R]; ring
  have hlast : 0 ≤ R M := by dsimp [R, q]; linarith only [hend]
  have hr := SmallForestResidual.supporting_residual_nonneg R f q t M ht hM hq
    hlevel rfl hprev hstep hleft hright hlast
  intro m hm
  have hb := hr m hm
  dsimp [R, q] at hb
  linarith only [hb]

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.supporting_line
#print axioms Erdos993Lean.Analytic.V213.SmallForest.supporting_line
