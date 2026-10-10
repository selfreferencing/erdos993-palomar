module

public import Erdos993Lean.Analytic.V213.SmallForestSignIntervals

/-!
Universal factorial-cancellation transport.
No finite catalogue or evaluated data is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForest

noncomputable def risingR (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | d + 1 => risingR x d * (x + d + 1)

theorem risingR_pos (x : ℝ) (hx : 0 ≤ x) (d : ℕ) : 0 < risingR x d := by
  induction d with
  | zero => simp [risingR]
  | succ d ih =>
      rw [risingR]
      exact mul_pos ih (by positivity)

/-- Cleared upper-index ratio, including d=0. -/
theorem choose_upper_transport (n k d : ℕ) (hkn : k ≤ n) :
    ((n + d).choose k : ℝ) * risingR ((n : ℝ) - k) d =
      (n.choose k : ℝ) * risingR n d := by
  induction d with
  | zero => simp [risingR]
  | succ d ih =>
      have hn : k ≤ n + d + 1 := by omega
      have hsNat := Nat.choose_mul_succ_eq (n + d) k
      have hs0 : ((n + d).choose k : ℝ) * ((n + d + 1 : ℕ) : ℝ) =
          ((n + d + 1).choose k : ℝ) * ((n + d + 1 - k : ℕ) : ℝ) := by
        exact_mod_cast hsNat
      simp only [Nat.cast_sub hn, Nat.cast_add, Nat.cast_one] at hs0
      have hd : n + (d + 1) = n + d + 1 := by omega
      rw [hd, risingR, risingR]
      calc
        ((n + d + 1).choose k : ℝ) *
            (risingR ((n : ℝ) - k) d * ((n : ℝ) - k + d + 1)) =
          (((n + d + 1).choose k : ℝ) * ((n : ℝ) + d + 1 - k)) *
            risingR ((n : ℝ) - k) d := by ring
        _ = (((n + d).choose k : ℝ) * ((n : ℝ) + d + 1)) *
            risingR ((n : ℝ) - k) d := by rw [← hs0]
        _ = (((n + d).choose k : ℝ) * risingR ((n : ℝ) - k) d) *
            ((n : ℝ) + d + 1) := by ring
        _ = ((n.choose k : ℝ) * risingR n d) * ((n : ℝ) + d + 1) := by rw [ih]
        _ = (n.choose k : ℝ) * (risingR n d * ((n : ℝ) + d + 1)) := by ring

noncomputable def GQuad (w j m : ℝ) : ℝ :=
  (m - j + 1) * (j + 1) - w * j * (j + 1) -
    (1 - w) * (m - j + 1) * (m - j)

theorem G_quad_clear (w : ℝ) (j m : ℕ) (hj : 1 ≤ j) (hm : j - 1 ≤ m) :
    (j : ℝ) * ((j : ℝ) + 1) * G w (j : ℤ) m =
      (m.choose (j - 1) : ℝ) * GQuad w j m := by
  have h := G_cleared_quadratic w (j - 1) m hm
  have hj' : j - 1 + 1 = j := by omega
  rw [hj'] at h
  simp only [Nat.cast_sub hj, Nat.cast_one] at h
  have he : GBracket w (j - 1) m = GQuad w j m := by
    simp only [GBracket, GQuad, Nat.cast_sub hj, Nat.cast_one]
    ring
  rw [he] at h
  convert h using 1 <;> ring

theorem G_pos_of_quad_pos (w : ℝ) (j m : ℕ) (hj : 1 ≤ j)
    (hm : j - 1 ≤ m) (hq : 0 < GQuad w j m) : 0 < G w (j : ℤ) m := by
  have hc : 0 < (m.choose (j - 1) : ℝ) := by exact_mod_cast Nat.choose_pos hm
  have hp := mul_pos hc hq
  rw [← G_quad_clear w j m hj hm] at hp
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  exact (mul_pos_iff_of_pos_left (mul_pos hjR (by positivity))).mp hp

/-- Relates the tangent increment to the same choose(t,j-1) as G_j(t). -/
theorem tangent_quad_clear (w : ℝ) (j t : ℕ) (hj : 2 ≤ j) (ht : j - 1 ≤ t) :
    (t : ℝ) * j * G w ((j : ℤ) - 1) (t - 1) =
      (t.choose (j - 1) : ℝ) * GQuad w ((j : ℝ) - 1) ((t : ℝ) - 1) := by
  have hj1 : 1 ≤ j := by omega
  have hjm : 1 ≤ j - 1 := by omega
  have ht1 : 1 ≤ t := by omega
  have hq := G_quad_clear w (j - 1) (t - 1) hjm (by omega)
  have hsNat := Nat.add_one_mul_choose_eq (t - 1) (j - 2)
  have htEq : t - 1 + 1 = t := by omega
  have hjEq : j - 2 + 1 = j - 1 := by omega
  rw [htEq, hjEq] at hsNat
  have hs : (t : ℝ) * ((t - 1).choose (j - 2) : ℝ) =
      (t.choose (j - 1) : ℝ) * ((j : ℝ) - 1) := by
    have hcast : (t : ℝ) * ((t - 1).choose (j - 2) : ℝ) =
        (t.choose (j - 1) : ℝ) * ((j - 1 : ℕ) : ℝ) := by exact_mod_cast hsNat
    simpa only [Nat.cast_sub hj1, Nat.cast_one] using hcast
  have hji : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  have hjj : j - 1 - 1 = j - 2 := by omega
  rw [hji, hjj] at hq
  simp only [Nat.cast_sub hj1, Nat.cast_sub ht1, Nat.cast_one] at hq
  have hp : ((j : ℝ) - 1) *
      ((t : ℝ) * j * G w ((j : ℤ) - 1) (t - 1) -
        (t.choose (j - 1) : ℝ) * GQuad w ((j : ℝ) - 1) ((t : ℝ) - 1)) = 0 := by
    linear_combination (t : ℝ) * hq +
      GQuad w ((j : ℝ) - 1) ((t : ℝ) - 1) * hs
  have hnon : (j : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hnon)

/-- Each printed quotient is proved by a polynomial identity after this
universal cancellation theorem. No fixed-j sampling occurs. -/
theorem pattern_residual_of_identity (w R : ℝ) (j t d : ℕ)
    (hj : 2 ≤ j) (ht : j - 1 ≤ t)
    (halg : (t : ℝ) *
      (risingR t d * GQuad w j ((t : ℝ) + d) -
        risingR ((t : ℝ) - j + 1) d * GQuad w j t) =
      ((d : ℝ) + R) * ((j : ℝ) + 1) * risingR ((t : ℝ) - j + 1) d *
        GQuad w ((j : ℝ) - 1) ((t : ℝ) - 1)) :
    G w (j : ℤ) (t + d) - G w (j : ℤ) t -
      (d : ℝ) * G w ((j : ℤ) - 1) (t - 1) =
      R * G w ((j : ℤ) - 1) (t - 1) := by
  have hj1 : 1 ≤ j := by omega
  have ht1 : 1 ≤ t := by omega
  have hM := G_quad_clear w j (t + d) hj1 (by omega)
  have hT := G_quad_clear w j t hj1 ht
  have hq := tangent_quad_clear w j t hj ht
  have hchoose := choose_upper_transport t (j - 1) d ht
  simp only [Nat.cast_sub hj1, Nat.cast_one] at hchoose
  have hchoice : ((t + d).choose (j - 1) : ℝ) * risingR ((t : ℝ) - j + 1) d =
      (t.choose (j - 1) : ℝ) * risingR t d := by
    have he : (t : ℝ) - ((j : ℝ) - 1) = (t : ℝ) - j + 1 := by ring
    rw [he] at hchoose
    exact hchoose
  simp only [Nat.cast_add] at hM
  have hMc : (j : ℝ) * ((j : ℝ) + 1) * risingR ((t : ℝ) - j + 1) d *
      G w (j : ℤ) (t + d) =
      (t.choose (j - 1) : ℝ) * risingR t d * GQuad w j ((t : ℝ) + d) := by
    linear_combination risingR ((t : ℝ) - j + 1) d * hM +
      GQuad w j ((t : ℝ) + d) * hchoice
  have hp : ((t : ℝ) * j * ((j : ℝ) + 1) * risingR ((t : ℝ) - j + 1) d) *
      (G w (j : ℤ) (t + d) - G w (j : ℤ) t -
        (d : ℝ) * G w ((j : ℤ) - 1) (t - 1) -
        R * G w ((j : ℤ) - 1) (t - 1)) = 0 := by
    linear_combination (t : ℝ) * hMc -
      (t : ℝ) * risingR ((t : ℝ) - j + 1) d * hT -
      ((d : ℝ) + R) * ((j : ℝ) + 1) * risingR ((t : ℝ) - j + 1) d * hq +
      (t.choose (j - 1) : ℝ) * halg
  have hjR : 0 < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have htR : 0 < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have hx : 0 ≤ (t : ℝ) - j + 1 := by
    have h : ((j - 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast ht
    rw [Nat.cast_sub hj1, Nat.cast_one] at h
    linarith
  have hpos : 0 < (t : ℝ) * j * ((j : ℝ) + 1) * risingR ((t : ℝ) - j + 1) d :=
    mul_pos (mul_pos (mul_pos htR hjR) (by positivity)) (risingR_pos _ hx d)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (ne_of_gt hpos))

end Erdos993Lean.Analytic.V213.SmallForest

#check Erdos993Lean.Analytic.V213.SmallForest.risingR_pos
#print axioms Erdos993Lean.Analytic.V213.SmallForest.risingR_pos
#check Erdos993Lean.Analytic.V213.SmallForest.choose_upper_transport
#print axioms Erdos993Lean.Analytic.V213.SmallForest.choose_upper_transport
#check Erdos993Lean.Analytic.V213.SmallForest.G_quad_clear
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_quad_clear
#check Erdos993Lean.Analytic.V213.SmallForest.G_pos_of_quad_pos
#print axioms Erdos993Lean.Analytic.V213.SmallForest.G_pos_of_quad_pos
#check Erdos993Lean.Analytic.V213.SmallForest.tangent_quad_clear
#print axioms Erdos993Lean.Analytic.V213.SmallForest.tangent_quad_clear
#check Erdos993Lean.Analytic.V213.SmallForest.pattern_residual_of_identity
#print axioms Erdos993Lean.Analytic.V213.SmallForest.pattern_residual_of_identity
