module

public import Erdos993Lean.Analytic.V213.FiberSmallData
public import Erdos993Lean.Analytic.V213.FiberSmallAMGM

/-!
Exhaustive accepted F07 consumption. Canonical choose/power fractions
use Int numerators and Nat denominators. All52 printed M,J pairs, the eight
attained maxima, strict caps and geometric caps are checked by grouped
Range.all with decide +kernel and interpreted by F4Fast and cast soundness.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberSmallTInt (N J : ℕ) : ℤ :=
  3 * N * ((N : ℤ) - 1) - 4 * J * ((N : ℤ) - J)

def fiberSmallCanonical (N J : ℕ) : lowMeanFraction :=
  ((N.choose J : ℤ) * fiberSmallTInt N J ^ (N + 1),
    N * (N - 1) * (N + 1) ^ (N + 1) * (4 * (N - 1)) ^ N)

def fiberSmallExpectedCap : FiberSmallIdentity → lowMeanFraction
  | .m0 => (51, 200) | .m1 => (17, 125) | .m2 => (159, 2000)
  | .m3 => (61, 1250) | .m4 => (161, 5000) | .m5 => (129, 5000)
  | .m6 => (101, 5000) | .m7 => (81, 5000)

def fiberSmallExpectedMaximum : FiberSmallIdentity → lowMeanFraction
  | .m0 => (1, 4) | .m1 => (2187, 16384) | .m2 => (243, 3125)
  | .m3 => (3125, 65536) | .m4 => (1, 32)
  | .m5 => lowMeanFractionMul (4, 1) (lowMeanFractionPow (17, 32) 8)
  | .m6 => lowMeanFractionMul (4, 1) (lowMeanFractionPow (5, 9) 9)
  | .m7 => lowMeanFractionMul (4, 1) (lowMeanFractionPow (23, 40) 10)

def fiberSmallGeometricCanonical (M : ℕ) : lowMeanFraction :=
  (51 * (27 : ℤ) ^ M, 200 * 40 ^ M)

instance fiberSmallValidDecidable (x : lowMeanFraction) : Decidable (lowMeanFractionValid x) :=
  inferInstanceAs (Decidable (0 < x.2))

instance fiberSmallEqDecidable (x y : lowMeanFraction) : Decidable (lowMeanFractionEq x y) :=
  inferInstanceAs (Decidable (x.1 * (y.2 : ℤ) = y.1 * (x.2 : ℤ)))

instance fiberSmallLEDecidable (x y : lowMeanFraction) : Decidable (lowMeanFractionLE x y) :=
  inferInstanceAs (Decidable (x.1 * (y.2 : ℤ) ≤ y.1 * (x.2 : ℤ)))

instance fiberSmallLTDecidable (x y : lowMeanFraction) : Decidable (lowMeanFractionLT x y) :=
  inferInstanceAs (Decidable (x.1 * (y.2 : ℤ) < y.1 * (x.2 : ℤ)))

def fiberSmallSupportCheck (id : FiberSmallIdentity) (J : ℕ) : Bool :=
  let r := fiberSmallById id
  let v := fiberSmallSupportValue id J
  let u := fiberSmallCanonical (fiberSmallWidth id + 2) J
  decide (lowMeanFractionValid v ∧ lowMeanFractionValid u ∧
    lowMeanFractionEq v u ∧ lowMeanFractionLE v r.maximum)

def fiberSmallWidthCheck (id : FiberSmallIdentity) : Bool :=
  let r := fiberSmallById id
  let g := fiberSmallGeometricCanonical (fiberSmallWidth id)
  let p := fiberSmallExpectedMaximum id
  let a := fiberSmallSupportValue id r.witnessJ
  decide (r.printed = fiberSmallPrinted id ∧ r.M = fiberSmallWidth id ∧ r.N = r.M + 2 ∧
    r.cap = fiberSmallExpectedCap id ∧ lowMeanFractionValid r.cap ∧
    lowMeanFractionValid r.maximum ∧ lowMeanFractionValid r.geometric ∧
    lowMeanFractionValid g ∧ lowMeanFractionValid p ∧ lowMeanFractionValid a ∧
    r.witnessJ ≤ r.N ∧ lowMeanFractionEq r.maximum p ∧ lowMeanFractionEq a r.maximum ∧
    lowMeanFractionLT r.maximum r.cap ∧ lowMeanFractionEq r.geometric g ∧
    lowMeanFractionLE r.cap r.geometric ∧ 0 ≤ r.cap.1) &&
    (List.range (fiberSmallWidth id + 3)).all (fiberSmallSupportCheck id)

theorem fiber_small_width_checks :
    (List.range 8).all (fun k => fiberSmallWidthCheck (fiberSmallIdentityAt k)) = true := by
  decide +kernel

theorem fiber_small_index_checked {k : ℕ} (hk : k < 8) :
    fiberSmallWidthCheck (fiberSmallIdentityAt k) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_small_width_checks k hk

theorem fiber_small_named_checked (id : FiberSmallIdentity) :
    fiberSmallWidthCheck id = true := by
  cases id with
  | m0 => exact fiber_small_index_checked (k := 0) (by decide +kernel)
  | m1 => exact fiber_small_index_checked (k := 1) (by decide +kernel)
  | m2 => exact fiber_small_index_checked (k := 2) (by decide +kernel)
  | m3 => exact fiber_small_index_checked (k := 3) (by decide +kernel)
  | m4 => exact fiber_small_index_checked (k := 4) (by decide +kernel)
  | m5 => exact fiber_small_index_checked (k := 5) (by decide +kernel)
  | m6 => exact fiber_small_index_checked (k := 6) (by decide +kernel)
  | m7 => exact fiber_small_index_checked (k := 7) (by decide +kernel)

theorem fiber_small_support_checked (id : FiberSmallIdentity) {J : ℕ}
    (hJ : J ≤ fiberSmallWidth id + 2) : fiberSmallSupportCheck id J = true := by
  have h := fiber_small_named_checked id
  simp only [fiberSmallWidthCheck, Bool.and_eq_true] at h
  exact Erdos993Lean.F4Fast.forall_lt_of_range_all h.2 J (by omega)

theorem fiber_small_canonical_real {N J : ℕ} (hN : 2 ≤ N) :
    lowMeanFractionReal (fiberSmallCanonical N J) = fiberSmallU N J := by
  unfold fiberSmallCanonical fiberSmallTInt lowMeanFractionReal fiberSmallU fiberSmallT
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  rw [Nat.cast_sub (by omega : 1 ≤ N)]
  norm_num only [Nat.cast_one, Int.cast_one]

theorem fiber_small_U_le_maximum (id : FiberSmallIdentity) {J : ℕ}
    (hJ : J ≤ fiberSmallWidth id + 2) :
    fiberSmallU (fiberSmallWidth id + 2) J ≤
      lowMeanFractionReal (fiberSmallById id).maximum := by
  have hs := of_decide_eq_true (fiber_small_support_checked id hJ)
  have h := fiber_small_named_checked id
  simp only [fiberSmallWidthCheck, Bool.and_eq_true] at h
  have hw := of_decide_eq_true h.1
  rcases hw with ⟨_,_,_,_,_,hm,_,_,_,_,_,_,_,_,_,_,_⟩
  rcases hs with ⟨hv,hu,he,hcmp⟩
  rw [← fiber_small_canonical_real (by omega : 2 ≤ fiberSmallWidth id + 2),
    ← (lowMean_fraction_eq_iff hv hu).mp he]
  exact (lowMean_fraction_le_iff hv hm).mp hcmp

theorem fiber_small_maximum_attained (id : FiberSmallIdentity) :
    (fiberSmallById id).witnessJ ≤ fiberSmallWidth id + 2 ∧
    fiberSmallU (fiberSmallWidth id + 2) (fiberSmallById id).witnessJ =
      lowMeanFractionReal (fiberSmallById id).maximum := by
  have h := fiber_small_named_checked id
  simp only [fiberSmallWidthCheck, Bool.and_eq_true] at h
  have hw := of_decide_eq_true h.1
  rcases hw with ⟨_,hM,hN,_,_,hm,_,_,_,ha,hJ,_,he,_,_,_,_⟩
  have hJ' : (fiberSmallById id).witnessJ ≤ fiberSmallWidth id + 2 := by omega
  have hs := of_decide_eq_true (fiber_small_support_checked id hJ')
  rcases hs with ⟨hv,hu,heU,_⟩
  refine ⟨hJ', ?_⟩
  rw [← fiber_small_canonical_real (by omega : 2 ≤ fiberSmallWidth id + 2),
    ← (lowMean_fraction_eq_iff hv hu).mp heU]
  exact (lowMean_fraction_eq_iff ha hm).mp he

theorem fiber_small_maximum_lt_cap (id : FiberSmallIdentity) :
    lowMeanFractionReal (fiberSmallById id).maximum <
      lowMeanFractionReal (fiberSmallById id).cap := by
  have h := fiber_small_named_checked id
  simp only [fiberSmallWidthCheck, Bool.and_eq_true] at h
  have hw := of_decide_eq_true h.1
  rcases hw with ⟨_,_,_,_,hc,hm,_,_,_,_,_,_,_,hcmp,_,_,_⟩
  exact (lowMean_fraction_lt_iff hm hc).mp hcmp

theorem fiber_small_geometric_cap (id : FiberSmallIdentity) :
    lowMeanFractionReal (fiberSmallById id).cap ≤
      (51 / 200 : ℝ) * (27 / 40 : ℝ) ^ fiberSmallWidth id := by
  have h := fiber_small_named_checked id
  simp only [fiberSmallWidthCheck, Bool.and_eq_true] at h
  have hw := of_decide_eq_true h.1
  rcases hw with ⟨_,_,_,_,hc,_,hg,hg',_,_,_,_,_,_,he,hcmp,_⟩
  have h := (lowMean_fraction_le_iff hc hg).mp hcmp
  rw [(lowMean_fraction_eq_iff hg hg').mp he] at h
  convert h using 1
  simp [fiberSmallGeometricCanonical, lowMeanFractionReal, div_pow]
  ring

theorem fiber_small_cap_nonneg (id : FiberSmallIdentity) :
    0 ≤ lowMeanFractionReal (fiberSmallById id).cap := by
  have h := fiber_small_named_checked id
  simp only [fiberSmallWidthCheck, Bool.and_eq_true] at h
  have hw := of_decide_eq_true h.1
  rcases hw with ⟨_,_,_,_,hc,_,_,_,_,_,_,_,_,_,_,_,hn⟩
  exact div_nonneg (by exact_mod_cast hn) (lowMean_fraction_den_pos hc).le

end Erdos993Lean.Analytic.V213
