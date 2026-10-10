module

public import Erdos993Lean.Analytic.V213.LowMeanCoverageGeometry
public import Erdos993Lean.Analytic.N44.Data.Params
public import Erdos993Lean.Analytic.V213.FreeCountVarianceCaps
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceDefs

/-! Exact group/routing interfaces, using the accepted N44 activity data. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

structure LowMeanGroupInput where
  iotaLo : ℕ := 0
  iotaHi : ℕ := 0
  certLo : ℕ := 0
  certHi : ℕ := 0
  l : lowMeanFraction := (0, 1)
  h : lowMeanFraction := (0, 1)
  D : lowMeanFraction := (0, 1)
  theta : lowMeanFraction := (0, 1)
  muLo : lowMeanFraction := (0, 1)
  muHi : lowMeanFraction := (0, 1)
  dWitness : ℕ := 0
  thetaWitness : ℕ := 0
  meanWitness : ℕ := 0
  deriving DecidableEq, Inhabited

structure LowMeanInputRow where
  group : ℕ := 0
  D : lowMeanFraction := (0, 1)
  theta : lowMeanFraction := (0, 1)
  mu0 : lowMeanFraction := (0, 1)
  deriving DecidableEq, Inhabited

/-- This is the numerator/denominator view of the actual accepted N44 datum. -/
def lowMeanN44LoFraction (i : ℕ) : lowMeanFraction :=
  ((Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0).num,
   (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0).den)
def lowMeanN44HiFraction (i : ℕ) : lowMeanFraction :=
  ((Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0).num,
   (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0).den)

@[simp] theorem lowMean_n44Lo_real (i : ℕ) :
    lowMeanFractionReal (lowMeanN44LoFraction i) =
      (Erdos993Lean.Analytic.N44.Data.pieceLo.getD i 0 : ℝ) := by
  simp only [lowMeanN44LoFraction, lowMeanFractionReal, Rat.cast_def]
@[simp] theorem lowMean_n44Hi_real (i : ℕ) :
    lowMeanFractionReal (lowMeanN44HiFraction i) =
      (Erdos993Lean.Analytic.N44.Data.pieceHi.getD i 0 : ℝ) := by
  simp only [lowMeanN44HiFraction, lowMeanFractionReal, Rat.cast_def]

def lowMeanActivityQFraction (x : lowMeanFraction) : lowMeanFraction :=
  (x.1, x.1.toNat + x.2)

def lowMeanActivityCapFraction (x : lowMeanFraction) : lowMeanFraction :=
  if lowMeanFractionLE x (263, 200) then (6, 5)
  else if lowMeanFractionLE x (3, 2) then (7, 5)
  else if lowMeanFractionLE x (7, 4) then (8, 5)
  else if lowMeanFractionLE x (2, 1) then (9, 5) else (21, 10)

theorem lowMean_activityQ_fraction {x : lowMeanFraction}
    (hx : lowMeanFractionValid x) (hn : 0 ≤ x.1) :
    lowMeanFractionReal (lowMeanActivityQFraction x) =
      FreeCountVariance.q (lowMeanFractionReal x) := by
  have hnR : (x.1.toNat : ℝ) = (x.1 : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn
  have hd := (lowMean_fraction_den_pos hx).ne'
  have hs : 0 < (x.1 : ℝ) + x.2 := by
    have hn' : (0 : ℝ) ≤ x.1 := by exact_mod_cast hn
    linarith [lowMean_fraction_den_pos hx]
  unfold lowMeanFractionReal lowMeanActivityQFraction FreeCountVariance.q
  simp only [Nat.cast_add]
  rw [hnR]
  field_simp [hd, hs.ne'] <;> ring

/-- The integer threshold branches are exactly the accepted left-selected cap. -/
theorem lowMean_activityCap_fraction {x : lowMeanFraction}
    (hx : lowMeanFractionValid x) :
    lowMeanFractionReal (lowMeanActivityCapFraction x) =
      FreeCountVariance.Dhat (lowMeanFractionReal x) := by
  have h1 : lowMeanFractionLE x (263, 200) ↔ lowMeanFractionReal x ≤ (263 / 200 : ℝ) := by
    simpa only [lowMeanFractionReal, Int.cast_ofNat, Nat.cast_ofNat] using
      lowMean_fraction_le_iff (y := (263, 200)) hx (by decide)
  have h2 : lowMeanFractionLE x (3, 2) ↔ lowMeanFractionReal x ≤ (3 / 2 : ℝ) := by
    simpa only [lowMeanFractionReal, Int.cast_ofNat, Nat.cast_ofNat] using
      lowMean_fraction_le_iff (y := (3, 2)) hx (by decide)
  have h3 : lowMeanFractionLE x (7, 4) ↔ lowMeanFractionReal x ≤ (7 / 4 : ℝ) := by
    simpa only [lowMeanFractionReal, Int.cast_ofNat, Nat.cast_ofNat] using
      lowMean_fraction_le_iff (y := (7, 4)) hx (by decide)
  have h4 : lowMeanFractionLE x (2, 1) ↔ lowMeanFractionReal x ≤ (2 : ℝ) := by
    simpa only [lowMeanFractionReal, Int.cast_ofNat, Nat.cast_one, div_one] using
      lowMean_fraction_le_iff (y := (2, 1)) hx (by decide)
  unfold lowMeanActivityCapFraction FreeCountVariance.Dhat FreeCountVariance.selectedCap
  by_cases hp1 : lowMeanFractionReal x ≤ 263 / 200
  · have hf1 := h1.mpr hp1
    simp only [hf1, hp1, ite_true]
    norm_num [lowMeanFractionReal, FreeCountVariance.Cap.value]
  · have hf1 := mt h1.mp hp1
    simp only [hf1, hp1, ite_false]
    by_cases hp2 : lowMeanFractionReal x ≤ 3 / 2
    · have hf2 := h2.mpr hp2
      simp only [hf2, hp2, ite_true]
      norm_num [lowMeanFractionReal, FreeCountVariance.Cap.value]
    · have hf2 := mt h2.mp hp2
      simp only [hf2, hp2, ite_false]
      by_cases hp3 : lowMeanFractionReal x ≤ 7 / 4
      · have hf3 := h3.mpr hp3
        simp only [hf3, hp3, ite_true]
        norm_num [lowMeanFractionReal, FreeCountVariance.Cap.value]
      · have hf3 := mt h3.mp hp3
        simp only [hf3, hp3, ite_false]
        by_cases hp4 : lowMeanFractionReal x ≤ 2
        · have hf4 := h4.mpr hp4
          simp only [hf4, hp4, ite_true]
          norm_num [lowMeanFractionReal, FreeCountVariance.Cap.value]
        · have hf4 := mt h4.mp hp4
          simp only [hf4, hp4, ite_false]
          norm_num [lowMeanFractionReal, FreeCountVariance.Cap.value]

end Erdos993Lean.Analytic.V213
