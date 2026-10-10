module

public import Erdos993Lean.Analytic.V213.FreeCountCAEllActivity
public import Erdos993Lean.Analytic.V213.FreeCountVarianceActivityPrintedData
public import Erdos993Lean.Analytic.V213.FreeCountScalarFinite

/-! Six literal parameter/vertex records imply actual
activity monotonicity. The first closed cap crosses two proved intervals;
the common endpoint 4/5 is explicitly used in the final comparison.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

open Real Set PrintedScalarRecords
open PrintedActivityData

theorem ell_band_H (i : ActivityBand6) : ellIntervalH (PrintedActivityData.a i) = PrintedActivityData.H i := by
  cases i with
  | first =>
    have h := parameter_K1_H
    push_cast at h
    convert h.symm using 1 <;> simp only [ellIntervalH, q, PrintedActivityData.a, PrintedActivityData.H] <;> ring
  | second =>
    have h := parameter_K2_H
    push_cast at h
    convert h.symm using 1 <;> simp only [ellIntervalH, q, PrintedActivityData.a, PrintedActivityData.H] <;> ring
  | third =>
    have h := parameter_K3_H
    push_cast at h
    convert h.symm using 1 <;> simp only [ellIntervalH, q, PrintedActivityData.a, PrintedActivityData.H] <;> ring
  | fourth =>
    have h := parameter_K4_H
    push_cast at h
    convert h.symm using 1 <;> simp only [ellIntervalH, q, PrintedActivityData.a, PrintedActivityData.H] <;> ring
  | fifth =>
    have h := parameter_K5_H
    push_cast at h
    convert h.symm using 1 <;> simp only [ellIntervalH, q, PrintedActivityData.a, PrintedActivityData.H] <;> ring
  | sixth =>
    have h := parameter_K6_H
    push_cast at h
    convert h.symm using 1 <;> simp only [ellIntervalH, q, PrintedActivityData.a, PrintedActivityData.H] <;> ring

theorem ell_band_K (i : ActivityBand6) : ellIntervalK (PrintedActivityData.D i) (PrintedActivityData.b i) = PrintedActivityData.K i := by
  cases i with
  | first =>
    have h := parameter_K1_K
    push_cast at h
    simpa only [ellIntervalK, PrintedActivityData.D, PrintedActivityData.b, PrintedActivityData.K] using h.symm
  | second =>
    have h := parameter_K2_K
    push_cast at h
    simpa only [ellIntervalK, PrintedActivityData.D, PrintedActivityData.b, PrintedActivityData.K] using h.symm
  | third =>
    have h := parameter_K3_K
    push_cast at h
    simpa only [ellIntervalK, PrintedActivityData.D, PrintedActivityData.b, PrintedActivityData.K] using h.symm
  | fourth =>
    have h := parameter_K4_K
    push_cast at h
    simpa only [ellIntervalK, PrintedActivityData.D, PrintedActivityData.b, PrintedActivityData.K] using h.symm
  | fifth =>
    have h := parameter_K5_K
    push_cast at h
    simpa only [ellIntervalK, PrintedActivityData.D, PrintedActivityData.b, PrintedActivityData.K] using h.symm
  | sixth =>
    have h := parameter_K6_K
    push_cast at h
    simpa only [ellIntervalK, PrintedActivityData.D, PrintedActivityData.b, PrintedActivityData.K] using h.symm

theorem ell_band_vertex (i : ActivityBand6) :
    ellIntervalK (PrintedActivityData.D i) (PrintedActivityData.b i)*ellIntervalH (PrintedActivityData.a i)+
      (ellIntervalK (PrintedActivityData.D i) (PrintedActivityData.b i)*(1-ellIntervalH (PrintedActivityData.a i))+PrintedActivityData.b i/2)^2/
        (4*(ellIntervalK (PrintedActivityData.D i) (PrintedActivityData.b i)+PrintedActivityData.b i/4)) < 8/3 := by
  rw [ell_band_H, ell_band_K]
  cases i with
  | first =>
    have h := fixed_F26
    push_cast at h
    exact h
  | second =>
    have h := fixed_F27
    push_cast at h
    exact h
  | third =>
    have h := fixed_F28
    push_cast at h
    exact h
  | fourth =>
    have h := fixed_F29
    push_cast at h
    exact h
  | fifth =>
    have h := fixed_F30
    push_cast at h
    exact h
  | sixth =>
    have h := fixed_F31
    push_cast at h
    exact h

theorem ell_band_antitone (i : ActivityBand6) {y : ℝ} (hy : 0 ≤ y) :
    AntitoneOn (fun lam => ell (PrintedActivityData.D i) lam y) (Icc (PrintedActivityData.a i) (PrintedActivityData.b i)) := by
  have hD : 0 < PrintedActivityData.D i := by cases i <;> norm_num [PrintedActivityData.D]
  have ha : 0 < PrintedActivityData.a i := by cases i <;> norm_num [PrintedActivityData.a]
  exact ell_antitone_on_activity_interval hD ha hy (ell_band_vertex i)

/-- The bound used by every C row, including both halves of the first cap. -/
theorem ell_upper_le_on_cap {c : Cap} {lam y : ℝ}
    (hc : c.Contains lam) (hy : 0 ≤ y) :
    ell c.value c.upper y ≤ ell c.value lam y := by
  cases c with
  | first =>
    have h1 := ell_band_antitone .first hy
    have h2 := ell_band_antitone .second hy
    simp only [PrintedActivityData.a, PrintedActivityData.b, PrintedActivityData.D] at h1 h2
    simp only [Cap.Contains, Cap.lower, Cap.upper] at hc
    change ell (6/5) (263/200) y ≤ ell (6/5) lam y
    by_cases hm : lam ≤ 4/5
    · have hright := h2 (show (4/5 : ℝ) ∈ Icc (4/5) (263/200) by
          constructor <;> norm_num)
        (show (263/200 : ℝ) ∈ Icc (4/5) (263/200) by
          constructor <;> norm_num) (by norm_num)
      have hleft := h1 ⟨hc.1, hm⟩
        (show (4/5 : ℝ) ∈ Icc (1/3) (4/5) by
          constructor <;> norm_num) hm
      exact hright.trans hleft
    · exact h2 ⟨le_of_lt (lt_of_not_ge hm), hc.2⟩
        (show (263/200 : ℝ) ∈ Icc (4/5) (263/200) by
          constructor <;> norm_num) hc.2
  | second =>
    have h := ell_band_antitone .third hy
    exact h hc ⟨by norm_num [PrintedActivityData.a, PrintedActivityData.b, Cap.upper], le_rfl⟩ hc.2
  | third =>
    have h := ell_band_antitone .fourth hy
    exact h hc ⟨by norm_num [PrintedActivityData.a, PrintedActivityData.b, Cap.upper], le_rfl⟩ hc.2
  | fourth =>
    have h := ell_band_antitone .fifth hy
    exact h hc ⟨by norm_num [PrintedActivityData.a, PrintedActivityData.b, Cap.upper], le_rfl⟩ hc.2
  | fifth =>
    have h := ell_band_antitone .sixth hy
    exact h hc ⟨by norm_num [PrintedActivityData.a, PrintedActivityData.b, Cap.upper], le_rfl⟩ hc.2

end Erdos993Lean.Analytic.V213.FreeCountVariance.Finite

#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_band_H
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_band_H
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_band_K
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_band_K
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_band_vertex
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_band_vertex
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_band_antitone
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_band_antitone
#check Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_upper_le_on_cap
#print axioms Erdos993Lean.Analytic.V213.FreeCountVariance.Finite.ell_upper_le_on_cap
