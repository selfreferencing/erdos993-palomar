module

public import Erdos993Lean.Analytic.V213.ResponseControlNormBound
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Exact whole-interval C/D/S consumers in current Lemma 5.29. The hypotheses
are the displayed scalar gates. No sample points inside the interval occur.
The second-derivative polynomial is derived from the actual centered sum. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape

open Set
open scoped BigOperators

noncomputable def centeredD1 (N : ℕ) (e : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N+1), e i*(i:ℝ)*t^(i-1)
noncomputable def centeredD2 (N : ℕ) (e : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (N+1), e i*(i:ℝ)*((i-1:ℕ):ℝ)*t^(i-2)
noncomputable def upperCurvature (N : ℕ) (e : ℕ → ℝ) (r : ℝ) : ℝ :=
  2*e 2+∑ i ∈ Finset.range (N+1),
    if 3 ≤ i then (i:ℝ)*((i-1:ℕ):ℝ)*|e i| *r^(i-2) else 0

theorem centeredValue_hasDerivAt (N : ℕ) (e : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (centeredValue N e) (centeredD1 N e t) t := by
  unfold centeredValue centeredD1
  apply HasDerivAt.fun_sum
  intro i hi
  simpa only [id_eq,mul_one,mul_assoc] using ((hasDerivAt_id t).fun_pow i).const_mul (e i)

theorem centeredD1_hasDerivAt (N : ℕ) (e : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (centeredD1 N e) (centeredD2 N e t) t := by
  unfold centeredD1 centeredD2
  apply HasDerivAt.fun_sum
  intro i hi
  simpa only [id_eq,mul_one,mul_assoc,Nat.sub_sub,Nat.reduceAdd] using
    ((hasDerivAt_id t).fun_pow (i-1)).const_mul (e i*(i:ℝ))

theorem centeredD2_split_low {N : ℕ} (hN : 2≤N) (e : ℕ → ℝ) (t : ℝ) :
    centeredD2 N e t=2*e 2+∑ i ∈ Finset.range (N+1),
      if 3 ≤ i then e i*(i:ℝ)*((i-1:ℕ):ℝ)*t^(i-2) else 0 := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [centeredD2,Finset.sum_range_succ]; ring
  | succ n hn ih =>
      unfold centeredD2 at ih ⊢
      rw [Finset.sum_range_succ (f:=fun i=>e i*(i:ℝ)*((i-1:ℕ):ℝ)*t^(i-2)) (n:=n+1),
        Finset.sum_range_succ (f:=fun i=>if 3 ≤ i then e i*(i:ℝ)*((i-1:ℕ):ℝ)*t^(i-2) else 0) (n:=n+1)]
      simp only [show 3≤n+1 by omega,if_true]
      rw [ih]
      ring

theorem centeredD2_upper {N : ℕ} (hN : 2≤N) (e : ℕ → ℝ) {r t : ℝ}
    (ht : |t|≤r) : centeredD2 N e t≤upperCurvature N e r := by
  rw [centeredD2_split_low hN]
  unfold upperCurvature
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i hi
  by_cases h3 : 3 ≤ i
  · simp only [h3,if_pos]
    have hp := pow_le_pow_left₀ (abs_nonneg t) ht (i-2)
    have habs : e i*t^(i-2)≤|e i| *r^(i-2) := by
      calc
        e i*t^(i-2)≤|e i*t^(i-2)| := le_abs_self _
        _=|e i| *|t|^(i-2) := by rw [abs_mul,abs_pow]
        _≤|e i| *r^(i-2) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    have hm := mul_le_mul_of_nonneg_left habs (show 0≤(i:ℝ)*((i-1:ℕ):ℝ) by positivity)
    nlinarith
  · simp only [h3,if_false,le_refl]

theorem lowerQ_hasDerivAt (N : ℕ) (e : ℕ → ℝ) (r t : ℝ) :
    HasDerivAt (lowerQ N e r) (e 1+2*lowerK N e r*t) t := by
  unfold lowerQ
  convert ((hasDerivAt_const t (e 0)).add ((hasDerivAt_id t).const_mul (e 1))).add
    (((hasDerivAt_id t).fun_pow 2).const_mul (lowerK N e r)) using 1 <;>
    (try funext x) <;> (try dsimp) <;>
    simp only [id_eq,mul_one,Nat.reduceSub,pow_one,Nat.cast_ofNat] <;> ring

theorem lowerQ_slope_upper (N : ℕ) (e : ℕ → ℝ) {r t : ℝ} (ht : |t|≤r) :
    e 1+2*lowerK N e r*t≤e 1+2*|lowerK N e r| *r := by
  have hp : lowerK N e r*t≤|lowerK N e r| *r := by
    calc
      lowerK N e r*t≤|lowerK N e r*t| := le_abs_self _
      _=|lowerK N e r| *|t| := abs_mul _ _
      _≤|lowerK N e r| *r := mul_le_mul_of_nonneg_left ht (abs_nonneg _)
  nlinarith

theorem lowerQ_concave (N : ℕ) (e : ℕ → ℝ) (r : ℝ) (hk : lowerK N e r≤0) :
    ConcaveOn ℝ (Icc (-r) r) (lowerQ N e r) := by
  have hf : ContinuousOn (lowerQ N e r) (Icc (-r) r) :=
    fun t ht=>(lowerQ_hasDerivAt N e r t).continuousAt.continuousWithinAt
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (-r) r) hf
    (fun t ht=>(lowerQ_hasDerivAt N e r t).hasDerivWithinAt)
    (f'' := fun _=>2*lowerK N e r)
  · intro t ht
    have hh : HasDerivAt (fun x:ℝ=>e 1+2*lowerK N e r*x) (2*lowerK N e r) t := by
      simpa only [zero_add,mul_one,id_eq] using
        ((hasDerivAt_id t).const_mul (2*lowerK N e r)).const_add (e 1)
    exact hh.hasDerivWithinAt
  · intro t ht
    linarith

theorem lowerQ_antitone (N : ℕ) (e : ℕ → ℝ) (r : ℝ)
    (hs : e 1+2*|lowerK N e r| *r<0) :
    AntitoneOn (lowerQ N e r) (Icc (-r) r) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (-r) r)
    (fun t ht=>(lowerQ_hasDerivAt N e r t).continuousAt.continuousWithinAt)
    (fun t ht=>(lowerQ_hasDerivAt N e r t).hasDerivWithinAt)
  intro t ht
  have hx : t∈Icc (-r) r := interior_subset ht
  exact (lowerQ_slope_upper N e (abs_le.mpr hx)).trans hs.le

theorem centered_concave {N : ℕ} (hN : 2≤N) (e : ℕ → ℝ) (r : ℝ)
    (hU : upperCurvature N e r≤0) :
    ConcaveOn ℝ (Icc (-r) r) (centeredValue N e) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (-r) r)
    (fun t ht=>(centeredValue_hasDerivAt N e t).continuousAt.continuousWithinAt)
    (fun t ht=>(centeredValue_hasDerivAt N e t).hasDerivWithinAt)
    (fun t ht=>(centeredD1_hasDerivAt N e t).hasDerivWithinAt)
  intro t ht
  have hx : t∈Icc (-r) r := interior_subset ht
  exact (centeredD2_upper hN e (abs_le.mpr hx)).trans hU

theorem control_C_positive {N : ℕ} (hN : 2≤N) (e : ℕ → ℝ) {r t : ℝ}
    (hr : 0≤r) (ht : |t|≤r) (hk : lowerK N e r<0)
    (hl : 0<lowerQ N e r (-r)) (hu : 0<lowerQ N e r r) :
    0<centeredValue N e t := by
  have hc := lowerQ_concave N e r hk.le
  have hm := hc.min_le_of_mem_Icc (show -r∈Icc (-r) r by constructor <;> linarith)
    (show r∈Icc (-r) r by constructor <;> linarith) (abs_le.mp ht)
  exact (lt_of_lt_of_le (lt_min hl hu) hm).trans_le (centered_lower hN e ht)

theorem control_D_positive {N : ℕ} (hN : 2≤N) (e : ℕ → ℝ) {r t : ℝ}
    (hr : 0≤r) (ht : |t|≤r) (hs : e 1+2*|lowerK N e r| *r<0)
    (hu : 0<lowerQ N e r r) : 0<centeredValue N e t := by
  have hanti := lowerQ_antitone N e r hs
  have hmem := abs_le.mp ht
  have hm := hanti hmem (show r∈Icc (-r) r by constructor <;> linarith) hmem.2
  exact (hu.trans_le hm).trans_le (centered_lower hN e ht)

theorem control_S_positive {N : ℕ} (hN : 2≤N) (e : ℕ → ℝ) {r t : ℝ}
    (hr : 0≤r) (ht : |t|≤r) (hU : upperCurvature N e r<0)
    (hl : 0<centeredValue N e (-r)) (hu : 0<centeredValue N e r) :
    0<centeredValue N e t := by
  have hc := centered_concave hN e r hU.le
  have hm := hc.min_le_of_mem_Icc (show -r∈Icc (-r) r by constructor <;> linarith)
    (show r∈Icc (-r) r by constructor <;> linarith) (abs_le.mp ht)
  exact (lt_min hl hu).trans_le hm

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD1
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD1
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD2
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD2
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.upperCurvature
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.upperCurvature
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredValue_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredValue_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD1_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD1_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD2_split_low
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD2_split_low
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD2_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centeredD2_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ_hasDerivAt
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ_slope_upper
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ_slope_upper
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ_concave
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ_concave
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ_antitone
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.lowerQ_antitone
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centered_concave
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.centered_concave
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.control_C_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.control_C_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.control_D_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.control_D_positive
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.control_S_positive
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightShape.control_S_positive
