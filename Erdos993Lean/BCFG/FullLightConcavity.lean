module

public import Erdos993Lean.BCFG.FullLightGeometry
public import Mathlib.Analysis.Convex.Function

/-! Actual full-light source concavity, obtained from all four affine faces.
The closed-interval minorant lemma explicitly handles a collapsed phase. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Set Erdos993Lean.Analytic Erdos993Lean.Analytic.V213.VarianceResponse

private theorem affine_concave (a b l r : ℝ) :
    ConcaveOn ℝ (Icc l r) (fun x : ℝ => a*x+b) := by
  refine ⟨convex_Icc l r,?_⟩
  intro x hx y hy s t hs ht hst
  simp only [smul_eq_mul]
  apply le_of_eq
  calc
    s*(a*x+b)+t*(a*y+b) = a*(s*x+t*y)+(s+t)*b := by ring
    _ = a*(s*x+t*y)+b := by rw [hst,one_mul]

private theorem source_concave_of_branch {lam p l r k d : ℝ}
    (hl : 0 < lam) (hp : 0 < p) (hpq : p ≤ actQ lam)
    (hl0 : rhoMin lam p ≤ l) (hr1 : r ≤ 1)
    (hbranch : ∀ x ∈ Icc l r, O2.fq (actQ lam) (p*x) = k*x+d) :
    ConcaveOn ℝ (Icc l r) (O2.src lam p) := by
  let a := sourceSlopeA (actQ lam)
  let b := sourceSlopeB (actQ lam)
  let c := sourceIntercept (actQ lam)
  let H := O2.cavH lam p
  have h1 := affine_concave ((k+a)/2) ((1+d-a)/2) l r
  have h2 := affine_concave ((k+b)/2) ((1+d-b-c)/2) l r
  have h3 := affine_concave ((k+a*p*H)/2) ((1+d-a*H)/2) l r
  have h4 := affine_concave ((k+b*p*H)/2) ((1+d-b*H-c)/2) l r
  apply ((h1.inf h2).inf (h3.inf h4)).congr
  intro x hx
  simp only [Pi.inf_apply]
  rw [source_four_faces hl hp hpq (hl0.trans hx.1) (hx.2.trans hr1)]
  rw [hbranch x hx]
  congr 1 <;> congr 1 <;> dsimp [a,b,c,H] <;> ring

theorem fullLight_source_concave_one {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    ConcaveOn ℝ (Icc (rhoZero lam omega) (lightRhoStar lam omega))
      (O2.src lam (occupation lam omega)) := by
  have hp := fullLight_parent_bounds hl hlo hhi
  have hr := fullLight_phase_bounds hl hlo hhi
  apply source_concave_of_branch (k := sourceSlopeA (actQ lam)*occupation lam omega)
    (d := 0) hl hp.1 hp.2.1 (fullLight_rhoZero_eq hl hlo hhi).symm.le hr.2
  intro x hx
  rw [source_phase_one_branch hl hp.1 (hx.2.trans (fullLight_rhoStar_eq hl).le)]
  ring

theorem fullLight_source_concave_two {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    ConcaveOn ℝ (Icc (lightRhoStar lam omega) 1)
      (O2.src lam (occupation lam omega)) := by
  have hp := fullLight_parent_bounds hl hlo hhi
  have hr := fullLight_phase_bounds hl hlo hhi
  apply source_concave_of_branch (k := sourceSlopeB (actQ lam)*occupation lam omega)
    (d := sourceIntercept (actQ lam)) hl hp.1 hp.2.1
    ((fullLight_rhoZero_eq hl hlo hhi).symm.le.trans hr.1) le_rfl
  intro x hx
  rw [source_phase_two_branch hl hp.1 ((fullLight_rhoStar_eq hl).symm.le.trans hx.1)]
  ring

theorem fullLight_Gh_concave {lam omega : ℝ} (hl : 0 < lam)
    (hlo : 1/(1+lam) ≤ omega) (hhi : omega ≤ 1) :
    ConcaveOn ℝ (Icc (rhoZero lam omega) (lightRhoStar lam omega)) (lightGh lam omega) ∧
    ConcaveOn ℝ (Icc (lightRhoStar lam omega) 1) (lightGh lam omega) := by
  have hr := fullLight_phase_bounds hl hlo hhi
  constructor
  · apply (fullLight_source_concave_one hl hlo hhi).congr
    intro x hx
    exact fullLight_source_eq_Gh hl hlo hhi hx.1 (hx.2.trans hr.2)
  · apply (fullLight_source_concave_two hl hlo hhi).congr
    intro x hx
    exact fullLight_source_eq_Gh hl hlo hhi (hr.1.trans hx.1) hx.2

theorem affine_minorant_of_concave_endpoints {l r x a b : ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc l r) f) (hx : x ∈ Icc l r)
    (hl : a*l+b ≤ f l) (hr : a*r+b ≤ f r) : a*x+b ≤ f x := by
  by_cases he : l = r
  · have hx' : x = l := by linarith [hx.1,hx.2]
    simpa only [hx'] using hl
  have hlt : l < r := lt_of_le_of_ne (hx.1.trans hx.2) he
  have hd : 0 < r-l := sub_pos.mpr hlt
  have hs : 0 ≤ (r-x)/(r-l) := div_nonneg (by linarith [hx.2]) hd.le
  have ht : 0 ≤ (x-l)/(r-l) := div_nonneg (by linarith [hx.1]) hd.le
  have hst : (r-x)/(r-l)+(x-l)/(r-l) = 1 := by field_simp [hd.ne'] <;> ring
  have harg : (r-x)/(r-l)*l+(x-l)/(r-l)*r = x := by field_simp [hd.ne'] <;> ring
  have hc := hf.2 (show l ∈ Icc l r from ⟨le_rfl,hlt.le⟩)
    (show r ∈ Icc l r from ⟨hlt.le,le_rfl⟩) hs ht hst
  simp only [smul_eq_mul,harg] at hc
  have heq : (r-x)/(r-l)*(a*l+b)+(x-l)/(r-l)*(a*r+b) = a*x+b := by
    field_simp [hd.ne'] <;> ring
  rw [← heq]
  exact (add_le_add (mul_le_mul_of_nonneg_left hl hs)
    (mul_le_mul_of_nonneg_left hr ht)).trans hc

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.fullLight_source_concave_one
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_source_concave_one
#check Erdos993Lean.BCFG.Analytic.fullLight_source_concave_two
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_source_concave_two
#check Erdos993Lean.BCFG.Analytic.fullLight_Gh_concave
#print axioms Erdos993Lean.BCFG.Analytic.fullLight_Gh_concave
#check Erdos993Lean.BCFG.Analytic.affine_minorant_of_concave_endpoints
#print axioms Erdos993Lean.BCFG.Analytic.affine_minorant_of_concave_endpoints
