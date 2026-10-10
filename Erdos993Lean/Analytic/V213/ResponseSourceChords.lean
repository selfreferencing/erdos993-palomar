module

public import Erdos993Lean.Analytic.V213.ResponseSourceEndpoints
public import Mathlib.Analysis.Convex.Function

/-! Actual source chords on both closed phases of Lemma 5.27. Endpoint
values are derived from O2.src. No source comparison is a hypothesis. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

open Set

private theorem affine_concave (a b l r : ℝ) :
    ConcaveOn ℝ (Icc l r) (fun x : ℝ => a*x+b) := by
  refine ⟨convex_Icc l r,?_⟩
  intro x hx y hy s t hs ht hst
  simp only [smul_eq_mul]
  apply le_of_eq
  calc
    s*(a*x+b)+t*(a*y+b)=a*(s*x+t*y)+(s+t)*b := by ring
    _=a*(s*x+t*y)+b := by rw [hst,one_mul]

private theorem affine_chord_below {l r x a b : ℝ} {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Icc l r) f) (hx : x∈Icc l r)
    (hl : a*l+b=f l) (hr : a*r+b=f r) : a*x+b ≤ f x := by
  by_cases he : l=r
  · have hx' : x=l := by rcases hx with ⟨h1,h2⟩; linarith
    rw [hx',hl]
  have hlt : l<r := lt_of_le_of_ne (hx.1.trans hx.2) he
  have hd : 0<r-l := by linarith
  have hs : 0≤(r-x)/(r-l) := div_nonneg (by linarith [hx.2]) hd.le
  have ht : 0≤(x-l)/(r-l) := div_nonneg (by linarith [hx.1]) hd.le
  have hst : (r-x)/(r-l)+(x-l)/(r-l)=1 := by field_simp [hd.ne']; ring
  have harg : (r-x)/(r-l)*l+(x-l)/(r-l)*r=x := by field_simp [hd.ne']; ring
  have h := hf.2 (show l∈Icc l r from ⟨le_rfl,hlt.le⟩)
    (show r∈Icc l r from ⟨hlt.le,le_rfl⟩) hs ht hst
  simp only [smul_eq_mul,harg,←hl,←hr] at h
  have heq : (r-x)/(r-l)*(a*l+b)+(x-l)/(r-l)*(a*r+b)=a*x+b := by
    field_simp [hd.ne']
    ring
  rwa [heq] at h

theorem source_concave_phase_one {lam H : ℝ} (hl : 0<lam) (hH : 0≤H)
    (hcap : H≤childQ lam/2) :
    ConcaveOn ℝ (Icc (rhoMin lam (halfParent lam H)) (rhoStar lam (halfParent lam H)))
      (O2.src lam (halfParent lam H)) := by
  let p := halfParent lam H
  let q := childQ lam
  let a := sourceSlopeA q
  let b := sourceSlopeB q
  let c := sourceIntercept q
  have ha := affine_concave ((a*p+a)/2) ((1-a)/2) (rhoMin lam p) (rhoStar lam p)
  have hb := affine_concave ((a*p+b)/2) ((1-b-c)/2) (rhoMin lam p) (rhoStar lam p)
  apply (ha.inf hb).congr
  intro rho hrho
  simp only [Pi.inf_apply]
  rw [half_phase_one_source hl hH hcap hrho.1 hrho.2]
  congr 1 <;> dsimp [p,q,a,b,c] <;> ring

theorem source_concave_phase_two {lam H : ℝ} (hl : 0<lam) (hH : 0≤H)
    (hcap : H≤childQ lam/2) :
    ConcaveOn ℝ (Icc (rhoStar lam (halfParent lam H)) 1)
      (O2.src lam (halfParent lam H)) := by
  let p := halfParent lam H
  let q := childQ lam
  let a := sourceSlopeA q
  let b := sourceSlopeB q
  let c := sourceIntercept q
  have ha := affine_concave ((b*p+a)/2) ((1+c-a)/2) (rhoStar lam p) 1
  have hb := affine_concave ((b*p+a*p*H)/2) ((1+c-a*H)/2) (rhoStar lam p) 1
  apply (ha.inf hb).congr
  intro rho hrho
  simp only [Pi.inf_apply]
  rw [half_phase_two_source hl hH hcap hrho.1 hrho.2]
  congr 1 <;> dsimp [p,q,a,b,c] <;> ring

theorem sourceChord_one_endpoints {lam H : ℝ} (hl : 0<lam) (hH : 0≤H)
    (hcap : H≤childQ lam/2) :
    (sourceChordA 1 lam H*rhoMin lam (halfParent lam H)+sourceChordB 1 lam H =
      O2.src lam (halfParent lam H) (rhoMin lam (halfParent lam H))) ∧
    (sourceChordA 1 lam H*rhoStar lam (halfParent lam H)+sourceChordB 1 lam H =
      O2.src lam (halfParent lam H) (rhoStar lam (halfParent lam H))) := by
  have hp := halfParent_bounds hl hH hcap
  have hpc : 0<1-halfParent lam H := sub_pos.mpr hp.2.2.1
  have hd : 1+lam*(1-halfParent lam H)≠0 := ne_of_gt (by positivity)
  rw [source_at_rhoMin hl hH hcap,source_at_rhoStar hl hH hcap]
  constructor
  · simp only [sourceChordA,sourceChordB,ite_true]
    unfold rhoMin sourceSlopeA childQ
    field_simp [hl.ne',hd,show 1+lam≠0 by positivity]
    ring
  · simp only [sourceChordA,sourceChordB,ite_true]
    unfold rhoStar
    rw [sourceSwitch_activity hl]
    field_simp [hl.ne',hp.2.1.ne',show 1+lam≠0 by positivity,
      show 1+2*lam≠0 by positivity]
    ring

theorem sourceChord_two_endpoints {lam H : ℝ} (hl : 0<lam) (hH : 0≤H)
    (hcap : H≤childQ lam/2) :
    (sourceChordA 2 lam H*rhoStar lam (halfParent lam H)+sourceChordB 2 lam H =
      O2.src lam (halfParent lam H) (rhoStar lam (halfParent lam H))) ∧
    (sourceChordA 2 lam H*1+sourceChordB 2 lam H = O2.src lam (halfParent lam H) 1) := by
  have hp := halfParent_bounds hl hH hcap
  have hcross : 2*H*(1+lam)≤lam :=
    (le_div_iff₀ (show 0<1+lam by linarith)).mp (show 2*H≤childQ lam by linarith)
  have hd : 0<lam-(1+lam)*H := by nlinarith
  have hHm : 0<1-H := by linarith [hp.1]
  rw [source_at_rhoStar hl hH hcap,source_at_one hl hH hcap]
  constructor
  · simp only [sourceChordA,sourceChordB,show (2:ℕ)≠1 by decide,if_false]
    unfold sourceChordError rhoStar
    rw [sourceSwitch_activity hl]
    unfold sourceSlopeB sourceIntercept childQ halfParent chartParent
    field_simp [hl.ne',hd.ne',show 1-H≠0 by linarith [hp.1],
      show 1+lam≠0 by positivity,show 1+2*lam≠0 by positivity,
      show 1+lam*(1-H)≠0 by positivity]
    ring
  · simp only [sourceChordA,sourceChordB,show (2:ℕ)≠1 by decide,if_false,mul_one]
    ring

theorem sourceChord_lower {phase : ℕ} {lam H rho : ℝ} (hl : 0<lam) (hH : 0≤H)
    (hcap : H≤childQ lam/2) (hphase : phaseDomain phase lam H rho) :
    sourceChordA phase lam H*rho+sourceChordB phase lam H ≤
      O2.src lam (halfParent lam H) rho := by
  rcases hphase with ⟨rfl,hr0,hrstar⟩ | ⟨rfl,hrstar,hr1⟩
  · have he := sourceChord_one_endpoints hl hH hcap
    exact affine_chord_below (source_concave_phase_one hl hH hcap) ⟨hr0,hrstar⟩ he.1 he.2
  · have he := sourceChord_two_endpoints hl hH hcap
    exact affine_chord_below (source_concave_phase_two hl hH hcap) ⟨hrstar,hr1⟩ he.1 he.2

theorem source_strictMono_phase_two {lam H : ℝ} (hl : 0<lam) (hH : 0≤H)
    (hcap : H≤childQ lam/2) :
    StrictMonoOn (O2.src lam (halfParent lam H)) (Icc (rhoStar lam (halfParent lam H)) 1) := by
  have hp := halfParent_bounds hl hH hcap
  have hq : 0<childQ lam := div_pos hl (by linarith)
  have ha : 0<sourceSlopeA (childQ lam) := by unfold sourceSlopeA; positivity
  have hb : 0<sourceSlopeB (childQ lam) := by unfold sourceSlopeB; positivity
  intro x hx y hy hxy
  rw [half_phase_two_source hl hH hcap hx.1 hx.2,
    half_phase_two_source hl hH hcap hy.1 hy.2]
  apply lt_min
  · exact (min_le_left _ _).trans_lt (by
      nlinarith [mul_pos (mul_pos hb hp.2.1) (sub_pos.mpr hxy),
        mul_pos ha (sub_pos.mpr hxy)])
  · exact (min_le_right _ _).trans_lt (by
      nlinarith [mul_pos (mul_pos hb hp.2.1) (sub_pos.mpr hxy),
        mul_nonneg (mul_nonneg (mul_nonneg ha.le hp.2.1.le) hH) (sub_nonneg.mpr hxy.le)])

theorem sourceChord_slopes_pos {lam H : ℝ} (hl : 0<lam) (hH : 0≤H)
    (hcap : H≤childQ lam/2) : 0<sourceChordA 1 lam H ∧ 0<sourceChordA 2 lam H := by
  have hp := halfParent_bounds hl hH hcap
  have hr := phase_split_bounds hl hH hcap
  refine ⟨?_,?_⟩
  · have hpp := hp.2.1
    simp only [sourceChordA,ite_true]
    positivity
  · have he := sourceChord_two_endpoints hl hH hcap
    have hm := source_strictMono_phase_two hl hH hcap
      (show rhoStar lam (halfParent lam H)∈Icc (rhoStar lam (halfParent lam H)) 1 from
        ⟨le_rfl,hr.2.2.le⟩) (show (1:ℝ)∈Icc (rhoStar lam (halfParent lam H)) 1 from
        ⟨hr.2.2.le,le_rfl⟩) hr.2.2
    rw [←he.1,←he.2] at hm
    by_contra hn
    have hneg : sourceChordA 2 lam H≤0 := le_of_not_gt hn
    have hx := mul_nonpos_of_nonpos_of_nonneg hneg (show 0≤1-rhoStar lam (halfParent lam H) by linarith)
    nlinarith

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_concave_phase_one
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_concave_phase_one
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_concave_phase_two
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_concave_phase_two
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_one_endpoints
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_one_endpoints
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_two_endpoints
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_two_endpoints
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_lower
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_lower
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_strictMono_phase_two
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.source_strictMono_phase_two
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_slopes_pos
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLight.sourceChord_slopes_pos
