module

public import Erdos993Lean.F4U.Light.Construction.LogBrackets
public import Erdos993Lean.F4U.Light.Construction.Domain

@[expose] public section


namespace F4Unified.LightConstruction

/-- The fourth-order polynomial whose value at q/2 is the literal manuscript hPlus. -/
noncomputable def childTaylor4 (u : ℝ) : ℝ :=
  1 - u / 2 - u ^ 2 / 12 - u ^ 3 / 24 - 19 * u ^ 4 / 720

theorem childTaylor4_pos {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < childTaylor4 u := by
  have h2 : u ^ 2 ≤ 1 := pow_le_one₀ hu0 hu1
  have h3 : u ^ 3 ≤ 1 := pow_le_one₀ hu0 hu1
  have h4 : u ^ 4 ≤ 1 := pow_le_one₀ hu0 hu1
  unfold childTaylor4
  linarith

theorem childTaylor4_hasDerivAt (u : ℝ) :
    HasDerivAt childTaylor4 (-1 / 2 - u / 6 - u ^ 2 / 8 - 19 * u ^ 3 / 180) u := by
  have hid := hasDerivAt_id u
  convert ((((hasDerivAt_const u (1 : ℝ)).sub (hid.div_const 2)).sub
    ((hid.pow 2).div_const 12)).sub ((hid.pow 3).div_const 24)).sub
    (((hid.pow 4).const_mul 19).div_const 720) using 1
  · ext v
    dsimp [childTaylor4]
  · dsimp
    ring

/-- Exact positive remainder for the actual child logarithm, with a checked denominator. -/
theorem childTaylor4_gap_hasDerivAt {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    HasDerivAt (fun v : ℝ => -Real.log (1 - v) - v / childTaylor4 v)
      (u ^ 5 * (361 * u ^ 3 + 1140 * u ^ 2 + 3180 * u + 58320) /
        (518400 * (1 - u) * (childTaylor4 u) ^ 2)) u := by
  have ht := ne_of_gt (childTaylor4_pos hu0 hu1.le)
  have hd := (hasDerivAt_id u).div (childTaylor4_hasDerivAt u) ht
  have hg := (parentLog_hasDerivAt hu1).sub hd
  convert hg using 1
  · ext v
    rfl
  · have h1 := ne_of_gt (sub_pos.mpr hu1)
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num : (518400 : ℝ) ≠ 0) h1)
      (pow_ne_zero 2 ht))).mpr
    generalize hTeq : childTaylor4 u = T at ht ⊢
    field_simp [h1, ht]
    rw [← hTeq]
    dsimp [childTaylor4]
    ring

theorem childTaylor4_log_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    u / childTaylor4 u ≤ -Real.log (1 - u) := by
  let f : ℝ → ℝ := fun v => -Real.log (1 - v) - v / childTaylor4 v
  let f' : ℝ → ℝ := fun v =>
    v ^ 5 * (361 * v ^ 3 + 1140 * v ^ 2 + 3180 * v + 58320) /
      (518400 * (1 - v) * (childTaylor4 v) ^ 2)
  have hd : ∀ v ∈ Set.Icc 0 u, HasDerivAt f (f' v) v := by
    intro v hv
    exact childTaylor4_gap_hasDerivAt hv.1 (lt_of_le_of_lt hv.2 hu1)
  have hm : MonotoneOn f (Set.Icc 0 u) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 u)
    · intro v hv
      exact (hd v hv).continuousAt.continuousWithinAt
    · intro v hv
      exact (hd v (interior_subset hv)).hasDerivWithinAt
    · intro v hv
      have hv0 : 0 ≤ v := (interior_subset hv).1
      have hv1 : v < 1 := lt_of_le_of_lt (interior_subset hv).2 hu1
      dsimp [f']
      apply div_nonneg
      · positivity
      · exact mul_nonneg (mul_nonneg (by norm_num) (sub_pos.mpr hv1).le) (sq_nonneg _)
  have he := hm (show (0 : ℝ) ∈ Set.Icc 0 u by exact ⟨le_refl _, hu0⟩)
    (show u ∈ Set.Icc 0 u by exact ⟨hu0, le_refl _⟩) hu0
  have hf0 : f 0 = 0 := by simp [f, childTaylor4]
  rw [hf0] at he
  dsimp [f] at he
  linarith

/-- Upper bound for the actual total childH definition, including its u=0 convention. -/
theorem childH_le_childTaylor4 {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    childH u ≤ childTaylor4 u := by
  by_cases hu : u = 0
  · subst u
    simp [childH, childTaylor4]
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hz : 0 < zMinus u := by
      unfold zMinus
      exact div_pos (mul_pos (mul_pos (by norm_num) hup) (by linarith)) (zMinus_den_pos hu1)
    have hphi : 0 < phi u := by
      simp only [phi, hu, ite_false]
      exact lt_of_lt_of_le hz (zMinus_le_parentLog hu0 hu1)
    have hlog := childTaylor4_log_lower hu0 hu1
    have ht := childTaylor4_pos hu0 hu1.le
    have hmul : u ≤ (-Real.log (1 - u)) * childTaylor4 u := (div_le_iff₀ ht).mp hlog
    simp only [childH, hu, ite_false]
    apply (div_le_iff₀ hphi).mpr
    simpa only [phi, hu, ite_false, mul_comm] using hmul

/-- The retained quadratic parent bound follows from the same actual child function. -/
theorem childH_le_parentHBound {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    childH u ≤ parentHBound u := by
  calc
    childH u ≤ childTaylor4 u := childH_le_childTaylor4 hu0 hu1
    _ ≤ parentHBound u := by
      unfold childTaylor4 parentHBound
      nlinarith [pow_nonneg hu0 3, pow_nonneg hu0 4]

theorem childTaylor4_antitoneOn : AntitoneOn childTaylor4 (Set.Ici 0) := by
  intro a ha b hb hab
  have h2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha hab 2
  have h3 : a ^ 3 ≤ b ^ 3 := pow_le_pow_left₀ ha hab 3
  have h4 : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha hab 4
  unfold childTaylor4
  linarith

theorem childTaylor4_q_half (lam : ℝ) : childTaylor4 (q lam / 2) = hPlus lam := by
  unfold childTaylor4 hPlus
  ring

/-- Literal hPlus on the original light child domain, without an extra analytic hypothesis. -/
theorem childH_le_hPlus {r : Row} {lam Y u : ℝ}
    (hlam : InRow r lam) (hY : 0 < Y) (hcap : parentH Y ≤ q lam)
    (hu0 : q lam / 2 ≤ u) (huH : u ≤ parentH Y) : childH u ≤ hPlus lam := by
  have hu := light_child_integral_domain hlam hY hcap hu0 huH
  have hq := inRow_q_bounds hlam
  calc
    childH u ≤ childTaylor4 u := childH_le_childTaylor4 hu.1 hu.2
    _ ≤ childTaylor4 (q lam / 2) :=
      childTaylor4_antitoneOn (by change 0 ≤ q lam / 2; linarith [hq.1]) hu.1 hu0
    _ = hPlus lam := childTaylor4_q_half lam

end F4Unified.LightConstruction
