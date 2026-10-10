module

public import Mathlib
public import Erdos993Lean.Analytic.Tail.Unit

/-!
# The tail input T3, part 11: Theorem T3-2 (repaired) — the reduction to `U ≥ 0`

Sources: T23 §3, Theorem T3-2,
as repaired in
the repaired potential proof.

**Theorem (`t3_reduction`).**  Let `F` be a forest, `B` an independent set containing every leaf of
each component of order at least three and one endpoint of each K2 component (`LeafCondition`;
isolated vertices may lie in `B` or not), `0 < λ ≤ 6`, `q = λ/(1+λ)`, `z ∈ [0, 1]`, `a ≥ 0`,
`k = a r(λ)`, and `ℓ ≤ log((1 + λ)/(1 + λ z))` (isolated B-vertices).  If `U_z ≥ 0` on `Y_B > 0`
(`T3UNonneg λ z a ℓ`), then `E(1 − q + q z)^M ≤ exp(−ℓ m)` for `forestMixture F B λ`.

Proof: root each nontrivial component at a C-vertex.  With the unit surplus
`σ_c = −log τ_c − (ℓ/q)(1 − h(p_c)) s_c` (`sigmaU`), the induction (`potential_induction`) gives
`S_c = ∑_{C-vertices d below c} σ_d ≥ Ψ(p_c) = a L(p_c) + k T(p_c)` at C-vertices (`unit_step`: the
children's potentials add up by Lemma C, the B-children through the knapsack bound `T3UNonneg`, the
case without B-children through `boundary_lemma`) and `S ≥ a T(p_b) + [p_b < q] k That_+(T(p_b))`
at B-vertices.  At the root `S ≥ Ψ ≥ 0`, i.e. `toy ≤ exp(−(ℓ/q) ∑_c (1 − h(p_c)) s_c)`, and by
Lemma B `∑_c (1 − h(p_c)) s_c ≥ ∑_c (1 − π_c) s_c = ∑_{b ∈ B} π_b = q m` (per component).  Lemma A
turns the toy product into the Laplace transform.  The only numerical input is `T3UNonneg`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Tail

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### Generic fold lemmas -/

theorem treeProd_congr (hG : G.IsAcyclic) {f g : Finset V → V → ℝ}
    (h : ∀ s r, ConnectedIn G s → r ∈ s → f s r = g s r) {s : Finset V} (hs : ConnectedIn G s)
    {r : V} (hr : r ∈ s) : treeProd G f s r = treeProd G g s r := by
  refine rooted_induction hG (P := fun s r => treeProd G f s r = treeProd G g s r) ?_ hs hr
  intro s r hs hr ih
  rw [treeProd_eq _ hr, treeProd_eq _ hr, h s r hs hr, Finset.prod_congr rfl ih]

theorem treeSum_neg_sub (f g : Finset V → V → ℝ) (c : ℝ) (s : Finset V) (r : V) :
    treeSum G (fun s r => -f s r - c * g s r) s r = -treeSum G f s r - c * treeSum G g s r := by
  refine tree_induction (G := G) (P := fun s r =>
    treeSum G (fun s r => -f s r - c * g s r) s r = -treeSum G f s r - c * treeSum G g s r)
    ?_ ?_ s r
  · intro s r hr ih
    rw [treeSum_eq _ hr, treeSum_eq _ hr, treeSum_eq _ hr, Finset.sum_congr rfl ih,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  · intro s r hr
    rw [treeSum, dif_neg hr, treeSum, dif_neg hr, treeSum, dif_neg hr]
    ring

/-! ### The leaf condition and the invariant "every C-vertex has a child" -/

variable (G) in
/-- **The leaf condition on `B`** (T23 §3): every vertex `c ∉ B` with a neighbour
`x` has a second neighbour, or else `x ∈ B` and `c` is the only neighbour of `x` (a K2 component
with one endpoint in `B`).  For an independent `B` this says: `B` contains every leaf of each
component of order at least three and one endpoint of each K2 component (isolated vertices are
unrestricted). -/
def LeafCondition (B : Finset V) : Prop :=
  ∀ c x : V, c ∉ B → G.Adj c x → (∃ y, y ≠ x ∧ G.Adj c y) ∨ (x ∈ B ∧ ∀ y, G.Adj x y → y = c)

variable (G) in
/-- `s` is a union of components of `G` (closed under adjacency). -/
def AdjClosed (s : Finset V) : Prop := ∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s

variable (G) in
/-- The invariant of the potential induction: the C-root has a child, and every other C-vertex
has two neighbours (a parent and a child). -/
def HasChildren (B s : Finset V) (r : V) : Prop :=
  (r ∉ B → (nbrsIn G s r).Nonempty) ∧
    ∀ v ∈ s, v ≠ r → v ∉ B → ∃ u ∈ nbrsIn G s v, ∃ u' ∈ nbrsIn G s v, u ≠ u'

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem adjClosed_compIn {s : Finset V} (hs : AdjClosed G s) (x : V) :
    AdjClosed G (compIn G s x) := fun v hv w hvw =>
  mem_compIn_of_adjIn hv ⟨compIn_subset _ _ hv, hs v (compIn_subset _ _ hv) w hvw, hvw⟩

omit [DecidableRel G.Adj] in
theorem adjClosed_sdiff {s : Finset V} (hs : AdjClosed G s) (x : V) :
    AdjClosed G (s \ compIn G s x) := by
  intro v hv w hvw
  rw [Finset.mem_sdiff] at hv ⊢
  refine ⟨hs v hv.1 w hvw, fun hwK => hv.2 ?_⟩
  exact mem_compIn_of_adjIn hwK ⟨compIn_subset _ _ hwK, hv.1, hvw.symm⟩

omit [DecidableEq V] in
/-- A vertex joined inside `K` to another vertex has a neighbour in `K`. -/
theorem exists_nbr_of_reachIn {K : Finset V} {a b : V} (h : ReachIn G K a b) (hab : a ≠ b) :
    ∃ z ∈ nbrsIn G K a, True := by
  rcases Relation.ReflTransGen.cases_head h with h1 | ⟨z, hz, _⟩
  · exact absurd h1 hab
  · exact ⟨z, mem_nbrsIn.mpr ⟨hz.2.1, hz.2.2⟩, trivial⟩

theorem hasChildren_branch (hG : G.IsAcyclic) {B s : Finset V} {r w : V}
    (hw : w ∈ nbrsIn G s r) (h : HasChildren G B s r) :
    HasChildren G B (compIn G (s.erase r) w) w := by
  have hrw := (mem_nbrsIn.mp hw).2
  have hwC := self_mem_branch hw
  have hin : ∀ v ∈ compIn G (s.erase r) w, ∀ u ∈ nbrsIn G s v, u ≠ r →
      u ∈ nbrsIn G (compIn G (s.erase r) w) v := by
    intro v hv u hu hur
    obtain ⟨hus, hvu⟩ := mem_nbrsIn.mp hu
    exact mem_nbrsIn.mpr
      ⟨mem_compIn_of_adjIn hv ⟨compIn_subset _ _ hv, Finset.mem_erase.mpr ⟨hur, hus⟩, hvu⟩, hvu⟩
  have hws : w ∈ s := (mem_nbrsIn.mp hw).1
  have hwr : w ≠ r := (G.ne_of_adj hrw).symm
  refine ⟨fun hwB => ?_, fun v hv hvw hvB => ?_⟩
  · obtain ⟨u, hu, u', hu', huu'⟩ := h.2 w hws hwr hwB
    by_cases hur : u = r
    · exact ⟨u', hin w hwC u' hu' (fun h' => huu' (hur.trans h'.symm))⟩
    · exact ⟨u, hin w hwC u hu hur⟩
  · have hvs := Finset.mem_of_mem_erase (compIn_subset _ _ hv)
    have hvr := Finset.ne_of_mem_erase (compIn_subset _ _ hv)
    obtain ⟨u, hu, u', hu', huu'⟩ := h.2 v hvs hvr hvB
    have hnr : ∀ x ∈ nbrsIn G s v, x ≠ r := by
      intro x hx hxr
      rw [hxr] at hx
      exact hvw (eq_of_mem_branch_of_adj hG hrw hv (mem_nbrsIn.mp hx).2.symm)
    exact ⟨u, hin v hv u hu (hnr u hu), u', hin v hv u' hu' (hnr u' hu'), huu'⟩

/-- **The leaf condition gives the invariant** on a nontrivial component rooted at a C-vertex. -/
theorem hasChildren_of_leaf {B : Finset V} (hleaf : LeafCondition G B) {K : Finset V}
    (hKcl : AdjClosed G K) (hK : ConnectedIn G K) {c : V} (hc : c ∈ K) (hcB : c ∉ B)
    (hnt : ∃ y ∈ K, y ≠ c) : HasChildren G B K c := by
  refine ⟨fun _ => ?_, fun v hv hvc hvB => ?_⟩
  · obtain ⟨y, hy, hyc⟩ := hnt
    obtain ⟨z, hz, -⟩ := exists_nbr_of_reachIn (hK c hc y hy) (Ne.symm hyc)
    exact ⟨z, hz⟩
  · obtain ⟨x, hx, -⟩ := exists_nbr_of_reachIn (hK v hv c hc) hvc
    obtain ⟨hxK, hvx⟩ := mem_nbrsIn.mp hx
    by_cases h2 : ∃ y, y ≠ x ∧ G.Adj v y
    · obtain ⟨y, hyx, hvy⟩ := h2
      exact ⟨x, hx, y, mem_nbrsIn.mpr ⟨hKcl v hv y hvy, hvy⟩, fun h => hyx h.symm⟩
    · push_neg at h2
      rcases hleaf v x hvB hvx with ⟨y, hyx, hvy⟩ | ⟨hxB, hxonly⟩
      · exact absurd hvy (h2 y hyx)
      · -- the component is `{v, x}`, so `c = x ∈ B`: impossible
        exfalso
        have key : ∀ z, ReachIn G K v z → z = v ∨ z = x := by
          intro z hz
          induction hz with
          | refl => exact Or.inl rfl
          | tail _ hab ih =>
            rcases ih with rfl | rfl
            · right
              by_contra hne
              exact h2 _ hne hab.2.2
            · left
              exact hxonly _ hab.2.2
        rcases key c (hK v hv c hc) with h | h
        · exact hvc h.symm
        · exact hcB (h ▸ hxB)

/-! ### The unit surplus and the potential induction -/

section Potential

variable (B : Finset V) (lam z ell : ℝ)

variable (G) in
/-- **The unit surplus** `σ_c = −log τ_c − (ℓ/q)(1 − h(p_c)) s_c` (at a B-vertex `τ = 1`, `s = 0`). -/
noncomputable def sigmaU (s : Finset V) (r : V) : ℝ :=
  -Real.log (toyLocal G B lam z s r) -
    ell / actQ lam * ((1 - hmin lam (rootProb G lam s r)) * sB G B lam s r)

variable (G) in
/-- `S(s, r) = ∑` of the unit surpluses over the rooted tree. -/
noncomputable def surplus (s : Finset V) (r : V) : ℝ := treeSum G (sigmaU G B lam z ell) s r

variable {B lam z ell}

theorem toyLocal_pos (hlam0 : 0 < lam) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) {s : Finset V} {r : V}
    (hr : r ∈ s) : 0 < toyLocal G B lam z s r := by
  unfold toyLocal
  split_ifs
  · exact one_pos
  · unfold tauC
    have hp := rootProb_pos (G := G) hlam0 s r
    have hp1 := rootProb_le_one (G := G) hlam0.le hr
    have hβ := betaB_nonneg (G := G) (B := B) hlam0.le hz0 hz1 s r
    nlinarith

/-- `toy = exp(∑ log τ_c)`. -/
theorem toy_eq_exp (hG : G.IsAcyclic) (hlam0 : 0 < lam) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s) :
    toy G B lam z s r = Real.exp (treeSum G (fun s r => Real.log (toyLocal G B lam z s r)) s r) := by
  rw [← treeProd_exp]
  unfold toy
  exact treeProd_congr hG (fun s r _ hr => (Real.exp_log (toyLocal_pos hlam0 hz0 hz1 hr)).symm) hs hr

theorem surplus_eq (s : Finset V) (r : V) :
    surplus G B lam z ell s r =
      -treeSum G (fun s r => Real.log (toyLocal G B lam z s r)) s r -
        ell / actQ lam * mSumMax G B lam s r := by
  unfold surplus mSumMax
  exact treeSum_neg_sub _ _ _ s r

/-- **The potential induction** (Theorem T3-2): at a C-root `S ≥ Ψ(p_r) = a L(p_r) + k T(p_r)`;
at a B-root `S ≥ a T(p_r) + [p_r < q] k That_+(T(p_r))`. -/
theorem potential_induction (hG : G.IsAcyclic) (hB : IsIndepFinset G B) {a : ℝ}
    (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 ≤ a)
    (hU : T3UNonneg lam z a ell) {s : Finset V} (hs : ConnectedIn G s) {r : V} (hr : r ∈ s)
    (hC : HasChildren G B s r) :
    (r ∉ B → a * Lf (rootProb G lam s r) + kK lam a * Tf lam (rootProb G lam s r) ≤
        surplus G B lam z ell s r) ∧
      (r ∈ B → a * Tf lam (rootProb G lam s r) +
          (if rootProb G lam s r < actQ lam then
            kK lam a * ThatPlus lam (Tf lam (rootProb G lam s r)) else 0) ≤
        surplus G B lam z ell s r) := by
  refine rooted_induction hG (P := fun s r => HasChildren G B s r →
    (r ∉ B → a * Lf (rootProb G lam s r) + kK lam a * Tf lam (rootProb G lam s r) ≤
        surplus G B lam z ell s r) ∧
      (r ∈ B → a * Tf lam (rootProb G lam s r) +
          (if rootProb G lam s r < actQ lam then
            kK lam a * ThatPlus lam (Tf lam (rootProb G lam s r)) else 0) ≤
        surplus G B lam z ell s r)) ?_ hs hr hC
  intro s r hs hr ih hC
  have hk0 := kK_nonneg hlam0 ha
  have hq1 := actQ_lt_one hlam0.le
  -- the children's claims
  have ihw : ∀ w ∈ nbrsIn G s r, _ := fun w hw => ih w hw (hasChildren_branch hG hw hC)
  have hpw0 : ∀ w ∈ nbrsIn G s r, 0 < rootProb G lam (compIn G (s.erase r) w) w :=
    fun w _ => rootProb_pos hlam0 _ _
  have hpwq : ∀ w ∈ nbrsIn G s r, rootProb G lam (compIn G (s.erase r) w) w ≤ actQ lam :=
    fun w hw => rootProb_le_actQ hlam0.le (self_mem_branch hw)
  have hS : surplus G B lam z ell s r = sigmaU G B lam z ell s r +
      ∑ w ∈ nbrsIn G s r, surplus G B lam z ell (compIn G (s.erase r) w) w := by
    unfold surplus
    rw [treeSum_eq _ hr]
  -- Lemma C (exact)
  have hC1 := lemmaC_exact hG hlam0 hs hr
  refine ⟨fun hrB => ?_, fun hrB => ?_⟩
  · ------------------------------------------------------------------ C-root
    set I := (nbrsIn G s r).filter (· ∈ B) with hI
    set J := (nbrsIn G s r).filter (· ∉ B) with hJ
    set p : V → ℝ := fun w => rootProb G lam (compIn G (s.erase r) w) w with hp
    have hsumL : ∑ i ∈ I, Lf (p i) + ∑ j ∈ J, Lf (p j) = Tf lam (rootProb G lam s r) := by
      rw [hI, hJ, Finset.sum_filter_add_sum_filter_not, ← hC1]
    have hpr : rootProb G lam s r = pC lam (∑ i ∈ I, Lf (p i) + ∑ j ∈ J, Lf (p j)) := by
      rw [hsumL]
      exact eq_pC_of_Tf hlam0 (rootProb_pos hlam0 s r) (rootProb_lt_one hlam0.le hr) rfl
    have hne : I.Nonempty ∨ J.Nonempty := by
      obtain ⟨w, hw⟩ := hC.1 hrB
      by_cases hwB : w ∈ B
      · exact Or.inl ⟨w, Finset.mem_filter.mpr ⟨hw, hwB⟩⟩
      · exact Or.inr ⟨w, Finset.mem_filter.mpr ⟨hw, hwB⟩⟩
    have hunitY : unitY G B lam s r = ∑ i ∈ I, Lf (p i) := by
      rw [hI, Finset.sum_filter]
      rfl
    have hsB : sB G B lam s r = ∑ i ∈ I, p i := by
      rw [hI, Finset.sum_filter]
      rfl
    have hτ0 := toyLocal_pos (G := G) (B := B) hlam0 hz0 hz1 hr
    have hτeq : toyLocal G B lam z s r = tauC G B lam z s r := by
      unfold toyLocal
      rw [if_neg hrB]
    have hτ : toyLocal G B lam z s r ≤ rootProb G lam s r + (1 - rootProb G lam s r) *
        Real.exp (-(rFallback lam z * ∑ i ∈ I, Lf (p i))) := by
      rw [hτeq, tauC, betaB_eq_exp hlam0.le hz0, ← hunitY]
      have h1 := rFallback_mul_unitY_le (G := G) (B := B) hlam0 hz0 hz1 s r
      have h2 : Real.exp (-unitYz G B lam z s r) ≤ Real.exp (-(rFallback lam z * unitY G B lam s r)) :=
        Real.exp_le_exp.mpr (by linarith)
      have h3 : 0 ≤ 1 - rootProb G lam s r := by linarith [rootProb_le_one (G := G) hlam0.le hr]
      nlinarith [mul_le_mul_of_nonneg_left h2 h3]
    have hstep := unit_step hlam0 hlam6 ha hU I J p
      (fun i hi => hpw0 i (Finset.mem_filter.mp hi).1) (fun i hi => hpwq i (Finset.mem_filter.mp hi).1)
      (fun j hj => hpw0 j (Finset.mem_filter.mp hj).1) (fun j hj => hpwq j (Finset.mem_filter.mp hj).1)
      hne hpr hτ0 hτ
    -- the unit surplus is `σ = −log τ − c(s) ∑_I p`
    have hσ : sigmaU G B lam z ell s r = -Real.log (toyLocal G B lam z s r) -
        T3c lam ell (∑ i ∈ I, Lf (p i) + ∑ j ∈ J, Lf (p j)) * ∑ i ∈ I, p i := by
      unfold sigmaU T3c
      rw [← hpr, hsB]
      ring
    -- the children
    have hkids : ∑ i ∈ I, (a * Tf lam (p i) +
          (if p i < actQ lam then kK lam a * ThatPlus lam (Tf lam (p i)) else 0)) +
        ∑ j ∈ J, (a * Lf (p j) + kK lam a * Tf lam (p j)) ≤
        ∑ w ∈ nbrsIn G s r, surplus G B lam z ell (compIn G (s.erase r) w) w := by
      rw [← Finset.sum_filter_add_sum_filter_not (nbrsIn G s r) (· ∈ B), ← hI, ← hJ]
      apply add_le_add
      · apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hiN, hiB⟩ := Finset.mem_filter.mp hi
        exact (ihw i hiN).2 hiB
      · apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hjN, hjB⟩ := Finset.mem_filter.mp hj
        exact (ihw j hjN).1 hjB
    rw [hS, hσ]
    linarith
  · ------------------------------------------------------------------ B-root
    have hσ : sigmaU G B lam z ell s r = 0 := by
      unfold sigmaU toyLocal
      rw [if_pos hrB, Real.log_one, sB_eq_zero hB hrB]
      ring
    have hkidsC : ∀ w ∈ nbrsIn G s r, w ∉ B := fun w hw hwB => hB r hrB w hwB (mem_nbrsIn.mp hw).2
    have hsum : a * Tf lam (rootProb G lam s r) +
        kK lam a * ∑ w ∈ nbrsIn G s r, Tf lam (rootProb G lam (compIn G (s.erase r) w) w) ≤
        ∑ w ∈ nbrsIn G s r, surplus G B lam z ell (compIn G (s.erase r) w) w := by
      rw [← hC1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum (fun w hw => (ihw w hw).1 (hkidsC w hw))
    rw [hS, hσ, zero_add]
    rcases (nbrsIn G s r).eq_empty_or_nonempty with hnil | hne
    · have hpq : rootProb G lam s r = actQ lam := rootProb_eq_actQ hlam0.le hr hnil
      rw [hpq, if_neg (lt_irrefl _), Tf_actQ hlam0, mul_zero, add_zero, hnil, Finset.sum_empty]
    · have hlt := rootProb_lt_actQ hlam0 hr hne
      rw [if_pos hlt]
      have hTh := lemmaC_tree hG hlam0 hs hr hne
      nlinarith [mul_le_mul_of_nonneg_left hTh hk0]

end Potential

/-! ### Components and forests -/

section Assembly

variable {B : Finset V} {lam z a ell : ℝ}

/-- **One nontrivial component rooted at a C-vertex**:
`toy ≤ exp(−(ℓ/q) ∑_{b ∈ B ∩ K} π_b(K))`. -/
theorem toy_le_exp_mean (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (hlam0 : 0 < lam)
    (hlam6 : lam ≤ 6) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 ≤ a) (hell : 0 ≤ ell)
    (hU : T3UNonneg lam z a ell) {K : Finset V} (hK : ConnectedIn G K) {c : V} (hc : c ∈ K)
    (hcB : c ∉ B) (hC : HasChildren G B K c) :
    toy G B lam z K c ≤ Real.exp (-(ell / actQ lam) * ∑ b ∈ K.filter (· ∈ B), marg G lam K b) := by
  have hind := (potential_induction hG hB hlam0 hlam6 hz0 hz1 ha hU hK hc hC).1 hcB
  have hΨ : 0 ≤ a * Lf (rootProb G lam K c) + kK lam a * Tf lam (rootProb G lam K c) := by
    have h1 := Lf_nonneg (rootProb_nonneg (G := G) hlam0.le K c) (rootProb_lt_one hlam0.le hc)
    have h2 := Tf_nonneg hlam0 (rootProb_pos (G := G) hlam0 K c) (rootProb_le_actQ hlam0.le hc)
    exact add_nonneg (mul_nonneg ha h1) (mul_nonneg (kK_nonneg hlam0 ha) h2)
  rw [surplus_eq] at hind
  have hq0 := actQ_pos hlam0
  have hcq : 0 ≤ ell / actQ lam := div_nonneg hell hq0.le
  -- Lemma B: `∑ π_b = mSum ≤ mSumMax`
  have hmean : ∑ b ∈ K.filter (· ∈ B), marg G lam K b ≤ mSumMax G B lam K c := by
    rw [lemmaB_component hG hlam0.le hK hc hcB]
    exact mSum_le_max hG hlam0 hK hc (one_div_le_one_of_rootProb hlam0.le hc) le_rfl
  rw [toy_eq_exp hG hlam0 hz0 hz1 hK hc]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hmean hcq]

/-- **One component** (closed under adjacency). -/
theorem t3_component (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (hleaf : LeafCondition G B)
    (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 ≤ a) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hU : T3UNonneg lam z a ell)
    {K : Finset V} (hK : ConnectedIn G K) (hKcl : AdjClosed G K) {x : V} (hx : x ∈ K) :
    phiF G B lam z K ≤
      Real.exp (-(ell / actQ lam) * ∑ b ∈ K.filter (· ∈ B), marg G lam K b) := by
  have hq0 := actQ_pos hlam0
  by_cases h : ∃ c ∈ K, c ∉ B
  · obtain ⟨c, hcK, hcB⟩ := h
    by_cases hnt : ∃ y ∈ K, y ≠ c
    · have hC := hasChildren_of_leaf hleaf hKcl hK hcK hcB hnt
      exact (phiF_le_toy hG hB hlam0.le hz0 hz1 hK hcK).trans
        (toy_le_exp_mean hG hB hlam0 hlam6 hz0 hz1 ha hell hU hK hcK hcB hC)
    · -- an isolated C-vertex: `E = 1` and no B-mass
      push_neg at hnt
      have hKc : K = {c} := by
        ext y
        rw [Finset.mem_singleton]
        exact ⟨fun hy => hnt y hy, fun hy => hy ▸ hcK⟩
      subst hKc
      have hfilt : ({c} : Finset V).filter (· ∈ B) = ∅ := by
        rw [Finset.filter_singleton, if_neg hcB]
      rw [hfilt, Finset.sum_empty, mul_zero, Real.exp_zero, phiF_singleton]
      unfold lapW
      rw [if_neg hcB, div_self (by linarith)]
  · -- an isolated B-vertex
    push_neg at h
    have hKB : K ⊆ B := fun c hc => h c hc
    have hKx := eq_singleton_of_subset_indep hB hK hKB hx
    subst hKx
    have hxB : x ∈ B := hKB (Finset.mem_singleton_self x)
    have hnil : nbrsIn G {x} x = ∅ := by
      ext y
      simp only [mem_nbrsIn, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro rfl
      exact G.irrefl
    have hsum : ∑ b ∈ ({x} : Finset V).filter (· ∈ B), marg G lam {x} b = actQ lam := by
      rw [Finset.filter_singleton, if_pos hxB, Finset.sum_singleton,
        marg_of_mem (Finset.mem_singleton_self x),
        rootProb_eq_actQ hlam0.le (Finset.mem_singleton_self x) hnil]
    rw [hsum, neg_mul, div_mul_cancel₀ _ hq0.ne', phiF_singleton]
    unfold lapW
    rw [if_pos hxB]
    -- `(1 + λ z)/(1 + λ) = exp(−log((1 + λ)/(1 + λ z))) ≤ exp(−ℓ)`
    have h1 : 0 < 1 + lam * z := by positivity
    have h2 : 0 < 1 + lam := by linarith
    rw [show (1 + lam * z) / (1 + lam) = Real.exp (-Real.log ((1 + lam) / (1 + lam * z))) by
      rw [Real.exp_neg, Real.exp_log (div_pos h2 h1), inv_div]]
    exact Real.exp_le_exp.mpr (by linarith)

/-- **Theorem T3-2 on a union of components.** -/
theorem t3_set (hG : G.IsAcyclic) (hB : IsIndepFinset G B) (hleaf : LeafCondition G B)
    (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 ≤ a) (hell : 0 ≤ ell)
    (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z))) (hU : T3UNonneg lam z a ell)
    (s : Finset V) (hs : AdjClosed G s) :
    phiF G B lam z s ≤
      Real.exp (-(ell / actQ lam) * ∑ b ∈ s.filter (· ∈ B), marg G lam s b) := by
  induction s using Finset.strongInduction with
  | H s ih =>
    by_cases hne : s.Nonempty
    · obtain ⟨x, hxs⟩ := hne
      set K := compIn G s x with hK
      have hKc : ConnectedIn G K := connectedIn_compIn _ _
      have hxK : x ∈ K := self_mem_compIn hxs
      have hKs : K ⊆ s := compIn_subset _ _
      have hsub : s \ K ⊂ s := Finset.sdiff_ssubset hKs ⟨x, hxK⟩
      have hsplit : s.filter (· ∈ B) = K.filter (· ∈ B) ∪ (s \ K).filter (· ∈ B) := by
        rw [← Finset.filter_union, Finset.union_sdiff_of_subset hKs]
      have hdisj : Disjoint (K.filter (· ∈ B)) ((s \ K).filter (· ∈ B)) :=
        Finset.disjoint_filter_filter Finset.disjoint_sdiff
      have hno1 : ∀ a ∈ K, ∀ b ∈ s \ K, ¬ G.Adj a b := fun a ha b hb => not_adj_compIn_sdiff ha hb
      have hno2 : ∀ a ∈ s \ K, ∀ b ∈ s \ (s \ K), ¬ G.Adj a b := by
        intro a ha b hb hab
        rw [Finset.sdiff_sdiff_eq_self hKs] at hb
        exact hno1 b hb a ha hab.symm
      have hmass : ∑ b ∈ s.filter (· ∈ B), marg G lam s b =
          ∑ b ∈ K.filter (· ∈ B), marg G lam K b +
            ∑ b ∈ (s \ K).filter (· ∈ B), marg G lam (s \ K) b := by
        rw [hsplit, Finset.sum_union hdisj]
        congr 1
        · exact Finset.sum_congr rfl
            (fun b hb => marg_of_closed hlam0.le hKs hno1 (Finset.mem_filter.mp hb).1)
        · exact Finset.sum_congr rfl
            (fun b hb => marg_of_closed hlam0.le Finset.sdiff_subset hno2 (Finset.mem_filter.mp hb).1)
      rw [phiF_comp_split s x, hmass, mul_add, Real.exp_add]
      exact mul_le_mul
        (t3_component hG hB hleaf hlam0 hlam6 hz0 hz1 ha hell hiso hU hKc (adjClosed_compIn hs x) hxK)
        (ih _ hsub (adjClosed_sdiff hs x)) (phiF_nonneg hlam0.le hz0 _) (Real.exp_pos _).le
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      subst hne
      rw [phiF_empty, Finset.filter_empty, Finset.sum_empty, mul_zero, Real.exp_zero]

end Assembly

/-! ### The forest statement -/

/-- **Theorem T3-2 (repaired), hard-core form**: under the hypotheses of `t3_reduction`,
`(∑_{S indep} λ^{|S \ B|} (λ z)^{|S ∩ B|}) / Z_F(λ) ≤ exp(−(ℓ/q) W)`, `W = ∑_{b ∈ B} π_b`. -/
theorem t3_reduction_hardcore (F : FiniteForest) (B : Finset (Fin F.n))
    (hB : F.graph.IsIndepSet (B : Set (Fin F.n))) (hleaf : LeafCondition F.graph B)
    {lam z a ell : ℝ} (hlam0 : 0 < lam) (hlam6 : lam ≤ 6) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (ha : 0 ≤ a) (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z)))
    (hU : T3UNonneg lam z a ell) :
    (∑ S ∈ indepSets F, lam ^ (S \ B).card * (lam * z) ^ (S ∩ B).card) / partitionFn F lam ≤
      Real.exp (-(ell / actQ lam) * weightW F lam B) := by
  classical
  rw [lapSum_eq_Zw, partitionFn_eq_Zw]
  have hfilt : (Finset.univ : Finset (Fin F.n)).filter (· ∈ B) = B := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hW : weightW F lam B = ∑ b ∈ (Finset.univ : Finset (Fin F.n)).filter (· ∈ B),
      marg F.graph lam Finset.univ b := by
    rw [hfilt]
    unfold weightW
    exact Finset.sum_congr rfl (fun b _ => marginal_eq_marg F lam b)
  rw [hW]
  rcases le_or_gt 0 ell with hell | hell
  · exact t3_set F.isForest (isIndepFinset_of_isIndepSet hB) hleaf hlam0 hlam6 hz0 hz1 ha hell
      hiso hU Finset.univ (fun _ _ _ _ => Finset.mem_univ _)
  · -- `ℓ < 0`: the bound is at least `1 ≥ E`
    have h1 := phiF_le_one (G := F.graph) (B := B) hlam0.le hz0 hz1 Finset.univ
    have h2 : 0 ≤ ∑ b ∈ (Finset.univ : Finset (Fin F.n)).filter (· ∈ B),
        marg F.graph lam Finset.univ b := Finset.sum_nonneg (fun b _ => marg_nonneg hlam0.le _ _)
    have h3 : -(ell / actQ lam) * ∑ b ∈ (Finset.univ : Finset (Fin F.n)).filter (· ∈ B),
        marg F.graph lam Finset.univ b ≥ 0 := by
      have : ell / actQ lam < 0 := div_neg_of_neg_of_pos hell (actQ_pos hlam0)
      nlinarith
    unfold phiF at h1
    exact h1.trans (Real.one_le_exp_iff.mpr h3)

/-- **Theorem T3-2 (repaired), the reduction.**  For every forest `F`, every independent set `B`
satisfying the leaf condition (`LeafCondition`: every leaf of a component of order `≥ 3` is in `B`,
one endpoint of each K2 component is in `B`), `0 < λ ≤ 6`, `z ∈ [0, 1]`, `a ≥ 0` and
`ℓ ≤ log((1 + λ)/(1 + λ z))`: if the reduced unit inequality `T3UNonneg λ z a ℓ` holds (`U_z ≥ 0`
on `Y_B > 0`; the certification target), then `E(1 − q + q z)^M ≤ exp(−ℓ m)` for
`forestMixture F B λ`.  The two identities are the Laplace identity E2 and
`MixtureFacts.weight_eq`. -/
theorem t3_reduction (hLap : LaplaceIdentity) (hW : WeightIdentity) (F : FiniteForest)
    (B : Finset (Fin F.n)) (hB : F.graph.IsIndepSet (B : Set (Fin F.n)))
    (hleaf : LeafCondition F.graph B) {lam z a ell : ℝ} (hlam0 : 0 < lam) (hlam6 : lam ≤ 6)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (ha : 0 ≤ a) (hiso : ell ≤ Real.log ((1 + lam) / (1 + lam * z)))
    (hU : T3UNonneg lam z a ell) :
    (forestMixture F B lam).expect (fun M _ => (1 - actQ lam + actQ lam * z) ^ M) ≤
      Real.exp (-ell * (forestMixture F B lam).meanM) := by
  rw [hLap F B lam z hlam0 hB]
  have hmean : (forestMixture F B lam).meanM = weightW F lam B / actQ lam := by
    rw [← hW F lam B hlam0 hB]
    field_simp [(actQ_pos hlam0).ne']
  have h := t3_reduction_hardcore F B hB hleaf hlam0 hlam6 hz0 hz1 ha hiso hU
  rw [hmean]
  rw [show -ell * (weightW F lam B / actQ lam) = -(ell / actQ lam) * weightW F lam B by ring]
  exact h

end Erdos993Lean.Analytic.Tail
