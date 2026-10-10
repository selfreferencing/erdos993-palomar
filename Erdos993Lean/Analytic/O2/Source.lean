module

public import Erdos993Lean.Analytic.O2.Records
public import Erdos993Lean.Analytic.Tail.Marginal

/-!
# O2: the original-law source and its physical competitor (Lemma 2, eqs. (2)–(3))

Source: the O2 proof, §2 (the edge
bounds `π_u + q π_v ≤ q`, the feasible field `s_v = f_q(π_v)`, the refinement
`s'_v = (1 + s_v − s_{a(v)})/2` by the largest neighbouring source, the competitor `Γ`, and
Lemma 2, `g(p_v, r_v) ≤ s'_v`), the refined selector producer and the implementation map
§2, obligation 3.

For a finite acyclic graph `G` at activity `λ > 0`, with the actual marginals `π_v` (`gMarg`, the
hard-core marginal of the whole vertex set):

* `gMarg_edge`: **the edge bounds** `π_u + q π_v ≤ q` on every edge (the partition-function identity
  `Z = Z(V−u−v) + λ Z(V−N[u]) + λ Z(V−N[v])` and `Z(V−N[u]) ≤ Z(V−u−v)`);
* `fq_mono`, `fq_nonneg`, `fq_le_one`, **`fq_edge`** (`f_q(x) + f_q(y) ≤ 1` from the two edge bounds,
  checking the four pairs of affine pieces);
* `nbrMax v` (the largest neighbouring source `max(0, max_{y ~ v} s_y)`, the value `s_{a(v)}` of the
  maximizing owner) and the refined field `sRef v = (1 + s_v − nbrMax v)/2`; `sRef_nonneg`,
  `sRef_le_one`, **`sRef_edge`** (`s'_u + s'_v ≤ 1`), `fq_le_sRef` (`s'_v ≥ s_v`);
* **`src_le_sRef`** (Lemma 2 at a record): if `π_v = r p` and every neighbour's marginal is at most
  `M_up(p, r)`, then `g(p, r) ≤ s'_v`;
* **`dp_closed`** (the competitor, eq. (2)): for every edge-feasible field `σ ∈ [0, 1]` there is an
  actual independent set `I` with `∑_v π_v σ_v ≤ ∑_{v ∈ I} π_v`.  The proof is the top-down tree
  construction of `Γ` read as a dynamic programme: on a rooted subtree it produces independent sets
  `I₁` (root allowed) and `I₀ ∌ root` with `∑ π σ ≤ σ_root π(I₁) + (1 − σ_root) π(I₀)`, i.e. the
  mean score of `Γ` is a convex combination of scores of actual independent sets, each at most `W`.

Scalarity check.  `π` is the actual marginal field; `s = f_q ∘ π`, `nbrMax` and `sRef` are fields of
the actual vertices and their actual neighbours (the owner's source value), consumed by the source
term `c π g` of the local payment.  `dp_closed` returns an actual independent set (the witness), not
a scalar.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.O2

open Finset Erdos993Lean.Analytic.Tail

/-! ### The source function `f_q` -/

section Fq

variable {q : ℝ}

theorem fq_mono (hq : 0 < q) {x y : ℝ} (hxy : x ≤ y) : fq q x ≤ fq q y := by
  unfold fq
  have h1 : (1 + q) * x / (2 * q) ≤ (1 + q) * y / (2 * q) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (by linarith)) (by linarith)
  have h2 : (1 + q) * x / (2 * q ^ 2) ≤ (1 + q) * y / (2 * q ^ 2) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (by linarith)) (by positivity)
  exact max_le_max h1 (by linarith)

theorem fq_nonneg (hq : 0 < q) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ fq q x :=
  le_trans (div_nonneg (mul_nonneg (by linarith) hx) (by linarith)) (le_max_left _ _)

theorem fq_le_one (hq : 0 < q) (hq1 : q < 1) {x : ℝ} (hxq : x ≤ q) :
    fq q x ≤ 1 := by
  unfold fq
  refine max_le ?_ ?_
  · rw [div_le_one (by linarith)]
    nlinarith
  · have e : (1 + q) * x / (2 * q ^ 2) + (q - 1) / (2 * q) - 1 =
        (1 + q) * (x - q) / (2 * q ^ 2) := by
      field_simp
      ring
    have : (1 + q) * (x - q) / (2 * q ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
        (by positivity)
    linarith

private theorem max_add_max_le {A B C D : ℝ} (h1 : A + C ≤ 1) (h2 : A + D ≤ 1) (h3 : B + C ≤ 1)
    (h4 : B + D ≤ 1) : max A B + max C D ≤ 1 := by
  rcases max_cases A B with ⟨hA, _⟩ | ⟨hA, _⟩ <;> rcases max_cases C D with ⟨hC, _⟩ | ⟨hC, _⟩ <;>
    rw [hA, hC] <;> assumption

/-- **The two edge bounds give `f_q(x) + f_q(y) ≤ 1`** (the four pairs of affine pieces). -/
theorem fq_edge (hq : 0 < q) {x y : ℝ} (hxy : x + q * y ≤ q) (hyx : y + q * x ≤ q) :
    fq q x + fq q y ≤ 1 := by
  unfold fq
  apply max_add_max_le
  · have e : (1 + q) * x / (2 * q) + (1 + q) * y / (2 * q) - 1 =
        ((x + q * y - q) + (y + q * x - q)) / (2 * q) := by
      field_simp
      ring
    have : ((x + q * y - q) + (y + q * x - q)) / (2 * q) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    linarith
  · have e : (1 + q) * x / (2 * q) + ((1 + q) * y / (2 * q ^ 2) + (q - 1) / (2 * q)) - 1 =
        (1 + q) * (y + q * x - q) / (2 * q ^ 2) := by
      field_simp
      ring
    have : (1 + q) * (y + q * x - q) / (2 * q ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
        (by positivity)
    linarith
  · have e : (1 + q) * x / (2 * q ^ 2) + (q - 1) / (2 * q) + (1 + q) * y / (2 * q) - 1 =
        (1 + q) * (x + q * y - q) / (2 * q ^ 2) := by
      field_simp
      ring
    have : (1 + q) * (x + q * y - q) / (2 * q ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
        (by positivity)
    linarith
  · have e : (1 + q) * x / (2 * q ^ 2) + (q - 1) / (2 * q) +
        ((1 + q) * y / (2 * q ^ 2) + (q - 1) / (2 * q)) - 1 =
        ((x + q * y - q) + (y + q * x - q)) / (2 * q ^ 2) := by
      field_simp
      ring
    have : ((x + q * y - q) + (y + q * x - q)) / (2 * q ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
    linarith

end Fq

theorem actQ_pos' {lam : ℝ} (hl : 0 < lam) : 0 < actQ lam := by
  unfold actQ; positivity

theorem actQ_lt_one' {lam : ℝ} (hl : 0 < lam) : actQ lam < 1 := by
  unfold actQ; rw [div_lt_one (by linarith)]; linarith

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ### The actual marginals and the edge bounds -/

variable (G) in
/-- The actual hard-core marginal `π_v` of the whole vertex set at activity `λ`. -/
noncomputable def gMarg (lam : ℝ) (v : V) : ℝ := rootProb G lam univ v

theorem gMarg_nonneg {lam : ℝ} (hl : 0 ≤ lam) (v : V) : 0 ≤ gMarg G lam v :=
  rootProb_nonneg hl _ _

theorem gMarg_le_actQ {lam : ℝ} (hl : 0 ≤ lam) (v : V) : gMarg G lam v ≤ actQ lam :=
  rootProb_le_actQ hl (mem_univ v)

/-- **The edge bound** `π_u + q π_v ≤ q` (the hard-core conditional occupancy bound). -/
theorem gMarg_edge {lam : ℝ} (hl : 0 < lam) {u v : V} (huv : G.Adj u v) :
    gMarg G lam u + actQ lam * gMarg G lam v ≤ actQ lam := by
  have hw : ∀ _ : V, (0 : ℝ) ≤ lam := fun _ => hl.le
  set Zs := Zw G (fun _ => lam) univ
  set Zu := Zw G (fun _ => lam) (outsideClosedNbhd G univ u)
  set Zv := Zw G (fun _ => lam) (outsideClosedNbhd G univ v)
  set Zuv := Zw G (fun _ => lam) ((univ.erase u).erase v)
  have hvu : v ∈ univ.erase u := mem_erase.mpr ⟨(G.ne_of_adj huv).symm, mem_univ v⟩
  have h1 : Zs = Zw G (fun _ => lam) (univ.erase u) + lam * Zu := Zw_erase_add _ (mem_univ u)
  have h2 : Zw G (fun _ => lam) (univ.erase u) =
      Zuv + lam * Zw G (fun _ => lam) (outsideClosedNbhd G (univ.erase u) v) :=
    Zw_erase_add _ hvu
  have h3 : outsideClosedNbhd G (univ.erase u) v = outsideClosedNbhd G univ v := by
    rw [outside_erase_comm]
    apply Finset.erase_eq_of_notMem
    rw [mem_outsideClosedNbhd]
    exact fun h => h.2.2 huv.symm
  have h4 : Zu ≤ Zuv := by
    apply Zw_mono hw
    intro x hx
    rw [mem_outsideClosedNbhd] at hx
    refine mem_erase.mpr ⟨?_, mem_erase.mpr ⟨hx.2.1, hx.1⟩⟩
    rintro rfl
    exact hx.2.2 huv
  have hZs : 0 < Zs := Zw_pos hw _
  have hZv : 0 ≤ Zv := (Zw_pos hw _).le
  have key : (1 + lam) * (lam * Zu) + lam * (lam * Zv) ≤ lam * Zs := by
    rw [h1, h2, h3]
    nlinarith
  unfold gMarg rootProb actQ
  rw [show lam * Zu / Zs + lam / (1 + lam) * (lam * Zv / Zs) =
      ((1 + lam) * (lam * Zu) + lam * (lam * Zv)) / ((1 + lam) * Zs) by field_simp]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-! ### The refined source field -/

variable (G) in
/-- The largest neighbouring source `max(0, max_{y ~ v} f_q(π_y))` (the source value of the
maximizing owner `a(v)`; `0` for an isolated vertex). -/
noncomputable def nbrMax (lam : ℝ) (v : V) : ℝ :=
  (univ.filter (G.Adj v)).fold max 0 (fun y => fq (actQ lam) (gMarg G lam y))

variable (G) in
/-- **The refined source field** `s'_v = (1 + s_v − s_{a(v)})/2`, `s_v = f_q(π_v)`. -/
noncomputable def sRef (lam : ℝ) (v : V) : ℝ :=
  (1 + fq (actQ lam) (gMarg G lam v) - nbrMax G lam v) / 2

theorem nbrMax_nonneg (lam : ℝ) (v : V) : 0 ≤ nbrMax G lam v :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem le_nbrMax {lam : ℝ} {v y : V} (hvy : G.Adj v y) :
    fq (actQ lam) (gMarg G lam y) ≤ nbrMax G lam v :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨y, mem_filter.mpr ⟨mem_univ y, hvy⟩, le_rfl⟩)

theorem nbrMax_le {lam c : ℝ} {v : V} (h0 : 0 ≤ c)
    (h : ∀ y, G.Adj v y → fq (actQ lam) (gMarg G lam y) ≤ c) : nbrMax G lam v ≤ c :=
  (Finset.fold_max_le _).mpr ⟨h0, fun y hy => h y (mem_filter.mp hy).2⟩

theorem fq_gMarg_le_one {lam : ℝ} (hl : 0 < lam) (v : V) : fq (actQ lam) (gMarg G lam v) ≤ 1 :=
  fq_le_one (actQ_pos' hl) (actQ_lt_one' hl) (gMarg_le_actQ hl.le v)

theorem fq_gMarg_nonneg {lam : ℝ} (hl : 0 < lam) (v : V) : 0 ≤ fq (actQ lam) (gMarg G lam v) :=
  fq_nonneg (actQ_pos' hl) (gMarg_nonneg hl.le v)

/-- The source field is feasible on every edge. -/
theorem fq_gMarg_edge {lam : ℝ} (hl : 0 < lam) {u v : V} (huv : G.Adj u v) :
    fq (actQ lam) (gMarg G lam u) + fq (actQ lam) (gMarg G lam v) ≤ 1 :=
  fq_edge (actQ_pos' hl) (gMarg_edge hl huv) (gMarg_edge hl huv.symm)

/-- `f_q(π_v) + max_{y ~ v} f_q(π_y) ≤ 1`. -/
theorem fq_add_nbrMax_le {lam : ℝ} (hl : 0 < lam) (v : V) :
    fq (actQ lam) (gMarg G lam v) + nbrMax G lam v ≤ 1 := by
  have h := nbrMax_le (G := G) (lam := lam) (v := v)
    (c := 1 - fq (actQ lam) (gMarg G lam v)) (by linarith [fq_gMarg_le_one (G := G) hl v])
    (fun y hvy => by linarith [fq_gMarg_edge (G := G) hl hvy])
  linarith

theorem fq_le_sRef {lam : ℝ} (hl : 0 < lam) (v : V) :
    fq (actQ lam) (gMarg G lam v) ≤ sRef G lam v := by
  unfold sRef
  linarith [fq_add_nbrMax_le (G := G) hl v]

theorem sRef_nonneg {lam : ℝ} (hl : 0 < lam) (v : V) : 0 ≤ sRef G lam v :=
  le_trans (fq_gMarg_nonneg hl v) (fq_le_sRef hl v)

theorem sRef_le_one {lam : ℝ} (hl : 0 < lam) (v : V) : sRef G lam v ≤ 1 := by
  unfold sRef
  linarith [fq_gMarg_le_one (G := G) hl v, nbrMax_nonneg (G := G) lam v]

/-- **The refined field is feasible on every edge**: `s'_u + s'_v ≤ 1`. -/
theorem sRef_edge {lam : ℝ} {u v : V} (huv : G.Adj u v) : sRef G lam u + sRef G lam v ≤ 1 := by
  unfold sRef
  linarith [le_nbrMax (G := G) (lam := lam) huv, le_nbrMax (G := G) (lam := lam) huv.symm]

/-- **Lemma 2 at a record**: if `π_v = r p`, `r ≤ 1`, and every neighbour's marginal is at most
`M_up(p, r)`, then `g(p, r) ≤ s'_v`. -/
theorem src_le_sRef {lam : ℝ} (hl : 0 < lam) {v : V} {p ρ : ℝ} (hπ : gMarg G lam v = ρ * p)
    (hρ1 : ρ ≤ 1) (hnb : ∀ y, G.Adj v y → gMarg G lam y ≤ mUp lam p ρ) :
    src lam p ρ ≤ sRef G lam v := by
  have hq := actQ_pos' hl
  have hpr : p * ρ = gMarg G lam v := by rw [hπ, mul_comm]
  unfold src
  rw [hpr]
  refine max_le (fq_le_sRef hl v) ?_
  have hM0 : 0 ≤ mUp lam p ρ := le_trans (by linarith) (le_max_left _ _)
  have hnm : nbrMax G lam v ≤ fq (actQ lam) (mUp lam p ρ) :=
    nbrMax_le (fq_nonneg hq hM0) (fun y hvy => fq_mono hq (hnb y hvy))
  unfold sRef
  linarith

/-! ### The competitor: a dynamic programme over the rooted tree -/

section DP

variable (π σ : V → ℝ)

omit [Fintype V] in
/-- **The competitor on a rooted subtree.**  For an edge-feasible field `σ ∈ [0, 1]` there are
actual independent sets `I₁ ⊆ s` and `I₀ ⊆ s − r` with
`∑_{v ∈ s} π_v σ_v ≤ σ_r π(I₁) + (1 − σ_r) π(I₀)`. -/
theorem dp_rooted (hG : G.IsAcyclic) (hσ0 : ∀ v, 0 ≤ σ v)
    (hedge : ∀ u v, G.Adj u v → σ u + σ v ≤ 1) {s : Finset V} (hs : ConnectedIn G s) {r : V}
    (hr : r ∈ s) :
    ∃ I1 I0 : Finset V, I1 ⊆ s ∧ IsIndepFinset G I1 ∧ I0 ⊆ s.erase r ∧ IsIndepFinset G I0 ∧
      ∑ v ∈ s, π v * σ v ≤ σ r * ∑ v ∈ I1, π v + (1 - σ r) * ∑ v ∈ I0, π v := by
  refine rooted_induction hG (P := fun s r => ∃ I1 I0 : Finset V, I1 ⊆ s ∧ IsIndepFinset G I1 ∧
      I0 ⊆ s.erase r ∧ IsIndepFinset G I0 ∧
      ∑ v ∈ s, π v * σ v ≤ σ r * ∑ v ∈ I1, π v + (1 - σ r) * ∑ v ∈ I0, π v) ?_ hs hr
  intro s r hs hr ih
  choose! A1 A0 hA1s hA1i hA0s hA0i hAsum using ih
  have hJex : ∀ w, ∃ Jw : Finset V, (Jw = A1 w ∨ Jw = A0 w) ∧
      ∑ v ∈ A1 w, π v ≤ ∑ v ∈ Jw, π v ∧ ∑ v ∈ A0 w, π v ≤ ∑ v ∈ Jw, π v := by
    intro w
    rcases le_total (∑ v ∈ A0 w, π v) (∑ v ∈ A1 w, π v) with h | h
    · exact ⟨A1 w, Or.inl rfl, le_rfl, h⟩
    · exact ⟨A0 w, Or.inr rfl, h, le_rfl⟩
  choose J hJeq hJ1 hJ0 using hJex
  have hJs : ∀ w ∈ nbrsIn G s r, J w ⊆ compIn G (s.erase r) w := by
    intro w hw
    rcases hJeq w with h | h <;> rw [h]
    · exact hA1s w hw
    · exact (hA0s w hw).trans (Finset.erase_subset _ _)
  have hJi : ∀ w ∈ nbrsIn G s r, IsIndepFinset G (J w) := by
    intro w hw
    rcases hJeq w with h | h <;> rw [h]
    · exact hA1i w hw
    · exact hA0i w hw
  have hdisjC : (↑(nbrsIn G s r) : Set V).PairwiseDisjoint (fun w => compIn G (s.erase r) w) :=
    fun i hi j hj hij => disjoint_branches hG hi hj hij
  have hdisj0 : (↑(nbrsIn G s r) : Set V).PairwiseDisjoint A0 := fun i hi j hj hij =>
    (disjoint_branches hG hi hj hij).mono ((hA0s i hi).trans (Finset.erase_subset _ _))
      ((hA0s j hj).trans (Finset.erase_subset _ _))
  have hdisjJ : (↑(nbrsIn G s r) : Set V).PairwiseDisjoint J := fun i hi j hj hij =>
    (disjoint_branches hG hi hj hij).mono (hJs i hi) (hJs j hj)
  -- independence of a union of branch sets
  have hindep_union : ∀ K : V → Finset V,
      (∀ w ∈ nbrsIn G s r, K w ⊆ compIn G (s.erase r) w) →
      (∀ w ∈ nbrsIn G s r, IsIndepFinset G (K w)) → IsIndepFinset G ((nbrsIn G s r).biUnion K) := by
    intro K hKC hKi a ha b hb hab
    rw [Finset.mem_biUnion] at ha hb
    obtain ⟨i, hi, hai⟩ := ha
    obtain ⟨j, hj, hbj⟩ := hb
    by_cases hij : i = j
    · subst hij
      exact hKi i hi a hai b hbj hab
    · exact not_adj_branches hG hi hj hij (hKC i hi hai) (hKC j hj hbj) hab
  have hr0 : r ∉ (nbrsIn G s r).biUnion A0 := by
    intro h
    rw [Finset.mem_biUnion] at h
    obtain ⟨w, hw, hrw⟩ := h
    have := compIn_subset _ _ (Finset.mem_of_mem_erase (hA0s w hw hrw))
    exact (Finset.mem_erase.mp this).1 rfl
  refine ⟨insert r ((nbrsIn G s r).biUnion A0), (nbrsIn G s r).biUnion J, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with hxr | hx
    · rw [hxr]; exact hr
    · rw [Finset.mem_biUnion] at hx
      obtain ⟨w, hw, hxw⟩ := hx
      exact Finset.mem_of_mem_erase
        (compIn_subset _ _ (Finset.mem_of_mem_erase (hA0s w hw hxw)))
  · have hU := hindep_union A0 (fun w hw => (hA0s w hw).trans (Finset.erase_subset _ _)) hA0i
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with har | ha
    · rcases Finset.mem_insert.mp hb with hbr | hb
      · rw [har, hbr] at hab
        exact G.irrefl hab
      · rw [har] at hab
        rw [Finset.mem_biUnion] at hb
        obtain ⟨w, hw, hbw⟩ := hb
        have hbC := hA0s w hw hbw
        have hbw' : b = w := eq_of_mem_branch_of_adj hG (mem_nbrsIn.mp hw).2
          (Finset.mem_of_mem_erase hbC) hab
        exact (Finset.mem_erase.mp hbC).1 hbw'
    · rcases Finset.mem_insert.mp hb with hbr | hb
      · rw [hbr] at hab
        rw [Finset.mem_biUnion] at ha
        obtain ⟨w, hw, haw⟩ := ha
        have haC := hA0s w hw haw
        have haw' : a = w := eq_of_mem_branch_of_adj hG (mem_nbrsIn.mp hw).2
          (Finset.mem_of_mem_erase haC) hab.symm
        exact (Finset.mem_erase.mp haC).1 haw'
      · exact hU a ha b hb hab
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨w, hw, hxw⟩ := hx
    exact compIn_subset _ _ (hJs w hw hxw)
  · exact hindep_union J hJs hJi
  · -- the sum inequality
    have hsplit : ∑ v ∈ s, π v * σ v =
        π r * σ r + ∑ w ∈ nbrsIn G s r, ∑ v ∈ compIn G (s.erase r) w, π v * σ v := by
      rw [← Finset.add_sum_erase s _ hr]
      congr 1
      conv_lhs => rw [erase_eq_biUnion hs hr]
      rw [Finset.sum_biUnion hdisjC]
    have hI1 : ∑ v ∈ insert r ((nbrsIn G s r).biUnion A0), π v =
        π r + ∑ w ∈ nbrsIn G s r, ∑ v ∈ A0 w, π v := by
      rw [Finset.sum_insert hr0, Finset.sum_biUnion hdisj0]
    have hI0 : ∑ v ∈ (nbrsIn G s r).biUnion J, π v = ∑ w ∈ nbrsIn G s r, ∑ v ∈ J w, π v :=
      Finset.sum_biUnion hdisjJ
    rw [hsplit, hI1, hI0]
    have hchild : ∀ w ∈ nbrsIn G s r, ∑ v ∈ compIn G (s.erase r) w, π v * σ v ≤
        σ r * ∑ v ∈ A0 w, π v + (1 - σ r) * ∑ v ∈ J w, π v := by
      intro w hw
      have h1 := hAsum w hw
      have hσw : σ w ≤ 1 - σ r := by linarith [hedge r w (mem_nbrsIn.mp hw).2]
      have hm1 := hJ1 w
      have hm0 := hJ0 w
      have hσw0 := hσ0 w
      nlinarith [mul_le_mul_of_nonneg_left hm1 hσw0, mul_le_mul_of_nonneg_right hσw
        (by linarith : 0 ≤ ∑ v ∈ J w, π v - ∑ v ∈ A0 w, π v)]
    calc π r * σ r + ∑ w ∈ nbrsIn G s r, ∑ v ∈ compIn G (s.erase r) w, π v * σ v
        ≤ π r * σ r + ∑ w ∈ nbrsIn G s r,
            (σ r * ∑ v ∈ A0 w, π v + (1 - σ r) * ∑ v ∈ J w, π v) :=
          by linarith [Finset.sum_le_sum hchild]
      _ = σ r * (π r + ∑ w ∈ nbrsIn G s r, ∑ v ∈ A0 w, π v) +
            (1 - σ r) * ∑ w ∈ nbrsIn G s r, ∑ v ∈ J w, π v := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          ring

omit [Fintype V] in
/-- **The competitor on every vertex set closed under adjacency** (in particular the whole vertex
set): there is an actual independent set `I ⊆ s` with `∑_{v ∈ s} π_v σ_v ≤ ∑_{v ∈ I} π_v`. -/
theorem dp_closed (hG : G.IsAcyclic) (hσ0 : ∀ v, 0 ≤ σ v) (hσ1 : ∀ v, σ v ≤ 1)
    (hedge : ∀ u v, G.Adj u v → σ u + σ v ≤ 1) :
    ∀ s : Finset V, (∀ v ∈ s, ∀ w, G.Adj v w → w ∈ s) →
      ∃ I ⊆ s, IsIndepFinset G I ∧ ∑ v ∈ s, π v * σ v ≤ ∑ v ∈ I, π v := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro hsc
  rcases s.eq_empty_or_nonempty with hs0 | ⟨x, hx⟩
  · refine ⟨∅, Finset.empty_subset _, fun v hv => absurd hv (Finset.notMem_empty v), ?_⟩
    rw [hs0]
    simp
  · have hKs : compIn G s x ⊆ s := compIn_subset _ _
    have hxK : x ∈ compIn G s x := self_mem_compIn hx
    have hno : ∀ a ∈ compIn G s x, ∀ b ∈ s \ compIn G s x, ¬ G.Adj a b := by
      intro a ha b hb hab
      rw [Finset.mem_sdiff] at hb
      exact hb.2 (mem_compIn_of_adjIn ha ⟨hKs ha, hb.1, hab⟩)
    have hRc : ∀ v ∈ s \ compIn G s x, ∀ w, G.Adj v w → w ∈ s \ compIn G s x := by
      intro v hv w hvw
      rw [Finset.mem_sdiff] at hv ⊢
      refine ⟨hsc v hv.1 w hvw, fun hwK => hv.2 ?_⟩
      exact mem_compIn_of_adjIn hwK ⟨hKs hwK, hv.1, hvw.symm⟩
    obtain ⟨I1, I0, hI1s, hI1i, hI0s, hI0i, hK⟩ :=
      dp_rooted π σ hG hσ0 hedge (connectedIn_compIn s x) hxK
    obtain ⟨IR, hIRs, hIRi, hR⟩ :=
      ih (s \ compIn G s x) (Finset.sdiff_ssubset hKs ⟨x, hxK⟩) hRc
    obtain ⟨IK, hIKeq, hIK1, hIK0⟩ : ∃ IK : Finset V, (IK = I1 ∨ IK = I0) ∧
        ∑ v ∈ I1, π v ≤ ∑ v ∈ IK, π v ∧ ∑ v ∈ I0, π v ≤ ∑ v ∈ IK, π v := by
      rcases le_total (∑ v ∈ I0, π v) (∑ v ∈ I1, π v) with h | h
      · exact ⟨I1, Or.inl rfl, le_rfl, h⟩
      · exact ⟨I0, Or.inr rfl, h, le_rfl⟩
    have hIKs : IK ⊆ compIn G s x := by
      rcases hIKeq with h | h <;> rw [h]
      · exact hI1s
      · exact hI0s.trans (Finset.erase_subset _ _)
    have hIKi : IsIndepFinset G IK := by
      rcases hIKeq with h | h <;> rw [h]
      · exact hI1i
      · exact hI0i
    have hIKsum : ∑ v ∈ compIn G s x, π v * σ v ≤ ∑ v ∈ IK, π v := by
      have hσx0 := hσ0 x
      have hσx1 := hσ1 x
      nlinarith [mul_le_mul_of_nonneg_left hIK1 hσx0,
        mul_le_mul_of_nonneg_left hIK0 (by linarith : (0 : ℝ) ≤ 1 - σ x)]
    have hdisj : Disjoint IK IR := Finset.disjoint_of_subset_left hIKs
      (Finset.disjoint_of_subset_right hIRs Finset.disjoint_sdiff)
    refine ⟨IK ∪ IR, Finset.union_subset (hIKs.trans hKs) (hIRs.trans Finset.sdiff_subset), ?_, ?_⟩
    · intro a ha b hb hab
      rcases Finset.mem_union.mp ha with ha | ha <;> rcases Finset.mem_union.mp hb with hb | hb
      · exact hIKi a ha b hb hab
      · exact hno a (hIKs ha) b (hIRs hb) hab
      · exact hno b (hIKs hb) a (hIRs ha) hab.symm
      · exact hIRi a ha b hb hab
    · have hsplit : s = compIn G s x ∪ (s \ compIn G s x) :=
        (Finset.union_sdiff_of_subset hKs).symm
      rw [hsplit, Finset.sum_union Finset.disjoint_sdiff, Finset.sum_union hdisj]
      linarith

end DP

end Erdos993Lean.Analytic.O2
