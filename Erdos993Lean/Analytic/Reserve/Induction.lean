module

public import Mathlib
public import Erdos993Lean.Analytic.Reserve.Tree

/-!
# O1 by the two-generation reserve: the tree induction

Sources:
the two-generation reserve proof (the induction (R), the grandchild bound (4), the selected-leaf
base, "Actual transfer, termination"), with the signed term of
the upper sharp signed-port proof.


**The reserve (R)** at a rooted subtree `(s, r)` of an acyclic graph, for a set `B` and an activity
`t`, is `F(s) ≥ α y + β u + γ u²/y` with `F = A U(s) − V(s)`, `u` the port and `y` the log-mass of
the root's downward message (`ReserveAt`).  We prove it at every rooted subtree in which every
unselected vertex has a child (`Good`), for every independent `B`, from the per-activity step
certificate `StepCert` (`reserveAt_of_good`), by strong induction on the vertex set: at the root,
the recursion (1) (`resF_rec`, `port_rec`) expresses `F` through the children's `F`, the
children's `G = ∑ F_grandchild` (`resF_erase_root`) and ports; the children carry (R) by induction,
their `G` carries the grandchild bound by Cauchy over the actual grandchild list (`grand_bound`, from
(R) at the grandchildren); a childless child is a selected leaf (`Good`), whose `G = 0` and
`u = p = q`; and the vertex step `reserve_step_cert` closes.  A childless root is the selected-leaf
base.

Scalarity check.  The carried scalars are, for each rooted subtree, `U, V` at both boundaries (inside
`F = resF` and `G = resF (s − r)`), the port `u = port`, the message `p = rootProb` and its log-mass
`y = yLog`, and the children's / grandchildren's log-mass sums `T = Tmass`, `Y`.  Each is a
functional of the actual hard-core law of the actual subtree (`Reserve/Moments.lean`,
`Reserve/Tree.lean`); the step consumes them and emits (R) for the parent; the root consumer is the
assembly (`Reserve/Assembly.lean`), where (R) and PSD give `Var K_B ≤ A W` on the component.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.Reserve

open Finset Erdos993Lean.Analytic.Tail

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

variable (G) in
/-- **The reserve (R)** at the rooted subtree `(s, r)`: `A U(s) − V(s) ≥ α y + β u + γ u²/y`. -/
def ReserveAt (B : Finset V) (t α β γ A : ℝ) (s : Finset V) (r : V) : Prop :=
  α * yLog G t s r + β * port G B t s r + γ * port G B t s r ^ 2 / yLog G t s r ≤
    resF G B t A s

theorem aB_eq_one {B : Finset V} {r : V} (h : r ∈ B) : aB B r = 1 := by
  unfold aB
  rw [if_pos h]

theorem aB_eq_zero {B : Finset V} {r : V} (h : r ∉ B) : aB B r = 0 := by
  unfold aB
  rw [if_neg h]

theorem mem_of_aB_eq_one {B : Finset V} {r : V} (h : aB B r = 1) : r ∈ B := by
  by_contra hr
  rw [aB_eq_zero hr] at h
  norm_num at h

omit [DecidableRel G.Adj] in
/-- A branch of a branch is a proper subset of the vertex set. -/
theorem grandbranch_ssubset {s : Finset V} {r w x : V} (hr : r ∈ s) :
    compIn G ((compIn G (s.erase r) w).erase w) x ⊂ s :=
  ((compIn_subset _ _).trans ((Finset.erase_subset _ _).trans (compIn_subset _ _))).trans_ssubset
    (Finset.erase_ssubset hr)

/-- **The grandchild bound at a child** (inequality (4), second line): if (R) holds at every
grandchild subtree of the child `w`, then
`G_w ≥ α T_w + β (a_w − u_w/s_w) + γ (a_w − u_w/s_w)²/T_w`, `s_w = msg t T_w`. -/
theorem grand_bound_tree (hG : G.IsAcyclic) {B : Finset V} {t α β γ A : ℝ} (ht : 0 < t)
    (hγ : 0 ≤ γ) {C : Finset V} (hC : ConnectedIn G C) {w : V} (hw : w ∈ C)
    (hR : ∀ x ∈ nbrsIn G C w, ReserveAt G B t α β γ A (compIn G (C.erase w) x) x) :
    α * Tmass G t C w + β * (aB B w - port G B t C w / msg t (Tmass G t C w)) +
        γ * (aB B w - port G B t C w / msg t (Tmass G t C w)) ^ 2 / Tmass G t C w ≤
      resF G B t A (C.erase w) := by
  rw [resF_erase_root hG ht.le hC hw]
  refine grand_bound (nbrsIn G C w) (fun x => yLog G t (compIn G (C.erase w) x) x)
    (fun x => port G B t (compIn G (C.erase w) x) x)
    (fun x => resF G B t A (compIn G (C.erase w) x)) ?_ rfl hγ (msg_pos ht _).ne' ?_ hR
  · intro x hx
    exact yLog_pos hG ht (compIn_branch hG hC hw hx).1 (compIn_branch hG hC hw hx).2.1
  · rw [← rootProb_eq_msg hG ht hC hw]
    exact port_rec hG ht.le hC hw

/-- **The selected-leaf child**: a child `w` whose own children's log-mass is `0` has no children;
in a good tree it is selected, its occupied-parent budget is `G_w = 0` and its port is
`u_w = p_w = msg t 0`. -/
theorem leaf_child (hG : G.IsAcyclic) {B : Finset V} {t A : ℝ} (ht : 0 < t) {C : Finset V}
    (hC : ConnectedIn G C) {w : V} (hw : w ∈ C) (hgood : Good G B C w)
    (hT : Tmass G t C w = 0) :
    aB B w = 1 ∧ resF G B t A (C.erase w) = 0 ∧ port G B t C w = msg t (Tmass G t C w) := by
  have hN : nbrsIn G C w = ∅ := by
    by_contra hne
    have := Tmass_pos hG ht hC hw (Finset.nonempty_iff_ne_empty.mpr hne)
    linarith
  have hwB : w ∈ B := hgood.root_mem hw hN
  have hC1 : C = {w} := eq_singleton_of_nbrsIn_empty hC hw hN
  refine ⟨aB_eq_one hwB, ?_, ?_⟩
  · rw [hC1, Finset.erase_singleton]
    unfold resF
    rw [meanB_empty, varB_empty]
    ring
  · rw [port_rec hG ht.le hC hw, hN, Finset.sum_empty, aB_eq_one hwB,
      rootProb_eq_msg hG ht hC hw]
    ring

/-- **The reserve induction.**  For an acyclic graph, an independent set `B` and a step certificate
at activity `t`, the reserve (R) holds at every rooted subtree in which every unselected vertex has a
child. -/
theorem reserveAt_of_good (hG : G.IsAcyclic) {B : Finset V} (hB : IsIndepFinset G B)
    {t α β γ A : ℝ} (hcert : StepCert γ t α β A) :
    ∀ (s : Finset V) (r : V), ConnectedIn G s → r ∈ s → Good G B s r →
      ReserveAt G B t α β γ A s r := by
  have ht : 0 < t := hcert.lam_pos
  have hγ : 0 < γ := hcert.gamma_pos
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
  intro r hs hr hgood
  -- the children: connected, rooted, proper, good, carrying (R)
  have hCc : ∀ w ∈ nbrsIn G s r, ConnectedIn G (compIn G (s.erase r) w) := fun w hw =>
    (compIn_branch hG hs hr hw).1
  have hCw : ∀ w ∈ nbrsIn G s r, w ∈ compIn G (s.erase r) w := fun w hw =>
    (compIn_branch hG hs hr hw).2.1
  have hCs : ∀ w ∈ nbrsIn G s r, compIn G (s.erase r) w ⊂ s := fun _ _ =>
    (compIn_subset _ _).trans_ssubset (Finset.erase_ssubset hr)
  have hCg : ∀ w ∈ nbrsIn G s r, Good G B (compIn G (s.erase r) w) w := fun w hw =>
    hgood.branch hG hr hw
  have hRw : ∀ w ∈ nbrsIn G s r, ReserveAt G B t α β γ A (compIn G (s.erase r) w) w :=
    fun w hw => ih _ (hCs w hw) w (hCc w hw) (hCw w hw) (hCg w hw)
  -- the vertex step
  have key := reserve_step_cert hcert (nbrsIn G s r) (aB B r) (aB_cases B r)
    (fun hN => aB_eq_one (hgood.root_mem hr hN)) (fun w => aB B w)
    (fun w => port G B t (compIn G (s.erase r) w) w)
    (fun w => resF G B t A (compIn G (s.erase r) w))
    (fun w => resF G B t A ((compIn G (s.erase r) w).erase w))
    (fun w => Tmass G t (compIn G (s.erase r) w) w)
    (fun w _ => aB_cases B w)
    (fun ha w hw => by
      have hrB := mem_of_aB_eq_one ha
      have hwB : w ∉ B := fun hwB => hB r hrB w hwB (mem_nbrsIn.mp hw).2
      exact aB_eq_zero hwB)
    (fun w hw => Tmass_nonneg hG ht (hCc w hw) (hCw w hw))
    (fun w hw => by
      have h := hRw w hw
      unfold ReserveAt at h
      rw [yLog_eq_lmass hG ht (hCc w hw) (hCw w hw)] at h
      exact h)
    (fun w hw _ => grand_bound_tree hG ht hγ.le (hCc w hw) (hCw w hw) fun x hx =>
      ih _ (grandbranch_ssubset hr) x (compIn_branch hG (hCc w hw) (hCw w hw) hx).1
        (compIn_branch hG (hCc w hw) (hCw w hw) hx).2.1
        ((hCg w hw).branch hG (hCw w hw) hx))
    (fun w hw hT => leaf_child hG ht (hCc w hw) (hCw w hw) (hCg w hw) hT)
  beta_reduce at key
  rw [← Tmass_eq_sum_lmass hG ht hs hr, ← rootProb_eq_msg hG ht hs hr,
    ← yLog_eq_lmass hG ht hs hr, ← port_rec hG ht.le hs hr, ← resF_rec hG ht.le hs hr] at key
  exact key

end Erdos993Lean.Analytic.Reserve
