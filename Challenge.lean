module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Erdős Problem 993: the independence sequence of a finite forest is unimodal

**Statement.** For a finite graph `G` and a natural number `k`, let `i_k(G)` be the number of independent sets of `G`
with exactly `k` vertices (sets of vertices no two of which are adjacent). `erdos_993_forest`: for every finite
forest `G` there is an index `m` with `i_0(G) ≤ ... ≤ i_m(G)` and `i_m(G) ≥ i_(m+1)(G) ≥ ...` for all later indices.
`erdos_993`: the same for every finite tree; it is the special case of `erdos_993_forest` for connected graphs.

**Origin and status.** The question is attributed to Alavi, Malde, Schwenk and Erdős (Congressus Numerantium 58 (1987),
15-23), which we have not read. Li, Vallier and Zhang (arXiv:2610.07943v1) report its Problem 3 as "For trees (or
perhaps forests), is the vertex independence sequence unimodal?"; the problem page (https://www.erdosproblems.com/993)
states it for any tree or forest. The first claimed proof for all finite forests is by T. Zhang and W. Li (26 and 27
September 2026; doi:10.5281/zenodo.22999166). The Lean follows a second proof, by W. Li, K. Vallier and T. Zhang
("Unimodality of Forest Independence Polynomials"). Its public version is arXiv:2610.07943v1, which the Lean adapts; the
text the Lean follows is version 2.15, deposited with restricted access and under revision by its authors
(doi:10.5281/zenodo.23269638); it was written against version 2.13, and versions 2.14 and 2.15 record the
corrections found during formalization. These texts are not peer reviewed. No priority is claimed.

**How to read the Lean.**
* `SimpleGraph V` with `[Fintype V]` is a finite simple graph (no loops, no multiple edges) on the vertex type `V`;
  `[Fintype V]` is the only hypothesis on `V`. `IsAcyclic` (no cycle), `IsTree` (connected and acyclic) and
  `IsIndepSet` (no two distinct vertices of the set are adjacent) are Mathlib's definitions of the usual notions.
* A forest may have no vertices, no edges or several components. For the graph with no vertices the sequence is
  `1, 0, 0, ...`, which is unimodal. A tree is connected, and a connected graph in Mathlib has at least one vertex.
* `indepSeq G k` counts with `Nat.card`, which returns `0` on an infinite type. This default cannot arise in the
  theorems: when `V` is finite the type of `k`-element sets of vertices is finite and `Nat.card` is its size.
* The sequence is indexed by all natural numbers, not by `0, ..., α(G)` (`α` the independence number). Its terms
  vanish beyond the number of vertices, indeed beyond `α(G)`, and `i_α(G) ≥ 1`; so `UnimodalSeq (indepSeq G)` holds
  exactly when the finite sequence `i_0(G), ..., i_α(G)` is unimodal.
* Both inequalities in `UnimodalSeq` are weak: plateaus are allowed and the peak index `m` need not be unique. The
  statement is unimodality, not log-concavity, and it gives no bound on `m`.
* `V : Type` (universe 0) loses no generality for finite graphs: a finite type is in bijection with some `Fin n`,
  and the hypotheses and the conclusion are unchanged by relabelling vertices. `indepSeq` itself allows `Type*`.

**Relation to formal-conjectures.** The two definitions and the two statement types are taken from
google-deepmind/formal-conjectures, pull request #4192, file `FormalConjectures/ErdosProblems/993.lean` at commit
`99e1ae34a3295d5974bf143810fe98db84f501f2` (Apache License 2.0, copyright The Formal Conjectures Authors). That pull
request was opened on 6 June 2026 by another contributor, approved by a reviewer of that project on 9 October 2026,
and open and not merged on that day; its file marks the problem open. Mapping: `erdos_993_forest`
here is its `erdos_993` (forests), and `erdos_993` here is its `erdos_993.variants.tree` (trees). The names
therefore differ: `erdos_993` is the tree statement here and the forest statement there. With comments removed,
`indepSeq` (43 tokens) and `UnimodalSeq` (52 tokens) are identical in the two files, and each statement (30 tokens)
differs in one token, its name. Further differences: its attribute line `@[category research open, AMS 5]` before
each statement is absent here; it imports `FormalConjecturesUtil`, this file three Mathlib modules; its licence
header, module text and docstrings are not reproduced; its four other declarations, all about spiders, are omitted.
The two `sorry` below are placeholders; `Solution.lean` repeats the four declarations and proves both statements.
-/

@[expose] public section

namespace Erdos993

/-- `indepSeq G k` is the number of `k`-element independent sets of `G`, i.e. the `k`-th term
`i_k(G)` of the independence sequence.

It is the cardinality (`Nat.card`) of the type of finite sets `s` of vertices with `s.card = k` that are independent
in Mathlib's sense (`G.IsIndepSet`: no two distinct elements of `s` are adjacent). The empty set is counted, so
`indepSeq G 0 = 1`. When `V` is finite this type is finite and `Nat.card` is its number of elements, and the value
is `0` as soon as `k` exceeds the number of vertices. The value `0` that `Nat.card` assigns to an infinite type can
occur only for infinite `V`, which both theorems exclude by `[Fintype V]`. -/
noncomputable def indepSeq {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {s : Finset V // s.card = k ∧ G.IsIndepSet (s : Set V)}

/-- A sequence `a : ℕ → ℕ` is *unimodal* if it is nondecreasing up to some index `m` and
nonincreasing thereafter.

Both inequalities are weak, so plateaus are allowed and the index `m` need not be unique; `m = 0` gives a
nonincreasing sequence. The condition concerns the whole infinite sequence. It does not assert log-concavity and
puts no bound on `m`. -/
def UnimodalSeq (a : ℕ → ℕ) : Prop :=
  ∃ m, (∀ i, i < m → a i ≤ a (i + 1)) ∧ (∀ i, m ≤ i → a (i + 1) ≤ a i)

/-- **Erdős Problem 993, for forests.** The independence sequence of every finite forest is unimodal.

`G` ranges over all acyclic simple graphs on a finite vertex type `V`: the graph with no vertices, edgeless graphs
and disconnected graphs are included, and there is no further hypothesis. This is the statement that
formal-conjectures pull request #4192, at commit `99e1ae34`, names `erdos_993`. -/
theorem erdos_993_forest : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsAcyclic → UnimodalSeq (indepSeq G) := by
  sorry

/-- **Erdős Problem 993, for trees.** The independence sequence `i_k(T)` of every finite tree `T` is
unimodal.

It is the special case of `erdos_993_forest` for connected graphs: `IsTree` means connected and acyclic, so a tree
has at least one vertex. This is the statement that formal-conjectures pull request #4192, at commit `99e1ae34`,
names `erdos_993.variants.tree`; there the name `erdos_993` belongs to the forest statement. -/
theorem erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.IsTree → UnimodalSeq (indepSeq G) := by
  sorry

end Erdos993
