# Unimodality of the independence sequence of a finite forest (Erdős Problem 993), in Lean 4

A Lean 4 and Mathlib formalization of one theorem: for every finite forest, the numbers of independent sets with
0, 1, 2, ... vertices weakly increase up to some index and weakly decrease after it. This is the statement listed as
Erdős Problem 993; later sources attribute the question to a 1987 paper of Alavi, Malde, Schwenk and Erdős
(section 2). The first claimed proof for all finite forests is by T. Zhang and W. Li (self-archived preprints
of 26 and 27 September 2026). This repository formalizes a second proof, from a manuscript of W. Li, K. Vallier
and T. Zhang. No priority is claimed, and this is not the first formalization of the theorem (section 8).

## 1. The statement
For a finite graph `G` let `i_k(G)` be the number of independent sets of `G` with exactly `k` vertices (sets of
vertices no two of which are adjacent; the empty set counts, so `i_0(G) = 1`). **Forests:** for every finite forest
`G` there is an index `m` with `i_0(G) ≤ ... ≤ i_m(G)` and `i_m(G) ≥ i_(m+1)(G) ≥ ...`. **Trees:** the same for
every finite tree, which is the special case of connected forests. In `Challenge.lean` (namespace `Erdos993`):

    noncomputable def indepSeq {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
      Nat.card {s : Finset V // s.card = k ∧ G.IsIndepSet (s : Set V)}
    def UnimodalSeq (a : ℕ → ℕ) : Prop := ∃ m, (∀ i, i < m → a i ≤ a (i + 1)) ∧ (∀ i, m ≤ i → a (i + 1) ≤ a i)
    theorem erdos_993_forest : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsAcyclic → UnimodalSeq (indepSeq G)
    theorem erdos_993 : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.IsTree → UnimodalSeq (indepSeq G)

(Line breaks differ from the file.) `Solution.lean` repeats the four declarations and proves both theorems. The
module text of `Challenge.lean` explains every Lean idiom (`[Fintype V]`, `IsAcyclic`, `IsTree`, `Nat.card`, `Type`).

## 2. Comparison with the question as posed
- **The 1987 paper** (Alavi, Malde, Schwenk and Erdős, Congressus Numerantium 58 (1987), 15-23). Nobody on our side
  has read it. As reported by later sources: arXiv:2610.07943v1 prints its Problem 3 as "For trees (or perhaps
  forests), is the vertex independence sequence unimodal?"; the abstract of Levit and Mandrescu, arXiv:math/0211036,
  reports the same form; the formal-conjectures file locates it on page 21; the zbMATH review (Zbl 0679.05061)
  describes a sequence indexed from 1 to the independence number.
- **Problem page** (https://www.erdosproblems.com/993, read 9 October 2026): the sequence of any tree or forest is
  unimodal, `i_0 ≤ ... ≤ i_m ≥ i_(m+1) ≥ ...` for some `m ≥ 0`; first index 0, weak inequalities, no last index.
- **formal-conjectures** (google-deepmind/formal-conjectures, pull request #4192, opened on 6 June 2026 by another
  contributor (GitHub user AlperTheKing), approved by a reviewer of that project on 9 October 2026, open and not
  merged on that day; file `FormalConjectures/ErdosProblems/993.lean` at commit `99e1ae34a3295d5974bf143810fe98db84f501f2`). The
  file marks the problem open. Mapping: our `erdos_993_forest` is its `erdos_993` (forests) and our `erdos_993` is
  its `erdos_993.variants.tree` (trees); so `erdos_993` names the tree statement here, the forest statement there.
  With comments removed, `indepSeq` (43 tokens) and `UnimodalSeq` (52 tokens) are identical in the two files and
  each statement (30 tokens) differs in one token, its name. Not reproduced here: its attribute line `@[category
  research open, AMS 5]` before each statement, its import, its texts and its four declarations about spiders.
- **An earlier candidate statement of ours.** formal-conjectures issue #5012 (opened 16 August 2026 by K. Vallier,
  AI-assisted as disclosed there; open) proposed a statement for forests with `IsAcyclic`, counting with Mathlib's
  `indepSetFinset` and asking for a peak over all natural numbers. `Erdos993Lean/Statement.lean` counts the same
  way, and `count_eq` in `Erdos993Lean/PalomarBridge.lean` proves that this count equals the `Nat.card` count above.
- **Manuscript**, main theorem (the same in arXiv v1 and version 2.15): for every finite forest, `i_0, ..., i_α` is
  unimodal (`α` the independence number).
- **These forms agree.** The forest form contains the tree form. A first index 0 or 1 makes no difference, since
  `i_0 = 1 ≤ n = i_1` for `n ≥ 1` vertices; nor does an index over all natural numbers, since `i_k = 0` for `k > α`
  and `i_α ≥ 1`. All inequalities are weak. The empty graph is a forest (sequence `1, 0, 0, ...`). The Lean proves
  the theorem on `Fin n` up to index `α`; `Erdos993Lean/PalomarBridge.lean` proves the passage to the form above.

## 3. Background and prior work
Compiled on 9 October 2026 from arXiv abstracts, the problem page, GitHub and DOI registry records. Journal papers
were not read; what we take from another paper's report is marked. Every item has an entry in `formalization.yaml`.
- **Origin.** The 1987 paper shows that for general graphs the numbers of independent sets of each size can occur
  in any order (zbMATH review); the question for trees and forests is reported from it (section 2).
- **Partial results.** Claw-free graphs (Hamidoune 1990; Chudnovsky and Seymour 2007; as reported in
  arXiv:2610.07943v1); recursively built trees (Galvin and Hilyard, arXiv:1701.02204); spiders (Li, Li, Yang and
  Zhang, Selecta Math. 32 (2026), article 87); random trees (Basit and Galvin, Electron. J. Combin. 28(3), P3.23).
- **Stronger statements fail.** Log-concavity fails for trees from 26 vertices on (Kadrawi, Levit, Yosef and
  Mizrachi 2023, as reported by Ramos and Sun, arXiv:2510.18826; Kadrawi and Levit, Ars Math. Contemp. 25(4) (2025),
  P4.03; Galvin, arXiv:2502.10654). Bipartite graphs need not be unimodal (Bhattacharyya and Kahn, arXiv:1301.1752).
- **Large forests.** Fang, Lu, Nevo, Yao and Zheng (arXiv:2609.20961v1, 17 September 2026) report a proof for all
  forests with at least `N0` vertices, `N0` not explicit, and write that the question for all sizes remains open.
  A GitHub preprint by Z. Zou (release of 11 September 2026) reports a statement of the same kind.
- **First proof for all finite forests.** T. Zhang and W. Li, as the manuscript attributes it, citing T. Zhang,
  "Exact Certificates for Unimodality of Forest Independence Polynomials" (v1.1, 26 September 2026, GitHub), and
  T. Zhang and W. Li, "Unimodality of Forest Independence Polynomials" (doi:10.5281/zenodo.22999166, 27 September).
  Computer-assisted; self-archived, not peer reviewed, not found on arXiv.
- **Second proof.** W. Li, K. Vallier and T. Zhang, "Unimodality of Forest Independence Polynomials". The public
  version is arXiv:2610.07943v1 (6 October 2026), which the Lean adapts. The text the Lean follows is version 2.15,
  deposited on Zenodo with restricted access (doi:10.5281/zenodo.23269638) and under revision by its
  authors. It keeps the decomposition, binomial mixture and rank window of the first proof. Not peer reviewed.
- **Trackers on 9 October 2026.** The problem page shows no status word and lists two proof claims (Fang et al.;
  T. Zhang) under a notice that listing is no guarantee of correctness. formal-conjectures marks the problem open.

## 4. What is and is not claimed
Claimed: `Solution.lean` proves the two statements of `Challenge.lean` with no `sorry`, from the axioms `propext`,
`Classical.choice` and `Quot.sound` only; every finite computation is evaluated by the Lean kernel, without
`native_decide`. Not claimed: priority; a first formalization (section 8); correctness of the prose of any
manuscript (machine checking establishes the Lean theorem, not the text); peer review. Every 2026 manuscript cited
here, ours included, is a provisional preprint, not refereed. New here is only a formalization of the second proof
by kernel evaluation alone. Of that proof the public version is arXiv:2610.07943v1, which the Lean adapts; the text
the Lean follows is version 2.15, deposited with restricted access and under revision by its authors (section 5).
Our search of 9 October 2026 (the web, GitHub, arXiv, the problem page) found no Coq or Isabelle formalization.
Readers: combinatorialists working on independence polynomials; formalizers. Limits:
1. Heavy reliance on computation: about 13,700 kernel evaluations; at least 85% of the source is certificate data.
2. Two parts, at most 24 vertices and at least 25, by different arguments; one unified argument would be preferable.
3. Trusted: the Lean kernel, the three axioms, `Challenge.lean`, and Mathlib's definitions at the pinned revision.
   Six small custom elaborators and macros run during elaboration; the kernel checks their output.
4. No human has read the Lean proofs, and no human has yet read the manuscript's proofs in full (section 7).
5. Module comments were revised for publication (comments only; the code is unchanged). Some keep working labels
   of statements (T1, O1, ...) and names of data records; no claim rests on them.
6. Some imported files (for example `Erdos993Lean/Analytic/V22/`) hold declarations the final theorem does not use.
   `FinalChecks.lean` applies the theorem to four small graphs; these are not tests. "native" inside identifiers
   (280 files) names a coordinate, not an evaluation.
7. The text that the Lean follows is not openly posted; it is deposited with restricted access and available from
   the authors on request.

## 5. Correspondence with the manuscript
The public text is arXiv:2610.07943v1: the Lean proves its main theorem and keeps its reduction (window of ranks,
decomposition, choice of activity, moment criterion, split at 24 and 25 vertices). The text the Lean follows is
version 2.15 (restricted access; the Lean was written against version 2.13, and versions 2.14 and 2.15 record the
corrections found during formalization). The second column gives the statement of arXiv v1 where it is the same.
"V213" is the directory `Erdos993Lean/Analytic/V213/` (`V/` below).

| Version 2.15 | arXiv v1, same statement | Lean declaration | Module |
|---|---|---|---|
| Theorems 1.1, 2.9 | main theorem | `Erdos993.erdos_993_forest`; `theorem29`, `erdos993_v213_final` | `Solution.lean`; `V/Final.lean` |
| Lemma 2.2; Theorem 2.4 | Corollary 2.5; Theorem 3.9 | `window_reduction`; `occupationAt73` | `V/WindowReduction.lean`; `Erdos993Lean/Ceiling/Occupation/Main.lean` |
| Theorems 2.7, 2.8 | Theorem 5.5; changed (Theorem 5.6) | `theorem27_input`; `theorem28`, `theorem28_Dhat` | `V/FinalAboveStartingMean.lean`; `V/FinalParameterDomain.lean` |
| Theorems 3.1, 4.1 | Theorem 4.3; changed (Theorem 4.40) | `maxWeight_variances_Dhat`; `current_forest_laplace_maxWeight`, `current_forest_two_laplace_bounds` | `V/FreeCountVarianceClosedAssembly.lean`; `V/ZeroTiltLaplaceClosedForest.lean` |
| Theorem 5.1 | Theorem 4.22 (same caps; nine rows) | `finiteForest_variance_ratio_bound_closed` | `V/Theorem51/Closed.lean` |
| Theorems 6.2, 7.1 | none; Theorem 6.1 | `lowMean_input_noValley`; `small_forest_independenceSequenceUnimodal` | `V/LowMeanGroupSynthesis.lean`; `V/SmallForestTheorem.lean` |

Proved in the Lean by later arguments that arXiv v1 does not contain, with what each proves (`λ` an activity in
[1/3, 7/3], `q = λ/(1+λ)`, `A` an independent set of maximum weight `π(A)`, `M` the number of free vertices):
- variance of the free count: for every forest, `Var M ≤ D̂(λ) E M`, with the piecewise constant cap `D̂`
  (6/5, 7/5, 8/5, 9/5, 21/10 on five ranges of `λ`);
- Laplace transform: `E (1−q)^M ≤ exp(−ℓ_H(λ) E M)`, with an explicit rate `ℓ_H`;
- variance ratio: `Var K ≤ (1+θ)(1−q) π(A)` for the size `K` of a random independent set, on nine ranges of `λ`;
- small means: on each of 55 subintervals of activities, take a finite mixture of shifted binomials
  `K = Y + Bin(M, q)` and an integer rank `k` with `E(k − Y − qM) = 0`; if `Var M ≤ D E M`,
  `E(k − Y − qM)² ≤ θ q(1−q) E M` and the Laplace bound hold (`D`, `θ` the constants of the subinterval)
  and `E M` lies between `4/q` and the starting mean of the subinterval, then there is no valley at `k`;
- large means: the same conclusion when `E M` is at least the starting mean, by lower bounds for a weighted valley kernel and 55 averaging
  inequalities, each with margin greater than 1/500;
- at most 24 vertices: no valley at any rank of the window, over 203 triples of order, independence number and rank.

The abstract and Sections 7 and 8 of arXiv v1 describe interval-arithmetic coverings, compiled evaluations and an
earlier Lean development; none of these is how this repository works. AI systems made this comparison, on
statements and on the authors' change records; rates and end points in supplementary data were not compared.

An AI pass compared the 93 numbered statements of version 2.13 with the Lean statements at an earlier commit: 39
identical; 40 identical up to a split, a stronger form or a written-out assumption; 2 with only a fragment; 11 with
no counterpart; 1 erratum (Lemma 6.9). Version 2.14 corrects Lemma 6.9 and makes eleven few-word edits towards the
Lean; version 2.15 states the differences below in remarks at Lemma 5.21 and Subsection 5.8. Proofs and unprinted
data were not compared. Remaining differences (all in `formalization.yaml`):
- Theorem 5.1 on rows D, E1, E2, H has the printed statement and a different proof, a later construction of
  T. Zhang (Remark 9.1), with tail thresholds 5/16 and 1/4 where the text prints 1/8. Subsection 5.8, Appendix B
  and Table 18 describe objects absent from the Lean. Lemma 5.21, which the manuscript never cites, has no counterpart.
- Theorem 2.4 is reached by an earlier Lean proof with a kernel check of 181 + 247 integer pairs that the printed
  proof lacks. Theorem 7.1 uses kernel evaluation over 203 parameter triples in place of a printed classification.

## 6. Computational components
Every computation has one form: a record of integers or rationals is the argument of a Boolean function defined
in Lean; a Lean theorem proves that the value `true` implies the mathematical fact; the kernel evaluates the
function (`decide +kernel`). A wrong record makes the build fail. Textual counts on this tree:
13,215 lines containing `decide +kernel` (13,747 uses outside comments) in 2,842 files; 4,818 modules; 2,510,383
lines; 203 MiB, at least 85% of it data. The figures below count such lines unless they say otherwise.
- Low means (`V/LowMeanData/`, 843 files, 62% of the source): integer witness trees for 564 fibers; 408 evaluations.
- Theorem 5.1, rows B, C, F, G (`Erdos993Lean/BCFG/`): 28 polynomials positive on rectangles; 1,210 evaluations.
- Theorem 5.1, rows D, E1, E2, H: `F4Heavy/` (3,996 evaluations of exact rational facts); the half-light files in
  `V/` (2,321); `Erdos993Lean/F4U/Light/` (252 integer polynomials with 3,156 sign checks, and the equality of each
  stored polynomial with its symbolic definition; 4,464 evaluations).
- Elsewhere: 136 checked lists of rational comparisons; 187 evaluations for the Laplace bound; 202 for high means;
  about 100 for at most 24 vertices (over parameter triples; no forest is enumerated). No solver, floating-point
  result, compiled evaluation or data file is trusted. Of the generators only `tools/reflect_linking/` is included.

## 7. How it was produced and who checked what
- **People.** K. Vallier directed the project: goals, what was merged and published, the machines, and the carrying
  of prompts and results between systems. T. Zhang produced the library `F4Heavy` with OpenAI GPT-6.1 Sol through
  Codex (his own statement of 9 October 2026). Thomas Dias operated one of the Codex workspaces (the low-mean part).
  Authors: K. Vallier and T. Zhang; maintainer: K. Vallier.
- **AI systems** produced all of the Lean and all of the certificate data. As listed in Section 10 of the
  manuscript: Anthropic Claude Opus 5.5 and Claude Fable 5.1 (Claude Code agents); OpenAI GPT-5.6 Sol, GPT-6 Astra,
  GPT-6 Sol and GPT-6.1 Sol in Codex; OpenAI GPT-6 Astra in Pro mode in ChatGPT conversations. Per-task model
  revisions were not recorded, and the list is not claimed to be complete: the project log records one checker
  run by a model of another Claude family. Wall time: about two weeks, late September to 9 October 2026.
- **Checks by AI systems.** A coordinating Claude session rebuilt each part from source and printed its axioms
  before merging; others compared statements and tables with the manuscript. Some late rewrites had no such review.
- **Checks by humans.** K. Vallier directed the project. He does not read Lean; he checked the statements of
  `Challenge.lean` against a line-by-line plain-language gloss prepared by an AI system and confirmed that they
  state the conjecture; he proposed a formal statement for forests publicly on 16 August 2026 (formal-conjectures
  issue #5012); he has not checked the proofs. All Lean was produced by AI systems, T. Zhang's library by an AI
  system that he operated; he states that he has not read its Lean code. T. Zhang had an AI system review the
  statement file `Challenge.lean` line by line, and has himself read lines 67 to 97 of that file, which contain its
  four declarations (his statements of 9 October 2026); these are the only lines of Lean code he has read, and he
  has not read the proofs. No human has read the Lean proofs. Every comparison of the Lean with the manuscript was
  made by AI systems, on statements only. No independent human expert review is claimed. T. Zhang and W. Li have
  read the first four sections of the manuscript (T. Zhang, 9 October 2026) and have not yet revised them; no human
  has yet read the remaining sections' proofs in full.

## 8. Related formalizations
Identifiers and commits are in `formalization.yaml`. None of these repositories was rebuilt for this entry; each
line gives what the repository or its paper reports. The last four concern all finite forests.
- 11 September 2026, zouzh14/erdos-993-eventual (Z. Zou), and 15 to 21 September,
  junwei-lu/Erdos_993_Tree_Independent_Set_Unimodality (Theorem 1.1 of Fang et al.): large forests only.
- 29 September 2026, RichP0123/erdos993-floor38: every forest with at most 37 vertices, on the three standard
  axioms; its README says it does not settle the problem.
- 29 September 2026, selfreferencing/erdos993-lean (this project, version 1.0). As its README describes it: at
  most 60 vertices by T. Zhang's certificates, at least 61 by a different argument developed in this project and
  not independently reviewed; 271 `native_decide`, hence five axioms (the standard three and two compiler axioms).
- 2 October 2026, lixiang90/forest-unimodality: an independent formalization, by another person, of T. Zhang's
  manuscript of 26 September (proof commit of 29 September). Its README reports a clean rebuild on 2 October and
  the three standard axioms only; its one-line description still says verification is pending.
- 6 October 2026, selfreferencing/erdos993-forest-unimodality-lean (this project): accompanies arXiv:2610.07943v1;
  still with native evaluation (411 compiled evaluations and five axioms, as that paper reports).
- This repository: the second proof; every finite computation evaluated by the kernel; the three standard axioms
  only; the complete export accepted by three independent kernel checkers (section 10 says on which tree).

## 9. Repository layout
`Challenge.lean` (the statement); `Solution.lean` (the same declarations with proofs); `comparator.json`;
`Erdos993Lean/` with `Statement.lean` (the statement on `Fin n`), `PalomarBridge.lean` (101 lines, no computation),
`Analytic/V213/` (the final assembly), `BCFG/`, `F4U/`, `Ceiling/`, `Zhang/`, `ExactComparisons/`; `F4Heavy/`
(rows D, E1, E2, H of Theorem 5.1); `tools/reflect_linking/`. Every other module is reached by import lines from `Solution`.

## 10. Building and checking
Lean `v4.35.0-rc2` with Mathlib at the same tag (`lean-toolchain`, `lake-manifest.json`): run `lake exe cache get`,
then `lake build` (default targets `Challenge` and `Solution`). A fresh build took 31 to 35 minutes (1,857 to 2,067 s in four runs) on 16
cores with 32 GB and fails for lack of memory on 8 cores with 16 GB. `Solution.lean` ends with `#print axioms` for
both theorems; the build reports `propext`, `Classical.choice` and `Quot.sound` only. Four complete runs on a
tree whose code is that of this one (it differs in comments, `LICENSE`, this file and the yaml; a fresh build of
the comment-revised tree gave a byte-identical export, 3,386,265,533 bytes): the export was accepted by Lean's
`leanchecker`, NanoDa and con-ron in 9,949 s, 10,038 s and 10,260 s in total with the build (16 vCPU, 32 GB), and
by the registry's sandboxed Comparator in 10,108 s. The checkers were not re-run after the comment revision.

## 11. Licence
Apache License 2.0; see `LICENSE`. The definitions in `Challenge.lean` come from google-deepmind/formal-conjectures.
