# Gusfield et al. 2007: a decomposition theory for phylogenetic networks, in Lean

[![CI](https://github.com/vltanh/lean4-gusfield2007/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-gusfield2007/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of D. Gusfield, V. Bansal, V. Bafna, Y. S. Song, *A decomposition theory for phylogenetic networks and incompatible characters*, [J. Comput. Biol. 14 (2007), 1247–1272](https://doi.org/10.1089/cmb.2006.0137), with the results it cites. The paper studies phylogenetic networks with recombination that derive a set `M` of binary sequences. A blob is the set of arcs of a class of recombination cycles under sharing an arc, and contracting the blobs leaves a tree. The main result, the Decomposition Theorem (Theorem 1), says that every such `M` has a network in which each blob holds exactly the sites of one non-trivial connected component of the incompatibility graph `G(M)`, with every compatible site on a tree edge. The paper then gives sufficient conditions under which such a fully decomposed network uses the fewest recombinations, and refutes the Full-Decomposition Optimality Conjectures. Everything is proved with no `sorry` and no assumed result of the literature. One theorem is conditional, and says so in its statement: Theorem 10, with `R(M + S)` read by the definition at line 385, is refuted for multiple crossovers given a finite computation that Lean's kernel hasn't completed. The paper's own use of that symbol suggests `R_S(M)`, and with that Theorem 10 is proved. One statement of the paper, at its line 425, stays open. The formalization was made in [lean4-tob](https://github.com/vltanh/lean4-tob), a collection of formalizations on the tree of blobs of phylogenetic networks, and moved here on 2026-11-04: the others infer the tree of blobs of a species network from gene trees, and none of them uses this paper.

## What is proved

- **The paper's results**, by its arguments except the departures in [Section 7 of the report](REPORT.md#7-departures-from-the-papers-proofs): Lemmas 1–5; Theorems 1, 2, 3, 5, 6, 7, 8, 9, 11; Corollaries 1, 2, 3; and the refutation of all four Full-Decomposition Optimality Conjectures. Theorem 4 is false as printed, and its true form is proved in both directions. Theorem 10 is proved with the rooted count `R_S(M)`, and refuted with `R(M + S)` read literally, for multiple crossovers only given a computation (E51).
- **What it says in passing**: the sentences at lines 135, 156, 180, 299, 329, 381, 403, 411, 418, 420, 554, 559, 590 and 608 (lines 156, 180, 403 and 554 in corrected forms), Footnote 2, and the numbers of Figures 5–10. [Section 9 of the report](REPORT.md#9-not-formalized) lists what remains: Table 1 and the simulation study, the statements that are false, each with its counterexample, and the two open items.
- **The cited results**, in [`src/External/`](src/External), each with a README that says whether its source was read: the Perfect Phylogeny Theorem (Gusfield 1991), the Splits Equivalence Theorem (Semple, Steel 2003), proved in the library lean4-phylogenetics and restated here, Gusfield et al. 2004 (Theorems 2.2, 2.4–2.7, 8.1–8.3, Corollary 5.1 on galled trees, and an algorithm, proved correct, with a count of its operations), Myers and Griffiths 2003 (the haplotype bound, the integer program, Algorithms 1 and 3, Proposition 2, Corollary 5), Hudson and Kaplan 1985 (the bound and the algorithm of its Appendix 2), and Song and Hein 2005 (the bound by ordered SPR, and that the minimum over sequences of trees is `R¹`). Nothing is assumed ([Section 2 of the report](REPORT.md#2-results-from-prior-work-and-how-the-paper-uses-them)).
- `lake build` passes with no warnings, and there is no `sorry`, `axiom`, `native_decide` or `implemented_by` in [`src/`](src). [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of the project and of the library it uses, including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound); run it as in [Building](#building). [`scripts/check_kernels.sh`](scripts/check_kernels.sh) checks the main theorems under three kernels: Lean's, NanoDa and con-ron.

## The main results

[`src/MainResults.lean`](src/MainResults.lean) states and proves these theorems, in the namespace `TreeOfBlobs`, each with a docstring in plain terms. They keep the paper's hypotheses.

### The paper

- [`MainResults.gusfield_theorem1`](src/MainResults.lean#L57) (Theorem 1, the Decomposition Theorem): in any crossover model, a nonempty `M` with no constant column has a network in which every blob contains all and only the sites of one non-trivial connected component of `G(M)`, and every compatible site is on a tree edge.
- [`MainResults.gusfield_theorem3`](src/MainResults.lean#L64) (Theorem 3): for any ancestral sequence `S`, there is a network fully decomposed for the conflict graph `G_S(M)`, with `S` at its root and exactly `Σ_C R_{S(C)}(M(C))` recombination nodes.
- [`MainResults.gusfield_lemma4`](src/MainResults.lean#L74) (Lemma 4): for a component `C` of `G(M)`, the tree `T̄` has a node `v_C` on all the edges labelled by characters from `C`, on the 0-side of each of their splits, so the edges of a component form a star.
- [`MainResults.gusfield_theorem4_entry`](src/MainResults.lean#L85) (Theorem 4, corrected): for a fully decomposed network, the tree `T′` of its blobs is `T̄` exactly when the network is efficient with the entry node of a blob counted, and has `RegularArcs` and the degree condition. This repair is in Gusfield's 2014 book, for a stricter class (E42).
- [`MainResults.gusfield_theorem4_iff`](src/MainResults.lean#L93) (Theorem 4, exactly): with the printed definition of efficient, `T′` is `T̄` for a fully decomposed network exactly when it is efficient and has `IsTreeNormalStructural` and the degree condition.
- [`MainResults.gusfield_exists_realization`](src/MainResults.lean#L102): for every `M` with at least three rows, in any crossover model, some efficient fully decomposed network has `T′ = T̄` and all the hypotheses of the true forms. This isn't in the paper.
- [`MainResults.gusfield_theorem4_false_top`](src/MainResults.lean#L112): Theorem 4 as printed is false, in any crossover model, even for a network with `RegularArcs` and the degree condition, since the definition of efficient omits the entry node of a blob.
- [`MainResults.gusfield_theorem4_false_siteFree`](src/MainResults.lean#L118): Theorem 4 as printed is false on a perfect phylogeny with a site-free arc, which the paper allows.
- [`MainResults.gusfield_theorem5`](src/MainResults.lean#L125) (Theorem 5): if an optimal network for `M` with ancestral sequence `S` has node labels `L` such that `G_S(L)` and `G_S(M)` have the same number of components, then `M` is S-min (or S-min-1) decomposable.
- [`MainResults.gusfield_theorem6`](src/MainResults.lean#L132) (Theorem 6): if a network for `M` with ancestral sequence `S`, not necessarily optimal, has every node visible and at most one site on each edge, then `M` is S-min (or S-min-1) decomposable.
- [`MainResults.gusfield_theorem7`](src/MainResults.lean#L139) (Theorem 7): if every recombination node of a network for `M` with ancestral sequence `S` is a 0- or 1-component recombination for `G_S(M)`, then some fully decomposed network, in the same model, has at most as many recombination nodes.
- [`MainResults.gusfield_theorem8`](src/MainResults.lean#L148) (Theorem 8): if `M` is spatially disjoint, then it is S-min-1 decomposable.
- [`MainResults.gusfield_theorem9`](src/MainResults.lean#L154) (Theorem 9): if the node labels of a network for `M` with ancestral sequence `S` respect `G_S(M)`, then some fully decomposed network, in the same model, has at most as many recombination nodes.
- [`MainResults.gusfield_theorem10`](src/MainResults.lean#L162) (Theorem 10, with the rooted count): if `H(M + S) = R_S(M)`, or `R¹_S(M)`, then `M` is S-min, or S-min-1, decomposable, in each crossover model and with no hypothesis on the columns.
- [`MainResults.gusfield_theorem10_unrooted`](src/MainResults.lean#L205): if `H(M) = R(M)` then `M` is min decomposable, and likewise for single crossovers. This isn't in the paper.
- [`MainResults.gusfield_theorem10Printed_single_false`](src/MainResults.lean#L211): Theorem 10 with `R(M + S)` read by the definition at line 385, the minimum over all ancestral sequences, is false for single crossovers, on 14 rows and 8 sites.
- [`MainResults.gusfield_theorem10Printed_multiple_false_of_search`](src/MainResults.lean#L219): **conditional**. With that reading, for multiple crossovers, it is false on 74 rows and 34 sites, given [`Gusfield2007.printedMSearch`](src/Gusfield2007/Theorem10PrintedMultiple.lean#L269), a finite computation that the kernel hasn't completed.
- [`MainResults.gusfield_theorem11`](src/MainResults.lean#L168) (Theorem 11): for any positive `d` there is a set of sequences `M` with `F¹(M) − R¹(M) ≥ d`. [`MainResults.gusfield_Md_R_eq`](src/MainResults.lean#L244) (line 656): `R¹(M_d) = 3d`, where the paper claims the upper bound.
- [`MainResults.gusfield_corollary2`](src/MainResults.lean#L174) (Corollary 2): if every node of an optimal network for `M` with ancestral sequence `S` is visible, then `M` is S-min (or S-min-1) decomposable.
- [`MainResults.gusfield_corollary3`](src/MainResults.lean#L180) (Corollary 3): when recombinations only model back or recurrent mutations, `M` is S-min decomposable for any `S`, and the maximum parsimony score of `M` is the sum of the scores of the components of `G_S(M)`.
- [`MainResults.gusfield_unrootedConjecture_single_false`](src/MainResults.lean#L188), [`MainResults.gusfield_unrootedConjecture_multiple_false`](src/MainResults.lean#L193) (Sections 5.3.1, 5.3.2): the unrooted Full-Decomposition Optimality Conjecture is false for single crossovers, on Figure 6, where `F¹ ≥ 4` and `R¹ ≤ 3`, and for multiple crossovers, on Figure 8, where `F ≥ 4` and `R ≤ 3`.
- [`MainResults.gusfield_rootedConjecture_single_false`](src/MainResults.lean#L198), [`MainResults.gusfield_rootedConjecture_multiple_false`](src/MainResults.lean#L201) (Section 5.3): the rooted conjecture is false for single and for multiple crossovers.
- [`MainResults.gusfield_exists_isEfficientAtEntry`](src/MainResults.lean#L226) (line 329, with the entry node counted): a fully decomposed network can be made efficient, in the printed sense and with the entry node counted, without more recombination nodes, with the same ancestral sequence, and staying fully decomposed.
- [`MainResults.gusfield_treeness_merged_false`](src/MainResults.lean#L235) (Section 4.2): the treeness inequality fails for a blob that merges two components: a network with every other condition of the true form has treeness 5, where `T̄` has 4 edges.
- [`MainResults.gusfield_conjecture22_false`](src/MainResults.lean#L247) (line 590): the conjecture of Huson and Klöpper is false, as Conjecture 2.2 of Klöpper's thesis states it.

### Gusfield, Eddhu, Langley 2004

- [`MainResults.galled_exists_isCycle_of_conflict`](src/MainResults.lean#L258) (in the proof of Theorem 2.2): two sites that conflict, in any set of rows labelling nodes of a network, are together on a recombination cycle.
- [`MainResults.galled_theorem2_2`](src/MainResults.lean#L264) (Theorem 2.2): on a galled tree with single crossovers, two sites `i < j` conflict exactly when they are together on a gall with the recombination point between them, arranged on it in one of the three ways `W1`, `W2`, `W3`.
- [`MainResults.galled_theorem8_3`](src/MainResults.lean#L272) (Theorem 8.3): a reduced galled tree for `M` has the least number of recombination nodes, in its model and with multiple crossovers, and that number is the bound by removals.
- [`MainResults.galled_line381`](src/MainResults.lean#L278) (line 381 of the paper): a galled tree reduced for `G(M)` makes `M` min decomposable, in its model and for multiple crossovers.
- [`MainResults.galled_galledBuild_correct`](src/MainResults.lean#L286) (line 180 of the paper): if the computable function `galledBuild` returns a table, it is the table of a reduced galled tree that derives `M` with ancestral sequence `S` and single crossovers.
- [`MainResults.galled_galledBuildOps_le`](src/MainResults.lean#L295) (line 180 of the paper, "polynomial time"): on `n` rows and `m` sites, the algorithm counts at most `233 (n + m + 1)⁶` operations. This bound isn't the source's `O(nm + n³)`.

### Myers, Griffiths 2003; Hudson, Kaplan 1985; Song, Hein 2005

- [`MainResults.myersGriffiths_algorithm1_isOptimalValue`](src/MainResults.lean#L308) (Algorithm 1): the matrix that the computable function [`algorithm1`](src/External/MyersGriffiths2003/Algorithm1.lean#L257) builds is the matrix of optimal values of the integer program on regions.
- [`MainResults.myersGriffiths_Rh_le_R`](src/MainResults.lean#L313): the haplotype bounds on regions, combined by Algorithm 1, give a lower bound `R_h` on `R¹(M)`.
- [`MainResults.hudsonKaplan_isOptimalValue`](src/MainResults.lean#L318) (Appendix 2): the final number of intervals on the list of the computable function [`hudsonKaplan`](src/External/HudsonKaplan1985/Algorithm.lean#L72) is the bound `R_M`, the optimal value of the program for the matrix of incompatible pairs.
- [`MainResults.songHein_exists_orderedLength_eq_R`](src/MainResults.lean#L324) (equations (3), (5)): over sequences of binary trees with totally ordered internal nodes, compatible with the columns, the minimum of `L(P)` is `R¹(M)`, and it is attained, when no column is constant.

### Status of what's open

Stated in Lean and not settled here: line 425 ([`Gusfield2007.MinDecomposableOfForallS`](src/Gusfield2007/Conjectures.lean#L118)), "when M is S-min decomposable for all S, then M is min-decomposable", which is neither proved nor refuted, and holds when `H(M) = R(M)`; and Theorem 10 for multiple crossovers with `R(M + S)` read by the definition at line 385, refuted only given [`Gusfield2007.printedMSearch`](src/Gusfield2007/Theorem10PrintedMultiple.lean#L269). Two separate programs by the same author, not in the repository, and Lean's `#eval` support that hypothesis. The kernel hasn't completed it, and none of those is a proof.

## Palomar

No submission to [Palomar](https://github.com/mathlib-initiative) is planned. The files in [`palomar/`](palomar) are kept in case that changes, and the Comparator configuration is also useful on its own.

- [`palomar/comparator.json`](palomar/comparator.json) runs Comparator on the theorems above, with [`src/MainResults.lean`](src/MainResults.lean) as both the challenge and the solution. From the repository root, after `lake build`, run `scripts/check_kernels.sh palomar/comparator.json`. This checks the closure of each theorem under Lean's kernel, NanoDa and con-ron, and rejects `sorryAx`. The conditional theorem has its computation as a visible hypothesis, which this doesn't check. It doesn't compare a separate statement file with a proof, which is what Palomar's Challenge and Solution are for. `lake comparator`, `leanexport` and `con-ron` come from the toolchain under `lake env`.
- [`palomar/formalization.yaml`](palomar/formalization.yaml) is the entry's metadata, valid against the schema it names: the paper, the sources it cites, the statements aligned to the `MainResults.*` theorems, and its fidelity section, which lists every divergence from the paper. [`REPORT.md`](REPORT.md) has the details.

A submission would still need:

1. A Challenge that imports only Mathlib, with the definitions that its statements use in a block of its own, and the bridges from them to the formalization's definitions. The last such file of [lean4-tob](https://github.com/vltanh/lean4-tob), with `scripts/sync_challenge_defs.py`, which kept its block equal to the library's, and `scripts/gen_solution.py`, which generated the Solution from it, is in that repository's history at `f838ea4`, for three other papers.
2. A Solution that restates those theorems and proves them from the libraries, and a `comparator.json` that names the two modules.
3. These files at the root of the repository that holds the paper, with `formalization.yaml` pointing at the new modules.

## Audit summary

The numbers are those of [the report](REPORT.md#3-errors-and-gaps-in-the-paper), which gives each finding with its location, the paper's sentence, a Lean counterexample and the repair. They keep the numbers they have in [lean4-tob](https://github.com/vltanh/lean4-tob), where they were numbered across its papers, so that they match its documents and the history.

- **Theorem 4 is false as printed**, since the definition of "efficient" omits the node where a blob is entered (E42), and since site-free arcs are allowed (E43). It holds with both repaired, up to two conventions (E44). The first repair is in print, in Gusfield's 2014 book, in a stricter form, which we read only in snippets (E42). The Lean adds the exact characterization, the failure under the printed definition, and the check in the kernel.
- **Theorem 10 is false if `R(M + S)` is read by the definition at line 385**: for single crossovers by a counterexample in Lean, and for multiple crossovers given one search that the kernel hasn't completed. Lines 525 and 560 use that symbol for a network with ancestral sequence `S`, which suggests a slip for `R_S(M)`, and with that it is true and proved, with no hypothesis on the columns (E51).
- **Other statements false as printed**: line 373 on the most tree-like network (E45, E67), line 554 on galled networks (E49), line 560 on visible nodes (E50), the step at line 403 on one `M` (E48) and line 180's wording of "reduced" (E47). Theorem 1 and the refutations of the conjectures aren't affected. The misprints are E54.
- **Gaps**: the modification of line 329, which the paper doesn't give (E52), and gaps in the proofs at lines 135, 141, 187–190, 264, 271, 295, 299, 312–316, 411, 418 and 576 (E53). All are repaired, and the results hold.
- **Missing and redundant hypotheses**: [Section 4 of the report](REPORT.md#4-missing-hypotheses) has the conditions without which the statements above fail, each with its counterexample, and the standing assumptions; [Section 5](REPORT.md#5-redundant-hypotheses) has the hypotheses that the proofs don't use.
- **Use of cited results**: the definition of a reduced galled tree is paraphrased too weakly (E47), and Theorem 4 is applied at line 418 where it doesn't hold (E53). In the sources, one direction of Corollary 2.1 of Gusfield et al. 2004 is false (E76); the rest are gaps and a misprint, each of which leaves the result standing (E77–E79), and one point on Klöpper's thesis we didn't check (E85).
- **Texts**: all of this was read in the PMC manuscript and an author's copy with its symbols, where the misprints are too. The journal's typeset text wasn't reachable.
- **Proofs**: they follow the paper's arguments, except the departures in [Section 7 of the report](REPORT.md#7-departures-from-the-papers-proofs), each with what the paper does, what Lean does and why. Some repair a gap or an error; some have no printed argument to follow, such as the modification at line 329; a few weren't forced, and say so. [`docs/route_differences.tsv`](docs/route_differences.tsv) records every difference of route. Two sources of proved results weren't read, Gusfield 1991 and Semple and Steel 2003, and their proofs here are standard arguments. Huson and Klöpper 2007 wasn't read either: its conjecture comes from Klöpper's thesis of 2008, and its definitions from its errata and a later paper.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the paper and decided the layout, the kernels and publication. **No person has reviewed the proofs.** Independent agents reviewed the statements against the sources, compared the proofs with the paper, and checked the findings and the literature section.
- Statements, proofs, audit and documents by Claude (Opus 5.5) in Claude Code, with sub-agents, following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure. 
- Made in [lean4-tob](https://github.com/vltanh/lean4-tob) from 2026-10-31 to 2026-11-01, in two rounds shared with other papers: the round that added this paper and Allman et al. 2023, with 20 sub-agents, and the round that finished what the papers claim, with 10. Moved here on 2026-11-04. [`docs/CREDITS.md`](docs/CREDITS.md) has the details.

## Related work

From [Section 10 of the report](REPORT.md#10-the-paper-in-the-literature), searched on 2026-11-01.

- No other formalization of the paper was found, in any system, nor of `T̄`, the Buneman graph, perfect phylogeny, the four-gamete test or ancestral recombination graphs.
- Before: the lower bounds on recombinations of Hudson and Kaplan 1985 and Myers and Griffiths 2003; the galled trees of Gusfield, Eddhu, Langley 2004, whose reduced galled trees have the structure that Theorem 1 generalizes; and Gusfield and Bansal, RECOMB 2005, the first statement of the decomposition theorem and of the Full-Decomposition Optimality Conjecture.
- Concurrent: Huson and Klöpper, RECOMB 2007, on galled networks and their decomposition, with a conjecture that line 590 says is false. Klöpper's thesis of 2008 states it and says that this paper refutes it.
- Since: Gusfield's book *ReCombinatorics* (2014), read only in snippets, restates Theorem 4 with the entry node counted, for "canonical" ARGs. Huson et al. 2009 credit Yun Song with an example of the refutation of the conjectures, in a form on clusters, and van Iersel et al. 2010 and Kelk et al. 2012 state it. Dress et al. 2011 relate the blocks of the Buneman graph to the components of the incompatibility graph. [Allman et al. 2023](https://github.com/vltanh/lean4-tob/blob/main/papers/AllmanEtAl2023/README.md) cite this paper for the tree of blobs. We found no erratum, and no other work stating the errors recorded here, apart from the book's repair.

## What's next

How much does full decomposition cost? Theorem 11 says `F¹ − R¹` is unbounded for single crossovers, and line 666 says the authors don't know how robust their empirical results are in other ranges of data, for multiple crossovers, or with a fixed ancestral sequence; Gusfield's 2014 book, whose Section 7.4.3 and Chapter 11 are on this, should be read first. Line 425 stays open here, and the multiple-crossover case of E51 stays conditional until the kernel completes [`Gusfield2007.printedMSearch`](src/Gusfield2007/Theorem10PrintedMultiple.lean#L269), or another proof of the same bound exists. [Section 11 of the report](REPORT.md#11-whats-next) has these, the simpler arguments that the formalization found, and two routes not built: `T̄` through the Buneman graph of Dress et al. 2011, and line 411 through the cut nodes of the median network.

## Building

From the root of the repository:

```sh
lake exe cache get
lake build
lake build MainResults                                              # this paper's main theorems
lake env lean -DautoImplicit=false -DmaxSynthPendingDepth=3 scripts/Audit.lean   # axioms and dependencies
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
scripts/check_kernels.sh palomar/comparator.json            # Lean's kernel, NanoDa, con-ron
```

- Toolchain: Lean and Mathlib `v4.37.0-rc1` ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)).
- [`scripts/check_kernels.sh`](scripts/check_kernels.sh) uses `lake comparator`, `leanexport` and `con-ron`, under `lake env`.
- After adding a module, run `python3 scripts/gen_audit.py`. After moving declarations, run `python3 scripts/linkify_docs.py` to update the documents' links.
- [`docs/CONFIGURATION.md`](docs/CONFIGURATION.md) records the versions, the decisions and what "line N" means.

## Layout

| Folder | Content |
| --- | --- |
| [`src/Gusfield2007/`](src/Gusfield2007) | The paper, on sequence-labelled networks. [Its README](src/Gusfield2007/README.md) lists the modules |
| [`src/External/Gusfield1991/`](src/External/Gusfield1991) | The Perfect Phylogeny Theorem, as an undirected tree, as a network with no recombination node, and with a given ancestral sequence; uniqueness among reduced trees |
| [`src/External/GusfieldEtAl2004/`](src/External/GusfieldEtAl2004) | Conflicting sites on one blob and on one cycle; reduced galled trees are fully decomposed, exist and are optimal; a computable algorithm for a reduced galled tree, with its correctness and a count of its operations |
| [`src/External/HudsonKaplan1985/`](src/External/HudsonKaplan1985) | The lower bound by non-overlapping intervals of incompatible sites, and the algorithm of Appendix 2 |
| [`src/External/MyersGriffiths2003/`](src/External/MyersGriffiths2003) | The haplotype bound and its equality case with distinct columns, the integer program, Algorithms 1 and 3, the bounds `R_h` and `R_s`, Proposition 2, Lemma 4 and Corollary 5 |
| [`src/External/SongHein2005/`](src/External/SongHein2005) | The bound `R¹(M) ≤ L(P)` by ordered SPR, and that the minimum over sequences of trees is `R¹(M)` |
| [`src/External/SempleSteel2003/`](src/External/SempleSteel2003) | The Splits Equivalence Theorem, cited by the paper: proved in the library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) (`Phylogenetics.SplitsEquivalence`), and restated here with the label of its route |
| [`src/MainResults.lean`](src/MainResults.lean) | The main theorems |
| [``](.) | This README, [`REPORT.md`](REPORT.md), the audit, and [`palomar/`](palomar) |

The modules of [`src/Gusfield2007/`](src/Gusfield2007), in short:

- `Defs` and [`Basic`](src/Gusfield2007/Basic.lean): the definitions the statements mention, and the readings of the paper. `Blobs`, `NetworkOps`, `BlobFacts` and `Surgery`: blobs, `T′` as a tree, trimming, the restriction to a component and Lemma 5.
- `Structure`, `SuperCharacters`, `Decomposition` and the modules beside them: Section 3, Lemmas 1–4, `T̄`, and Theorems 1–3.
- `Uniqueness`, `Realizability`, `EntryNet`, `RootedFrame` and `MergedTreeness`: Theorem 4, line 329, line 299 and treeness (Sections 3.7, 4.2).
- `Conjectures`, `SufficientConditions`, `OpenStatements`, `Theorem10PrintedMultiple`, `GalledNetworks` and `HusonKloepper`: Section 5, the conjectures, Theorems 5–10, Corollaries 2 and 3, Theorem 10 read literally, line 425, line 554 and line 590.
- `Examples`, `LabelSearch`, the `Figure` modules, `TimeOrdered`, `MdLower` and `Counterexamples`: the matrices of the figures, a verified search for lower bounds on `R`, ordered SPR, and the refutation of the conjectures with Theorem 11.

The sources are stated on the paper's networks, [`Gusfield2007.Network`](src/Gusfield2007/Defs.lean#L129), and its proofs use them. The code imports Mathlib, and from the library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics) only the two modules of the Splits Equivalence Theorem, which import Mathlib only.

## License

Apache-2.0: [`LICENSE`](LICENSE).
