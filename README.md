# Gusfield et al. 2007: a decomposition theory for phylogenetic networks, in Lean

[![CI](https://github.com/vltanh/lean4-gusfield2007/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/vltanh/lean4-gusfield2007/actions/workflows/lean_action_ci.yml)

A Lean 4 formalization of D. Gusfield, V. Bansal, V. Bafna, Y. S. Song, *A decomposition theory for phylogenetic networks and incompatible characters*, [J. Comput. Biol. 14 (2007), 1247–1272](https://doi.org/10.1089/cmb.2006.0137), with the results it cites. The paper studies phylogenetic networks with recombination that derive a set `M` of binary sequences. A blob is the set of arcs of a class of recombination cycles under sharing an arc, and contracting the blobs leaves a tree. The Decomposition Theorem (Theorem 1) says that every such `M` has a network in which each blob holds exactly the sites of one non-trivial connected component of the incompatibility graph `G(M)`, with every compatible site on a tree edge. The paper then gives sufficient conditions under which such a fully decomposed network uses the fewest recombinations, and refutes the Full-Decomposition Optimality Conjectures.

Every numbered result is proved, as printed or in a corrected form, with no `sorry` and no assumed result of the literature. Theorem 4 is false as printed, and its true form is proved in both directions. One theorem is conditional, and says so in its statement: Theorem 10, with `R(M + S)` read by the definition at line 385, is refuted for multiple crossovers given a finite computation that Lean's kernel hasn't completed. The paper's own use of that symbol suggests `R_S(M)`, and with that Theorem 10 is proved. One statement of the paper, at its line 425, stays open.

## Status

| Part of the paper | Status |
| --- | --- |
| §2–3: blobs, `T′`, `T̄`, Lemmas 1–5, Theorems 1–3, Corollary 1 | proved |
| §3.7: Theorem 4 | false as printed (E42, E43); true form proved in both directions |
| §4.1: back and recurrent mutations, parsimony | proved |
| §4.2: treeness, line 373 | false as printed (E45, E67); true form proved |
| §5.1: the Full-Decomposition Optimality Conjectures, `F` and `F_S` | stated; all four refuted (§5.3) |
| §5.2: Theorems 5–9, Corollaries 2, 3 | proved |
| §5.2: Theorem 10 | proved with `R_S(M)`; with `R(M + S)` read literally, refuted for single crossovers and, conditionally on [`Gusfield2007.printedMSearch`](Gusfield2007/Theorem10PrintedMultiple.lean#L269), for multiple crossovers (E51) |
| §5.3: the refutations, Theorem 11 | proved |
| §5.4: the simulation study, Table 1 | not formalized |
| Figures 5–10, Footnote 2 | their numbers proved |
| Line 425 ([`Gusfield2007.MinDecomposableOfForallS`](Gusfield2007/Conjectures.lean#L87)) | open; proved when `H(M) = R(M)` |
| What the paper says in passing: lines 135, 156, 180, 299, 329, 381, 403, 411, 418, 420, 554, 559, 590, 608 | proved; lines 156, 180, 403 and 554 in corrected forms |
| Cited results (Gusfield 1991; Semple, Steel 2003; Gusfield, Eddhu, Langley 2004; Myers, Griffiths 2003; Hudson, Kaplan 1985; Song, Hein 2005) | proved, in [`Gusfield2007/External/`](Gusfield2007/External) |

[Section 9 of the report](docs/Gusfield2007/REPORT.md#9-not-formalized) lists what is not formalized.

## Main results

These are the theorems of the Challenge, [`palomar/Gusfield2007/Challenge.lean`](palomar/Gusfield2007/Challenge.lean), in the namespace `Gusfield2007Challenge`, each with a docstring in plain terms. They keep the paper's hypotheses, and [`palomar/Gusfield2007/Solution.lean`](palomar/Gusfield2007/Solution.lean) proves each of them, under the same name, from the library.

### The paper

| Paper | Lean | Statement |
| --- | --- | --- |
| Theorem 1 | [`gusfield_theorem1`](palomar/Gusfield2007/Challenge.lean#L68) | in any crossover model, a nonempty `M` with no constant column has a network in which every blob contains all and only the sites of one non-trivial component of `G(M)`, and every compatible site is on a tree edge |
| Theorem 3 | [`gusfield_theorem3`](palomar/Gusfield2007/Challenge.lean#L75) | for any ancestral sequence `S`, some network is fully decomposed for `G_S(M)`, with `S` at its root and exactly `Σ_C R_{S(C)}(M(C))` recombination nodes |
| Lemma 4 | [`gusfield_lemma4`](palomar/Gusfield2007/Challenge.lean#L85) | for a component `C` of `G(M)`, `T̄` has a node on all the edges labelled by characters from `C`, on the 0-side of each |
| Theorem 4, corrected | [`gusfield_theorem4_entry`](palomar/Gusfield2007/Challenge.lean#L95) | for a fully decomposed network, `T′ = T̄` exactly when the network is efficient with the entry node of a blob counted and has `RegularArcs` and the degree condition (E42) |
| Theorem 4, exactly | [`gusfield_theorem4_iff`](palomar/Gusfield2007/Challenge.lean#L103) | with the printed definition of efficient, `T′ = T̄` exactly when the network is efficient and has `IsTreeNormalStructural` and the degree condition |
| Theorem 4, realizable | [`gusfield_exists_realization`](palomar/Gusfield2007/Challenge.lean#L112) | for every `M` with at least three rows, some efficient fully decomposed network has `T′ = T̄` and all the hypotheses of the true forms; not in the paper |
| Theorem 4, false | [`gusfield_theorem4_false_top`](palomar/Gusfield2007/Challenge.lean#L122) | Theorem 4 as printed fails, in any crossover model, even with `RegularArcs` and the degree condition |
| Theorem 4, false | [`gusfield_theorem4_false_siteFree`](palomar/Gusfield2007/Challenge.lean#L127) | Theorem 4 as printed fails on a perfect phylogeny with a site-free arc (E43) |
| Theorem 5 | [`gusfield_theorem5`](palomar/Gusfield2007/Challenge.lean#L133) | if an optimal network for `M` with ancestral sequence `S` has node labels `L` with as many components in `G_S(L)` as in `G_S(M)`, then `M` is S-min (or S-min-1) decomposable |
| Theorem 6 | [`gusfield_theorem6`](palomar/Gusfield2007/Challenge.lean#L140) | the same for a network, not necessarily optimal, with every node visible and at most one site on each edge |
| Theorem 7 | [`gusfield_theorem7`](palomar/Gusfield2007/Challenge.lean#L146) | if every recombination node is a 0- or 1-component recombination for `G_S(M)`, some fully decomposed network in the same model has at most as many recombination nodes |
| Theorem 8 | [`gusfield_theorem8`](palomar/Gusfield2007/Challenge.lean#L154) | if `M` is spatially disjoint, it is S-min-1 decomposable |
| Theorem 9 | [`gusfield_theorem9`](palomar/Gusfield2007/Challenge.lean#L159) | if the node labels respect `G_S(M)`, some fully decomposed network in the same model has at most as many recombination nodes |
| Theorem 10 | [`gusfield_theorem10`](palomar/Gusfield2007/Challenge.lean#L166) | if `H(M + S) = R_S(M)`, or `R¹_S(M)`, then `M` is S-min, or S-min-1, decomposable, in each crossover model |
| Theorem 10, unrooted | [`gusfield_theorem10_unrooted`](palomar/Gusfield2007/Challenge.lean#L207) | if `H(M) = R(M)`, then `M` is min decomposable; not in the paper |
| Theorem 10, literal | [`gusfield_theorem10Printed_single_false`](palomar/Gusfield2007/Challenge.lean#L212) | with `R(M + S)` read by line 385, Theorem 10 is false for single crossovers, on 14 rows and 8 sites |
| Theorem 10, literal | [`gusfield_theorem10Printed_multiple_false_of_search`](palomar/Gusfield2007/Challenge.lean#L220) | **conditional**: with that reading, it is false for multiple crossovers on 74 rows and 34 sites, given [`Gusfield2007.printedMSearch`](Gusfield2007/Theorem10PrintedMultiple.lean#L269) |
| Theorem 11 | [`gusfield_theorem11`](palomar/Gusfield2007/Challenge.lean#L172) | for any positive `d`, some `M` has `F¹(M) − R¹(M) ≥ d` |
| Line 656 | [`gusfield_Md_R_eq`](palomar/Gusfield2007/Challenge.lean#L242) | `R¹(M_d) = 3d`, where the paper claims the upper bound |
| Corollary 2 | [`gusfield_corollary2`](palomar/Gusfield2007/Challenge.lean#L177) | if every node of an optimal network for `M` with ancestral sequence `S` is visible, `M` is S-min (or S-min-1) decomposable |
| Corollary 3 | [`gusfield_corollary3`](palomar/Gusfield2007/Challenge.lean#L183) | when recombinations only model back or recurrent mutations, `M` is S-min decomposable for any `S`, and its parsimony score is the sum over the components of `G_S(M)` |
| §5.3.1 | [`gusfield_unrootedConjecture_single_false`](palomar/Gusfield2007/Challenge.lean#L191) | the unrooted conjecture is false for single crossovers: on Figure 6, `F¹ ≥ 4` and `R¹ ≤ 3` |
| §5.3.2 | [`gusfield_unrootedConjecture_multiple_false`](palomar/Gusfield2007/Challenge.lean#L196) | the unrooted conjecture is false for multiple crossovers: on Figure 8, `F ≥ 4` and `R ≤ 3` |
| §5.3.1 | [`gusfield_rootedConjecture_single_false`](palomar/Gusfield2007/Challenge.lean#L200) | the rooted conjecture is false for single crossovers |
| §5.3 | [`gusfield_rootedConjecture_multiple_false`](palomar/Gusfield2007/Challenge.lean#L203) | the rooted conjecture is false for multiple crossovers |
| Line 329 | [`gusfield_exists_isEfficientAtEntry`](palomar/Gusfield2007/Challenge.lean#L226) | a fully decomposed network can be made efficient, also with the entry node counted, with no more recombination nodes, the same ancestral sequence, and staying fully decomposed |
| §4.2 | [`gusfield_treeness_merged_false`](palomar/Gusfield2007/Challenge.lean#L234) | the treeness inequality fails for a blob that merges two components: treeness 5, where `T̄` has 4 edges |
| Line 590 | [`gusfield_conjecture22_false`](palomar/Gusfield2007/Challenge.lean#L245) | the conjecture of Huson and Klöpper is false, as Conjecture 2.2 of Klöpper's thesis states it |

### The sources

| Source | Lean | Statement |
| --- | --- | --- |
| Gusfield, Eddhu, Langley 2004, proof of Theorem 2.2 | [`galled_exists_isCycle_of_conflict`](palomar/Gusfield2007/Challenge.lean#L256) | two sites that conflict, in any set of rows labelling nodes of a network, are together on a recombination cycle |
| Gusfield, Eddhu, Langley 2004, Theorem 2.2 | [`galled_theorem2_2`](palomar/Gusfield2007/Challenge.lean#L261) | on a galled tree with single crossovers, sites `i < j` conflict exactly when they are on one gall with the recombination point between them, arranged in one of three ways |
| Gusfield, Eddhu, Langley 2004, Theorem 8.3 | [`galled_theorem8_3`](palomar/Gusfield2007/Challenge.lean#L268) | a reduced galled tree for `M` has the least number of recombination nodes, in its model and with multiple crossovers, and that number is the bound by removals |
| Gusfield et al. 2007, line 381 | [`galled_line381`](palomar/Gusfield2007/Challenge.lean#L273) | a galled tree reduced for `G(M)` makes `M` min decomposable, in its model and for multiple crossovers |
| Gusfield, Eddhu, Langley 2004, the algorithm | [`galled_galledBuild_correct`](palomar/Gusfield2007/Challenge.lean#L280) | if the computable function `galledBuild` returns a table, it is that of a reduced galled tree deriving `M` with ancestral sequence `S` and single crossovers |
| Gusfield, Eddhu, Langley 2004, its count | [`galled_galledBuildOps_le`](palomar/Gusfield2007/Challenge.lean#L288) | on `n` rows and `m` sites, the algorithm counts at most `233 (n + m + 1)⁶` operations; not the source's `O(nm + n³)` |
| Myers, Griffiths 2003, Algorithm 1 | [`myersGriffiths_algorithm1_isOptimalValue`](palomar/Gusfield2007/Challenge.lean#L300) | the matrix that [`algorithm1`](Gusfield2007/External/MyersGriffiths2003/Algorithm1.lean#L258) builds is that of the optimal values of the integer program on regions |
| Myers, Griffiths 2003, `R_h` | [`myersGriffiths_Rh_le_R`](palomar/Gusfield2007/Challenge.lean#L304) | the haplotype bounds on regions, combined by Algorithm 1, are a lower bound on `R¹(M)` |
| Hudson, Kaplan 1985, Appendix 2 | [`Gusfield2007Challenge.hudsonKaplan_isOptimalValue`](palomar/Gusfield2007/Challenge.lean#L308) | the final number of intervals of [`hudsonKaplan`](Gusfield2007/External/HudsonKaplan1985/Algorithm.lean#L73) is the bound `R_M`, the optimal value of the program for the matrix of incompatible pairs |
| Song, Hein 2005, equations (3), (5) | [`songHein_exists_orderedLength_eq_R`](palomar/Gusfield2007/Challenge.lean#L313) | over sequences of binary trees with totally ordered internal nodes, compatible with the columns, the minimum of `L(P)` is `R¹(M)`, and it is attained |

## The conditional theorem

[`gusfield_theorem10Printed_multiple_false_of_search`](palomar/Gusfield2007/Challenge.lean#L220) takes [`Gusfield2007.printedMSearch`](Gusfield2007/Theorem10PrintedMultiple.lean#L269) as a hypothesis: a finite search showing that two extra labels never suffice on the second component of [`printedMRows`](Gusfield2007/Theorem10PrintedMultiple.lean#L51). It is a hypothesis of the theorem rather than an axiom, so the statement shows it; Lean's kernel hasn't completed the computation. Two programs by the same author, not in the repository, and Lean's `#eval` support it; none of these is a proof. Theorem 10 itself, with `R_S(M)`, is unconditional.

## What the audit found

| Finding | Where |
| --- | --- |
| Theorem 4 is false as printed: the definition of "efficient" omits the node where a blob is entered. The repair is in Gusfield's 2014 book, for a stricter class | E42 |
| Theorem 4 is also false on the site-free arcs that line 97 allows, and needs two implicit conventions | E43, E44 |
| Theorem 10 is false if `R(M + S)` is read by the definition at line 385; lines 525 and 560 suggest a slip for `R_S(M)`, under which it is proved | E51 |
| Line 373 on the most tree-like network is false as printed, and fails for blobs that merge components | E45, E67 |
| Line 554 on galled networks, line 560 on visible nodes, the step at line 403, and line 180's wording of "reduced" are false as printed | E49, E50, E48, E47 |
| Line 329's modification isn't given, and the proofs have gaps at lines 135, 141, 187–190, 264, 271, 295, 299, 312–316, 411, 418 and 576; all are repaired and the results hold | E52, E53 |
| Gusfield, Eddhu, Langley 2004, Corollary 2.1, is false in one direction | E76 |
| Misprints in the paper, gaps and a misprint in the sources, and one unchecked point on Klöpper's thesis | E54, E77–E79, E85 |

[Section 3 of the report](docs/Gusfield2007/REPORT.md#3-errors-and-gaps-in-the-paper) gives each finding with its location, the paper's sentence, a Lean counterexample and the repair; [Sections 4 and 5](docs/Gusfield2007/REPORT.md#4-missing-hypotheses) give the missing and the redundant hypotheses. The numbers are those that the findings have across the papers of [lean4-tob](https://github.com/vltanh/lean4-tob), where this formalization was made. The proofs follow the paper's arguments, except the departures in [Section 7 of the report](docs/Gusfield2007/REPORT.md#7-departures-from-the-papers-proofs), each with what the paper does, what Lean does and why.

## Trust

- `lake build` passes; the only warnings are the `sorry`s of the Challenge's statements. There is no `sorry`, `axiom`, `native_decide` or `implemented_by` in [`Gusfield2007/`](Gusfield2007) or in the Solution.
- [`scripts/Audit.lean`](scripts/Audit.lean) checks every declaration of the project and of the modules of the library `Phylogenetics` that it imports, including private and generated ones, against [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound), and writes the routes of the proofs.
- [`scripts/route_check.py`](scripts/route_check.py) compares those routes with the paper's, in [`docs/Gusfield2007/paper_routes.tsv`](docs/Gusfield2007/paper_routes.tsv); [`docs/Gusfield2007/route_differences.tsv`](docs/Gusfield2007/route_differences.tsv) records every difference, with its reason.
- [`scripts/check_kernels.sh`](scripts/check_kernels.sh) checks the Challenge's theorems, as the Solution proves them, under Lean's kernel and NanoDa, through Comparator, and under con-ron.
- **No person has reviewed the proofs.** Independent agents reviewed the statements against the sources, compared the proofs with the paper, and checked the findings and the literature section.

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4), at `v4.37.0-rc1`.
- [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), the library of the collection, pinned by commit in [`lakefile.toml`](lakefile.toml): the Splits Equivalence Theorem ([`Phylogenetics.Tree.SplitsEquivalence`](https://github.com/vltanh/lean4-phylogenetics/blob/b56ce531644230622f069aaa8aa51a5143c1411e/Phylogenetics/Tree/SplitsEquivalence.lean)), restated in [`Gusfield2007/External/SempleSteel2003/`](Gusfield2007/External/SempleSteel2003), and what it needs about X-trees ([`Phylogenetics.Tree.XTree`](https://github.com/vltanh/lean4-phylogenetics/blob/b56ce531644230622f069aaa8aa51a5143c1411e/Phylogenetics/Tree/XTree.lean)).

## Palomar

No submission to Palomar is planned. [`palomar/Gusfield2007/`](palomar/Gusfield2007) has the files of an entry: the Challenge, the Solution, [`comparator.json`](palomar/Gusfield2007/comparator.json), which names them and the 38 theorems, and [`formalization.yaml`](palomar/Gusfield2007/formalization.yaml), the entry's metadata, with the statements aligned to the Challenge's theorems and every divergence from the paper. Comparator checks that the Solution proves exactly the Challenge's statements: from the repository root, after `lake build`, run [`scripts/check_kernels.sh`](scripts/check_kernels.sh). The Challenge imports the library's definitions rather than restating them in Mathlib's vocabulary, which Palomar requires of a submission: that would need the definitions its statements use, from [`Gusfield2007/Defs.lean`](Gusfield2007/Defs.lean) and beyond, in a block that the Challenge copies, with the bridges to the library's.

## Building

From the root of the repository:

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean                                     # axioms and dependencies
python3 scripts/route_check.py check docs/Gusfield2007/paper_routes.tsv --accept docs/Gusfield2007/route_differences.tsv
scripts/check_kernels.sh                                             # Comparator: Lean's kernel, NanoDa; con-ron
python3 scripts/linkify_docs.py                                      # the documents' links to the code
```

- Toolchain: Lean and Mathlib `v4.37.0-rc1` ([`lean-toolchain`](lean-toolchain), [`lake-manifest.json`](lake-manifest.json)).
- `lake comparator`, `leanexport` and `con-ron` come from the toolchain, under `lake env`.
- [`docs/Gusfield2007/CONFIGURATION.md`](docs/Gusfield2007/CONFIGURATION.md) records the versions, the decisions and what "line N" means.

## Layout

| Folder | Content |
| --- | --- |
| [`Gusfield2007/`](Gusfield2007) | The paper's library, on sequence-labelled networks, in the namespace [`Gusfield2007`](Gusfield2007); [its README](Gusfield2007/README.md) lists the modules |
| [`Gusfield2007/External/`](Gusfield2007/External) | The cited results, one directory per source, in the namespaces `External.<Source>`; [its README](Gusfield2007/External/README.md) lists them |
| [`Gusfield2007/Basic/`](Gusfield2007/Basic) | General mathematics: none yet |
| [`palomar/Gusfield2007/`](palomar/Gusfield2007) | The Challenge, the Solution, the Comparator configuration and the metadata |
| [`docs/Gusfield2007/`](docs/Gusfield2007) | [The report](docs/Gusfield2007/REPORT.md), [the credits](docs/Gusfield2007/CREDITS.md), the configuration, the routes of the proofs and the hashes of the sources read |
| [`scripts/`](scripts) | The audit, the route check, the kernels, the links and the tables |

## Related work

From [Section 10 of the report](docs/Gusfield2007/REPORT.md#10-the-paper-in-the-literature), searched on 2026-11-01.

- No other formalization of the paper was found, in any system, nor of `T̄`, the Buneman graph, perfect phylogeny, the four-gamete test or ancestral recombination graphs.
- Before: the lower bounds on recombinations of Hudson and Kaplan 1985 and Myers and Griffiths 2003; the galled trees of Gusfield, Eddhu, Langley 2004, whose reduced galled trees have the structure that Theorem 1 generalizes; and Gusfield and Bansal, RECOMB 2005, the first statement of the decomposition theorem and of the Full-Decomposition Optimality Conjecture.
- Concurrent: Huson and Klöpper, RECOMB 2007, on galled networks and their decomposition, with a conjecture that line 590 says is false. Klöpper's thesis of 2008 states it and says that this paper refutes it.
- Since: Gusfield's book *ReCombinatorics* (2014), read only in snippets, restates Theorem 4 with the entry node counted, for "canonical" ARGs. Huson et al. 2009 credit Yun Song with an example of the refutation of the conjectures, in a form on clusters, and van Iersel et al. 2010 and Kelk et al. 2012 state it. Dress et al. 2011 relate the blocks of the Buneman graph to the components of the incompatibility graph. Allman et al. 2023 cite this paper for the tree of blobs. No erratum was found, and no other work stating the errors recorded here, apart from the book's repair.

## What's next

How much does full decomposition cost? Theorem 11 says `F¹ − R¹` is unbounded for single crossovers, and line 666 says the authors don't know how robust their empirical results are in other ranges of data, for multiple crossovers, or with a fixed ancestral sequence; Gusfield's 2014 book, whose Section 7.4.3 and Chapter 11 are on this, should be read first. Line 425 stays open, and the multiple-crossover case of E51 stays conditional until the kernel completes [`Gusfield2007.printedMSearch`](Gusfield2007/Theorem10PrintedMultiple.lean#L269), or another proof of the same bound exists. [Section 11 of the report](docs/Gusfield2007/REPORT.md#11-whats-next) has these, the simpler arguments that the formalization found, and two routes not built: `T̄` through the Buneman graph of Dress et al. 2011, and line 411 through the cut nodes of the median network. A private `NEXT.md` holds the candidate follow-up papers.

## Credits

- Requested and supervised by The-Anh Vu-Le, who chose the paper and decided the layout, the kernels and publication. **No person has reviewed the proofs.**
- Statements, proofs, audit and documents by Claude (Opus 5.5) in Claude Code, with sub-agents, following the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure.
- Made in [lean4-tob](https://github.com/vltanh/lean4-tob) from 2026-10-31 to 2026-11-01, in two rounds shared with other papers. [`docs/Gusfield2007/CREDITS.md`](docs/Gusfield2007/CREDITS.md) has the details.

## License

[Apache-2.0](LICENSE).
