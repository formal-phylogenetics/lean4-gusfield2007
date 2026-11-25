# Gusfield, Bansal, Bafna, Song 2007: a decomposition theory for phylogenetic networks and incompatible characters

Source: D. Gusfield, V. Bansal, V. Bafna, Y. S. Song, J. Comput. Biol. 14 (2007), 1247--1272. Read in the PMC author manuscript (PMC2581772), and, for the symbols its plain text loses, in an author's copy with the same words, on Yun Song's page: <https://people.eecs.berkeley.edu/~yss/Pub/decomposition.pdf>. The journal's typeset text wasn't reachable, so nothing here was checked against it.

"Line 342" in the docstrings means line 342 of the plain text of the PMC page, one line per paragraph. Symbols rendered as images are missing from that text.

The routes of the proofs are in `docs/Gusfield2007/paper_routes.tsv`, and their differences from the paper's in `docs/Gusfield2007/route_differences.tsv`.

The paper's library is in the namespace `Gusfield2007`. It imports Mathlib, `Basic/`, the definitions and the shared facts (`Defs`, `Networks/`), the cited results in `External/`, one directory per source in the namespace `External.<Source>` (`External/README.md` lists them, and each source's README says whether it was read), and, in `ProofOfDecomposition/TreeFacts`, `Phylogenetics.Tree.XTree` of the library lean4-phylogenetics.

## Theorem 4

Theorem 4 is false with the printed definition of "efficient", because that definition omits the entry node of a blob (`theorem4_false_top`, `theorem4_false_small`). It is true with the entry node counted, up to two conventions and site-free arcs. That repair is in print and isn't ours: Gusfield, *ReCombinatorics* (MIT Press, 2014), Section 7.3.5, counts an external node "without regard to edge direction", and states the theorem for its canonical networks, a stricter class, as Theorem 7.3.3; we read the book only in snippets (`REPORT.md`, E42). What this adds is the characterization in both directions, the failure under the printed definition and the check in the kernel: `theorem4_entry` says that, for a fully decomposed network, `T′` is `T̄` exactly when the network has `Network.IsEfficientAtEntry`, `Network.RegularArcs` and `Network.DegreeCond`.

- The two conventions are a root of degree two and a recombination leaf (`theorem4Printed_false_rootDegreeTwo`, `theorem4Printed_false_recombLeaf`). Site-free arcs are a case line 97 allows and the statement must exclude, so the theorem fails as printed on them (`theorem4_false_siteFree`).
- With the printed definition, `theorem4`, `theorem4_splits` and `theorem4_iff` state exactly what is needed.
- The hypotheses can be met, for every `M` with at least three rows (`exists_realization`).
- Line 329 for `IsEfficientAtEntry` keeps the number of recombinations (`exists_isEfficientAtEntry_of_fullyDecomposed`, `exists_isEfficientAtEntry_of_any`, in `EntryNet`). Line 299 holds with the root at any node of `T̄` that isn't a row (`exists_network_rooted_at`, in `RootedFrame`); with the root at a row, the network derives the other rows (`exists_network_rooted_at_row`), since a network deriving all the rows can't have its root at a row with `T′ = T̄` (`root_not_mem_range`).

Section 4.2's characterization is false too (`mostTreeLikePrinted_false`); `treeness_le_and_eq_iff` is the true form, and `MergedTreeness` has the blobs it leaves out, where the inequality can fail (`treeness_merged_false`). The head of `ProofOfDecomposition/Uniqueness.lean` has the whole account.

## Theorem 10

`theorem10` is the statement with the rooted count `R_S(M)`, which is what the paper's proof is about, in each crossover model and with no hypothesis on the columns. The sentence at line 560 is false with identical columns (`visibleOfTightPrinted_false`), so the proof uses the pair of labels on two sites with different columns; `sMinDecomposable_of_haplotype_tight` is the paper's proof, when the columns are distinct. Theorem 10 with `R(M + S)` read by line 385's definition is `Theorem10Printed`. It is false for single crossovers (`theorem10Printed_single_false`). The paper uses the symbol at lines 525 and 560 for a network with ancestral sequence `S`, which suggests a slip for `R_S(M)`, and that form is `theorem10`. For multiple crossovers `theorem10Printed_multiple_false_of_search` has a counterexample, given one computation, `printedMSearch`, which is a visible hypothesis of that theorem: the kernel hasn't completed it.

## What stays open

Line 425, `MinDecomposableOfForallS`. `minDecomposableOfForallS_of_haplotypeBound_eq` is the case `H(M) = R(M)`.

## Modules

The modules are in the namespace `Gusfield2007` and listed by the sections of the paper. `Basic/` and `External/` have READMEs
of their own.

### Definitions, and what the sources share

| Module | Contents |
| --- | --- |
| `Defs` | the definitions, with the readings of the paper; its block between the markers is the Challenge's, and imports only Mathlib |
| `Networks.Basic` | `G_S(M) = G(M + S)`, arcs, paths and reachability, embeddings, isomorphisms, recombinants, `R` and `R_S` under renaming, the non-trivial components (`Decomp.Cent`) |
| `Networks.Blobs` | Section 2.1: recombination cycles and blobs, line 139, the two paths lemma, `T′` is a tree, making blobs node-disjoint (line 135) |
| `Networks.Operations` | where a label comes from, the four-gamete test, trimming to the rows, moving a recombination node, `PreNet` |
| `Networks.Explicit` | rows from bits, and networks from lists of numbers, checked by the kernel |
| `Networks.Existence` | a network for every set of rows, with any ancestral sequence, used to inflate a node of `T̄` |
| `Networks.TimeOrdered` | Section 5.3.3: time-ordered trees and ordered SPR, for Song and Hein's bound |

### Section 3, the proof of the Decomposition Theorem (`ProofOfDecomposition/`)

| Module | Contents |
| --- | --- |
| `Structure` | Section 3.1: Lemmas 1, 2, Theorem 2, Corollary 1 |
| `TreeFacts`, `TreeCuts`, `TreeContract` | sides of edges of a tree, cut functions, a perfect phylogeny with every internal edge labelled, line 295 |
| `SuperCharacters`, `Figure1` | Sections 3.2, 3.3: Lemmas 3, 4, existence and uniqueness of `T̄`; Footnote 2 |
| `DecompNet`, `GlueNet`, `TBarFrame`, `SameCycles` | removing arcs and leaves, a new leaf, gluing networks into the central nodes, `T̄` as a frame, networks with the same cycles |
| `Decomposition` | Sections 2.3, 3.4, 3.5: Theorems 1, 3 and the converses |
| `BlobFacts`, `Hub`, `Uniqueness`, `Realizability`, `EntryNet`, `RootedFrame` | Section 3.7: Theorem 4, false as printed, and its true forms; the modification of line 329; line 299 with the root at any node; the hypotheses can be met |
| `FiniteNets`, `CounterexampleNets` | the networks of Sections 3.7 and 4.2, checked by the kernel |
| `GalledTrees.Existence`, `GalledTrees.Unrooted`, `GalledTrees.Decide`, `GalledTrees.Build` | the results of Gusfield, Eddhu, Langley 2004 that are proved with this section's construction or with line 212: reduced galled trees exist (Corollary 5.1 of the source), Theorem 2.7, and the correctness of the algorithm |

### Section 4, broader applications (`Applications/`)

| Module | Contents |
| --- | --- |
| `Histories` | the labels of a network generated one at a time (`Gen`), for the lower bounds of Section 5 and the trees of Section 4.1 |
| `Parsimony` | Section 4.1: mutation trees as networks, re-rooting |
| `MergedTreeness` | Section 4.2: the treeness inequality for blobs that merge components |

### Section 5, the Full-Decomposition Optimality Conjectures (`OptimalityConjectures/`)

| Module | Contents |
| --- | --- |
| `Introduction` | Section 5.1: the conjectures, the computation of `F` and `F_S`, line 425 |
| `SufficientConditions`, `Surgery` | Section 5.2: Theorems 5 to 10, Corollaries 2, 3, Lemma 5 |
| `OpenStatements`, `OpenSearch`, `LabelSearch`, `Theorem10PrintedMultiple` | Theorem 10 with `R(M + S)` read literally, and without an ancestral sequence; a verified search for lower bounds on `R` |
| `GalledNetworks` | line 554: non-degenerate galled networks |
| `HusonKloepper` | line 590: Conjecture 1 of Huson and Klöpper, read from Conjecture 2.2 of Klöpper's thesis; reticulate networks and the bridge to `R`; the refutation by Figure 8 |
| `Examples`, `Components` | the matrices of the figures, bookkeeping |
| `Figure5`, `Figure6`, `Figure8`, `EvenRows`, `MdMatrix`, `Mosaic` | Section 5.3: the numbers of the figures, `M_d` |
| `Figure10`, `MdLower` | Section 5.3.3: Figure 10, `R¹(M_d) ≤ 3d`, and `R¹(M_d) = 3d` |
| `Counterexamples` | Sections 5.1, 5.3: the conjectures are false, Theorem 11 |
