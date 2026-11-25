module

public meta import Lean.Elab.Command
public meta import Lean.DocString
-- One `import all` line per module of the libraries, so that proofs are visible to the dependency
-- traversal (the module system hides them from a plain `import`): every module of `Gusfield2007/`
-- (`External/` and the paper's library) and the paper's Solution in `palomar/`, but not the
-- Challenge, whose theorems the Solution restates under the same names; then the modules of the
-- library `Phylogenetics` that the project imports, whose proofs the audit reads too. Generate the
-- first lines with
--   { find Gusfield2007 -name '*.lean'; cd palomar && find . -name Solution.lean; } |
--     sed 's#^\./##; s/\.lean$//; s#/#.#g; s/^/import all /' | sort
import all Gusfield2007.BlobFacts
import all Gusfield2007.Blobs
import all Gusfield2007.Components
import all Gusfield2007.Conjectures
import all Gusfield2007.CounterexampleNets
import all Gusfield2007.Counterexamples
import all Gusfield2007.DecompNet
import all Gusfield2007.Decomposition
import all Gusfield2007.Defs
import all Gusfield2007.EntryNet
import all Gusfield2007.EvenRows
import all Gusfield2007.Examples
import all Gusfield2007.ExplicitNetworks
import all Gusfield2007.External.Gusfield1991.PerfectPhylogeny
import all Gusfield2007.External.GusfieldEtAl2004.Algorithm
import all Gusfield2007.External.GusfieldEtAl2004.Build
import all Gusfield2007.External.GusfieldEtAl2004.BuildCount
import all Gusfield2007.External.GusfieldEtAl2004.Counts
import all Gusfield2007.External.GusfieldEtAl2004.Elimination
import all Gusfield2007.External.GusfieldEtAl2004.GalledTree
import all Gusfield2007.External.GusfieldEtAl2004.GallFromChains
import all Gusfield2007.External.GusfieldEtAl2004.Optimality
import all Gusfield2007.External.GusfieldEtAl2004.ReducedExists
import all Gusfield2007.External.GusfieldEtAl2004.ReducedUnrooted
import all Gusfield2007.External.GusfieldEtAl2004.SameBlob
import all Gusfield2007.External.GusfieldEtAl2004.Theorem2_2
import all Gusfield2007.External.HudsonKaplan1985.Algorithm
import all Gusfield2007.External.HudsonKaplan1985.AlgorithmBound
import all Gusfield2007.External.HudsonKaplan1985.Bound
import all Gusfield2007.External.MyersGriffiths2003.Algorithm1
import all Gusfield2007.External.MyersGriffiths2003.Bound
import all Gusfield2007.External.MyersGriffiths2003.Composite
import all Gusfield2007.External.MyersGriffiths2003.Constraints
import all Gusfield2007.External.MyersGriffiths2003.Implementation
import all Gusfield2007.External.MyersGriffiths2003.Proposition2
import all Gusfield2007.External.MyersGriffiths2003.SampleHistory
import all Gusfield2007.External.SempleSteel2003.SplitsEquivalence
import all Gusfield2007.External.SongHein2005.BinaryPaths
import all Gusfield2007.External.SongHein2005.Bound
import all Gusfield2007.External.SongHein2005.Minimal
import all Gusfield2007.Figure1
import all Gusfield2007.Figure10
import all Gusfield2007.Figure5
import all Gusfield2007.Figure6
import all Gusfield2007.Figure8
import all Gusfield2007.FiniteNets
import all Gusfield2007.GalledNetworks
import all Gusfield2007.GlueNet
import all Gusfield2007.Histories
import all Gusfield2007.Hub
import all Gusfield2007.HusonKloepper
import all Gusfield2007.InflateNet
import all Gusfield2007.LabelSearch
import all Gusfield2007.MdLower
import all Gusfield2007.MdMatrix
import all Gusfield2007.MergedTreeness
import all Gusfield2007.Mosaic
import all Gusfield2007.NetworkOps
import all Gusfield2007.OpenSearch
import all Gusfield2007.OpenStatements
import all Gusfield2007.Parsimony
import all Gusfield2007.Preliminaries
import all Gusfield2007.Realizability
import all Gusfield2007.RootedFrame
import all Gusfield2007.SameCycles
import all Gusfield2007.Solution
import all Gusfield2007.Structure
import all Gusfield2007.SufficientConditions
import all Gusfield2007.SuperCharacters
import all Gusfield2007.Surgery
import all Gusfield2007.TBarFrame
import all Gusfield2007.Theorem10PrintedMultiple
import all Gusfield2007.TimeOrdered
import all Gusfield2007.TreeContract
import all Gusfield2007.TreeCuts
import all Gusfield2007.TreeFacts
import all Gusfield2007.Uniqueness
import all Phylogenetics.Tree.SplitsEquivalence
import all Phylogenetics.Tree.XTree

/-!
# Axiom and dependency audit

Run with `lake env lean scripts/Audit.lean` after `lake build`.

For every numbered result of the paper, this prints the axioms it depends on and the results from
prior work (`Gusfield2007/External/`) that it uses, whether proved there or, in a conditional formalization,
assumed as hypotheses of its statement. It then checks every declaration of the library and the
theorems that Palomar's comparator checks. The run fails if any of them depends on an axiom other
than Lean's standard `propext`, `Classical.choice` and `Quot.sound` (a `sorry` shows up as the
axiom `sorryAx`). Its table of results is the source of the report's dependency table.

It also writes the *route* of every numbered result to `.lake/route_deps.tsv`: the other
numbered results that its proof uses, found by following the proof through the library's helper
lemmas and stopping at numbered results, together with the TeX label that the result's docstring
names in backticks. `scripts/route_check.py` compares these routes with the results that the
paper's proofs cite, in `docs/Gusfield2007/paper_routes.tsv`.

The library's modules are imported with `import all`, which makes the proofs of their theorems
available: the module system does not export them otherwise. The traversal tests membership in a
precomputed set of the library's constants; looking up each constant's module instead
(`Environment.getModuleIdxFor?`) makes the interpreted script take minutes.

The library `Phylogenetics`, which this project requires, is audited with it: its modules that the
project imports have `import all` lines, and `isLibraryModule` counts them, so that one run covers
every axiom that a result depends on.
Keep one `import all` line per module of the libraries, each on its own line: a module that is
missing is still imported through the others, but without its proofs, and the audit then misses the
axioms and the routes inside them. CI checks the list.
-/

open Lean Elab Command

namespace Audit

/-- The results from prior work, with a short label: the theorems proved in `Gusfield2007/External/`
and in the library `Phylogenetics`. The traversal stops at them. -/
meta def externalResults : List (String × Name) :=
  [("Semple, Steel 2003, the Splits Equivalence Theorem, existence", ``External.SempleSteel2003.exists_xTree_iff),
   ("Semple, Steel 2003, the Splits Equivalence Theorem, uniqueness", ``External.SempleSteel2003.xTree_unique),
   ("Gusfield 1991, the Perfect Phylogeny Theorem", ``External.Gusfield1991.exists_isPerfectPhylogeny_iff),
   ("Gusfield 1991, a network with no recombination", ``External.Gusfield1991.exists_network_of_no_conflict),
   ("Gusfield 1991, a tree for a matrix with no incompatible pair", ``External.Gusfield1991.exists_network_iff),
   ("Gusfield 1991, a rooted tree for a matrix with no conflicting pair", ``External.Gusfield1991.exists_network_rooted_iff),
   ("Gusfield 1991, the rooted tree is unique", ``External.Gusfield1991.network_rooted_unique),
   ("Gusfield, Eddhu, Langley 2004, incompatible sites are on one blob", ``External.GusfieldEtAl2004.exists_isBlob_of_incompatible),
   ("Gusfield, Eddhu, Langley 2004, a reduced galled tree is fully decomposed, rooted", ``External.GusfieldEtAl2004.IsReducedGalledTree.isFullyDecomposedFor_conflictGraph),
   ("Gusfield, Eddhu, Langley 2004, a reduced galled tree is fully decomposed, unrooted", ``External.GusfieldEtAl2004.IsReducedGalledTree.isFullyDecomposedFor_incompatGraph),
   ("Myers, Griffiths 2003, the haplotype bound", ``External.MyersGriffiths2003.haplotypeBound_le_R),
   ("Myers, Griffiths 2003, the haplotype bound with an ancestral sequence", ``External.MyersGriffiths2003.haplotypeBound_addRow_le_RS),
   ("Myers, Griffiths 2003, the equality case of the bound", ``External.MyersGriffiths2003.allVisible_of_eq),
   ("Hudson, Kaplan 1985, the bound", ``External.HudsonKaplan1985.card_le_R),
   ("Song, Hein 2005, the bound by ordered SPR", ``External.SongHein2005.R_le_sprLength),
   ("Song, Hein 2005, equations (3), (5), for time-ordered trees", ``External.SongHein2005.exists_sprLength_eq_R),
   ("Song, Hein 2005, equations (3), (5), for the source's trees", ``External.SongHein2005.exists_orderedLength_eq_R),
   ("Gusfield, Eddhu, Langley 2004, conflicting sites are on one cycle", ``External.GusfieldEtAl2004.exists_isCycle_of_conflict),
   ("Gusfield, Eddhu, Langley 2004, Theorem 2.2", ``External.GusfieldEtAl2004.theorem2_2),
   ("Gusfield, Eddhu, Langley 2004, Corollary 5.1 for galled trees", ``External.GusfieldEtAl2004.exists_isReducedGalledTree),
   ("Gusfield, Eddhu, Langley 2004, Theorem 8.3", ``External.GusfieldEtAl2004.theorem8_3),
   ("Gusfield, Eddhu, Langley 2004, the algorithm", ``External.GusfieldEtAl2004.Algorithm.galledBuild_correct),
   ("Gusfield, Eddhu, Langley 2004, the count of the algorithm", ``External.GusfieldEtAl2004.Algorithm.galledBuildOps_le),
   ("Myers, Griffiths 2003, Algorithm 1", ``External.MyersGriffiths2003.algorithm1_isOptimalValue),
   ("Myers, Griffiths 2003, the composite bound", ``External.MyersGriffiths2003.algorithm1_le_R),
   ("Myers, Griffiths 2003, the bound R_h", ``External.MyersGriffiths2003.Rh_le_R),
   ("Myers, Griffiths 2003, the bound R_s", ``External.MyersGriffiths2003.Rs_le_R),
   ("Myers, Griffiths 2003, Proposition 2", ``External.MyersGriffiths2003.proposition2),
   ("Hudson, Kaplan 1985, the algorithm of Appendix 2", ``External.HudsonKaplan1985.hudsonKaplan_isOptimalValue),
   ("Hudson, Kaplan 1985, the bound R_M", ``External.HudsonKaplan1985.rM_le_R)]

/-- The numbered results of the papers, and the labelled claims that their proofs use, which the routes need, in the order
of the paper. The results that Gusfield et al. 2007 cite are here too, for their route labels. -/
meta def paperResults1 : List (String × Name) :=
  [("Gusfield 1991, the Perfect Phylogeny Theorem", ``External.Gusfield1991.exists_isPerfectPhylogeny_iff),
   ("Semple, Steel 2003, the Splits Equivalence Theorem, existence", ``External.SempleSteel2003.exists_xTree_iff),
   ("Semple, Steel 2003, the Splits Equivalence Theorem, uniqueness", ``External.SempleSteel2003.xTree_unique),
   ("Hudson, Kaplan 1985, the bound", ``External.HudsonKaplan1985.card_le_R),
   ("Myers, Griffiths 2003, the haplotype bound", ``External.MyersGriffiths2003.haplotypeBound_le_R),
   ("Myers, Griffiths 2003, the equality case of the bound", ``External.MyersGriffiths2003.allVisible_of_eq),
   ("Song, Hein 2005, the bound by ordered SPR", ``External.SongHein2005.R_le_sprLength),
   ("Gusfield, Eddhu, Langley 2004, incompatible sites are on one blob", ``External.GusfieldEtAl2004.exists_isBlob_of_incompatible),
   ("Gusfield, Eddhu, Langley 2004, a reduced galled tree is fully decomposed", ``External.GusfieldEtAl2004.IsReducedGalledTree.isFullyDecomposedFor_conflictGraph),
   ("Song, Hein 2005, the first tree", ``External.SongHein2005.hasState_init),
   ("Song, Hein 2005, one ordered SPR is one recombination node", ``External.SongHein2005.HasState.spr),
   ("Gusfield et al. 2007, line 135", ``Gusfield2007.Network.exists_blobsNodeDisjoint),
   ("Gusfield et al. 2007, line 139", ``Gusfield2007.Network.IsBlob.eq_of_inter_nonempty),
   ("Gusfield et al. 2007, lines 140 to 142", ``Gusfield2007.Network.blobbedTree_isTree),
   ("Gusfield et al. 2007, lines 152, 160", ``Gusfield2007.conflictGraph_eq_incompatGraph_addRow),
   ("Gusfield et al. 2007, lines 152, 160, S in M", ``Gusfield2007.conflictGraph_eq_of_mem),
   ("Gusfield et al. 2007, lines 182 to 185", ``Gusfield2007.converse),
   ("Gusfield et al. 2007, line 190", ``Gusfield2007.converse_rooted),
   ("Gusfield et al. 2007, line 178", ``Gusfield2007.isFullyDecomposedFor_iff_correspondence),
   ("Gusfield 1991, uniqueness of the rooted perfect phylogeny (Gusfield et al. 2007, line 156)", ``External.Gusfield1991.network_rooted_unique),
   ("Gusfield et al. 2007, line 156: the undirected tree of a perfect phylogeny is invariant", ``Gusfield2007.perfectPhylogeny_invariant),
   ("Gusfield et al. 2007, line 156 without the conventions", ``Gusfield2007.perfectPhylogeny_not_invariant),
   ("Gusfield et al. 2007, lines 180, 381, a reduced galled tree is fully decomposed", ``External.GusfieldEtAl2004.IsReducedGalledTree.isFullyDecomposedFor_incompatGraph),
   ("Gusfield et al. 2007, the sentence of line 180 is false", ``External.GusfieldEtAl2004.line180_printed_false),
   ("Gusfield et al. 2007, line 200", ``Gusfield2007.exists_isDominantPair),
   ("Gusfield et al. 2007, Lemma 1", ``Gusfield2007.lemma1),
   ("Gusfield et al. 2007, line 212", ``Gusfield2007.exists_isDominantFor),
   ("Gusfield et al. 2007, lines 200, 212", ``Gusfield2007.isDominantFor_unique)]

/-- The numbered results of the papers, and the labelled claims that their proofs use, continued. -/
meta def paperResults2 : List (String × Name) :=
  [("Gusfield et al. 2007, Theorem 2", ``Gusfield2007.theorem2),
   ("Gusfield et al. 2007, line 229", ``Gusfield2007.dominant_mem_restrictRows),
   ("Gusfield et al. 2007, Corollary 1", ``Gusfield2007.corollary1),
   ("Gusfield et al. 2007, line 237", ``Gusfield2007.ncard_pairs_eq_three),
   ("Gusfield et al. 2007, Lemma 2", ``Gusfield2007.lemma2),
   ("Gusfield et al. 2007, line 283", ``Gusfield2007.existsUnique_charValue_eq_true),
   ("Gusfield et al. 2007, line 281", ``Gusfield2007.four_le_card_restrictRows),
   ("Gusfield et al. 2007, Lemma 3", ``Gusfield2007.lemma3),
   ("Gusfield et al. 2007, line 264", ``Gusfield2007.exists_isTBar),
   ("Gusfield et al. 2007, lines 156, 344", ``Gusfield2007.isTBar_unique),
   ("Gusfield et al. 2007, Lemma 4", ``Gusfield2007.lemma4),
   ("Gusfield et al. 2007, line 277, the edges at the centre", ``Gusfield2007.adj_center_labelled),
   ("Gusfield et al. 2007, line 299", ``Gusfield2007.inflate),
   ("Gusfield et al. 2007, Theorem 1, the proof", ``Gusfield2007.exists_network_of_pieces),
   ("Gusfield et al. 2007, Theorem 1", ``Gusfield2007.theorem1),
   ("Gusfield et al. 2007, Theorem 1 with an ancestral sequence, line 187", ``Gusfield2007.theorem1_rooted),
   ("Gusfield et al. 2007, Theorem 3", ``Gusfield2007.theorem3),
   ("Gusfield et al. 2007, line 330", ``Gusfield2007.exists_isEfficient),
   ("Gusfield et al. 2007, line 330, fully decomposed", ``Gusfield2007.exists_efficient_fullyDecomposed),
   ("Gusfield et al. 2007, Theorem 4, as printed (a definition)", ``Gusfield2007.Theorem4Printed),
   ("Gusfield et al. 2007, Theorem 4 as printed fails, a root of degree two", ``Gusfield2007.theorem4Printed_false_rootDegreeTwo),
   ("Gusfield et al. 2007, Theorem 4 as printed fails, a recombination leaf", ``Gusfield2007.theorem4Printed_false_recombLeaf),
   ("Gusfield et al. 2007, Theorem 4 is false, the error at line 342", ``Gusfield2007.theorem4_false_top),
   ("Gusfield et al. 2007, Theorem 4, closest true form, on splits", ``Gusfield2007.theorem4_splits),
   ("Gusfield et al. 2007, Theorem 4, closest true form", ``Gusfield2007.theorem4),
   ("Gusfield et al. 2007, splits of tree arcs are compatible with the characters", ``Gusfield2007.treeSplits_compatible),
   ("Gusfield et al. 2007, line 329, for any network", ``Gusfield2007.exists_isEfficient_of_any),
   ("Gusfield et al. 2007, efficient, counting the entry node (a definition)", ``Gusfield2007.Network.IsEfficientAtEntry),
   ("Gusfield et al. 2007, line 329, for efficient at entry", ``Gusfield2007.exists_isEfficientAtEntry),
   ("Gusfield et al. 2007, Theorem 4 exactly, with the printed definition", ``Gusfield2007.theorem4_iff),
   ("Gusfield et al. 2007, Theorem 4 exactly, with the entry node counted", ``Gusfield2007.theorem4_entry),
   ("Gusfield et al. 2007, Theorem 4 is not vacuous", ``Gusfield2007.exists_realization),
   ("Gusfield et al. 2007, Theorem 4 is false, a smaller instance", ``Gusfield2007.theorem4_false_small),
   ("Gusfield et al. 2007, Theorem 4 is false, a site-free arc", ``Gusfield2007.theorem4_false_siteFree),
   ("Gusfield et al. 2007, Theorem 4, a blob at the root can have an exit at the top", ``Gusfield2007.fourGametes_rootExit),
   ("Gusfield et al. 2007, Theorem 4, a blob at the root, with the entry node", ``Gusfield2007.fourRootNet_isEfficientAtEntry),
   ("Gusfield et al. 2007, Theorem 4, the counterexample, with the entry node", ``Gusfield2007.topNet_not_isEfficientAtEntry),
   ("Gusfield et al. 2007, Theorem 4, T prime is not invariant", ``Gusfield2007.topRows_not_invariant),
   ("Gusfield et al. 2007, Theorem 4, on splits, the exemption", ``Gusfield2007.theorem4_splits_siteFreeRoot),
   ("Gusfield et al. 2007, line 341 fails for the printed definition", ``Gusfield2007.line341_false_fig2),
   ("Gusfield et al. 2007, Section 4.1, a tree in which every row labels a node", ``Gusfield2007.MutationTree.exists_fin_of_displays),
   ("Gusfield et al. 2007, Section 4.1, a tree bounds the parsimony score", ``Gusfield2007.MutationTree.parsimonyScore_le_of_displays),
   ("Gusfield et al. 2007, Section 4.1, re-rooting", ``Gusfield2007.MutationTree.exists_reroot),
   ("Gusfield et al. 2007, Section 4.1, the score at a row", ``Gusfield2007.MutationTree.parsimonyScore_row_le),
   ("Gusfield et al. 2007, Section 4.1, a network of mutations gives a tree", ``Gusfield2007.Network.exists_mutationTree),
   ("Gusfield et al. 2007, Section 4.1, a tree is a history", ``Gusfield2007.MutationTree.exists_gen),
   ("Gusfield et al. 2007, Section 4.1, a history is a pre-network", ``Gusfield2007.Gen.exists_preNet),
   ("Gusfield et al. 2007, Section 4.2, as printed (a definition)", ``Gusfield2007.MostTreeLikePrinted),
   ("Gusfield et al. 2007, Section 4.2 is false", ``Gusfield2007.mostTreeLikePrinted_false),
   ("Gusfield et al. 2007, Section 4.2, the first example", ``Gusfield2007.treeness_example₁),
   ("Gusfield et al. 2007, Section 4.2, the second example", ``Gusfield2007.treeness_example₂),
   ("Gusfield et al. 2007, Section 4.2, the positive form", ``Gusfield2007.treeness_le_and_eq_iff),
   ("Gusfield et al. 2007, Section 4.2, the positive form needs the root", ``Gusfield2007.treeness_positive_needs_root),
   ("Gusfield et al. 2007, Section 4.2, beyond fully decomposed networks", ``Gusfield2007.treeness_nonFD_example),
   ("Gusfield et al. 2007, Section 4.2, the inequality can be strict", ``Gusfield2007.treeness_strict_example),
   ("Gusfield et al. 2007, line 403, one input at a time", ``Gusfield2007.minDecomposable_of_sMinDecomposable),
   ("Gusfield et al. 2007, the rooted conjectures imply the unrooted ones", ``Gusfield2007.rootedConjecture_imp_unrootedConjecture),
   ("Gusfield et al. 2007, line 403, the rooted equivalence", ``Gusfield2007.sMinDecomposable_iff),
   ("Gusfield et al. 2007, line 413", ``Gusfield2007.FS_eq_sum),
   ("Gusfield et al. 2007, line 635, two components", ``Gusfield2007.add_R_le_F),
   ("Gusfield et al. 2007, line 635", ``Gusfield2007.sum_R_le_F),
   ("Gusfield et al. 2007, lines 416, 418", ``Gusfield2007.F_eq_sInf_interior),
   ("Gusfield et al. 2007, lines 416, 418, without the tree", ``Gusfield2007.F_eq_sInf_roots),
   ("Gusfield et al. 2007, line 418, the second fact", ``Gusfield2007.exists_interior_sum_rootCost_le),
   ("Gusfield et al. 2007, line 420", ``Gusfield2007.sum_R_le_of_minDecomposable),
   ("Gusfield et al. 2007, line 420, rooted", ``Gusfield2007.sum_le_RS_of_sMinDecomposable),
   ("Gusfield et al. 2007, lines 404 to 410, Figure 5", ``Gusfield2007.fig5_counts),
   ("Gusfield et al. 2007, line 410, the caption of Figure 5", ``Gusfield2007.fig5_counts_multiple),
   ("Gusfield et al. 2007, Lemma 5", ``Gusfield2007.lemma5),
   ("Gusfield et al. 2007, Theorem 7", ``Gusfield2007.theorem7),
   ("Gusfield et al. 2007, Corollary 3, the bridge to parsimony", ``Gusfield2007.parsimonyScore_eq),
   ("Gusfield et al. 2007, line 411, the second sentence", ``Gusfield2007.unrootedParsimonyScore_eq_sum),
   ("Gusfield et al. 2007, Corollary 3", ``Gusfield2007.corollary3),
   ("Gusfield et al. 2007, line 411", ``Gusfield2007.minDecomposable_pointwise),
   ("Gusfield et al. 2007, Theorem 8", ``Gusfield2007.theorem8),
   ("Gusfield et al. 2007, line 533", ``Gusfield2007.respects_iff_card),
   ("Gusfield et al. 2007, Theorem 9", ``Gusfield2007.theorem9),
   ("Gusfield et al. 2007, Theorem 5", ``Gusfield2007.theorem5),
   ("Gusfield et al. 2007, Corollary 2", ``Gusfield2007.corollary2),
   ("Gusfield et al. 2007, the network of the counterexample to lines 560 to 563", ``Gusfield2007.chainNet),
   ("Gusfield et al. 2007, the sentence of lines 560 to 563 is false", ``Gusfield2007.visibleOfTightPrinted_false),
   ("Gusfield et al. 2007, Theorem 10 with R(M + S) read literally (a definition)", ``Gusfield2007.Theorem10Printed),
   ("Gusfield et al. 2007, line 559, the haplotype bound with an ancestral sequence", ``External.MyersGriffiths2003.haplotypeBound_addRow_le_RS),
   ("Gusfield et al. 2007, Theorem 10, with the ancestral sequence", ``Gusfield2007.theorem10),
   ("Gusfield et al. 2007, Theorem 6", ``Gusfield2007.theorem6),
   ("Gusfield et al. 2007, line 554, with the ancestral sequence", ``Gusfield2007.incompatible_labelSet_iff),
   ("Gusfield et al. 2007, line 554, the graphs", ``Gusfield2007.conflictGraph_labelSet_eq),
   ("Gusfield et al. 2007, line 554, the application of Theorem 5", ``Gusfield2007.sMinDecomposable_of_galled),
   ("Gusfield et al. 2007, the sentence of line 554 is false", ``Gusfield2007.galledIncompatPrinted_false),
   ("Gusfield et al. 2007, the unrooted conjecture is false, single crossover", ``Gusfield2007.unrootedConjecture_single_false),
   ("Gusfield et al. 2007, the unrooted conjecture is false, multiple crossover", ``Gusfield2007.unrootedConjecture_multiple_false),
   ("Gusfield et al. 2007, the rooted conjecture is false, single crossover", ``Gusfield2007.rootedConjecture_single_false),
   ("Gusfield et al. 2007, the rooted conjecture is false, multiple crossover", ``Gusfield2007.rootedConjecture_multiple_false),
   ("Gusfield et al. 2007, Figure 10", ``Gusfield2007.figure10),
   ("Gusfield et al. 2007, line 656", ``Gusfield2007.Md_R_le),
   ("Gusfield et al. 2007, Theorem 11", ``Gusfield2007.theorem11),
   ("Gusfield et al. 2007, line 608, the incompatible pair", ``Gusfield2007.fig6_line608_incompatible),
   ("Gusfield et al. 2007, line 608, consistent with Theorem 8", ``Gusfield2007.fig6_line608_theorem8),
   ("Gusfield et al. 2007, line 608, consistent with Theorem 10", ``Gusfield2007.fig6_line608_theorem10),
   ("Gusfield et al. 2007, Footnote 2", ``Gusfield2007.footnote2)]

/-- The numbered results of the papers, and the labelled claims that their proofs use, continued. -/
meta def paperResults3 : List (String × Name) :=
  [("Gusfield et al. 2007, where a label comes from", ``Gusfield2007.Network.exists_source),
   ("Gusfield et al. 2007, trimming", ``Gusfield2007.Network.exists_derives_of_displays),
   ("Gusfield et al. 2007, a network from a pre-network", ``Gusfield2007.PreNet.exists_network)]

/-- The further labelled results on Gusfield et al. 2007, and those of Gusfield, Eddhu, Langley 2004. -/
meta def paperResults4 : List (String × Name) :=
  [("Gusfield et al. 2007, line 381 (line381_rooted)", ``External.GusfieldEtAl2004.line381_rooted),
   ("Gusfield et al. 2007, line 381 (reducedGalledTree_recombCount_eq_RS)", ``External.GusfieldEtAl2004.reducedGalledTree_recombCount_eq_RS),
   ("Gusfield et al. 2007, line 381 (line381)", ``External.GusfieldEtAl2004.line381),
   ("Gusfield et al. 2007, line 381 (reducedGalledTree_recombCount_eq_R)", ``External.GusfieldEtAl2004.reducedGalledTree_recombCount_eq_R),
   ("Gusfield et al. 2007, line 381 (sMinDecomposable_of_isGalledTree)", ``External.GusfieldEtAl2004.sMinDecomposable_of_isGalledTree),
   ("Gusfield et al. 2007, line 381 (minDecomposable_of_isGalledTree)", ``External.GusfieldEtAl2004.minDecomposable_of_isGalledTree),
   ("Gusfield et al. 2007, line 180", ``External.GusfieldEtAl2004.exists_isReducedGalledTree_incompatGraph),
   ("Gusfield et al. 2007, line 381 (R_eq_card_cent)", ``External.GusfieldEtAl2004.R_eq_card_cent),
   ("Gusfield et al. 2007, line 180, polynomial time", ``External.GusfieldEtAl2004.Algorithm.galledBuildOps_le),
   ("Gusfield et al. 2007, The proof of Theorem 10 as the paper gives it", ``Gusfield2007.sMinDecomposable_of_haplotype_tight),
   ("Gusfield et al. 2007, A tight network, on two sites with different columns", ``Gusfield2007.exists_row_of_eq_haplotypeBound),
   ("Gusfield et al. 2007, Line 329 for IsEfficientAtEntry, without increasing recombinations", ``Gusfield2007.exists_isEfficientAtEntry_of_fullyDecomposed),
   ("Gusfield et al. 2007, Line 329 for IsEfficientAtEntry, for any network", ``Gusfield2007.exists_isEfficientAtEntry_of_any),
   ("Gusfield et al. 2007, Line 590, for the conjecture as the thesis states it", ``Gusfield2007.conjecture22_false),
   ("Gusfield et al. 2007, Conjecture 2.2 of the thesis, which is Conjecture 1 of Huson and Klöpper 2007", ``Gusfield2007.Conjecture22),
   ("Gusfield et al. 2007, A reticulate network, with its sampled splits, is a network", ``Gusfield2007.ReticulateNetwork.toNetwork),
   ("Gusfield et al. 2007, The fewest reticulations explaining the splits of M are R(M)", ``Gusfield2007.ReticulateNetwork.exists_reticulateNetwork),
   ("Gusfield et al. 2007, Definition 2.1 of the thesis", ``Gusfield2007.ReticulateNetwork),
   ("Gusfield et al. 2007, The reticulations are at least R(M)", ``Gusfield2007.ReticulateNetwork.R_multiple_le_reticCount),
   ("Gusfield et al. 2007, Sites on which the parents of a recombination node differ", ``Gusfield2007.Network.exists_onCommonCycle_of_label_ne),
   ("Gusfield et al. 2007, The conjecture on the networks of this library", ``Gusfield2007.HusonKloepperConjecture),
   ("Gusfield et al. 2007, Two cycles sharing an edge", ``Gusfield2007.exists_isCycle_of_share_edge),
   ("Gusfield et al. 2007, Line 590", ``Gusfield2007.husonKloepperConjecture_false),
   ("Gusfield et al. 2007, A network for M with no recombination node as a leaf is a reticulate network on the rows", ``Gusfield2007.ReticulateNetwork.ofNetwork),
   ("Gusfield et al. 2007, A network for M explains the splits of M, each on the arc of its site", ``Gusfield2007.ReticulateNetwork.ofNetwork_explains),
   ("Gusfield et al. 2007, R¹_0(M_2) = 6", ``Gusfield2007.Md2_RS_eq),
   ("Gusfield et al. 2007, R¹(M_d) = 3d", ``Gusfield2007.Md_R_eq),
   ("Gusfield et al. 2007, The positive form of Section 4.2, with blobs that have no site", ``Gusfield2007.treeness_le_and_eq_iff_of_siteFree),
   ("Gusfield et al. 2007, With a merged blob, equality doesn't give T′ = T̄", ``Gusfield2007.treeness_merged_tie),
   ("Gusfield et al. 2007, The treeness inequality fails for a blob that merges two components", ``Gusfield2007.treeness_merged_false),
   ("Gusfield et al. 2007, The treeness inequality, for blobs with a site of a non-trivial component", ``Gusfield2007.treeness_le_of_merged),
   ("Gusfield et al. 2007, Theorem 10 with R(M + S) read literally is false for single crossovers", ``Gusfield2007.theorem10Printed_single_false),
   ("Gusfield et al. 2007, Theorem 10 without an ancestral sequence", ``Gusfield2007.minDecomposable_of_haplotypeBound_eq),
   ("Gusfield et al. 2007, The gap to the haplotype bound doesn't grow on restricting the sites", ``Gusfield2007.RS_restrict_gap_le),
   ("Gusfield et al. 2007, Theorem 10 with R(M + S) read literally, when the tight root differs from S in at most one component", ``Gusfield2007.sMinDecomposable_of_tight_root),
   ("Gusfield et al. 2007, Line 425 when the haplotype bound is tight", ``Gusfield2007.minDecomposableOfForallS_of_haplotypeBound_eq),
   ("Gusfield et al. 2007, Line 299, with the root at any node of T̄", ``Gusfield2007.exists_network_rooted_at),
   ("Gusfield et al. 2007, Line 299, with the root at a row", ``Gusfield2007.exists_network_rooted_at_row),
   ("Gusfield et al. 2007, A network deriving all the rows can't have its root at a row", ``Gusfield2007.root_not_mem_range),
   ("Gusfield et al. 2007, Theorem 10 with R(M + S) read literally, for multiple crossovers: false, given one computation", ``Gusfield2007.theorem10Printed_multiple_false_of_search),
   ("Gusfield, Eddhu, Langley 2004, the proof of Theorem 2.2 (exists_isCycle_of_incompatible)", ``External.GusfieldEtAl2004.exists_isCycle_of_incompatible),
   ("Gusfield, Eddhu, Langley 2004, the proof of Theorem 2.2 (exists_isCycle_of_conflict)", ``External.GusfieldEtAl2004.exists_isCycle_of_conflict),
   ("Gusfield, Eddhu, Langley 2004, Lemma 8.2", ``External.GusfieldEtAl2004.incompatGraph_image_maskCol),
   ("Gusfield, Eddhu, Langley 2004, Theorem 8.1", ``External.GusfieldEtAl2004.theorem8_1),
   ("Gusfield, Eddhu, Langley 2004, Corollary 2.1", ``External.GusfieldEtAl2004.corollary2_1_printed_false),
   ("Gusfield, Eddhu, Langley 2004, Theorem 8.2", ``External.GusfieldEtAl2004.theorem8_2),
   ("Gusfield, Eddhu, Langley 2004, Theorem 2.7 (theorem2_7_moreover)", ``External.GusfieldEtAl2004.theorem2_7_moreover),
   ("Gusfield, Eddhu, Langley 2004, Theorem 8.3", ``External.GusfieldEtAl2004.theorem8_3),
   ("Gusfield, Eddhu, Langley 2004, Theorem 2.6", ``External.GusfieldEtAl2004.theorem2_6),
   ("Gusfield, Eddhu, Langley 2004, Lemma 8.5", ``External.GusfieldEtAl2004.lemma8_5),
   ("Gusfield, Eddhu, Langley 2004, Lemma 8.1", ``External.GusfieldEtAl2004.lemma8_1),
   ("Gusfield, Eddhu, Langley 2004, Lemma 8.6", ``External.GusfieldEtAl2004.lemma8_6),
   ("Gusfield, Eddhu, Langley 2004, Corollary 5.1 (corollary5_1_min)", ``External.GusfieldEtAl2004.corollary5_1_min),
   ("Gusfield, Eddhu, Langley 2004, Theorem 2.7 (theorem2_7)", ``External.GusfieldEtAl2004.theorem2_7),
   ("Gusfield, Eddhu, Langley 2004, Corollary 5.1 (exists_isReducedGalledTree)", ``External.GusfieldEtAl2004.exists_isReducedGalledTree),
   ("Gusfield, Eddhu, Langley 2004, The decision", ``External.GusfieldEtAl2004.Algorithm.galledDecide_iff),
   ("Gusfield, Eddhu, Langley 2004, The count of the decision", ``External.GusfieldEtAl2004.Algorithm.galledDecide_ops_le),
   ("Gusfield, Eddhu, Langley 2004, The algorithm returns something exactly when there is a galled tree", ``External.GusfieldEtAl2004.Algorithm.galledBuild_isSome_iff),
   ("Gusfield, Eddhu, Langley 2004, The algorithm", ``External.GusfieldEtAl2004.Algorithm.galledBuild),
   ("Gusfield, Eddhu, Langley 2004, What the algorithm returns is a reduced galled tree", ``External.GusfieldEtAl2004.Algorithm.galledBuild_correct),
   ("Gusfield, Eddhu, Langley 2004, The source's steps, counted", ``External.GusfieldEtAl2004.galledTreeOperations_le),
   ("Gusfield, Eddhu, Langley 2004, Theorem 2.2", ``External.GusfieldEtAl2004.theorem2_2)]

/-- The labelled results of the other sources. -/
meta def paperResults5 : List (String × Name) :=
  [("Myers, Griffiths 2003, The placement from the top row is as far to the right as possible", ``External.MyersGriffiths2003.sum_rStarVec_le_of_feasible),
   ("Myers, Griffiths 2003, The solution from the right-hand column", ``External.MyersGriffiths2003.isOptimalValue_column),
   ("Myers, Griffiths 2003, Algorithm 1 (algorithm1_isOptimalValue)", ``External.MyersGriffiths2003.algorithm1_isOptimalValue),
   ("Myers, Griffiths 2003, The composite bound for two regions", ``External.MyersGriffiths2003.algorithm1_add_le),
   ("Myers, Griffiths 2003, The optimal bounds are tight in all optimal solutions", ``External.MyersGriffiths2003.sum_eq_of_chainSum_eq),
   ("Myers, Griffiths 2003, The particular solution of the top row", ``External.MyersGriffiths2003.algorithm1_top_row),
   ("Myers, Griffiths 2003, Corollary 8", ``External.MyersGriffiths2003.corollary8),
   ("Myers, Griffiths 2003, Algorithm 1 (algorithm1)", ``External.MyersGriffiths2003.algorithm1),
   ("Myers, Griffiths 2003, Proposition 6", ``External.MyersGriffiths2003.proposition6),
   ("Myers, Griffiths 2003, The example of the source (example_values)", ``External.MyersGriffiths2003.example_values),
   ("Myers, Griffiths 2003, Lemma 7", ``External.MyersGriffiths2003.lemma7),
   ("Myers, Griffiths 2003, The composite bound for a network", ``External.MyersGriffiths2003.algorithm1_le_recombCount),
   ("Myers, Griffiths 2003, R_m is a lower bound on R¹", ``External.MyersGriffiths2003.Rm_eq_rM),
   ("Myers, Griffiths 2003, R_h", ``External.MyersGriffiths2003.Rh),
   ("Myers, Griffiths 2003, The events of a network satisfy the system", ``External.MyersGriffiths2003.exists_feasible),
   ("Myers, Griffiths 2003, R_h is a lower bound on R¹", ``External.MyersGriffiths2003.Rh_le_R),
   ("Myers, Griffiths 2003, R_m, R_h with known ancestral types", ``External.MyersGriffiths2003.Rh_addRow_le_RS),
   ("Myers, Griffiths 2003, The composite bound with known ancestral types", ``External.MyersGriffiths2003.algorithm1_le_RS),
   ("Myers, Griffiths 2003, The composite bound", ``External.MyersGriffiths2003.algorithm1_le_R),
   ("Myers, Griffiths 2003, R¹ of the region is a local bound", ``External.MyersGriffiths2003.isLocalBounds_region),
   ("Myers, Griffiths 2003, The example of the source, from its sample", ``External.MyersGriffiths2003.exampleSample_values),
   ("Myers, Griffiths 2003, Two regions", ``External.MyersGriffiths2003.add_R_le_R),
   ("Myers, Griffiths 2003, The haplotype bounds are local bounds", ``External.MyersGriffiths2003.isLocalBounds_haplotypeBounds),
   ("Myers, Griffiths 2003, R_m ≤ R_h", ``External.MyersGriffiths2003.Rm_le_Rh),
   ("Myers, Griffiths 2003, R_m", ``External.MyersGriffiths2003.Rm),
   ("Myers, Griffiths 2003, The program with the constraints", ``External.MyersGriffiths2003.isLeast_of_merging),
   ("Myers, Griffiths 2003, No solution", ``External.MyersGriffiths2003.exists_ne_zero_of_merging),
   ("Myers, Griffiths 2003, ne_zero_of_pos", ``External.MyersGriffiths2003.ne_zero_of_pos),
   ("Myers, Griffiths 2003, Imposing r_k = 0", ``External.MyersGriffiths2003.isLeast_of_eq_zero),
   ("Myers, Griffiths 2003, Lemma 4, (7)", ``External.MyersGriffiths2003.typeCount_erase_le),
   ("Myers, Griffiths 2003, Corollary 5", ``External.MyersGriffiths2003.corollary5),
   ("Myers, Griffiths 2003, Lemma 4, (8)", ``External.MyersGriffiths2003.typeCount_le_erase_add_one),
   ("Myers, Griffiths 2003, Corollary 5, on the number of types", ``External.MyersGriffiths2003.typeCount_le_incompatibleSites),
   ("Myers, Griffiths 2003, More rows and sites give a larger bound", ``External.MyersGriffiths2003.historyBound_steps),
   ("Myers, Griffiths 2003, R_s, for known types", ``External.MyersGriffiths2003.RsKnown),
   ("Myers, Griffiths 2003, The local bounds of Algorithm 3 are local bounds", ``External.MyersGriffiths2003.isLocalBounds_historyBounds),
   ("Myers, Griffiths 2003, R_s, for unknown types", ``External.MyersGriffiths2003.Rs),
   ("Myers, Griffiths 2003, R_h ≤ R_s with known types", ``External.MyersGriffiths2003.Rh_addRow_le_RsKnown),
   ("Myers, Griffiths 2003, R_s is a lower bound on R¹", ``External.MyersGriffiths2003.Rs_le_R),
   ("Myers, Griffiths 2003, Algorithm 3 is a lower bound", ``External.MyersGriffiths2003.historyBound_le_breakCount),
   ("Myers, Griffiths 2003, The proof of Algorithm 3", ``External.MyersGriffiths2003.historyBound_le_card),
   ("Myers, Griffiths 2003, The bound is monotone", ``External.MyersGriffiths2003.historyBound_rowsAt_le),
   ("Myers, Griffiths 2003, R_s with known types is a lower bound on R¹_S", ``External.MyersGriffiths2003.RsKnown_le_RS),
   ("Myers, Griffiths 2003, H - S' - 1 is at most Algorithm 3", ``External.MyersGriffiths2003.typeCount_le_historyBound),
   ("Myers, Griffiths 2003, Algorithm 3", ``External.MyersGriffiths2003.historyBound),
   ("Myers, Griffiths 2003, The example of the source (exampleSample_Rs)", ``External.MyersGriffiths2003.exampleSample_Rs),
   ("Myers, Griffiths 2003, R_h ≤ R_s", ``External.MyersGriffiths2003.Rh_le_Rs),
   ("Myers, Griffiths 2003, Proposition 2, known types", ``External.MyersGriffiths2003.proposition2_rooted),
   ("Myers, Griffiths 2003, In fact, we can easily construct a history with exactly four recombinations in this case, so four is the true ...", ``External.MyersGriffiths2003.exampleSample_RS),
   ("Myers, Griffiths 2003, The network with the noninformative site put back", ``External.MyersGriffiths2003.exists_network_of_row),
   ("Myers, Griffiths 2003, Proposition 2, unknown types", ``External.MyersGriffiths2003.proposition2),
   ("Hudson, Kaplan 1985, The minimum of events in the region up to any site", ``External.HudsonKaplan1985.isOptimalValue_countUpTo),
   ("Hudson, Kaplan 1985, The final list of intervals of Appendix 2", ``External.HudsonKaplan1985.finalList),
   ("Hudson, Kaplan 1985, The final list is a largest disjoint family", ``External.HudsonKaplan1985.card_le_hudsonKaplan),
   ("Hudson, Kaplan 1985, It is clear from the definition of R_M that increasing S cannot decrease R_M", ``External.HudsonKaplan1985.hudsonKaplan_comp_le),
   ("Hudson, Kaplan 1985, R_M, as computed by Appendix 2", ``External.HudsonKaplan1985.hudsonKaplan),
   ("Hudson, Kaplan 1985, Figure 1", ``External.HudsonKaplan1985.figure1),
   ("Hudson, Kaplan 1985, R_M equals the final number of intervals on the list", ``External.HudsonKaplan1985.hudsonKaplan_isOptimalValue),
   ("Hudson, Kaplan 1985, The right end points", ``External.HudsonKaplan1985.rStarVec_ne_zero_iff),
   ("Hudson, Kaplan 1985, At this point all of the intervals are disjoint", ``External.HudsonKaplan1985.finalList_disjoint),
   ("Hudson, Kaplan 1985, The two methods lead to the same bound", ``External.HudsonKaplan1985.hudsonKaplan_eq_algorithm1),
   ("Hudson, Kaplan 1985, R_M of a sample of sequences", ``External.HudsonKaplan1985.rM),
   ("Hudson, Kaplan 1985, R_M is a lower bound on R¹", ``External.HudsonKaplan1985.rM_le_R),
   ("Song, Hein 2005, The tree of a site is compatible with its column", ``External.SongHein2005.keptReach_iff_label_ne),
   ("Song, Hein 2005, The minimum of L(P) is R¹(M), and it's attained", ``External.SongHein2005.exists_sprLength_eq_R),
   ("Song, Hein 2005, The time-ordered tree of a sampling", ``External.SongHein2005.sampledTree),
   ("Song, Hein 2005, The same, as an infimum", ``External.SongHein2005.R_eq_iInf_sprLength),
   ("Song, Hein 2005, The other inequality", ``External.SongHein2005.exists_sprLength_le),
   ("Song, Hein 2005, The choices of a network", ``External.SongHein2005.exists_choices),
   ("Song, Hein 2005, Choices that differ at few nodes", ``External.SongHein2005.exists_steps),
   ("Song, Hein 2005, Changing the kept arc at one node is one ordered-SPR operation, or no change", ``External.SongHein2005.same_or_isOrderedSPR),
   ("Song, Hein 2005, Every network can have at most two arcs out of each node", ``External.SongHein2005.exists_outDegree_le_two),
   ("Song, Hein 2005, The minimum of L(P) over the source's trees is R¹(M)", ``External.SongHein2005.exists_orderedLength_eq_R),
   ("Song, Hein 2005, Over the source's trees, every path is at least R¹", ``External.SongHein2005.R_le_orderedLength),
   ("Song, Hein 2005, The tree of a sampling is an ordered tree of the source", ``External.SongHein2005.isOrdered_sampledTree),
   ("Song, Hein 2005, An ordered tree of the source", ``External.SongHein2005.IsOrdered)]

/-- All the labelled results. The list is split because one literal of this length exceeds the limit on elaboration. -/
meta def paperResults : List (String × Name) :=
  paperResults1 ++ paperResults2 ++ paperResults3 ++ paperResults4 ++ paperResults5

/-- The theorems that Palomar's comparator checks (`theorem_names` of
`palomar/Gusfield2007/comparator.json`), as the Solution restates them. -/
meta def solutionResults : List Name :=
  [``Gusfield2007Challenge.gusfield_theorem1,
   ``Gusfield2007Challenge.gusfield_theorem3,
   ``Gusfield2007Challenge.gusfield_lemma4,
   ``Gusfield2007Challenge.gusfield_theorem4_entry,
   ``Gusfield2007Challenge.gusfield_theorem4_iff,
   ``Gusfield2007Challenge.gusfield_exists_realization,
   ``Gusfield2007Challenge.gusfield_theorem4_false_top,
   ``Gusfield2007Challenge.gusfield_theorem4_false_siteFree,
   ``Gusfield2007Challenge.gusfield_theorem5,
   ``Gusfield2007Challenge.gusfield_theorem6,
   ``Gusfield2007Challenge.gusfield_theorem7,
   ``Gusfield2007Challenge.gusfield_theorem8,
   ``Gusfield2007Challenge.gusfield_theorem9,
   ``Gusfield2007Challenge.gusfield_theorem10,
   ``Gusfield2007Challenge.gusfield_theorem11,
   ``Gusfield2007Challenge.gusfield_corollary2,
   ``Gusfield2007Challenge.gusfield_corollary3,
   ``Gusfield2007Challenge.gusfield_unrootedConjecture_single_false,
   ``Gusfield2007Challenge.gusfield_unrootedConjecture_multiple_false,
   ``Gusfield2007Challenge.gusfield_rootedConjecture_single_false,
   ``Gusfield2007Challenge.gusfield_rootedConjecture_multiple_false,
   ``Gusfield2007Challenge.gusfield_theorem10_unrooted,
   ``Gusfield2007Challenge.gusfield_theorem10Printed_single_false,
   ``Gusfield2007Challenge.gusfield_theorem10Printed_multiple_false_of_search,
   ``Gusfield2007Challenge.gusfield_exists_isEfficientAtEntry,
   ``Gusfield2007Challenge.gusfield_treeness_merged_false,
   ``Gusfield2007Challenge.gusfield_Md_R_eq,
   ``Gusfield2007Challenge.gusfield_conjecture22_false,
   ``Gusfield2007Challenge.galled_exists_isCycle_of_conflict,
   ``Gusfield2007Challenge.galled_theorem2_2,
   ``Gusfield2007Challenge.galled_theorem8_3,
   ``Gusfield2007Challenge.galled_line381,
   ``Gusfield2007Challenge.galled_galledBuild_correct,
   ``Gusfield2007Challenge.galled_galledBuildOps_le,
   ``Gusfield2007Challenge.myersGriffiths_algorithm1_isOptimalValue,
   ``Gusfield2007Challenge.myersGriffiths_Rh_le_R,
   ``Gusfield2007Challenge.hudsonKaplan_isOptimalValue,
   ``Gusfield2007Challenge.songHein_exists_orderedLength_eq_R]

/-- Lean's standard axioms. -/
meta def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `m` is a module of the libraries: under the root `Gusfield2007` (`External/`, the
paper's library and the Solution), but not the Challenge; or a module of the library
`Phylogenetics`, which the project imports. -/
meta def isLibraryModule (m : Name) : Bool :=
  ((`Gusfield2007).isPrefixOf m && m != `Gusfield2007.Challenge) || (`Phylogenetics).isPrefixOf m

/-- The constants declared in the library. -/
meta def libraryConstants (env : Environment) : NameSet := Id.run do
  let mut s : NameSet := {}
  for m in env.header.moduleNames, d in env.header.moduleData do
    if isLibraryModule m then
      for c in d.constNames do
        s := s.insert c
  return s

/-- The constants used by the type and the value of `c`. -/
meta def usedConstants (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | some (.thmInfo t) => t.type.getUsedConstants ++ t.value.getUsedConstants
  | some (.defnInfo d) => d.type.getUsedConstants ++ d.value.getUsedConstants
  | some (.opaqueInfo o) => o.type.getUsedConstants ++ o.value.getUsedConstants
  | some (.inductInfo i) => i.type.getUsedConstants ++ i.ctors.toArray
  | some ci => ci.type.getUsedConstants
  | none => #[]

/-- The external results reached from `root` through constants of the library, without looking
inside the proofs of the external results themselves. `deps` caches the constants of the library
that each constant uses, across calls. -/
meta def externalUses (env : Environment) (library : NameSet) (deps : NameMap (Array Name))
    (root : Name) :
    List Name × NameMap (Array Name) := Id.run do
  let externals := externalResults.map (·.2)
  let mut deps := deps
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  let mut found : NameSet := {}
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c then continue
      visited := visited.insert c
      if c != root && externals.contains c then
        found := found.insert c
        continue
      let ds := match deps.find? c with
        | some ds => ds
        | none => (usedConstants env c).filter library.contains
      deps := deps.insert c ds
      for d in ds do
        if !visited.contains d then stack := d :: stack
  return (externalResults.filterMap fun (_, n) => if found.contains n then some n else none, deps)

/-- Where `#audit` writes the routes, relative to the project root (`.lake/` is not committed). -/
meta def routeFile : System.FilePath := ".lake/route_deps.tsv"

/-- The numbered results that the proof of `root` uses: those reached from it through constants
of the library, without looking inside the proofs of numbered results themselves. -/
meta def resultUses (env : Environment) (library results : NameSet) (root : Name) :
    Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := (usedConstants env root).toList
  let mut found : Array Name := #[]
  while true do
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if visited.contains c || c == root then continue
      visited := visited.insert c
      if results.contains c then
        found := found.push c
        continue
      if !library.contains c then continue
      for d in usedConstants env c do
        if !visited.contains d then stack := d :: stack
  return found

/-- The code spans of the docstring of `c` that contain no space or comma: the candidates for its
TeX label. -/
meta def docLabels (env : Environment) (c : Name) : IO (Array String) := do
  let some doc ← findDocString? env c | return #[]
  let mut out : Array String := #[]
  let mut inside := false
  for part in doc.splitOn "`" do
    if inside && !part.isEmpty && !part.any (fun ch => ch.isWhitespace || ch == ',') then
      out := out.push part
    inside := !inside
  return out

elab "#audit" : command => do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let library := libraryConstants env
  let mut deps : NameMap (Array Name) := {}
  let mut rows : Array String := #["| Result | Lean | Results from prior work used | Axioms |",
    "| --- | --- | --- | --- |"]
  for (label, n) in paperResults do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
    let (uses, deps') := externalUses env library deps n
    deps := deps'
    let usesStr := if uses.isEmpty then "–" else ", ".intercalate (uses.map fun u => s!"`{u}`")
    let axStr := ", ".intercalate (axs.toList.map toString)
    rows := rows.push s!"| {label} | `{n}` | {usesStr} | {axStr} |"
  for n in solutionResults ++ externalResults.map (·.2) do
    let axs ← liftCoreM <| collectAxioms n
    if axs.any (!standardAxioms.contains ·) then bad := bad.push n
  -- Every declaration of the library, including private and auxiliary ones.
  for c in library do
    let axs ← liftCoreM <| collectAxioms c
    if axs.any (!standardAxioms.contains ·) then bad := bad.push c
  -- The routes: for each numbered result, its docstring's labels and the results it uses.
  let results : NameSet := paperResults.foldl (fun s p => s.insert p.2) {}
  let mut routes : Array String := #[]
  for (label, n) in paperResults do
    let labels ← docLabels env n
    let uses := resultUses env library results n
    routes := routes.push (s!"{label}\t{n}\t{",".intercalate labels.toList}\t" ++
      ",".intercalate (uses.map toString).toList)
  IO.FS.createDirAll ".lake"
  IO.FS.writeFile routeFile ("\n".intercalate routes.toList ++ "\n")
  logInfo ("\n".intercalate rows.toList ++
    s!"\n\nChecked {library.size} declarations of the library: " ++
    (if bad.isEmpty then "all use only the standard axioms." else "see the error."))
  unless bad.isEmpty do
    throwError m!"non-standard axioms used by: {bad}"

end Audit

#audit
