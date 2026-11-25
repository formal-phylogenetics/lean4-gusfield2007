# The results the paper cites

One directory per source, `Gusfield2007/External/<Source>/`, with modules
`Gusfield2007.External.<Source>.…`, declarations in the namespace `External.<Source>`, and a
`README.md` giving the source, the statement, how the paper uses it, whether the source was read,
and the argument that proves it. Each result is stated in its source's terms and proved; none is
assumed.

| Source | Directory | What is proved |
| --- | --- | --- |
| Gusfield 1991 | [`Gusfield1991/`](Gusfield1991) | the Perfect Phylogeny Theorem, as an undirected tree, as a network with no recombination node, and with a given ancestral sequence; uniqueness among reduced trees |
| Semple, Steel 2003 | [`SempleSteel2003/`](SempleSteel2003) | the Splits Equivalence Theorem, proved in lean4-phylogenetics (`Phylogenetics.Tree.SplitsEquivalence`) and restated here with the label of its route |
| Gusfield, Eddhu, Langley 2004 | [`GusfieldEtAl2004/`](GusfieldEtAl2004) | conflicting sites on one blob and on one cycle; reduced galled trees are fully decomposed, exist and are optimal; a computable algorithm for a reduced galled tree, with its correctness and a count of its operations |
| Myers, Griffiths 2003 | [`MyersGriffiths2003/`](MyersGriffiths2003) | the haplotype bound and its equality case with distinct columns, the integer program, Algorithms 1 and 3, the bounds `R_h` and `R_s`, Proposition 2, Lemma 4 and Corollary 5 |
| Hudson, Kaplan 1985 | [`HudsonKaplan1985/`](HudsonKaplan1985) | the lower bound by non-overlapping intervals of incompatible sites, and the algorithm of Appendix 2 |
| Song, Hein 2005 | [`SongHein2005/`](SongHein2005) | the bound `R¹(M) ≤ L(P)` by ordered SPR, and that the minimum over sequences of trees is `R¹(M)` |

## What the sources share with the paper's library

The sources on networks state their results on the networks of the paper. The definitions shared with the paper's library
are in `Gusfield2007/Defs.lean` and `Gusfield2007/Networks/`, and import nothing of the paper's results: only Mathlib and
`Gusfield2007/Basic/`. The modules here import only these, `Basic/`, lean4-phylogenetics and one another.

| Module | What it holds | Imported here by |
| --- | --- | --- |
| `Gusfield2007.Defs` | rows, `NoConstantColumn`, `addRow`, `restrictRows`, `Incompatible`, `Conflict`, `incompatGraph`, `conflictGraph`, `haplotypeBound`; `Crossover`; `Network` with its arcs, paths, cycles, blobs, `Obeys`, `Derives`, `IsFullyDecomposedFor`; `R`, `RS`, `F`, `FS`; `MutationTree`, `parsimonyScore`; the conjectures; super-characters and `T̄` | `SongHein2005/Bound`, and the others through the modules below |
| `Gusfield2007.Networks.Basic` | facts about these definitions: `G_S(M) = G(M + S)`, reachability and paths, embeddings and isomorphisms of networks, `Recombinant`, renaming the sites, the non-trivial components `Decomp.Cent` | through the modules below |
| `Gusfield2007.Networks.Blobs` | recombination cycles and blobs: `pathVerts`, the two paths lemma, line 139, `T′` is a tree, the separation of blobs that share a node (line 135) | `GusfieldEtAl2004/SameBlob` |
| `Gusfield2007.Networks.Operations` | where a label comes from, the four-gamete test, trimming a network to its rows (`Kept`, `trim`), moving a recombination node (`reattach`), networks from parent maps (`PreNet`) | `GusfieldEtAl2004/SameBlob`, `GusfieldEtAl2004/Elimination`, `HudsonKaplan1985/Bound`, `MyersGriffiths2003/Bound`, `SongHein2005/Bound` |
| `Gusfield2007.Networks.Explicit` | rows from bits (`ofBits`), networks from lists of numbers (`NetSpec`) checked by the kernel | `GusfieldEtAl2004/GalledTree`, `MyersGriffiths2003/Composite`, `MyersGriffiths2003/Proposition2` |
| `Gusfield2007.Networks.Existence` | a network for every nonempty set of rows, with any ancestral sequence (`Decomp.exists_inflate_net`) | `Gusfield1991/Existence` |
| `Gusfield2007.Networks.TimeOrdered` | time-ordered trees, ordered SPR, `sprLength` | `SongHein2005/Bound` |

Two groups of declarations are not where their source would put them:

- `Gusfield2007.recombSet_nonempty` and `Gusfield2007.rootedRecombSet_nonempty`, which say that the minima `R` and `R_S` are
  over nonempty sets, are in `Gusfield1991/Existence`, since their proof uses the network of the Perfect Phylogeny Theorem
  when there is no site. The lower bounds of the sources need them.
- The results of Gusfield, Eddhu, Langley 2004 whose proofs use this paper's results are in the paper's library, under the
  same names, in `ProofOfDecomposition/GalledTrees/`: reduced galled trees exist (Corollary 5.1 of the source, by gluing a
  gall for each component into `T̄`), Theorem 2.7 and the counts by the components, the decision procedure, and the
  correctness of the algorithm, which uses the paper's dominant classes (line 212).
