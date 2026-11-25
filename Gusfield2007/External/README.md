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

The sources on networks state their results on the networks of the paper's library, so their
modules import the modules of `Gusfield2007/` that define those networks and the facts they use
(`Gusfield2007.Defs`, `Gusfield2007.Networks.Operations`, `Gusfield2007.ProofOfDecomposition.Decomposition`, …), and the
paper's library imports them in turn, with no cycle between modules. The modules with no networks
in them, the Splits Equivalence Theorem, the program of Myers and Griffiths (`Algorithm1`) and the
algorithm of Hudson and Kaplan (`Algorithm`), import only Mathlib, lean4-phylogenetics and one
another.
