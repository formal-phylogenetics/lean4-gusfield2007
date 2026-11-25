# Credits

How this formalization was made. It was made in [lean4-tob](https://github.com/vltanh/lean4-tob), a collection of
formalizations on the tree of blobs of phylogenetic networks, and moved to this repository on 2026-11-04.
[That repository's credits](https://github.com/vltanh/lean4-tob/blob/47250e1/docs/CREDITS.md), at its last commit before the move, record every round in full, with the figures
of each.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, chose the paper, decided the layout, the kernels
  and publication, and moved it to this repository.
- **Formalization:** Claude Code 2.1.314 (VS Code extension) with Claude Opus 5.5 (`claude-opus-5-5`), for the statements,
  proofs, audit and documents, with sub-agents.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill, checkout commit `e339f64`.
- **Review:** no person has reviewed the proofs. Independent agents, which didn't write what they checked, reviewed the
  statements against the sources, compared the proofs with the paper, and checked the audit's findings and its literature
  section. The three kernels and the route check ran locally.

## Rounds

- **2026-10-31 to 2026-11-01, with Allman et al. 2023.** The user asked to formalize this paper and Allman, Baños, Mitchell,
  Rhodes 2023 as primary papers. Agents wrote the statements with `sorry`, and found the first errors: Theorem 4, §4.2 and
  line 560. Independent agents reviewed them against the paper, with search programs of their own. Proof agents worked in
  parallel, one set of files each: the foundations and cited results, the decomposition, uniqueness and the conjectures, the
  sufficient conditions, and the counterexamples and their counts. Independent agents compared the proofs with the paper,
  and their findings sent the proof agents back: Theorem 4's account was corrected, a realizability theorem added, and
  departures that weren't forced replaced by the paper's argument. The round took 8.34 h elapsed, with 20 sub-agents, for
  both papers.
- **2026-11-01, finishing what the papers claim.** Agents proved what the report had listed as not formalized, among them the
  integer program, Algorithms 1 and 3 of Myers and Griffiths 2003, and the count of Gusfield, Eddhu, Langley 2004's
  algorithm, and stated the remaining counterexamples as theorems. Theorem 10 is graded by what the paper's own use of its
  symbol suggests. The round took 4.61 h elapsed, with 10 sub-agents, for all the papers of the collection.
- **2026-11-04, the move.** The paper got its own front page, report and Palomar entry, and then this repository. The Splits
  Equivalence Theorem of Semple, Steel 2003, which this paper and Allman et al. 2023 both use, moved to the library
  [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), and [`Gusfield2007/External/SempleSteel2003/`](../../Gusfield2007/External/SempleSteel2003) restates it.
- **2026-11-24, the collection's layout.** Claude Opus 5.5 in Claude Code, one agent, gave the repository the layout and the
  names of the collection rooted at lean4-phylogenetics: the code under the root [`Gusfield2007/`](../../Gusfield2007), the cited results in
  [`Gusfield2007/External/`](../../Gusfield2007/External) in the namespaces `External.<Source>`, the main theorems as the Challenge and the Solution in
  [`palomar/Gusfield2007/`](../../palomar/Gusfield2007), and the documents in `docs/Gusfield2007/`. No statement or proof changed. It took 0.5 h
  elapsed.
