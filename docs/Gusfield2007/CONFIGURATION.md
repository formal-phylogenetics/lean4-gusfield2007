# Formalization configuration

The configuration of the collection where this formalization was made is in
[lean4-tob's `docs/CONFIGURATION.md`](https://github.com/vltanh/lean4-tob/blob/47250e1/docs/CONFIGURATION.md), at its last commit before the move; what concerns this paper is below.

## Sources of record

- Gusfield et al. 2007: Gusfield, Bansal, Bafna and Song, *A decomposition theory for phylogenetic networks and incompatible characters*, [J. Comput. Biol. 14, 1247-1272 (2007)](https://doi.org/10.1089/cmb.2006.0137), read in the PMC author manuscript (PMC2581772), and, for the symbols that its plain text loses, in an [author's copy](https://people.eecs.berkeley.edu/~yss/Pub/decomposition.pdf) on Yun Song's page, made from a DVI file on 2008-01-19, with the same words apart from moved floats, footnotes and hyphenation. That copy isn't the journal's typeset text.

Downloads, working inventories and notes are private, and aren't in this repository. [`sources.json`](sources.json) has the
hashes of the texts that the line numbers refer to, and of the later sources that were read. No author TeX source exists, so
the rows of [`paper_routes.tsv`](paper_routes.tsv) are written by hand from these sources.

### Line numbers in the docstrings

The docstrings locate a passage by the lines of a text of the paper. The texts aren't distributed, so a line number is a
locator only.

| Paper | "Line N" |
| --- | --- |
| Gusfield et al. 2007 | a line of the plain text of the PMC page (PMC2581772), one line per paragraph: "line 342". The misprints in symbols were read in the author's copy above |

## Repository and toolchain

- Lean and Mathlib `v4.37.0-rc1`, Mathlib commit `31ce06eaadf4a200c0e1407c5f10953cf606b8f8`.
- The library [lean4-phylogenetics](https://github.com/vltanh/lean4-phylogenetics), the root of the collection, is required
  at the train's commit, for the Splits Equivalence Theorem and what it needs about X-trees
  ([`lakefile.toml`](../../lakefile.toml)).
- The layout and the names are the collection's: the root and the paper `Gusfield2007`, the library in the namespace
  `Gusfield2007`, the cited results in `External.<Source>`, and the Challenge's theorems in `Gusfield2007Challenge`.
- Palomar is not a target. [`palomar/Gusfield2007/`](../../palomar/Gusfield2007) keeps the files for a possible submission:
  the Challenge, which imports the library's definitions, the Solution, `comparator.json`, which names them, and
  `formalization.yaml`. `scripts/check_kernels.sh` runs Comparator and con-ron, Palomar's three kernels.

## Publishing

The repository is public. Pushes need the user's go-ahead. No Palomar preflight, submission or registration is authorized.
