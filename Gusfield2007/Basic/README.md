# General mathematics

Lemmas that say nothing about phylogenetics, filed by field as Mathlib files them and named as
Mathlib would name them, in Mathlib's namespaces, so that they can be contributed to Mathlib. They
import only Mathlib.

| File | Contents | Where it could go |
| --- | --- | --- |
| `Logic/Relation.lean` | a function increasing along a relation increases along its transitive closure, which is then acyclic; a finite acyclic relation has such a function into `ℕ`; adding a pair that closes no cycle keeps a relation acyclic | `Mathlib/Logic/Relation.lean` |
| `Data/List.lean` | the image of the elements of two lists; membership in a prefix by `List.idxOf`; a sum bounded termwise; filters by comparable predicates; a sum of counts over `Finset.range` | `Mathlib/Data/List/Basic.lean`, `Mathlib/Algebra/Order/BigOperators/Group/List.lean` |
| `Data/Nat/Bitwise.lean` | `Nat.beq`, the top bit `Nat.log2`, `Nat.land` and `Nat.xor` bit by bit, `xor` with a power of two below `2 ^ m`; a chain of powers | `Mathlib/Data/Nat/Bitwise.lean` |
| `Data/Finset.lean` | `Finset.image` with two decidability instances; `Equiv.finsetCongr` and unions, differences, inclusion and cardinality; a shift of an interval of summation | `Mathlib/Data/Finset/Image.lean`, `Mathlib/Logic/Equiv/Finset.lean`, `Mathlib/Algebra/BigOperators/Intervals.lean` |
| `Data/Bool.lean` | when two maps to `Bool` have the same fibres; when the sets where two such maps leave a base value are disjoint or nested | `Mathlib/Data/Bool/Basic.lean` |
| `Order/Fin.lean` | a lower set of `Fin m` is an initial segment, in three forms; functions composed with an order isomorphism and its inverse | `Mathlib/Order/Interval/Finset/Fin.lean`, `Mathlib/Order/Hom/Basic.lean` |
| `Combinatorics/SimpleGraph/Connectivity.lean` | reachability from adjacency; one or two connected components; sums over the components; the components of two graphs with the same reachability; the edges of a non-trivial component | `Mathlib/Combinatorics/SimpleGraph/Connectivity/Connected.lean` |
| `Combinatorics/SimpleGraph/Acyclic.lean` | a node farthest from `v` in a finite acyclic graph has at most one neighbour; isomorphic graphs have as many edges | `Mathlib/Combinatorics/SimpleGraph/Acyclic.lean`, `Mathlib/Combinatorics/SimpleGraph/Maps.lean` |
| `Combinatorics/SimpleGraph/Walk.lean` | two paths sharing only their ends, and no edge, make a cycle; a walk splits at its first node in a set and at an edge on it; a cycle through an edge is that edge and a path | `Mathlib/Combinatorics/SimpleGraph/Paths.lean` |

Some general facts stay where they are used, because they state a claim of a paper or of a
source, or rest on notions defined there: the edges of a tree that meet pairwise share a node
(line 295, in the proof of Lemma 4) and the cut functions of a tree that it uses, two cycles
sharing an edge (`g:cycle_transitive`, line 590), Hudson and Kaplan's count of disjoint intervals,
and the count of the reads of Gusfield, Eddhu and Langley's algorithm.

Before adding a lemma, search Mathlib and lean4-phylogenetics (`Phylogenetics/ForMathlib/`): a
lemma that a second repository of the collection needs moves up the tree, to the lowest node above
both (lean4-phylogenetics, docs/CONVENTIONS.md, Section 4).
