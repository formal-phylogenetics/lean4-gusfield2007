module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.UpperLower.CompleteLattice

/-!
# Gusfield et al. 2007: the main results

D. Gusfield, V. Bansal, V. Bafna, Y. S. Song, *A decomposition theory for phylogenetic networks and incompatible characters*,
J. Comput. Biol. 14 (2007), 1247--1272: the Decomposition Theorem, its form with an ancestral sequence, the sufficient
conditions for a fully decomposed network to be optimal, the refutation of the Full-Decomposition Optimality Conjectures, and
the unbounded gap between `F¹` and `R¹`. These are the statements of record, with `sorry` proofs; `Gusfield2007.Solution`
proves each of them under the same name. The definitions are those of the library, copied from `Gusfield2007/Defs.lean` by
`scripts/sync_challenge_defs.py`, and this module imports only Mathlib.

## Conventions

* Sites are a finite linearly ordered type `ι` (`Fin m` in the examples). A row is a function `ι → Bool`, and the input `M` is
  a `Finset` of rows, so it has no repeated row. `NoConstantColumn M` is the paper's standing assumption (line 112).
* `incompatGraph M` is the incompatibility graph `G(M)`: two sites are adjacent when all four pairs of states occur on them.
  `conflictGraph S M` is the conflict graph `G_S(M)`: two sites are adjacent when the three pairs of states other than
  `(S i, S j)` occur on them.
* A `Network ι V E` has nodes `V` and arcs `E`, a root, each site on one arc (`site`), and a label `ι → Bool` on each node: a
  tree node's label is its parent's with the sites of its arc flipped, and a recombination node (two incoming arcs) takes each state
  from one of its parents. `Network.Obeys c` restricts the recombinations to the model `c`: a single crossover, multiple
  crossovers, or `pointwise`, a recombination that models one back or recurrent mutation. `Network.Derives M` says that the
  leaves are labelled one-to-one by the rows of `M`; `Network.ancestral` is the label of the root.
* A blob is a class of recombination cycles under sharing an arc (`Network.IsBlob`). `IsFullyDecomposedFor G` says that each
  blob holds all and only the sites of one non-trivial component of `G`, that each isolated site of `G` is on an arc of no
  cycle, and that blobs share no node.
* `R c M`, `RS c S M` and `F c M` are the least numbers of recombination nodes of a network for `M` in the model `c`: any, with
  the ancestral sequence `S`, and fully decomposed for `G(M)`. `MinDecomposable` and `SMinDecomposable` say that a fully
  decomposed network attains `R` and `R_S`. `haplotypeBound M` is the number of rows minus the number of distinct columns,
  minus one. `parsimonyScore S M` is the least number of mutations of a tree rooted at `S` with its leaves labelled
  by `M`.

## The theorems

* `theorem1`: every nonempty `M` has a fully decomposed network, in each model. `theorem3`: one with ancestral sequence `S`,
  fully decomposed for `G_S(M)`, with `Σ_C R_{S(C)}(M(C))` recombination nodes.
* `theorem5` to `theorem10`, `corollary2`, `corollary3`: conditions under which `M` is S-min (or S-min-1) decomposable: the
  labels of an optimal network have as many components as `M` (Theorem 5), every node is visible (Theorem 6, Corollary 2), the
  recombinations are 0- or 1-component (Theorem 7), the components are spatially disjoint (Theorem 8), the labels respect the
  components (Theorem 9), the haplotype bound is tight (Theorem 10, with `R_S(M)`: see its docstring), and recombinations
  that model mutations (Corollary 3, with the parsimony score).
* `unrootedConjecture_single_false` and the three others: the four Full-Decomposition Optimality Conjectures are false.
  `theorem11`: `F¹(M) − R¹(M)` is unbounded.

Theorem 4 (false as printed, proved in corrected forms), Lemma 4, the statements that the paper makes in passing and the
results of the cited sources are proved in the library and are not restated here.
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007

-- BEGIN SHARED DEFINITIONS

universe u v w

section Matrix

variable {ι : Type*}

/-- The standing assumption of the paper (line 112): "there is no site `i` where all the sequences have the same
state at site `i`". `M + S` and `M(C)` keep it (`NoConstantColumn.addRow`, `NoConstantColumn.restrictRows`). Results that need it have it as
a hypothesis. It's needed in the rooted results: with `M = {S}`, a site must mutate on an arc and come back. -/
def NoConstantColumn (M : Finset (ι → Bool)) : Prop :=
  ∀ i, ∃ r ∈ M, ∃ r' ∈ M, r i ≠ r' i

/-- `M + S`: the set resulting from adding the sequence `S` to `M` (line 152). -/
def addRow (M : Finset (ι → Bool)) (S : ι → Bool) : Finset (ι → Bool) := insert S M

/-- `M(C)`: the sequences of `M` restricted to the sites in `C`; its elements are the distinct restrictions (line 223). -/
def restrictRows (C : Set ι) (M : Finset (ι → Bool)) : Finset (C → Bool) := M.image C.domRestrict

/-- Columns `i` and `j` of `M` are incompatible: all four ordered pairs occur, the four-gamete test (line 150). -/
def Incompatible (M : Finset (ι → Bool)) (i j : ι) : Prop :=
  ∀ a b : Bool, ∃ r ∈ M, r i = a ∧ r j = b

/-- Columns `i` and `j` conflict relative to `S`: they contain all three of the pairs that differ from the pair of
`S` at `i, j` (line 152). -/
def Conflict (S : ι → Bool) (M : Finset (ι → Bool)) (i j : ι) : Prop :=
  ∀ a b : Bool, (a ≠ S i ∨ b ≠ S j) → ∃ r ∈ M, r i = a ∧ r j = b

/-- The incompatibility graph `G(M)` (line 160). -/
def incompatGraph (M : Finset (ι → Bool)) : SimpleGraph ι where
  Adj := Incompatible M
  symm := ⟨fun i j h a b => by
    obtain ⟨r, hr, h₁, h₂⟩ := h b a
    exact ⟨r, hr, h₂, h₁⟩⟩
  loopless := ⟨fun i h => by
    obtain ⟨r, -, h₁, h₂⟩ := h true false
    exact absurd (h₁.symm.trans h₂) (by decide)⟩

/-- The conflict graph `G_S(M)` (line 160). -/
def conflictGraph (S : ι → Bool) (M : Finset (ι → Bool)) : SimpleGraph ι where
  Adj := Conflict S M
  symm := ⟨fun i j h a b hab => by
    obtain ⟨r, hr, h₁, h₂⟩ := h b a hab.symm
    exact ⟨r, hr, h₂, h₁⟩⟩
  loopless := ⟨fun i h => by
    obtain ⟨r, -, h₁, h₂⟩ := h (!S i) (S i) (Or.inl (Bool.not_ne_self (S i)))
    exact Bool.not_ne_self (S i) (h₁.symm.trans h₂)⟩

/-- The number of distinct columns of `M`. -/
def distinctColumns (M : Finset (ι → Bool)) : ℕ :=
  Set.ncard (Set.range fun i : ι => fun r : M => (r : ι → Bool) i)

/-- The haplotype bound `H(M)` of Myers and Griffiths, as printed (line 559): "the number of rows of `M`, minus the
number of distinct columns of `M`, minus one". It can be negative. -/
def haplotypeBound (M : Finset (ι → Bool)) : ℤ :=
  (M.card : ℤ) - distinctColumns M - 1

end Matrix

/-- The constraint on recombination nodes. `single`: a single crossover (line 116). `multiple`: unbounded multiple
crossovers, no constraint (line 116). `pointwise`: a recombination modelling one back or recurrent mutation: two
crossovers, just before and just after one site (lines 358, 511). -/
inductive Crossover where
  | single
  | multiple
  | pointwise

/-- A phylogenetic network on the sites `ι` (lines 94 to 106), on the vertices `V` and arcs `E`. Each site is on exactly
one arc (`site` is a function); there can be arcs with no site. The label of the root is the ancestral sequence. -/
structure Network (ι : Type u) (V : Type v) (E : Type w) where
  /-- The source of an arc. -/
  src : E → V
  /-- The target of an arc. -/
  tgt : E → V
  /-- The root. -/
  root : V
  /-- The arc to which a site is assigned. -/
  site : ι → E
  /-- The sequence labelling a node. -/
  label : V → ι → Bool
  /-- A digraph: no parallel arcs. -/
  simple : ∀ e f, src e = src f → tgt e = tgt f → e = f
  /-- It is acyclic. -/
  acyclic : ∀ v, ¬ Relation.TransGen (fun a b => ∃ e, src e = a ∧ tgt e = b) v v
  /-- Exactly one node, the root, has no incoming edge. -/
  root_iff : ∀ v, (∀ e, tgt e ≠ v) ↔ v = root
  /-- Each node has at most two incoming edges. -/
  inDegree_le_two : ∀ e f g, tgt e = tgt f → tgt f = tgt g → e = f ∨ e = g ∨ f = g
  /-- No site is on an edge entering a recombination node. -/
  site_not_recomb : ∀ i f, tgt f = tgt (site i) → f = site i
  /-- At a non-recombination node, the label is the parent's with the sites of the incoming edge changed. -/
  label_tree : ∀ e, (∀ f, tgt f = tgt e → f = e) →
    ∀ i, label (tgt e) i = if site i = e then !label (src e) i else label (src e) i
  /-- At a recombination node, every state equals that of one of the two parents. -/
  label_recomb : ∀ e f, e ≠ f → tgt e = tgt f →
    ∀ i, label (tgt e) i = label (src e) i ∨ label (tgt e) i = label (src f) i

namespace Network

variable {ι : Type u} {V : Type v} {E : Type w} (N : Network ι V E)

/-- The ancestral sequence: the label of the root. -/
def ancestral : ι → Bool := N.label N.root

/-- A recombination node: a node with two incoming edges (line 94). -/
def IsRecomb (x : V) : Prop := ∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x

/-- A leaf: a node with no outgoing edge (line 94). -/
def IsLeaf (v : V) : Prop := ∀ e, N.src e ≠ v

/-- `R(N)`, the number of recombination nodes. -/
def recombCount : ℕ := Nat.card {x // N.IsRecomb x}

/-- `N` derives `M`: the leaves are in bijection with the rows of `M`, through the labels (lines 94, 111). -/
def Derives (M : Finset (ι → Bool)) : Prop := Set.BijOn N.label {v | N.IsLeaf v} (M : Set (ι → Bool))

/-- The recombination nodes of `N` obey the crossover model (line 116). -/
def Obeys [LinearOrder ι] (N : Network ι V E) : Crossover → Prop
  | .single => ∀ x, N.IsRecomb x → ∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x ∧
      ∃ L : LowerSet ι, ∀ i, N.label x i = if i ∈ L then N.label (N.src e) i else N.label (N.src f) i
  | .multiple => True
  | .pointwise => ∀ x, N.IsRecomb x → ∃ e f, e ≠ f ∧ N.tgt e = x ∧ N.tgt f = x ∧
      ∃ j, ∀ i, N.label x i = if i = j then N.label (N.src f) i else N.label (N.src e) i

/-- A list of arcs is a directed path from `u` to `v`. -/
def IsPath : V → V → List E → Prop
  | u, v, [] => u = v
  | u, v, e :: p => N.src e = u ∧ IsPath (N.tgt e) v p

/-- `w` has two paths `p`, `q` out of it that meet at the recombination node `x` (line 133): they share no vertex other
than `w` and `x`. `w` is the coalescent node, and `x` the recombination node, of the cycle. -/
def IsCycleOn (w x : V) (p q : List E) : Prop :=
  N.IsRecomb x ∧ N.IsPath w x p ∧ N.IsPath w x q ∧ p ≠ q ∧
    ∀ e ∈ p, ∀ f ∈ q, N.tgt e = N.tgt f → N.tgt e = x

/-- A recombination cycle, as its set of arcs (line 133). -/
def IsCycle (Q : Set E) : Prop :=
  ∃ w x p q, N.IsCycleOn w x p q ∧ Q = {e | e ∈ p ∨ e ∈ q}

/-- The arc `e` is on a recombination cycle. -/
def OnCycle (e : E) : Prop := ∃ Q, N.IsCycle Q ∧ e ∈ Q

/-- A tree edge: an arc on no recombination cycle. These are the edges of `T′` (line 143). -/
def IsTreeArc (e : E) : Prop := ¬ N.OnCycle e

/-- Two recombination cycles share an edge (line 135). -/
def ShareArc (Q Q' : Set E) : Prop := N.IsCycle Q ∧ N.IsCycle Q' ∧ (Q ∩ Q').Nonempty

/-- A blob, as the set of arcs on its cycles: the union of a class of recombination cycles, obtained from a cycle by
repeatedly adding a cycle sharing an edge with one already there (line 135). A blob contains a site if the site's arc
lies on it. -/
def IsBlob (B : Set E) : Prop :=
  ∃ Q, N.IsCycle Q ∧ B = ⋃₀ {Q' | Relation.ReflTransGen N.ShareArc Q Q'}

/-- The nodes of a blob. -/
def blobVerts (B : Set E) : Set V := N.src '' B ∪ N.tgt '' B

/-- No blob shares a node with any other blob (lines 140, 364). -/
def BlobsNodeDisjoint : Prop :=
  ∀ B B', N.IsBlob B → N.IsBlob B' → B ≠ B' → Disjoint (N.blobVerts B) (N.blobVerts B')

/-- `N` is fully decomposed with respect to the graph `G` on sites: every blob contains all and only the sites of a single
non-trivial connected component of `G`, every site that's isolated in `G` is on a tree edge, and blobs share no node
(Theorem 1, line 173; line 178). `G` is `G(M)`, or `G_S(M)` when the ancestral sequence is `S` (line 187). The second
wording of the paper, a one-one correspondence, is `isFullyDecomposedFor_iff_correspondence`. -/
structure IsFullyDecomposedFor (G : SimpleGraph ι) : Prop where
  blob_component : ∀ B, N.IsBlob B →
    ∃ c : G.ConnectedComponent, c.supp.Nontrivial ∧ ∀ i, N.site i ∈ B ↔ i ∈ c.supp
  isolated_treeArc : ∀ i, (∀ j, ¬ G.Adj i j) → N.IsTreeArc (N.site i)
  nodeDisjoint : N.BlobsNodeDisjoint

/-- The component `C` is broken at the recombination node `x`: `h(C) ≠ h₁(C)` and `h(C) ≠ h₂(C)` (line 457), where `h`
is the label of `x` and `h₁`, `h₂` those of its parents. -/
def BreaksAt (x : V) (C : Set ι) : Prop :=
  ∀ e, N.tgt e = x → C.domRestrict (N.label x) ≠ C.domRestrict (N.label (N.src e))

/-- A 0-component recombination, for the components of `G` (line 457). -/
def IsZeroComponent (G : SimpleGraph ι) (x : V) : Prop :=
  ∀ c : G.ConnectedComponent, ¬ N.BreaksAt x c.supp

/-- A 1-component recombination, for the components of `G` (line 457). -/
def IsOneComponent (G : SimpleGraph ι) (x : V) : Prop :=
  ∃! c : G.ConnectedComponent, N.BreaksAt x c.supp

/-- `L`, the set of node labels of `N` (line 426). -/
def labelSet [Fintype V] : Finset (ι → Bool) := Finset.univ.image N.label

/-- Every node is visible, in the rooted case: `L = M + S` (line 427), for `N` with ancestral sequence `S`. -/
def AllVisible (M : Finset (ι → Bool)) (S : ι → Bool) : Prop := ∀ v, N.label v ∈ addRow M S

end Network

section Counts

variable {ι : Type u} [LinearOrder ι]

/-- `R(M)`, `R¹(M)`: the minimum number of recombination nodes in a network deriving `M` in the model `c` (line 385).
By `Network.exists_fin_iso`, it doesn't matter that the vertices and arcs here are `Fin a` and `Fin b`, and by
`recombSet_nonempty` the minimum is over a nonempty set when `M` is nonempty. -/
def R (c : Crossover) (M : Finset (ι → Bool)) : ℕ :=
  sInf {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.recombCount = k}

/-- `R_S(M)`, `R¹_S(M)`: the same, with ancestral sequence `S` (line 385). -/
def RS (c : Crossover) (S : ι → Bool) (M : Finset (ι → Bool)) : ℕ :=
  sInf {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)),
    N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧ N.recombCount = k}

/-- `F(M)`, `F¹(M)`: the minimum over fully decomposed networks for `M` (line 418). -/
def F (c : Crossover) (M : Finset (ι → Bool)) : ℕ :=
  sInf {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)),
    N.Obeys c ∧ N.Derives M ∧ N.IsFullyDecomposedFor (incompatGraph M) ∧ N.recombCount = k}

/-- `N` is optimal for `M` with ancestral sequence `S`, in the model `c` (line 386). -/
def Network.IsOptimalRooted {V E : Type*} (N : Network ι V E) (c : Crossover) (S : ι → Bool)
    (M : Finset (ι → Bool)) : Prop :=
  N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧ N.recombCount = RS c S M

/-- `M` is min decomposable (`c = multiple`), or min-1 decomposable (`c = single`) (line 388). -/
def MinDecomposable (c : Crossover) (M : Finset (ι → Bool)) : Prop :=
  ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
    N.IsFullyDecomposedFor (incompatGraph M) ∧ N.recombCount = R c M

/-- `M` is S-min decomposable (`c = multiple`), or S-min-1 decomposable (`c = single`) (line 390). -/
def SMinDecomposable (c : Crossover) (S : ι → Bool) (M : Finset (ι → Bool)) : Prop :=
  ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
    N.IsFullyDecomposedFor (conflictGraph S M) ∧ N.recombCount = RS c S M

/-- `M` is spatially disjoint, given `S`: for every connected component of `G_S(M)`, its sites are an interval (line 515). -/
def SpatiallyDisjoint (S : ι → Bool) (M : Finset (ι → Bool)) : Prop :=
  ∀ c : (conflictGraph S M).ConnectedComponent, c.supp.OrdConnected

end Counts

/-- `L` respects the components of `G_S(M)`: adding `L − M` to `M + S` creates no incompatibility between sites in
different components of `G_S(M)` (line 533). -/
def Respects {ι : Type*} (L : Finset (ι → Bool)) (S : ι → Bool) (M : Finset (ι → Bool)) : Prop :=
  ∀ i j, Incompatible L i j → (conflictGraph S M).Reachable i j

/-- A tree deriving rows with back and recurrent mutations allowed (lines 358, 510): a rooted tree whose arcs change any
sites. Its cost is the number of changes. Maximum parsimony minimizes it. -/
structure MutationTree (ι : Type u) (V : Type v) (E : Type w) where
  /-- The source of an arc. -/
  src : E → V
  /-- The target of an arc. -/
  tgt : E → V
  /-- The root. -/
  root : V
  /-- The sequence labelling a node. -/
  label : V → ι → Bool
  /-- It is acyclic. -/
  acyclic : ∀ v, ¬ Relation.TransGen (fun a b => ∃ e, src e = a ∧ tgt e = b) v v
  /-- Exactly one node, the root, has no incoming edge. -/
  root_iff : ∀ v, (∀ e, tgt e ≠ v) ↔ v = root
  /-- Each node has at most one incoming edge. -/
  inDegree_le_one : ∀ e f, tgt e = tgt f → e = f

/-- The number of mutations on a `MutationTree`. -/
def MutationTree.mutationCount {ι : Type u} {V : Type v} {E : Type w} (T : MutationTree ι V E) : ℕ :=
  ∑ᶠ e, Set.ncard {i | T.label (T.src e) i ≠ T.label (T.tgt e) i}

/-- The maximum parsimony score of `M` with ancestral sequence `S` (line 510): the least number of mutations on a tree
with root label `S`, whose leaves are in bijection with the rows of `M`. -/
def parsimonyScore {ι : Type u} (S : ι → Bool) (M : Finset (ι → Bool)) : ℕ :=
  sInf {k | ∃ (a b : ℕ) (T : MutationTree ι (Fin a) (Fin b)), T.label T.root = S ∧
    Set.BijOn T.label {v | ∀ e, T.src e ≠ v} (M : Set (ι → Bool)) ∧ T.mutationCount = k}

/-- The Unrooted Full-Decomposition Optimality Conjecture (line 395): every set of binary sequences, under the standing
assumption, is min decomposable (`c = multiple`), or min-1 decomposable (`c = single`). -/
def UnrootedConjecture (c : Crossover) : Prop :=
  ∀ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty → NoConstantColumn M → MinDecomposable c M

/-- The Rooted Full-Decomposition Optimality Conjecture (line 399): every set of binary sequences, under the standing
assumption, is S-min decomposable (`c = multiple`), or S-min-1 decomposable (`c = single`), for any ancestral `S`. -/
def RootedConjecture (c : Crossover) : Prop :=
  ∀ (m : ℕ) (M : Finset (Fin m → Bool)) (S : Fin m → Bool), M.Nonempty → NoConstantColumn M →
    SMinDecomposable c S M

-- END SHARED DEFINITIONS

end Gusfield2007

namespace Gusfield2007Challenge

open Gusfield2007

/-- **Theorem 1**, the Decomposition Theorem. In any crossover model, a nonempty `M` with no constant column has a
network in which every blob contains all and only the sites of one non-trivial connected component of the incompatibility graph, and
every compatible site is on a tree edge. The paper assumes no constant column at line 112, and that `M` is nonempty implicitly. -/
theorem theorem1 {ι : Type*} [LinearOrder ι] [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) := by
  sorry

/-- **Theorem 3.** For any ancestral sequence `S` and crossover model, there is a network fully decomposed for the
conflict graph `G_S(M)`, with `S` at its root and exactly `Σ_C R_{S(C)}(M(C))` recombination nodes. -/
theorem theorem3 {ι : Type*} [LinearOrder ι] [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool)
    (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) ∧
      N.recombCount = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        RS c (C.supp.domRestrict S) (restrictRows C.supp M) := by
  sorry

/-- **Theorem 5.** If an optimal network for `M` with ancestral sequence `S` has node labels `L` with `G_S(L)` and
`G_S(M)` having the same number of components, then `M` is S-min (or S-min-1) decomposable. -/
theorem theorem5 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (h : Nat.card (conflictGraph S N.labelSet).ConnectedComponent = Nat.card (conflictGraph S M).ConnectedComponent) :
    SMinDecomposable c S M := by
  sorry

/-- **Theorem 6.** If a network for `M` with ancestral sequence `S`, not necessarily optimal, has every node visible
and at most one site on each edge, then `M` is S-min (or S-min-1) decomposable. -/
theorem theorem6 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S) (hv : N.AllVisible M S) (he : Function.Injective N.site) : SMinDecomposable c S M := by
  sorry

/-- **Theorem 7.** If every recombination node of a network for `M` with ancestral sequence `S` is a 0- or 1-component
recombination for `G_S(M)`, then there is a fully decomposed network, in the same model, with at most as many recombination nodes. -/
theorem theorem7 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount := by
  sorry

/-- **Theorem 8.** Given `S`, if `M` is spatially disjoint then it is S-min-1 decomposable. -/
theorem theorem8 {ι : Type*} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty)
    (hC : NoConstantColumn M) (h : SpatiallyDisjoint S M) : SMinDecomposable .single S M := by
  sorry

/-- **Theorem 9.** If the node labels of a network for `M` with ancestral sequence `S` respect `G_S(M)`, then there is a
fully decomposed network, in the same model, with at most as many recombination nodes. -/
theorem theorem9 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S) (h : Respects N.labelSet S M) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount := by
  sorry

/-- **Theorem 10**, with the rooted count. If `H(M + S) = R_S(M)`, or `R¹_S(M)`, then `M` is S-min, or S-min-1, decomposable. The paper prints `R(M + S)`, and uses that symbol at lines 525 and 560 for a network with ancestral sequence `S`, which suggests a slip for `R_S(M)`. Read by the definition of line 385, the statement is false for single crossovers (`Gusfield2007.theorem10Printed_single_false`). -/
theorem theorem10 {ι : Type*} [LinearOrder ι] [Finite ι] {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool}
    (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : haplotypeBound (addRow M S) = RS c S M) : SMinDecomposable c S M := by
  sorry

/-- **Corollary 2.** If every node of an optimal network for `M` with ancestral sequence `S` is visible, then `M` is S-min (or
S-min-1) decomposable. -/
theorem corollary2 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (h : N.AllVisible M S) : SMinDecomposable c S M := by
  sorry

/-- **Corollary 3.** When recombinations only model back or recurrent mutations, the model `pointwise`, `M` is S-min decomposable
for any `S`, and the maximum parsimony score of `M` is the sum of the scores of the components of `G_S(M)`. -/
theorem corollary3 {ι : Type*} [LinearOrder ι] [Finite ι] (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    SMinDecomposable .pointwise S M ∧
      parsimonyScore S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        parsimonyScore (C.supp.domRestrict S) (restrictRows C.supp M) := by
  sorry

/-- **Theorem 11.** For any positive `d` there is a set of sequences `M` with `F¹(M) - R¹(M) ≥ d`, written as a sum so
that the truncation on `ℕ` plays no part. -/
theorem theorem11 (d : ℕ) (hd : 0 < d) :
    ∃ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty ∧ NoConstantColumn M ∧ R .single M + d ≤ F .single M := by
  sorry

/-- **The conjectures are false**: the unrooted Full-Decomposition Optimality Conjecture is false for single crossovers (Section 5.3.1). Figure 6 is a counterexample: there `F¹ ≥ 4` and `R¹ ≤ 3` (`Gusfield2007.unrootedConjecture_single_false`). -/
theorem unrootedConjecture_single_false : ¬ UnrootedConjecture .single := by
  sorry

/-- **The conjectures are false**: the unrooted Full-Decomposition Optimality Conjecture is false for multiple crossovers (Section 5.3.2). Figure 8 is a counterexample: there `F ≥ 4` and `R ≤ 3` (`Gusfield2007.unrootedConjecture_multiple_false`). -/
theorem unrootedConjecture_multiple_false : ¬ UnrootedConjecture .multiple := by
  sorry

/-- **The conjectures are false**: the rooted Full-Decomposition Optimality Conjecture is false for single crossovers (Section 5.3.1). -/
theorem rootedConjecture_single_false : ¬ RootedConjecture .single := by
  sorry

/-- **The conjectures are false**: the rooted Full-Decomposition Optimality Conjecture is false for multiple crossovers (Section 5.3). -/
theorem rootedConjecture_multiple_false : ¬ RootedConjecture .multiple := by
  sorry

end Gusfield2007Challenge
