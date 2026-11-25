module

public import Gusfield2007.External.GusfieldEtAl2004.Algorithm
public import Gusfield2007.ProofOfDecomposition.GalledTrees.Build
public import Gusfield2007.External.GusfieldEtAl2004.BuildCount
public import Gusfield2007.External.GusfieldEtAl2004.Elimination
public import Gusfield2007.External.GusfieldEtAl2004.GalledTree
public import Gusfield2007.External.GusfieldEtAl2004.Optimality
public import Gusfield2007.External.GusfieldEtAl2004.SameBlob
public import Gusfield2007.External.GusfieldEtAl2004.Theorem2_2
public import Gusfield2007.External.HudsonKaplan1985.Algorithm
public import Gusfield2007.External.MyersGriffiths2003.Algorithm1
public import Gusfield2007.External.MyersGriffiths2003.Composite
public import Gusfield2007.External.SongHein2005.BinaryPaths
public import Gusfield2007.ProofOfDecomposition.CounterexampleNets
public import Gusfield2007.OptimalityConjectures.Counterexamples
public import Gusfield2007.ProofOfDecomposition.Decomposition
public import Gusfield2007.Defs
public import Gusfield2007.ProofOfDecomposition.EntryNet
public import Gusfield2007.OptimalityConjectures.Examples
public import Gusfield2007.OptimalityConjectures.HusonKloepper
public import Gusfield2007.OptimalityConjectures.MdLower
public import Gusfield2007.Applications.MergedTreeness
public import Gusfield2007.Networks.Operations
public import Gusfield2007.OptimalityConjectures.OpenStatements
public import Gusfield2007.ProofOfDecomposition.Realizability
public import Gusfield2007.OptimalityConjectures.SufficientConditions
public import Gusfield2007.ProofOfDecomposition.SuperCharacters
public import Gusfield2007.OptimalityConjectures.Theorem10PrintedMultiple
public import Gusfield2007.Networks.TimeOrdered
public import Gusfield2007.ProofOfDecomposition.Uniqueness

/-!
# Gusfield et al. 2007: the proofs of the Challenge

Each theorem of `Gusfield2007.Challenge` is restated here word for word, under the same name, and proved from the library.
The Challenge's definitions are the library's own, from `Gusfield2007.Defs`, so no bridge between two versions of them is
needed. This module imports the library, of which it is the entry point.
-/

@[expose] public noncomputable section

open scoped Classical

namespace Gusfield2007Challenge

open Gusfield2007

/-- **Theorem 1**, the Decomposition Theorem. In any crossover model, a nonempty `M` with no constant column has a
network in which every blob contains all and only the sites of one non-trivial connected component of the incompatibility graph, and
every compatible site is on a tree edge. The paper assumes no constant column at line 112, and that `M` is nonempty implicitly. -/
theorem theorem1 {ι : Type*} [LinearOrder ι] [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧
      N.IsFullyDecomposedFor (incompatGraph M) := Gusfield2007.theorem1 c M hM hC

/-- **Theorem 3.** For any ancestral sequence `S` and crossover model, there is a network fully decomposed for the
conflict graph `G_S(M)`, with `S` at its root and exactly `Σ_C R_{S(C)}(M(C))` recombination nodes. -/
theorem theorem3 {ι : Type*} [LinearOrder ι] [Finite ι] (c : Crossover) (M : Finset (ι → Bool)) (S : ι → Bool)
    (hM : M.Nonempty) (hC : NoConstantColumn M) :
    ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.IsFullyDecomposedFor (conflictGraph S M) ∧
      N.recombCount = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        RS c (C.supp.domRestrict S) (restrictRows C.supp M) := Gusfield2007.theorem3 c M S hM hC

/-- **Theorem 5.** If an optimal network for `M` with ancestral sequence `S` has node labels `L` with `G_S(L)` and
`G_S(M)` having the same number of components, then `M` is S-min (or S-min-1) decomposable. -/
theorem theorem5 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (h : Nat.card (conflictGraph S N.labelSet).ConnectedComponent = Nat.card (conflictGraph S M).ConnectedComponent) :
    SMinDecomposable c S M := Gusfield2007.theorem5 hC N hN h

/-- **Theorem 6.** If a network for `M` with ancestral sequence `S`, not necessarily optimal, has every node visible
and at most one site on each edge, then `M` is S-min (or S-min-1) decomposable. -/
theorem theorem6 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S) (hv : N.AllVisible M S) (he : Function.Injective N.site) : SMinDecomposable c S M :=
  Gusfield2007.theorem6 hC N hc hd hS hv he

/-- **Theorem 7.** If every recombination node of a network for `M` with ancestral sequence `S` is a 0- or 1-component
recombination for `G_S(M)`, then there is a fully decomposed network, in the same model, with at most as many recombination nodes. -/
theorem theorem7 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S)
    (h : ∀ x, N.IsRecomb x → N.IsZeroComponent (conflictGraph S M) x ∨ N.IsOneComponent (conflictGraph S M) x) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount :=
  Gusfield2007.theorem7 hC N hc hd hS h

/-- **Theorem 8.** Given `S`, if `M` is spatially disjoint then it is S-min-1 decomposable. -/
theorem theorem8 {ι : Type*} [LinearOrder ι] [Finite ι] {M : Finset (ι → Bool)} {S : ι → Bool} (hM : M.Nonempty)
    (hC : NoConstantColumn M) (h : SpatiallyDisjoint S M) : SMinDecomposable .single S M :=
  Gusfield2007.theorem8 hM hC h

/-- **Theorem 9.** If the node labels of a network for `M` with ancestral sequence `S` respect `G_S(M)`, then there is a
fully decomposed network, in the same model, with at most as many recombination nodes. -/
theorem theorem9 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hc : N.Obeys c) (hd : N.Derives M)
    (hS : N.ancestral = S) (h : Respects N.labelSet S M) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧
      N'.IsFullyDecomposedFor (conflictGraph S M) ∧ N'.recombCount ≤ N.recombCount :=
  Gusfield2007.theorem9 hC N hc hd hS h

/-- **Theorem 10**, with the rooted count. If `H(M + S) = R_S(M)`, or `R¹_S(M)`, then `M` is S-min, or S-min-1, decomposable. The paper prints `R(M + S)`, and uses that symbol at lines 525 and 560 for a network with ancestral sequence `S`, which suggests a slip for `R_S(M)`. Read by the definition of line 385, the statement is false for single crossovers (`Gusfield2007.theorem10Printed_single_false`). -/
theorem theorem10 {ι : Type*} [LinearOrder ι] [Finite ι] {c : Crossover} {M : Finset (ι → Bool)} {S : ι → Bool}
    (hM : M.Nonempty) (hC : NoConstantColumn M)
    (h : haplotypeBound (addRow M S) = RS c S M) : SMinDecomposable c S M := Gusfield2007.theorem10 hM hC h

/-- **Corollary 2.** If every node of an optimal network for `M` with ancestral sequence `S` is visible, then `M` is S-min (or
S-min-1) decomposable. -/
theorem corollary2 {ι : Type*} [LinearOrder ι] [Finite ι] {V E : Type*} [Fintype V] [Finite E] {c : Crossover}
    {M : Finset (ι → Bool)} {S : ι → Bool} (hC : NoConstantColumn M) (N : Network ι V E) (hN : N.IsOptimalRooted c S M)
    (h : N.AllVisible M S) : SMinDecomposable c S M := Gusfield2007.corollary2 hC N hN h

/-- **Corollary 3.** When recombinations only model back or recurrent mutations, the model `pointwise`, `M` is S-min decomposable
for any `S`, and the maximum parsimony score of `M` is the sum of the scores of the components of `G_S(M)`. -/
theorem corollary3 {ι : Type*} [LinearOrder ι] [Finite ι] (M : Finset (ι → Bool)) (S : ι → Bool) (hM : M.Nonempty)
    (hC : NoConstantColumn M) :
    SMinDecomposable .pointwise S M ∧
      parsimonyScore S M = ∑ᶠ C : (conflictGraph S M).ConnectedComponent,
        parsimonyScore (C.supp.domRestrict S) (restrictRows C.supp M) := Gusfield2007.corollary3 M S hM hC

/-- **Theorem 11.** For any positive `d` there is a set of sequences `M` with `F¹(M) - R¹(M) ≥ d`, written as a sum so
that the truncation on `ℕ` plays no part. -/
theorem theorem11 (d : ℕ) (hd : 0 < d) :
    ∃ (m : ℕ) (M : Finset (Fin m → Bool)), M.Nonempty ∧ NoConstantColumn M ∧ R .single M + d ≤ F .single M :=
  Gusfield2007.theorem11 d hd

/-- **The conjectures are false**: the unrooted Full-Decomposition Optimality Conjecture is false for single crossovers (Section 5.3.1). Figure 6 is a counterexample: there `F¹ ≥ 4` and `R¹ ≤ 3` (`Gusfield2007.unrootedConjecture_single_false`). -/
theorem unrootedConjecture_single_false : ¬ UnrootedConjecture .single :=
  Gusfield2007.unrootedConjecture_single_false.2.2

/-- **The conjectures are false**: the unrooted Full-Decomposition Optimality Conjecture is false for multiple crossovers (Section 5.3.2). Figure 8 is a counterexample: there `F ≥ 4` and `R ≤ 3` (`Gusfield2007.unrootedConjecture_multiple_false`). -/
theorem unrootedConjecture_multiple_false : ¬ UnrootedConjecture .multiple :=
  Gusfield2007.unrootedConjecture_multiple_false.2.2

/-- **The conjectures are false**: the rooted Full-Decomposition Optimality Conjecture is false for single crossovers (Section 5.3.1). -/
theorem rootedConjecture_single_false : ¬ RootedConjecture .single :=
  Gusfield2007.rootedConjecture_single_false

/-- **The conjectures are false**: the rooted Full-Decomposition Optimality Conjecture is false for multiple crossovers (Section 5.3). -/
theorem rootedConjecture_multiple_false : ¬ RootedConjecture .multiple :=
  Gusfield2007.rootedConjecture_multiple_false

end Gusfield2007Challenge
