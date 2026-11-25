module

public import Phylogenetics.Tree.SplitsEquivalence

/-!
# The Splits Equivalence Theorem (Semple, Steel 2003, Theorem 3.1.4)

Gusfield et al. 2007 cite it twice: at line 156, as a reference for the Perfect Phylogeny Theorem, and at line 344, in the
proof of Theorem 4, "the splits of an undirected tree uniquely define the tree". It is proved in the library
`Phylogenetics`, as `Phylogenetics.SplitsEquivalence.exists_xTree_iff` and `Phylogenetics.SplitsEquivalence.xTree_unique`.
Its two halves are restated here, with the label of their route. See the `README.md` of this directory for the source and
what was read.
-/

@[expose] public section

namespace External.SempleSteel2003

open Phylogenetics.SplitsEquivalence

variable {X W W' : Type*}

/-- **The Splits Equivalence Theorem** (`ext:splits_equivalence`), existence (Semple, Steel 2003, Theorem 3.1.4). -/
theorem exists_xTree_iff [Finite X] [Nonempty X] {F : Set (Set X)} (hF : IsSplitSystem F) :
    PairwiseCompatible F ↔ ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (φ : X → Fin n), IsXTree T φ ∧ splitSides T φ = F :=
  Phylogenetics.SplitsEquivalence.exists_xTree_iff hF

/-- **The Splits Equivalence Theorem** (`ext:splits_equivalence`), uniqueness (Semple, Steel 2003, Theorem 3.1.4). -/
theorem xTree_unique [Finite X] [Nonempty X] [Finite W] [Finite W'] {T : SimpleGraph W} {T' : SimpleGraph W'}
    {φ : X → W} {φ' : X → W'} (hT : IsXTree T φ) (hT' : IsXTree T' φ') (h : splitSides T φ = splitSides T' φ') :
    ∃ f : T ≃g T', ∀ x, f (φ x) = φ' x :=
  Phylogenetics.SplitsEquivalence.xTree_unique hT hT' h

end External.SempleSteel2003
