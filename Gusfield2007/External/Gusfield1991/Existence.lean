module

public import Gusfield2007.External.Gusfield1991.PerfectPhylogeny
public import Gusfield2007.Networks.Existence

/-!
# Every set of rows has a network

A network derives any nonempty `M`, with any ancestral sequence, in each crossover model: by the network of the Perfect
Phylogeny Theorem when there is no site (`External.Gusfield1991.exists_network_of_no_conflict`), and by the network of
`Decomp.exists_inflate_net` otherwise. So the minima `R` and `R_S` of `Gusfield2007.Defs` are over nonempty sets, which the
lower bounds of the sources need. The statements are on the definitions of the paper, in its namespace; they are here
because their proof uses the cited Perfect Phylogeny Theorem.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

universe u

variable {ι : Type u} [LinearOrder ι] [Finite ι]

/-- The minimum `RS c S M` is over a nonempty set when `M` is nonempty. -/
theorem rootedRecombSet_nonempty (c : Crossover) (S : ι → Bool) {M : Finset (ι → Bool)} (hM : M.Nonempty) :
    {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.ancestral = S ∧
      N.recombCount = k}.Nonempty := by
  have : Fintype ι := Fintype.ofFinite ι
  by_cases hι : IsEmpty ι
  · obtain ⟨a, b, N, hr, hd, hs, -⟩ := External.Gusfield1991.exists_network_of_no_conflict M S hM (fun i => hι.elim i) (fun i => hι.elim i)
    exact ⟨_, a, b, N, Network.obeys_of_tgt_injective (Network.tgt_injective_of_no_recomb hr) c, hd, hs, rfl⟩
  · have hcard : 1 ≤ Fintype.card ι := by
      rw [not_isEmpty_iff] at hι
      exact Fintype.card_pos
    obtain ⟨a, b, N, h₁, h₂, h₃, -, -⟩ := Decomp.exists_inflate_net c hcard M hM S
    exact ⟨_, a, b, N, h₁, h₃, h₂, rfl⟩

/-- The minimum `R c M` is over a nonempty set when `M` is nonempty. So `sInf` is the minimum of the paper. -/
theorem recombSet_nonempty (c : Crossover) {M : Finset (ι → Bool)} (hM : M.Nonempty) :
    {k | ∃ (a b : ℕ) (N : Network ι (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.recombCount = k}.Nonempty := by
  obtain ⟨k, a, b, N, h₁, h₂, -, h₄⟩ := rootedRecombSet_nonempty c hM.choose hM
  exact ⟨k, a, b, N, h₁, h₂, h₄⟩

end Gusfield2007
