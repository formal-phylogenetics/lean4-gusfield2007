module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

/-!
# Acyclic graphs and isomorphisms

In a finite acyclic graph, a node farthest from `v` in its component has at most one neighbour; isomorphic graphs have as many edges.
-/

@[expose] public section

open scoped Classical

namespace SimpleGraph

/-- In a finite acyclic graph, the farthest node from `v` in its component has at most one neighbour, and if it's `v`, then none. -/
theorem IsAcyclic.exists_reachable_neighborSet_subsingleton {W : Type*} [Finite W] {G : SimpleGraph W} (hG : G.IsAcyclic) (v : W) :
    ∃ y, G.Reachable v y ∧ (G.neighborSet y).Subsingleton ∧ (y = v → ∀ z, ¬ G.Adj v z) := by
  obtain ⟨y, hy, hmax⟩ := (Set.toFinite {y | G.Reachable v y}).exists_maximalFor (G.dist v) _
    ⟨v, SimpleGraph.Reachable.refl _⟩ |> fun ⟨y, hy⟩ => (⟨y, hy.1, fun z hz => not_lt.1 fun hlt => absurd (hy.2 hz hlt.le) (not_le.2 hlt)⟩ :
      ∃ y, G.Reachable v y ∧ ∀ z, G.Reachable v z → G.dist v z ≤ G.dist v y)
  have hd : ∀ z, G.Adj y z → G.dist v z + 1 = G.dist v y := by
    intro z hz
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable v hz hy with h | h
    · exact h.symm
    · have := hmax z (SimpleGraph.Reachable.trans hy hz.reachable)
      omega
  refine ⟨y, hy, ?_, ?_⟩
  · obtain ⟨p, hp, hpl⟩ := SimpleGraph.Reachable.exists_path_of_dist hy
    have hkey : ∀ z, G.Adj y z → z = p.penultimate := by
      intro z hz
      have hzr : G.Reachable v z := SimpleGraph.Reachable.trans hy hz.reachable
      obtain ⟨q, hq, hql⟩ := SimpleGraph.Reachable.exists_path_of_dist hzr
      have hy' : y ∉ q.support := by
        intro hmem
        have h₁ : G.dist v y ≤ (q.takeUntil y hmem).length := SimpleGraph.dist_le _
        have h₂ := q.length_takeUntil_le_length hmem
        have h₃ := hd z hz
        omega
      exact hG.eq_penultimate_of_adj_end hp hz (hG.mem_support_of_ne_mem_support_of_adj_of_isPath hp hq hz hy')
    intro z₁ h₁ z₂ h₂
    exact (hkey z₁ h₁).trans (hkey z₂ h₂).symm
  · rintro rfl z hz
    have := hd z hz
    rw [SimpleGraph.dist_self] at this
    omega

/-- An isomorphism of graphs preserves the number of edges. -/
theorem Iso.ncard_edgeSet_eq {W : Type*} {T : SimpleGraph W} {W' : Type*} {T' : SimpleGraph W'} (f : T ≃g T') : T'.edgeSet.ncard = T.edgeSet.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr f.mapEdgeSet.symm

end SimpleGraph
