module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Reachability and connected components

Reachability from adjacency, counting connected components when there are one or two, sums over the components, components with the same reachability, and the edges of a non-trivial component.
-/

@[expose] public section

open scoped Classical

namespace SimpleGraph

/-- A node reached from another, other than it, has a neighbour. -/
theorem Reachable.exists_adj_of_ne {ι : Type*} {G : SimpleGraph ι} {i j : ι} (h : G.Reachable i j) (hij : i ≠ j) : ∃ k, G.Adj i k := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hij
  | @cons _ k _ hk _ => exact ⟨k, hk⟩

/-- A vertex at distance at most two from `a` reaches `a`. -/
theorem reachable_of_eq_or_adj_or_adj_adj {ι : Type*} {G : SimpleGraph ι} {i a : ι} (h : i = a ∨ G.Adj i a ∨ ∃ k, G.Adj i k ∧ G.Adj k a) : G.Reachable i a := by
  rcases h with rfl | h | ⟨k, h₁, h₂⟩
  · exact SimpleGraph.Reachable.refl _
  · exact h.reachable
  · exact h₁.reachable.trans h₂.reachable

/-- Two connected components, from the fact that adjacent vertices are on the same side, and that each side reaches a vertex of its own. -/
theorem reachable_iff_mem_iff_of_adj {ι : Type*} (G : SimpleGraph ι) {A : Set ι} (hadj : ∀ i j, G.Adj i j → (i ∈ A ↔ j ∈ A)) {a b : ι}
    (ha : ∀ i ∈ A, G.Reachable i a) (hb : ∀ i, i ∉ A → G.Reachable i b) (i j : ι) : G.Reachable i j ↔ (i ∈ A ↔ j ∈ A) := by
  constructor
  · intro h
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => rfl
    | tail _ huv ih => exact ih.trans (hadj _ _ huv)
  · intro h
    by_cases hi : i ∈ A
    · exact (ha i hi).trans (ha j (h.1 hi)).symm
    · exact (hb i hi).trans (hb j fun hj => hi (h.2 hj)).symm

/-- A sum over the connected components, when they are two: `A` and its complement. -/
theorem finsum_connectedComponent_supp_eq_add {ι : Type*} {G : SimpleGraph ι} {A : Set ι} (hA : ∀ i j, G.Reachable i j ↔ (i ∈ A ↔ j ∈ A)) {a b : ι} (ha : a ∈ A) (hb : b ∉ A)
    (f : Set ι → ℕ) : ∑ᶠ C : G.ConnectedComponent, f C.supp = f A + f Aᶜ := by
  have hsuppa : (G.connectedComponentMk a).supp = A := by
    ext i
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq, hA]
    exact ⟨fun h => h.2 ha, fun h => ⟨fun _ => ha, fun _ => h⟩⟩
  have hsuppb : (G.connectedComponentMk b).supp = Aᶜ := by
    ext i
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq, hA]
    exact ⟨fun h hi => hb (h.1 hi), fun h => ⟨fun hi => absurd hi h, fun hb' => absurd hb' hb⟩⟩
  have hne : G.connectedComponentMk a ≠ G.connectedComponentMk b := by
    intro h
    have := SimpleGraph.ConnectedComponent.eq.1 h
    rw [hA] at this
    exact hb (this.1 ha)
  have hsub : (Function.support fun C : G.ConnectedComponent => f C.supp) ⊆
      ↑({G.connectedComponentMk a, G.connectedComponentMk b} : Finset G.ConnectedComponent) := by
    intro C _
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ i =>
      by_cases hi : i ∈ A
      · have : G.connectedComponentMk i = G.connectedComponentMk a :=
          SimpleGraph.ConnectedComponent.eq.2 ((hA i a).2 ⟨fun _ => ha, fun _ => hi⟩)
        simp [this]
      · have : G.connectedComponentMk i = G.connectedComponentMk b :=
          SimpleGraph.ConnectedComponent.eq.2 ((hA i b).2 ⟨fun h => absurd h hi, fun h => absurd h hb⟩)
        simp [this]
  rw [finsum_eq_sum_of_support_subset _ hsub, Finset.sum_pair hne, hsuppa, hsuppb]

/-- The number of connected components, when they are two: `A` and its complement. -/
theorem card_connectedComponent_eq_two_of_reachable_iff {ι : Type*} {G : SimpleGraph ι} {A : Set ι} (hA : ∀ i j, G.Reachable i j ↔ (i ∈ A ↔ j ∈ A)) {a b : ι} (ha : a ∈ A) (hb : b ∉ A) :
    Nat.card G.ConnectedComponent = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨G.connectedComponentMk a, G.connectedComponentMk b, fun h => ?_, ?_⟩
  · have := SimpleGraph.ConnectedComponent.eq.1 h
    rw [hA] at this
    exact hb (this.1 ha)
  · ext C
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    induction C using SimpleGraph.ConnectedComponent.ind with
    | _ i =>
      by_cases hi : i ∈ A
      · exact Or.inl (SimpleGraph.ConnectedComponent.eq.2 ((hA i a).2 ⟨fun _ => ha, fun _ => hi⟩))
      · exact Or.inr (SimpleGraph.ConnectedComponent.eq.2 ((hA i b).2 ⟨fun h => absurd h hi, fun h => absurd h hb⟩))

/-- A graph all of whose vertices reach one another has one connected component. -/
theorem card_connectedComponent_eq_one_of_reachable {ι : Type*} {G : SimpleGraph ι} [Nonempty ι] (h : ∀ i j, G.Reachable i j) : Nat.card G.ConnectedComponent = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun C C' => ?_⟩, ⟨G.connectedComponentMk (Classical.arbitrary ι)⟩⟩
  induction C using SimpleGraph.ConnectedComponent.ind with
  | _ i =>
    induction C' using SimpleGraph.ConnectedComponent.ind with
    | _ j => exact SimpleGraph.ConnectedComponent.eq.2 (h i j)

/-- The components of two graphs with the same reachability correspond, with the same supports. -/
def connectedComponentEquivOfReachableIff {ι : Type*} {G G' : SimpleGraph ι} (h : ∀ i j, G.Reachable i j ↔ G'.Reachable i j) :
    G.ConnectedComponent ≃ G'.ConnectedComponent where
  toFun C := C.lift (fun i => G'.connectedComponentMk i) fun _ _ p _ =>
    SimpleGraph.ConnectedComponent.eq.2 ((h _ _).1 p.reachable)
  invFun C := C.lift (fun i => G.connectedComponentMk i) fun _ _ p _ =>
    SimpleGraph.ConnectedComponent.eq.2 ((h _ _).2 p.reachable)
  left_inv C := by
    induction C using SimpleGraph.ConnectedComponent.ind
    rfl
  right_inv C := by
    induction C using SimpleGraph.ConnectedComponent.ind
    rfl

theorem connectedComponentEquivOfReachableIff_supp {ι : Type*} {G G' : SimpleGraph ι} (h : ∀ i j, G.Reachable i j ↔ G'.Reachable i j) (C : G.ConnectedComponent) :
    (connectedComponentEquivOfReachableIff h C).supp = C.supp := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | _ i₀ =>
    ext i
    change i ∈ (G'.connectedComponentMk i₀).supp ↔ i ∈ (G.connectedComponentMk i₀).supp
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact (h i i₀).symm

/-- A sum over the components of a graph depends only on the components, as sets of vertices. -/
theorem finsum_connectedComponent_supp_congr {ι : Type*} {G G' : SimpleGraph ι} (h : ∀ i j, G.Reachable i j ↔ G'.Reachable i j) (g : Set ι → ℕ) :
    ∑ᶠ C : G.ConnectedComponent, g C.supp = ∑ᶠ C : G'.ConnectedComponent, g C.supp := by
  rw [← finsum_comp_equiv (connectedComponentEquivOfReachableIff h)]
  exact finsum_congr fun C => by rw [connectedComponentEquivOfReachableIff_supp]

/-- A non-trivial component has an edge. -/
theorem ConnectedComponent.exists_adj_of_supp_nontrivial {ι : Type*} {G : SimpleGraph ι} {c : G.ConnectedComponent} (hc : c.supp.Nontrivial) :
    ∃ i ∈ c.supp, ∃ j ∈ c.supp, G.Adj i j := by
  obtain ⟨i₀, hi₀, i₁, hi₁, hne⟩ := hc
  obtain ⟨p⟩ : G.Reachable i₀ i₁ := SimpleGraph.ConnectedComponent.eq.1 (hi₀.trans (Eq.symm hi₁))
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ j _ hj _ =>
    refine ⟨i₀, hi₀, j, ?_, hj⟩
    have : G.connectedComponentMk i₀ = G.connectedComponentMk j := SimpleGraph.ConnectedComponent.eq.2 hj.reachable
    exact this.symm.trans hi₀

/-- The component of a vertex with an edge is non-trivial. -/
theorem Adj.connectedComponentMk_supp_nontrivial {ι : Type*} {G : SimpleGraph ι} {i j : ι} (h : G.Adj i j) : (G.connectedComponentMk i).supp.Nontrivial :=
  ⟨i, rfl, j, (SimpleGraph.ConnectedComponent.eq.2 h.reachable).symm, h.ne⟩

/-- A set closed under adjacency in a connected graph is everything. -/
theorem Preconnected.forall_of_forall_adj {W : Type*} {T : SimpleGraph W} (hT : T.Preconnected) {P : W → Prop} (hP : ∀ ⦃u v⦄, T.Adj u v → P u → P v) {w : W}
    (hw : P w) (x : W) : P x := by
  obtain ⟨p⟩ := hT w x
  induction p with
  | nil => exact hw
  | cons h _ ih => exact ih (hP h hw)

end SimpleGraph
