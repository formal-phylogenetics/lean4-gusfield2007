module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Walks, paths and cycles

Two paths that share only their ends make a cycle; a walk splits at its first node in a set and at an edge on it; a cycle through an edge is that edge and a path.
-/

@[expose] public section

open scoped Classical

namespace SimpleGraph

/-- Two paths between two nodes, with no other node and no edge in common, make a cycle. -/
theorem Walk.IsPath.isCycle_append_of_edges_disjoint {V : Type*} {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath) (huv : u ≠ v)
    (hsupp : ∀ w ∈ p.support, w ∈ q.support → w = u ∨ w = v) (hedges : ∀ g ∈ p.edges, g ∉ q.edges) : (p.append q).IsCycle := by
  rw [Walk.isCycle_def]
  have hpn := hp.support_nodup
  have hqn := hq.support_nodup
  rw [← Walk.cons_tail_support, List.nodup_cons] at hpn hqn
  refine ⟨?_, ?_, ?_⟩
  · rw [Walk.isTrail_def, Walk.edges_append, List.nodup_append]
    exact ⟨hp.isTrail.edges_nodup, hq.isTrail.edges_nodup, fun a ha b hb hab => hedges a ha (hab ▸ hb)⟩
  · intro h
    have := congrArg Walk.length h
    rw [Walk.length_append, Walk.length_nil] at this
    exact huv (Walk.eq_of_length_eq_zero (by omega : p.length = 0))
  · rw [Walk.tail_support_append, List.nodup_append]
    refine ⟨hpn.2, hqn.2, fun a ha b hb hab => ?_⟩
    subst hab
    have ha' : a ∈ p.support := List.mem_of_mem_tail ha
    have hb' : a ∈ q.support := List.mem_of_mem_tail hb
    rcases hsupp a ha' hb' with rfl | rfl
    · exact hpn.1 ha
    · exact hqn.1 hb

/-- The first node of a walk in a set. -/
theorem Walk.exists_eq_append_forall_mem_support {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (A : Set V) (h : ∃ w ∈ p.support, w ∈ A) :
    ∃ (c : V) (_ : c ∈ A) (p₁ : G.Walk u c) (p₂ : G.Walk c v), p = p₁.append p₂ ∧ ∀ w ∈ p₁.support, w ∈ A → w = c := by
  induction p with
  | nil =>
    obtain ⟨w, hw, hA⟩ := h
    rw [Walk.support_nil, List.mem_singleton] at hw
    subst hw
    exact ⟨_, hA, Walk.nil, Walk.nil, rfl, by simp⟩
  | @cons a b c hadj p ih =>
    by_cases ha : a ∈ A
    · exact ⟨a, ha, Walk.nil, Walk.cons hadj p, rfl, by simp⟩
    · have h' : ∃ w ∈ p.support, w ∈ A := by
        obtain ⟨w, hw, hA⟩ := h
        rw [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact absurd hA ha
        · exact ⟨w, hw, hA⟩
      obtain ⟨d, hd, p₁, p₂, rfl, hp₁⟩ := ih h'
      refine ⟨d, hd, Walk.cons hadj p₁, p₂, rfl, fun w hw hA => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact absurd hA ha
      · exact hp₁ w hw hA

/-- A walk splits at an edge on it. -/
theorem Walk.exists_eq_append_cons_of_mem_edges {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {b : Sym2 V} (hb : b ∈ p.edges) :
    ∃ (x y : V) (h : G.Adj x y) (p₁ : G.Walk u x) (p₂ : G.Walk y v), s(x, y) = b ∧ p = p₁.append (Walk.cons h p₂) := by
  induction p with
  | nil => simp at hb
  | @cons a c d hadj p ih =>
    rw [Walk.edges_cons, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨a, c, hadj, Walk.nil, p, rfl, rfl⟩
    · obtain ⟨x, y, h, p₁, p₂, hxy, rfl⟩ := ih hb
      exact ⟨x, y, h, Walk.cons hadj p₁, p₂, hxy, rfl⟩

/-- A cycle through an edge is that edge and a path between its ends. -/
theorem Walk.IsCycle.exists_isPath_of_mem_edges {V : Type*} {G : SimpleGraph V} {u : V} {c : G.Walk u u} (hc : c.IsCycle) {b : Sym2 V} (hb : b ∈ c.edges) :
    ∃ (x y : V) (_ : G.Adj x y) (R : G.Walk y x), s(x, y) = b ∧ R.IsPath ∧ b ∉ R.edges ∧ (∀ z ∈ c.edges, z = b ∨ z ∈ R.edges) := by
  obtain ⟨x, y, h, p₁, p₂, hxy, rfl⟩ := Walk.exists_eq_append_cons_of_mem_edges c hb
  refine ⟨x, y, h, p₂.append p₁, hxy, ?_, ?_, ?_⟩
  · have htail := hc.support_nodup
    rw [Walk.tail_support_append, Walk.support_cons, List.tail_cons] at htail
    rw [Walk.isPath_def, Walk.support_append]
    exact (List.perm_append_comm.nodup_iff).1 htail
  · have hnd := hc.isTrail.edges_nodup
    rw [Walk.edges_append, Walk.edges_cons, List.nodup_append] at hnd
    rw [Walk.edges_append, List.mem_append]
    rintro (h₁ | h₁)
    · exact (List.nodup_cons.1 hnd.2.1).1 (hxy ▸ h₁)
    · exact hnd.2.2 b h₁ b (hxy ▸ List.mem_cons_self) rfl
  · intro z hz
    rw [Walk.edges_append, List.mem_append, Walk.edges_cons, List.mem_cons] at hz
    rw [Walk.edges_append, List.mem_append]
    rcases hz with hz | rfl | hz
    · exact Or.inr (Or.inr hz)
    · exact Or.inl hxy
    · exact Or.inr (Or.inl hz)

/-- An edge with both ends in a set isn't on a path having only its last node in the set. -/
theorem Walk.false_of_mem_edges_of_forall_mem_support {V : Type*} {G : SimpleGraph V} {u c : V} {p : G.Walk u c} {A : Set V} (hp : ∀ w ∈ p.support, w ∈ A → w = c) {g : Sym2 V} (hg : g ∈ p.edges)
    (hA : ∀ w ∈ g, w ∈ A) : False := by
  induction g using Sym2.ind with
  | _ a b =>
    have ha := hp a (p.fst_mem_support_of_mem_edges hg) (hA a (Sym2.mem_mk_left a b))
    have hb := hp b (p.snd_mem_support_of_mem_edges hg) (hA b (Sym2.mem_mk_right a b))
    exact G.ne_of_adj (p.adj_of_mem_edges hg) (ha.trans hb.symm)

end SimpleGraph
