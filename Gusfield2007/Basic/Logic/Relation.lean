module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Basic

/-!
# Relations along which a function increases

A function that increases along a relation increases along its paths, so the relation is acyclic; on a finite type, an acyclic relation has such a function; and adding one arc that closes no cycle keeps a relation acyclic.
-/

@[expose] public section

open scoped Classical

namespace Relation

/-- A function that increases along a relation increases along its paths. -/
theorem TransGen.lt_of_forall_lt {α β : Type*} [Preorder β] {r : α → α → Prop} (f : α → β) (h : ∀ a b, r a b → f a < f b) {a b : α} (hab : Relation.TransGen r a b) : f a < f b := by
  induction hab with
  | single hb => exact h _ _ hb
  | tail _ hb ih => exact ih.trans (h _ _ hb)

/-- A relation along which a function increases is acyclic. -/
theorem not_transGen_self_of_forall_lt {α β : Type*} [Preorder β] {r : α → α → Prop} (f : α → β) (h : ∀ a b, r a b → f a < f b) (x : α) : ¬ Relation.TransGen r x x :=
  fun hx => lt_irrefl _ (TransGen.lt_of_forall_lt f h hx)

/-- A strictly increasing rank exists on a finite acyclic relation. -/
theorem exists_forall_lt_of_not_transGen_self {α : Type*} [Finite α] (r : α → α → Prop) (hr : ∀ a, ¬ Relation.TransGen r a a) :
    ∃ f : α → ℕ, ∀ a b, r a b → f a < f b := by
  refine ⟨fun b => {u | Relation.TransGen r u b}.ncard, fun a b hab => Set.ncard_lt_ncard ?_ (Set.toFinite _)⟩
  refine ⟨fun u hu => Relation.TransGen.tail hu hab, fun h => ?_⟩
  exact hr a (h (Relation.TransGen.single hab))

/-- A rank that increases along the arcs `src e → tgt e` makes the relation of the arcs acyclic. -/
theorem not_transGen_arc_self_of_rank {V : Type*} {E : Type*} {src tgt : E → V} (f : V → ℕ) (h : ∀ e, f (src e) < f (tgt e)) (v : V) :
    ¬ Relation.TransGen (fun a b => ∃ e, src e = a ∧ tgt e = b) v v :=
  not_transGen_self_of_forall_lt f (by rintro a b ⟨e, rfl, rfl⟩; exact h e) v

/-- A relation with one more pair `(y, x)` is acyclic if `r` is and `x` doesn't reach `y`. -/
theorem not_transGen_self_of_le_or_eq {α : Type*} {r r' : α → α → Prop} {y x : α} (hr : ∀ a, ¬ Relation.TransGen r a a)
    (hle : ∀ a b, r' a b → r a b ∨ (a = y ∧ b = x)) (hxy : ¬ Relation.ReflTransGen r x y) (a : α) :
    ¬ Relation.TransGen r' a a := by
  have key : ∀ a b, Relation.TransGen r' a b →
      Relation.TransGen r a b ∨ (Relation.ReflTransGen r x b ∧ Relation.ReflTransGen r a y) := by
    intro a b h
    induction h with
    | single hab =>
      rcases hle _ _ hab with h | ⟨rfl, rfl⟩
      · exact Or.inl (Relation.TransGen.single h)
      · exact Or.inr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    | tail _ hbc ih =>
      rcases hle _ _ hbc with h | ⟨rfl, rfl⟩
      · rcases ih with ih | ⟨ih₁, ih₂⟩
        · exact Or.inl (ih.tail h)
        · exact Or.inr ⟨ih₁.tail h, ih₂⟩
      · rcases ih with ih | ⟨ih₁, ih₂⟩
        · exact Or.inr ⟨Relation.ReflTransGen.refl, ih.to_reflTransGen⟩
        · exact absurd ih₁ hxy
  intro h
  rcases key a a h with h | ⟨h₁, h₂⟩
  · exact hr a h
  · exact hxy (h₁.trans h₂)

end Relation
