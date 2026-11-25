module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Disjoint
public import Mathlib.Order.Disjoint

/-!
# Maps to `Bool`

When two maps to `Bool` have the same fibres, and when the sets where two such maps differ from a base value are disjoint or nested.
-/

@[expose] public section

open scoped Classical

namespace Bool

/-- Two maps to `Bool` with one partition. -/
theorem apply_eq_apply_iff_of_forall_iff {X : Type*} {f g : X → Bool} {c d : Bool} (h : ∀ x, f x = c ↔ g x = d) (x y : X) : f x = f y ↔ g x = g y := by
  have hx := h x
  have hy := h y
  revert hx hy
  cases f x <;> cases f y <;> cases g x <;> cases g y <;> cases c <;> cases d <;> simp

theorem eq_true_iff_eq_false_of_not_and {a b : Bool} (h₁ : ¬ (a = true ∧ b = true)) (h₂ : a = false → b ≠ false) :
    a = true ↔ b = false := by
  revert h₁ h₂
  cases a <;> cases b <;> simp

/-- Two maps that separate `x` from everything else have the same fibres. -/
theorem apply_eq_apply_iff_of_forall_eq_iff {X : Type*} {f g : X → Bool} {x : X} (hf : ∀ z, f z = f x ↔ z = x) (hg : ∀ z, g z = g x ↔ z = x)
    (a b : X) : f a = f b ↔ g a = g b := by
  have nb : ∀ {α β γ : Bool}, α ≠ γ → β ≠ γ → α = β := by decide
  by_cases ha : a = x <;> by_cases hb : b = x
  · simp [ha, hb]
  · subst ha
    exact ⟨fun h => absurd h.symm (mt (hf b).1 hb), fun h => absurd h.symm (mt (hg b).1 hb)⟩
  · subst hb
    exact ⟨fun h => absurd h (mt (hf a).1 ha), fun h => absurd h (mt (hg a).1 ha)⟩
  · exact ⟨fun _ => nb (mt (hg a).1 ha) (mt (hg b).1 hb), fun _ => nb (mt (hf a).1 ha) (mt (hf b).1 hb)⟩

/-- Two columns that miss a pair of states, other than the pair of the base, have their sets disjoint or nested. -/
theorem disjoint_or_subset_of_forall_not_and {X : Type*} {f g : X → Bool} {p q a b : Bool} (hne : a ≠ p ∨ b ≠ q) (h : ∀ x, ¬ (f x = a ∧ g x = b)) :
    Disjoint {x | f x ≠ p} {x | g x ≠ q} ∨ {x | f x ≠ p} ⊆ {x | g x ≠ q} ∨ {x | g x ≠ q} ⊆ {x | f x ≠ p} := by
  have flip : ∀ {u v : Bool}, u ≠ v → u = !v := by decide
  by_cases ha : a = p
  · have hb : b = !q := flip (hne.resolve_left (by simpa using ha))
    subst ha hb
    refine Or.inr (Or.inr fun x hx => ?_)
    by_contra hxf
    have hxf' : f x = a := by simpa using hxf
    exact h x ⟨hxf', flip hx⟩
  · have ha' : a = !p := flip ha
    by_cases hb : b = q
    · subst ha' hb
      refine Or.inr (Or.inl fun x hx => ?_)
      by_contra hxg
      have hxg' : g x = b := by simpa using hxg
      exact h x ⟨flip hx, hxg'⟩
    · have hb' : b = !q := flip hb
      subst ha' hb'
      refine Or.inl (Set.disjoint_left.2 fun x hx hy => ?_)
      exact h x ⟨flip hx, flip hy⟩

end Bool
