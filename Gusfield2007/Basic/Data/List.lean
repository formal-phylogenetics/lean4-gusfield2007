module

public import Mathlib.Data.Set.Image
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Lists: images, filters, sums and counts

Facts about lists that the algorithms use.
-/

@[expose] public section

open scoped Classical

namespace List

/-- The image of the elements of two lists is the set of elements of their images. -/
theorem image_setOf_mem_or_mem {α β : Type*} (g : α → β) (p q : List α) :
    g '' {e | e ∈ p ∨ e ∈ q} = {a | a ∈ p.map g ∨ a ∈ q.map g} := by
  ext a
  simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨e, he | he, rfl⟩
    · exact Or.inl ⟨e, he, rfl⟩
    · exact Or.inr ⟨e, he, rfl⟩
  · rintro (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact ⟨e, Or.inl he, rfl⟩
    · exact ⟨e, Or.inr he, rfl⟩

/-- The elements of `c` are those whose first index in `c ++ d` is below the length of `c`. -/
theorem mem_iff_idxOf_append_lt_length {E : Type*} {a : E} {c d : List E} : a ∈ c ↔ (c ++ d).idxOf a < c.length := by
  constructor
  · intro h
    rw [List.idxOf_append_of_mem h]
    exact List.idxOf_lt_length_iff.2 h
  · intro h
    by_contra hc
    rw [List.idxOf_append_of_notMem hc] at h
    omega

theorem sum_map_le_length_mul {β : Type*} {l : List β} {g : β → ℕ} {c : ℕ} (h : ∀ b ∈ l, g b ≤ c) : (l.map g).sum ≤ l.length * c := by
  have := List.sum_le_length_nsmul (l.map g) c (by simpa using h)
  simpa using this

theorem length_filter_le_length_filter {β : Type*} {l : List β} {p q : β → Bool} (hpq : ∀ x ∈ l, p x = true → q x = true) : (l.filter p).length ≤ (l.filter q).length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih fun x hx => hpq x (List.mem_cons_of_mem _ hx)
    have ha := hpq a List.mem_cons_self
    simp only [List.filter_cons]
    by_cases hp : p a = true
    · simp [hp, ha hp]
      omega
    · by_cases hq : q a = true
      · simp [hp, hq]
        omega
      · simp [hp, hq]
        omega

theorem length_filter_lt_length_filter {β : Type*} {l : List β} {p q : β → Bool} (hpq : ∀ x ∈ l, p x = true → q x = true) (h : ∃ x ∈ l, q x = true ∧ p x = false) : (l.filter p).length < (l.filter q).length := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    have hle := length_filter_le_length_filter (l := t) fun x hx => hpq x (List.mem_cons_of_mem _ hx)
    have ha := hpq a List.mem_cons_self
    obtain ⟨x, hx, hqx, hpx⟩ := h
    simp only [List.filter_cons]
    rcases List.mem_cons.1 hx with rfl | hx'
    · simp [hqx, hpx]
      omega
    · have hlt := ih (fun y hy => hpq y (List.mem_cons_of_mem _ hy)) ⟨x, hx', hqx, hpx⟩
      by_cases hp : p a = true
      · simp [hp, ha hp]
        omega
      · by_cases hq : q a = true
        · simp [hp, hq]
          omega
        · simp [hp, hq]
          omega

/-- The events of `eventVector` before `k`. -/
theorem sum_range_countP_snd_sub_one_eq (F : List (ℕ × ℕ)) (hF : ∀ p ∈ F, 1 ≤ p.2) (k : ℕ) :
    ∑ l ∈ Finset.range k, F.countP (fun p => decide (p.2 - 1 = l)) = F.countP fun p => decide (p.2 ≤ k) := by
  induction F with
  | nil => simp
  | cons a F ih =>
    have ih' := ih fun p hp => hF p (List.mem_cons_of_mem _ hp)
    have ha := hF a List.mem_cons_self
    simp only [List.countP_cons, Finset.sum_add_distrib, ih', add_right_inj]
    have hsum : ∑ l ∈ Finset.range k, (if decide (a.2 - 1 = l) = true then 1 else 0) = if a.2 - 1 ∈ Finset.range k then 1 else 0 := by
      simp only [decide_eq_true_eq]
      exact Finset.sum_ite_eq (Finset.range k) (a.2 - 1) fun _ => 1
    rw [hsum]
    simp only [Finset.mem_range, decide_eq_true_eq]
    congr 1
    apply propext
    omega

end List
