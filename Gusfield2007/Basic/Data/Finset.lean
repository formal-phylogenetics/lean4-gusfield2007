module

public import Mathlib.Data.Finset.Image
public import Mathlib.Logic.Equiv.Finset
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite sets: images, transport along an equivalence, sums over intervals

Facts about `Finset.image` with two decidability instances, about `Equiv.finsetCongr`, and a shift of the interval of a sum.
-/

@[expose] public section

open scoped Classical

namespace Finset

open Finset

/-- `Finset.image_subset_image` with two instances. -/
theorem image_subset_image_of_decidableEq {α β : Type*} (i₁ i₂ : DecidableEq β) (f : α → β) {M A : Finset α} (h : M ⊆ A) :
    @Finset.image _ _ i₁ f M ⊆ @Finset.image _ _ i₂ f A := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := (@Finset.mem_image _ _ i₁ _ _ _).1 hr
  exact (@Finset.mem_image _ _ i₂ _ _ _).2 ⟨x, h hx, rfl⟩

end Finset

namespace Equiv

theorem finsetCongr_symm_union {X Y : Type*} [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (A B : Finset Y) : (Equiv.finsetCongr e).symm (A ∪ B) = (Equiv.finsetCongr e).symm A ∪ (Equiv.finsetCongr e).symm B := by
  simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_union]

theorem finsetCongr_symm_sdiff {X Y : Type*} [DecidableEq X] [DecidableEq Y] (e : X ≃ Y) (A B : Finset Y) : (Equiv.finsetCongr e).symm (A \ B) = (Equiv.finsetCongr e).symm A \ (Equiv.finsetCongr e).symm B := by
  simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, Finset.map_sdiff]

theorem card_finsetCongr_symm {X Y : Type*} (e : X ≃ Y) (A : Finset Y) : ((Equiv.finsetCongr e).symm A).card = A.card := by
  simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply]

theorem finsetCongr_symm_subset_iff {X Y : Type*} (e : X ≃ Y) (A B : Finset Y) : (Equiv.finsetCongr e).symm A ⊆ (Equiv.finsetCongr e).symm B ↔ A ⊆ B := by
  simp [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply]

end Equiv

namespace Finset

open Finset

theorem sum_Ico_add_add (r : ℕ → ℕ) (s p q : ℕ) : ∑ l ∈ Ico (s + p) (s + q), r l = ∑ l ∈ Ico p q, r (s + l) := by
  rw [sum_Ico_add r p q s, add_comm s p, add_comm s q]

end Finset
