module

public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.Hom.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Lower sets of `Fin m`, and order isomorphisms

A lower set of `Fin m` is an initial segment; rows transported along an order isomorphism and back.
-/

@[expose] public section

open scoped Classical

namespace Fin

/-- A lower set of `Fin m` is `{i | i < n}` for some `n ≤ m`. -/
theorem exists_le_forall_mem_lowerSet_iff_lt {m : ℕ} (L₀ : LowerSet (Fin m)) : ∃ n, n ≤ m ∧ ∀ i : Fin m, i ∈ L₀ ↔ i.val < n := by
  by_cases hall : ∀ i : Fin m, i ∈ L₀
  · exact ⟨m, le_rfl, fun i => ⟨fun _ => i.2, fun _ => hall i⟩⟩
  · push Not at hall
    obtain ⟨i₀, hi₀⟩ := hall
    have hex : ∃ k, ∃ i : Fin m, i.val = k ∧ i ∉ L₀ := ⟨i₀.val, i₀, rfl, hi₀⟩
    refine ⟨Nat.find hex, ?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · obtain ⟨i, hi, -⟩ := Nat.find_spec hex
      rw [← hi]
      exact i.2.le
    · by_contra hge
      push Not at hge
      obtain ⟨j, hj, hjL⟩ := Nat.find_spec hex
      exact hjL (L₀.lower (show j ≤ i from by rw [Fin.le_def, hj]; exact hge) hi)
    · by_contra hiL
      exact Nat.find_min hex hi ⟨i, rfl, hiL⟩

/-- A lower set of `Fin S` is an initial segment `{a | a < c}`. -/
theorem exists_forall_mem_lowerSet_iff_lt {S : ℕ} (L : LowerSet (Fin S)) : ∃ c : ℕ, ∀ a : Fin S, a ∈ L ↔ a.val < c := by
  classical
  refine ⟨(Finset.univ.filter (· ∈ L)).sup fun a => a.val + 1, fun a => ⟨fun ha => ?_, fun ha => ?_⟩⟩
  · exact Nat.lt_of_succ_le (Finset.le_sup (f := fun a : Fin S => a.val + 1) (Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩))
  · by_contra hna
    have hle : (Finset.univ.filter (· ∈ L)).sup (fun a : Fin S => a.val + 1) ≤ a.val := by
      refine Finset.sup_le fun b hb => ?_
      have hbL : b ∈ L := (Finset.mem_filter.1 hb).2
      by_contra hc
      exact hna (L.lower (Fin.le_def.2 (by omega)) hbL)
    omega

/-- A lower set of `Fin m` is an initial segment. -/
theorem exists_fin_forall_mem_lowerSet_iff_lt {m : ℕ} (L : LowerSet (Fin m)) : ∃ n : Fin (m + 1), ∀ i : Fin m, i ∈ L ↔ i.val < n.val := by
  by_cases hall : ∀ i : Fin m, i ∈ L
  · exact ⟨⟨m, Nat.lt_succ_self m⟩, fun i => ⟨fun _ => i.2, fun _ => hall i⟩⟩
  · push Not at hall
    have hex : ∃ k, ∃ h : k < m, (⟨k, h⟩ : Fin m) ∉ L := by
      obtain ⟨i, hi⟩ := hall
      exact ⟨i.val, i.2, hi⟩
    obtain ⟨hk, hnot⟩ := Nat.find_spec hex
    refine ⟨⟨Nat.find hex, Nat.lt_succ_of_lt hk⟩, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · by_contra hlt
      exact hnot (L.lower (show (⟨Nat.find hex, hk⟩ : Fin m) ≤ i from not_lt.1 hlt) hi)
    · by_contra hi'
      exact Nat.find_min hex hi ⟨i.2, hi'⟩

end Fin

namespace OrderIso

theorem comp_symm_comp {ι : Type*} [LinearOrder ι] {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') (r : ι → Bool) : (r ∘ e.symm) ∘ e = r :=
  funext fun i => by simp

/-- `(M.image (· ∘ e.symm)).image (· ∘ e) = M`. -/
theorem image_comp_image_comp_symm {ι : Type*} [LinearOrder ι] {ι' : Type*} [LinearOrder ι'] (e : ι ≃o ι') (M : Finset (ι → Bool)) :
    (M.image fun r => r ∘ e.symm).image (fun r => r ∘ e) = M := by
  ext r
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    rwa [comp_symm_comp]
  · exact fun hr => ⟨r ∘ e.symm, ⟨r, hr, rfl⟩, comp_symm_comp e r⟩

theorem eq_symm_iff_val_eq {κ : Type*} [LinearOrder κ] {n : ℕ} (e : κ ≃o Fin (n + 1)) {l : Fin (n + 1)} {i : κ} : i = e.symm l ↔ (e i).1 = l.1 := by
  constructor
  · rintro rfl
    simp
  · intro h
    have : e i = l := Fin.ext h
    rw [← this]
    simp

end OrderIso
