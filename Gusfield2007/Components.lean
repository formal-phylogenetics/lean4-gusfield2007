module

public import Gusfield2007.ExplicitNetworks
public import Gusfield2007.LabelSearch
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Order.Hom.Set
public import Gusfield2007.Basic.Combinatorics.SimpleGraph.Connectivity

/-!
# Gusfield et al. 2007: bookkeeping for the numbers of the figures

The matrix `M(C)` on the sites `↥C` as a matrix on `Fin k`, a sum over two connected components, and `R` from a network and a search.
-/

@[expose] public section

open scoped Classical

namespace Gusfield2007

section Transport

variable {ι : Type} [LinearOrder ι] {k : ℕ}

/-- The sites of `C`, from an increasing list of them. -/
noncomputable def sitesIso (f : Fin k → ι) (hf : StrictMono f) {C : Set ι} (hC : Set.range f = C) : Fin k ≃o C :=
  (hf.orderIso f).trans (Set.orderIsoOfEq _ _ hC)

theorem sitesIso_apply_coe (f : Fin k → ι) (hf : StrictMono f) {C : Set ι} (hC : Set.range f = C) (a : Fin k) :
    ((sitesIso f hf hC a : C) : ι) = f a := by
  subst hC
  rfl

theorem sitesIso_symm_apply (f : Fin k → ι) (hf : StrictMono f) {C : Set ι} (hC : Set.range f = C) (x : C) :
    f ((sitesIso f hf hC).symm x) = x := by
  rw [← sitesIso_apply_coe f hf hC, OrderIso.apply_symm_apply]

theorem restrictRows_eq_image (f : Fin k → ι) (hf : StrictMono f) {C : Set ι} (hC : Set.range f = C) (M : Finset (ι → Bool)) :
    restrictRows C M = (M.image fun r => r ∘ f).image fun r => r ∘ (sitesIso f hf hC).symm := by
  rw [Finset.image_image]
  refine Finset.image_congr fun r _ => ?_
  funext x
  simp [Set.domRestrict, sitesIso_symm_apply]

/-- `M(C)`, with the sites of `C` numbered in their order. -/
theorem R_restrictRows (f : Fin k → ι) (hf : StrictMono f) {C : Set ι} (hC : Set.range f = C) (c : Crossover) (M : Finset (ι → Bool)) :
    R c (restrictRows C M) = R c (M.image fun r => r ∘ f) := by
  rw [restrictRows_eq_image f hf hC, R_map_orderIso]

/-- `M(C)`, with the sites of `C` numbered in their order, and the ancestral sequence `S(C)`. -/
theorem RS_restrictRows (f : Fin k → ι) (hf : StrictMono f) {C : Set ι} (hC : Set.range f = C) (c : Crossover) (S : ι → Bool) (M : Finset (ι → Bool)) :
    RS c (C.domRestrict S) (restrictRows C M) = RS c (S ∘ f) (M.image fun r => r ∘ f) := by
  rw [restrictRows_eq_image f hf hC, ← RS_map_orderIso (sitesIso f hf hC) c (S ∘ f) (M.image fun r => r ∘ f)]
  congr 1
  funext x
  simp [Set.domRestrict, sitesIso_symm_apply]

end Transport

section TwoComponents

variable {ι : Type*} (G : SimpleGraph ι)

variable {G}

end TwoComponents

section Haplotype

/-- The number of distinct columns, from a set of representatives. -/
theorem distinctColumns_eq {ι : Type*} {M : Finset (ι → Bool)} (s : Finset ι) (h₁ : ∀ i, ∃ j ∈ s, ∀ r ∈ M, r i = r j)
    (h₂ : ∀ i ∈ s, ∀ j ∈ s, (∀ r ∈ M, r i = r j) → i = j) : distinctColumns M = s.card := by
  have hrange : (Set.range fun i : ι => fun r : M => (r : ι → Bool) i) = (fun i : ι => fun r : M => (r : ι → Bool) i) '' (s : Set ι) := by
    ext f
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj, h⟩ := h₁ i
      exact ⟨j, hj, funext fun r => (h r.1 r.2).symm⟩
    · rintro ⟨j, -, rfl⟩
      exact ⟨j, rfl⟩
  have hinj : Set.InjOn (fun i : ι => fun r : M => (r : ι → Bool) i) (s : Set ι) := fun i hi j hj h =>
    h₂ i hi j hj fun r hr => congrFun h ⟨r, hr⟩
  rw [distinctColumns, hrange, hinj.ncard_image, Set.ncard_coe_finset]

/-- `M(C)` has two distinct columns, when each column of `C` in `M` is one of two. -/
theorem distinctColumns_restrictRows_eq_two {ι : Type*} {M : Finset (ι → Bool)} {C : Set ι} {a b : ι} (ha : a ∈ C) (hb : b ∈ C)
    (h₁ : ∀ i ∈ C, (∀ r ∈ M, r i = r a) ∨ ∀ r ∈ M, r i = r b) (h₂ : ¬ ∀ r ∈ M, r a = r b) : distinctColumns (restrictRows C M) = 2 := by
  have hne : (⟨a, ha⟩ : C) ≠ ⟨b, hb⟩ := fun h => h₂ fun r _ => by rw [Subtype.mk.inj h]
  have hcol : ∀ i j : C, (∀ r ∈ M, r i.1 = r j.1) → ∀ r ∈ restrictRows C M, r i = r j := fun i j h r hr => by
    obtain ⟨r', hr', rfl⟩ := mem_restrictRows.1 hr
    exact h r' hr'
  rw [distinctColumns_eq {⟨a, ha⟩, ⟨b, hb⟩} ?_ ?_, Finset.card_pair hne]
  · intro i
    rcases h₁ i.1 i.2 with h | h
    · exact ⟨⟨a, ha⟩, by simp, hcol i _ h⟩
    · exact ⟨⟨b, hb⟩, by simp, hcol i _ h⟩
  · intro i hi j hj h
    by_contra hij
    have hij' : (i = ⟨a, ha⟩ ∧ j = ⟨b, hb⟩) ∨ (i = ⟨b, hb⟩ ∧ j = ⟨a, ha⟩) := by
      rw [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all
    have hab : ∀ r ∈ M, r a = r b := fun r hr => by
      have := h _ (mem_restrictRows.2 ⟨r, hr, rfl⟩)
      rcases hij' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact this
      · exact this.symm
    exact h₂ hab

/-- `M(C)` has as many rows as the matrix with the sites of `C` numbered in their order. -/
theorem card_restrictRows {ι : Type} [LinearOrder ι] {k : ℕ} (f : Fin k → ι) (hf : StrictMono f) {C : Set ι} (hC : Set.range f = C) (M : Finset (ι → Bool)) :
    (restrictRows C M).card = (M.image fun r => r ∘ f).card := by
  rw [restrictRows_eq_image f hf hC]
  exact Finset.card_image_of_injective _ fun r r' h => (sitesIso f hf hC).symm.surjective.injective_comp_right h

end Haplotype

section Numbers

variable {m a b : ℕ} [NeZero a] [NeZero b] {s : NetSpec m a b} {M : Finset (Fin m → Bool)} {c : Crossover} {k : ℕ}

/-- A lower bound on `R` for any model, from a search and the existence of a network in the model. -/
theorem lt_R_of_check {M : Finset (Fin m → Bool)} {Mc : List ℕ} {c : Crossover} {k : ℕ}
    (hne : ∃ (a b : ℕ) (N : Network (Fin m) (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M) (hMc : CodesOf M Mc)
    (hch : LabelSearch.check m Mc k = false) : k < R c M := by
  have hset : {n | ∃ (a b : ℕ) (N : Network (Fin m) (Fin a) (Fin b)), N.Obeys c ∧ N.Derives M ∧ N.recombCount = n}.Nonempty := by
    obtain ⟨a, b, N, h₁, h₂⟩ := hne
    exact ⟨_, a, b, N, h₁, h₂, rfl⟩
  obtain ⟨a, b, N, h₁, h₂, h₃⟩ := Nat.sInf_mem hset
  rw [R, ← h₃]
  exact N.lt_recombCount_of_check h₁ h₂ hMc hch

/-- `R`, from a network and a search. -/
theorem R_eq_of_spec {Mc : List ℕ} (hv : s.Valid) (hd : s.DerivesCheck M) (hc : (NetSpec.toNetwork hv).Obeys c)
    (hr : s.recombs = k + 1) (hMc : CodesOf M Mc) (hch : LabelSearch.check m Mc k = false) : R c M = k + 1 := by
  have h₁ := NetSpec.R_le hv hd hc
  have h₂ := lt_R_of_check ⟨a, b, _, hc, NetSpec.derives_toNetwork hv hd⟩ hMc hch
  omega

end Numbers

end Gusfield2007
