module

public import Gusfield2007.External.GusfieldEtAl2004.Build
public import Gusfield2007.GalledTreeDecide
public import Gusfield2007.Structure

/-!
# Gusfield, Eddhu, Langley 2004: what the algorithm returns is a reduced galled tree

The correctness of `galledBuild` (`External.GusfieldEtAl2004.Algorithm.galledBuild_correct`): the network `gNet` that its
table describes derives `M`, has single crossovers and is a reduced galled tree. The proof uses the paper's dominant classes
(line 212, `Gusfield2007.exists_isDominantFor`) for the laminar structure of the labels, so it is in the paper's library;
the algorithm and its count of operations are in `Gusfield2007/External/GusfieldEtAl2004/`.
-/

@[expose] public section

namespace External.GusfieldEtAl2004.Algorithm

variable {m : ℕ}

section Core

variable (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (ar : Fin m → Arr m)

end Core

/-! ### The clusters are nested or disjoint -/

section Laminar

open scoped Classical

open Gusfield2007 Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)} {f : Fin m → Fin m}

/-- **The two components** (Theorem 2 of Gusfield et al. 2007, for `M + S`): the rows off the ancestral sequence on two components are disjoint, or those of one are all at one sequence of the other. -/
theorem trichotomy (hf : IsLab S M f) {k₀ k₀' : Fin m} (hne : f k₀ ≠ f k₀') :
    (∀ r ∈ M, mkRow S f (f k₀) r = S ∨ mkRow S f (f k₀') r = S) ∨ (∃ σ, σ ≠ S ∧ ∀ r ∈ M, mkRow S f (f k₀') r ≠ S → mkRow S f (f k₀) r = σ) ∨ (∃ σ', σ' ≠ S ∧ ∀ r ∈ M, mkRow S f (f k₀) r ≠ S → mkRow S f (f k₀') r = σ') := by
  set G := incompatGraph (addRow M.toFinset S) with hG
  have hmem : ∀ {k k' : Fin m}, f k = f k' ↔ k ∈ (G.connectedComponentMk k').supp := fun {k k'} =>
    (hf k k').trans (SimpleGraph.ConnectedComponent.eq (G := G)).symm
  have hc : G.connectedComponentMk k₀ ≠ G.connectedComponentMk k₀' := fun h => hne ((hf _ _).2 (SimpleGraph.ConnectedComponent.exact h))
  obtain ⟨d, d', hdom⟩ := exists_isDominantFor (addRow M.toFinset S) hc
  have hS : S ∈ addRow M.toFinset S := mem_addRow.2 (Or.inl rfl)
  have hrow : ∀ {r}, r ∈ M → r ∈ addRow M.toFinset S := fun hr => mem_addRow.2 (Or.inr (List.mem_toFinset.2 hr))
  by_cases h₁ : ∀ i (hi : f i = f k₀), S i = d ⟨i, hmem.1 hi⟩
  · by_cases h₂ : ∀ i (hi : f i = f k₀'), S i = d' ⟨i, hmem.1 hi⟩
    · refine Or.inl fun r hr => ?_
      by_contra hno
      push Not at hno
      obtain ⟨i, hi, hri⟩ := mk_ne_iff.1 hno.1
      obtain ⟨i', hi', hri'⟩ := mk_ne_iff.1 hno.2
      rcases hdom ⟨i, hmem.1 hi⟩ ⟨i', hmem.1 hi'⟩ r (hrow hr) with h | h
      · exact hri (h.trans (h₁ i hi).symm)
      · exact hri' (h.trans (h₂ i' hi').symm)
    · -- the ancestral sequence isn't dominant on the second
      push Not at h₂
      obtain ⟨i', hi', hne'⟩ := h₂
      refine Or.inr (Or.inr ⟨fun j => if hj : f j = f k₀' then d' ⟨j, hmem.1 hj⟩ else S j, fun h => hne' ?_, fun r hr hrne => ?_⟩)
      · have := congrFun h i'
        simp only [hi', ↓reduceDIte] at this
        exact this.symm
      · funext j
        by_cases hj : f j = f k₀'
        · obtain ⟨i, hi, hri⟩ := mk_ne_iff.1 hrne
          simp only [mkRow, hj, ite_true, ↓reduceDIte]
          rcases hdom ⟨i, hmem.1 hi⟩ ⟨j, hmem.1 hj⟩ r (hrow hr) with h | h
          · exact absurd (h.trans (h₁ i hi).symm) hri
          · exact h
        · simp [mkRow, hj]
  · push Not at h₁
    obtain ⟨i₁, hi₁, hne₁⟩ := h₁
    refine Or.inr (Or.inl ⟨fun j => if hj : f j = f k₀ then d ⟨j, hmem.1 hj⟩ else S j, fun h => hne₁ ?_, fun r hr hrne => ?_⟩)
    · have := congrFun h i₁
      simp only [hi₁, ↓reduceDIte] at this
      exact this.symm
    · funext j
      by_cases hj : f j = f k₀
      · obtain ⟨i', hi', hri'⟩ := mk_ne_iff.1 hrne
        simp only [mkRow, hj, ite_true, ↓reduceDIte]
        rcases hdom ⟨j, hmem.1 hj⟩ ⟨i', hmem.1 hi'⟩ r (hrow hr) with h | h
        · exact h
        · -- the second is dominated by the ancestral sequence, which isn't dominant on the first
          have hSd := hdom ⟨i₁, hmem.1 hi₁⟩ ⟨i', hmem.1 hi'⟩ S hS
          rcases hSd with h' | h'
          · exact absurd h' hne₁
          · exact absurd (h.trans h'.symm) hri'
      · simp [mkRow, hj]

variable {u v w : GNode m}

/-- `trichotomy` for labels of components. -/
theorem Std.tri (hs : Std S M f) {c c' : Fin m} (hc : ∃ k, f k = c) (hc' : ∃ k, f k = c') (hne : c ≠ c') :
    (∀ r ∈ M, mkRow S f c r = S ∨ mkRow S f c' r = S) ∨ (∃ σ, σ ≠ S ∧ ∀ r ∈ M, mkRow S f c' r ≠ S → mkRow S f c r = σ) ∨ (∃ σ', σ' ≠ S ∧ ∀ r ∈ M, mkRow S f c r ≠ S → mkRow S f c' r = σ') := by
  obtain ⟨k, rfl⟩ := hc
  obtain ⟨k', rfl⟩ := hc'
  exact trichotomy hs.lab hne

/-- **Nested or disjoint**: the clusters of two nodes. -/
theorem Std.laminar (hs : Std S M f) (hu : Valid S M f u) (hv : Valid S M f v) (r : Row m) (hr : r ∈ M) (h₁ : u.cl S f r = true) (h₂ : v.cl S f r = true) : SubCl S M f u v ∨ SubCl S M f v u := by
  have hroot : ∀ {x : GNode m}, SubCl S M f x .root := fun _ _ _ => rfl
  have hleaf : ∀ {x : GNode m} {ρ : Row m}, x.cl S f ρ = true → SubCl S M f (.leaf ρ) x := by
    intro x ρ hx r' _ h'
    rw [cl_leaf.1 h']
    exact hx
  have hsame : ∀ {c : Fin m} {σ : Row m}, (mkRow S f c r = σ) → σ ≠ S → SubCl S M f (.part c σ) (.top c) := by
    intro c σ _ hσ r' _ h'
    rw [cl_top, cl_part.1 h']
    exact hσ
  cases u with
  | root => exact Or.inr hroot
  | leaf ρ => exact Or.inl (hleaf (by rwa [← cl_leaf.1 h₁]))
  | top c =>
    cases v with
    | root => exact Or.inl hroot
    | leaf ρ => exact Or.inr (hleaf (by rwa [← cl_leaf.1 h₂]))
    | top c' =>
      by_cases hcc : c = c'
      · subst hcc
        exact Or.inl fun _ _ h => h
      rcases hs.tri hu hv hcc with h | ⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩
      · rcases h r hr with h' | h'
        · exact absurd h' (cl_top.1 h₁)
        · exact absurd h' (cl_top.1 h₂)
      · exact Or.inr fun r' hr' h' => cl_top.2 (by rw [h r' hr' (cl_top.1 h')]; exact hσ)
      · exact Or.inl fun r' hr' h' => cl_top.2 (by rw [h r' hr' (cl_top.1 h')]; exact hσ)
    | part c' τ =>
      by_cases hcc : c = c'
      · subst hcc
        exact Or.inr (hsame (cl_part.1 h₂) (mem_rowsOf.1 hv.2).2)
      rcases hs.tri hu (exists_of_isNT hv.1) hcc with h | ⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩
      · rcases h r hr with h' | h'
        · exact absurd h' (cl_top.1 h₁)
        · exact absurd (h'.symm.trans (cl_part.1 h₂)) (mem_rowsOf.1 hv.2).2.symm
      · refine Or.inr fun r' hr' h' => cl_top.2 ?_
        have hne : mkRow S f c' r' ≠ S := by
          rw [cl_part.1 h']
          exact (mem_rowsOf.1 hv.2).2
        rw [h r' hr' hne]
        exact hσ
      · refine Or.inl fun r' hr' h' => cl_part.2 ?_
        rw [h r' hr' (cl_top.1 h'), ← h r hr (cl_top.1 h₁)]
        exact cl_part.1 h₂
  | part c σ =>
    have hmemσ := mem_rowsOf.1 hu.2
    cases v with
    | root => exact Or.inl hroot
    | leaf ρ => exact Or.inr (hleaf (by rwa [← cl_leaf.1 h₂]))
    | top c' =>
      by_cases hcc : c = c'
      · subst hcc
        exact Or.inl (hsame (cl_part.1 h₁) hmemσ.2)
      rcases hs.tri (exists_of_isNT hu.1) hv hcc with h | ⟨τ, hτ, h⟩ | ⟨τ, hτ, h⟩
      · rcases h r hr with h' | h'
        · exact absurd (h'.symm.trans (cl_part.1 h₁)) hmemσ.2.symm
        · exact absurd h' (cl_top.1 h₂)
      · refine Or.inr fun r' hr' h' => cl_part.2 ?_
        rw [h r' hr' (cl_top.1 h'), ← h r hr (cl_top.1 h₂)]
        exact cl_part.1 h₁
      · refine Or.inl fun r' hr' h' => cl_top.2 ?_
        have hne : mkRow S f c r' ≠ S := by
          rw [cl_part.1 h']
          exact hmemσ.2
        rw [h r' hr' hne]
        exact hτ
    | part c' τ =>
      have hmemτ := mem_rowsOf.1 hv.2
      by_cases hcc : c = c'
      · subst hcc
        obtain rfl : σ = τ := (cl_part.1 h₁).symm.trans (cl_part.1 h₂)
        exact Or.inl fun _ _ h => h
      rcases hs.tri (exists_of_isNT hu.1) (exists_of_isNT hv.1) hcc with h | ⟨ρ, hρ, h⟩ | ⟨ρ, hρ, h⟩
      · rcases h r hr with h' | h'
        · exact absurd (h'.symm.trans (cl_part.1 h₁)) hmemσ.2.symm
        · exact absurd (h'.symm.trans (cl_part.1 h₂)) hmemτ.2.symm
      · refine Or.inr fun r' hr' h' => cl_part.2 ?_
        have hne : ∀ {r₀}, (GNode.part c' τ).cl S f r₀ = true → mkRow S f c' r₀ ≠ S := fun {r₀} h₀ => by
          rw [cl_part.1 h₀]
          exact hmemτ.2
        rw [h r' hr' (hne h'), ← h r hr (hne h₂)]
        exact cl_part.1 h₁
      · refine Or.inl fun r' hr' h' => cl_part.2 ?_
        have hne : ∀ {r₀}, (GNode.part c σ).cl S f r₀ = true → mkRow S f c r₀ ≠ S := fun {r₀} h₀ => by
          rw [cl_part.1 h₀]
          exact hmemσ.2
        rw [h r' hr' (hne h'), ← h r hr (hne h₁)]
        exact cl_part.1 h₂

/-! ### The order on the nodes -/

/-- Two nodes above a third are in a line. -/
theorem Std.chain (hs : Std S M f) {u u' v : GNode m} (hu : Valid S M f u) (hu' : Valid S M f u') (hv : Valid S M f v) (h : Up S M f u v = true) (h' : Up S M f u' v = true) :
    u = u' ∨ Up S M f u u' = true ∨ Up S M f u' u = true := by
  by_cases hne : u = u'
  · exact Or.inl hne
  obtain ⟨r, hr, hrv⟩ := hs.nonempty_cl hv
  have h₁ := (up_iff.1 h).2.1 r hr hrv
  have h₂ := (up_iff.1 h').2.1 r hr hrv
  right
  rcases hs.laminar hu hu' r hr h₁ h₂ with hsub | hsub
  · by_cases hsub' : SubCl S M f u' u
    · rcases Tie.total hu hu' hne ⟨r, h₁, h₂⟩ with ht | ht
      · exact Or.inl (up_iff.2 ⟨hne, hsub', fun _ => ht⟩)
      · exact Or.inr (up_iff.2 ⟨Ne.symm hne, hsub, fun _ => ht⟩)
    · exact Or.inr (up_iff.2 ⟨Ne.symm hne, hsub, fun h₃ => absurd h₃ hsub'⟩)
  · by_cases hsub' : SubCl S M f u u'
    · rcases Tie.total hu hu' hne ⟨r, h₁, h₂⟩ with ht | ht
      · exact Or.inl (up_iff.2 ⟨hne, hsub, fun _ => ht⟩)
      · exact Or.inr (up_iff.2 ⟨Ne.symm hne, hsub', fun _ => ht⟩)
    · exact Or.inl (up_iff.2 ⟨hne, hsub, fun h₃ => absurd h₃ hsub'⟩)

/-- **The parent by clusters**: the lowest of the nodes above a node. -/
theorem Std.treePar_spec (hs : Std S M f) {v : GNode m} (hv : Valid S M f v) (hne : v ≠ .root) :
    ∃ u, treePar S M f v = some u ∧ Valid S M f u ∧ (∀ ρ, u ≠ .leaf ρ) ∧ Up S M f u v = true ∧ ∀ u', Valid S M f u' → Up S M f u' v = true → u' = u ∨ Up S M f u' u = true := by
  have hrootm : (GNode.root : GNode m) ∈ (cands S M f).filter fun u => Up S M f u v := List.mem_filter.2 ⟨mem_cands_of_valid trivial (by simp), up_root hne⟩
  have hnone : ((cands S M f).filter fun u => Up S M f u v).argmax (key S M f) ≠ none := by
    rw [Ne, List.argmax_eq_none]
    intro h
    rw [h] at hrootm
    simp at hrootm
  obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hnone
  have humem := List.argmax_mem hu
  obtain ⟨huc, huv⟩ := List.mem_filter.1 humem
  have hul : ∀ ρ, u ≠ .leaf ρ := by
    rintro ρ rfl
    rw [hs.not_up_leaf hv] at huv
    exact absurd huv (by simp)
  refine ⟨u, hu, valid_of_mem_cands huc, hul, huv, fun u' hu' h' => ?_⟩
  have hu'l : ∀ ρ, u' ≠ .leaf ρ := by
    rintro ρ rfl
    rw [hs.not_up_leaf hv] at h'
    exact absurd h' (by simp)
  rcases hs.chain hu' (valid_of_mem_cands huc) hv h' huv with h₁ | h₁ | h₁
  · exact Or.inl h₁
  · exact Or.inr h₁
  · have hle := List.le_of_mem_argmax (List.mem_filter.2 ⟨mem_cands_of_valid hu' hu'l, h'⟩) hu
    have hlt := key_lt h₁
    omega

/-! ### The nodes of a gall among the others -/

/-- What is above a node of a gall, off the gall, is above the coalescent node. -/
theorem Std.up_top_of_up_part (hs : Std S M f) {c : Fin m} {σ : Row m} (hc : isNT f c = true) (hσ : σ ∈ rowsOf S M f c) {k : GNode m} (hk : Valid S M f k) (hk₁ : k ≠ .top c) (hk₂ : ∀ τ, k ≠ .part c τ)
    (h : Up S M f k (.part c σ) = true) : Up S M f k (.top c) = true := by
  obtain ⟨-, hsub, htie⟩ := up_iff.1 h
  have hσv : Valid S M f (.part c σ) := ⟨hc, hσ⟩
  obtain ⟨⟨r₀, hr₀, hr₀σ⟩, hσS⟩ := mem_rowsOf.1 hσ
  have hr₀k := hsub r₀ hr₀ (cl_part.2 hr₀σ)
  have hrc : mkRow S f c r₀ ≠ S := by rw [hr₀σ]; exact hσS
  refine up_iff.2 ⟨hk₁, ?_, ?_⟩
  · cases k with
    | root => exact fun _ _ _ => rfl
    | leaf ρ => exact absurd h (by rw [hs.not_up_leaf hσv]; simp)
    | top c' =>
      have hcc : c ≠ c' := fun h' => hk₁ (by rw [h'])
      rcases hs.tri (exists_of_isNT hc) hk hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', hσ', h'⟩
      · exfalso
        rcases h' r₀ hr₀ with h₁ | h₁
        · exact hrc h₁
        · exact cl_top.1 hr₀k h₁
      · exfalso
        have hσ₁ : σ = σ₁ := hr₀σ.symm.trans (h' r₀ hr₀ (cl_top.1 hr₀k))
        exact not_tie_top (by simp [GNode.rank]) (htie fun r hr hrk => cl_part.2 ((h' r hr (cl_top.1 hrk)).trans hσ₁.symm))
      · exact fun r hr hrt => cl_top.2 (by rw [h' r hr (cl_top.1 hrt)]; exact hσ')
    | part c' τ =>
      have hcc : c ≠ c' := by
        rintro rfl
        exact hk₂ τ rfl
      have hτS := (mem_rowsOf.1 hk.2).2
      rcases hs.tri (exists_of_isNT hc) (exists_of_isNT hk.1) hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', -, h'⟩
      · exfalso
        rcases h' r₀ hr₀ with h₁ | h₁
        · exact hrc h₁
        · exact hτS ((cl_part.1 hr₀k).symm.trans h₁)
      · exfalso
        obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hk.1
        have hσ₁ : σ = σ₁ := hr₀σ.symm.trans (h' r₀ hr₀ (by rw [cl_part.1 hr₀k]; exact hτS))
        have hin : ∀ {x}, x ∈ M → mkRow S f c' x ≠ S → mkRow S f c' x = τ := fun {x} hx hxn =>
          cl_part.1 (hsub x hx (cl_part.2 ((h' x hx hxn).trans hσ₁.symm)))
        exact h₅ ((hin hr h₃).trans (hin hr' h₄).symm)
      · have hτ : τ = σ' := (cl_part.1 hr₀k).symm.trans (h' r₀ hr₀ hrc)
        exact fun r hr hrt => cl_part.2 ((h' r hr (cl_top.1 hrt)).trans hτ.symm)
  · intro hsub'
    cases k with
    | root => exact Or.inl (by simp only [GNode.rank, hc, ite_true]; omega)
    | leaf ρ => exact absurd h (by rw [hs.not_up_leaf hσv]; simp)
    | part c' τ => exact Or.inl (by simp only [GNode.rank, hc, ite_true]; omega)
    | top c' =>
      have hcc : c ≠ c' := fun h' => hk₁ (by rw [h'])
      refine Or.inl ?_
      simp only [GNode.rank, hc, ite_true]
      by_cases hc' : isNT f c' = true
      · exfalso
        obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hc'
        rcases hs.tri (exists_of_isNT hc) hk hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', -, h'⟩
        · rcases h' r₀ hr₀ with h₁ | h₁
          · exact hrc h₁
          · exact cl_top.1 hr₀k h₁
        · have hσ₁ : σ = σ₁ := hr₀σ.symm.trans (h' r₀ hr₀ (cl_top.1 hr₀k))
          have hin : ∀ {x}, x ∈ M → mkRow S f c' x ≠ S → mkRow S f c x = σ₁ := fun {x} hx hxn => h' x hx hxn
          exact not_tie_top (by simp [GNode.rank]) (htie fun x hx hxk => cl_part.2 ((hin hx (cl_top.1 hxk)).trans hσ₁.symm))
        · exact h₅ ((h' r hr (cl_top.1 (hsub' r hr (cl_top.2 h₃)))).trans (h' r' hr' (cl_top.1 (hsub' r' hr' (cl_top.2 h₄)))).symm)
      · simp [hc']

/-- A coalescent node above a node off its gall has a node of the gall above that node too: the rows of the node are at one sequence of the component. -/
theorem Std.exists_part_of_up_top (hs : Std S M f) {c : Fin m} (hc : isNT f c = true) {v : GNode m} (hv : Valid S M f v) (hv₁ : v ≠ .top c) (hv₂ : ∀ τ, v ≠ .part c τ)
    (h : Up S M f (.top c) v = true) : ∃ τ ∈ rowsOf S M f c, Up S M f (.part c τ) v = true := by
  obtain ⟨-, hsub, htie⟩ := up_iff.1 h
  obtain ⟨r₀, hr₀, hr₀v⟩ := hs.nonempty_cl hv
  have hr₀c : mkRow S f c r₀ ≠ S := cl_top.1 (hsub r₀ hr₀ hr₀v)
  have hτ : mkRow S f c r₀ ∈ rowsOf S M f c := mem_rowsOf.2 ⟨⟨r₀, hr₀, rfl⟩, hr₀c⟩
  refine ⟨_, hτ, ?_⟩
  cases v with
  | root =>
    exact absurd (htie fun _ _ _ => rfl) (not_tie_top (by simp [GNode.rank]))
  | leaf ρ =>
    obtain rfl := cl_leaf.1 hr₀v
    refine up_iff.2 ⟨by simp, fun r _ h' => ?_, fun _ => Or.inl (by simp [GNode.rank])⟩
    rw [cl_leaf.1 h']
    exact cl_part.2 rfl
  | top c₂ =>
    have hcc : c₂ ≠ c := fun h' => hv₁ (by rw [h'])
    rcases hs.tri hv (exists_of_isNT hc) hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', -, h'⟩
    · exfalso
      rcases h' r₀ hr₀ with h₁ | h₁
      · exact cl_top.1 hr₀v h₁
      · exact hr₀c h₁
    · exfalso
      have hsub₂ : SubCl S M f (.top c) (.top c₂) := fun r hr hrt => cl_top.2 (by
        rw [h' r hr (cl_top.1 hrt), ← h' r₀ hr₀ hr₀c]
        exact cl_top.1 hr₀v)
      by_cases hc₂ : isNT f c₂ = true
      · obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hc₂
        exact h₅ ((h' r hr (cl_top.1 (hsub r hr (cl_top.2 h₃)))).trans (h' r' hr' (cl_top.1 (hsub r' hr' (cl_top.2 h₄)))).symm)
      · have ht := htie hsub₂
        have hr₁ : (GNode.top c : GNode m).rank f = 3 := by simp [GNode.rank, hc]
        have hr₂ : (GNode.top c₂ : GNode m).rank f = 2 := by simp [GNode.rank, hc₂]
        unfold Tie at ht
        rw [hr₁, hr₂] at ht
        omega
    · have hτ' : mkRow S f c r₀ = σ' := h' r₀ hr₀ (cl_top.1 hr₀v)
      refine up_iff.2 ⟨by simp, fun r hr hrt => cl_part.2 ((h' r hr (cl_top.1 hrt)).trans hτ'.symm), fun _ => Or.inl ?_⟩
      have := rank_top_ge (f := f) (c := c₂)
      simp only [GNode.rank] at this ⊢
      omega
  | part c₂ σ₂ =>
    have hcc : c₂ ≠ c := by
      rintro rfl
      exact hv₂ σ₂ rfl
    have hσ₂S := (mem_rowsOf.1 hv.2).2
    have hne₂ : ∀ {x}, (GNode.part c₂ σ₂).cl S f x = true → mkRow S f c₂ x ≠ S := fun {x} hx => by
      rw [cl_part.1 hx]
      exact hσ₂S
    rcases hs.tri (exists_of_isNT hv.1) (exists_of_isNT hc) hcc with h' | ⟨σ₁, -, h'⟩ | ⟨σ', -, h'⟩
    · exfalso
      rcases h' r₀ hr₀ with h₁ | h₁
      · exact hne₂ hr₀v h₁
      · exact hr₀c h₁
    · exfalso
      have hσ₁ : σ₂ = σ₁ := (cl_part.1 hr₀v).symm.trans (h' r₀ hr₀ hr₀c)
      exact not_tie_top (by simp [GNode.rank]) (htie fun r hr hrt => cl_part.2 ((h' r hr (cl_top.1 hrt)).trans hσ₁.symm))
    · have hτ' : mkRow S f c r₀ = σ' := h' r₀ hr₀ (hne₂ hr₀v)
      refine up_iff.2 ⟨by
        intro h₀
        exact hcc ((GNode.part.inj h₀).1.symm), fun r hr hrt => cl_part.2 ((h' r hr (hne₂ hrt)).trans hτ'.symm), fun hsub₂ => ?_⟩
      exfalso
      obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hv.1
      have hin : ∀ {x}, x ∈ M → mkRow S f c₂ x ≠ S → mkRow S f c₂ x = σ₂ := fun {x} hx hxn => cl_part.1 (hsub₂ x hx (cl_part.2 ((h' x hx hxn).trans hτ'.symm)))
      exact h₅ ((hin hr h₃).trans (hin hr' h₄).symm)

/-! ### Chains -/

section Labels

variable (hs : Std S M f)

include hs

/-- **On the other components, a node of a gall has the labels of its coalescent node** (Lemma 2.1 of the source). -/
theorem Std.label_part_off {c : Fin m} (hc : isNT f c = true) {σ : Row m} (hσ : σ ∈ rowsOf S M f c) {i : Fin m} (hi : f i ≠ c) : label S M f (.part c σ) i = label S M f (.top c) i := by
  have hvp : Valid S M f (.part c σ) := ⟨hc, hσ⟩
  have hvt : Valid S M f (.top c) := exists_of_isNT hc
  have htp := hs.top_up_part hc hσ
  have hvo : ∀ σ', (GNode.part c σ : GNode m) ≠ .part (f i) σ' := fun σ' h => hi (GNode.part.inj h).1.symm
  by_cases hc₁ : isNT f (f i) = true
  · by_cases hex : ∃ τ ∈ rowsOf S M f (f i), Up S M f (.part (f i) τ) (.top c) = true
    · obtain ⟨τ, hτ, hup⟩ := hex
      rw [hs.label_of_up hc₁ hτ hvp hvo (up_trans hup htp), hs.label_of_up hc₁ hτ hvt (by simp) hup]
    · push Not at hex
      rw [label_of_not hc₁ hvo fun τ hτ => ?_, label_of_not hc₁ (by simp) fun τ hτ => by simpa using hex τ hτ]
      refine Bool.eq_false_iff.2 fun h => hex τ hτ ?_
      refine hs.up_top_of_up_part hc hσ (show Valid S M f (.part (f i) τ) from ⟨hc₁, hτ⟩) (by simp) (fun τ' h' => hi (GNode.part.inj h').1) h
  · rw [label_trivial hc₁, label_trivial hc₁]
    have hk : Valid S M f (.top (f i)) := ⟨i, rfl⟩
    have hiff : Up S M f (.top (f i)) (.part c σ) = true ↔ Up S M f (.top (f i)) (.top c) = true :=
      ⟨fun h => hs.up_top_of_up_part hc hσ hk (by simp [hi]) (by simp) h, fun h => up_trans h htp⟩
    have h₁ : (GNode.part c σ : GNode m) ≠ .top (f i) := by simp
    have h₂ : (GNode.top c : GNode m) ≠ .top (f i) := by simpa using Ne.symm hi
    simp only [h₁, h₂, false_or, hiff]

end Labels

/-! ### The network -/

section Net

variable {ar : Fin m → Arr m} (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c))

include hs har

/-- The parent of a node is a node. -/
theorem par_valid {v u : GNode m} (hv : Valid S M f v) (h : par S M f ar v = some u) : Valid S M f u := by
  cases v with
  | root => simp [par] at h
  | top c =>
    obtain ⟨u', hu', hv', -⟩ := hs.treePar_spec hv (by simp)
    have : treePar S M f (.top c) = some u := h
    rw [hu'] at this
    rwa [← Option.some.inj this]
  | leaf ρ =>
    obtain ⟨u', hu', hv', -⟩ := hs.treePar_spec hv (by simp)
    have : treePar S M f (.leaf ρ) = some u := h
    rw [hu'] at this
    rwa [← Option.some.inj this]
  | part c σ =>
    have hA := har c hv.1
    simp only [par] at h
    split_ifs at h with h₁ h₂
    · rw [← Option.some.inj h]
      exact endNode_valid hv.1 hA.chX fun y hy => (hA.X_mem y hy).1
    · rw [← Option.some.inj h]
      exact endNode_valid hv.1 (hA.chX.filter _) fun y hy => (hA.X_mem y (List.mem_filter.1 hy).1).1
    · rw [← Option.some.inj h]
      exact endNode_valid hv.1 (hA.chY.filter _) fun y hy => (hA.Y_mem y (List.mem_filter.1 hy).1).1

/-- **A step along a chain of a gall.** -/
theorem label_chain_step {c : Fin m} (hc : isNT f c = true) {X : List (Row m)} (hch : Ch S X) (hrows : ∀ y ∈ X, y ∈ rowsOf S M f c) {σ : Row m} (hσ : σ ∈ X)
    (hsp : ∀ i, f i = c → σ i ≠ S i → ∃ z, siteNode S f ar i = .part c z ∧ z ∈ X ∧ z i ≠ S i ∧ ∀ a ∈ X, a i ≠ S i → Sub1 S z a) (i : Fin m) :
    label S M f (.part c σ) i = if siteNode S f ar i = .part c σ then !label S M f (predNode S c X σ) i else label S M f (predNode S c X σ) i := by
  have hσr := hrows σ hσ
  have hb₁ : ∀ {u v w : Bool}, u ≠ w → v = w → u = !v := by decide
  have hb₂ : ∀ {u v w : Bool}, u ≠ w → v ≠ w → u = v := by decide
  by_cases hi : f i = c
  · subst hi
    have hne : ∀ {τ : Row m}, siteNode S f ar i = .part (f i) τ → τ i ≠ S i := by
      intro τ hτ
      by_cases hcc : isNT f (f i) = true
      · obtain ⟨z, h, hz, -⟩ := siteNode_spec (ar := ar) har hcc
        rw [h] at hτ
        rwa [← (GNode.part.inj hτ).2]
      · exact absurd hc hcc
    rw [label_part_self hc]
    rcases predNode_spec (S := S) hch (f i) hσ with ⟨h₁, h₂⟩ | ⟨y, hy, h₁, h₂, h₃, -, h₄⟩
    · rw [h₁, hs.label_top_self hc]
      by_cases hσi : σ i ≠ S i
      · obtain ⟨z, h₅, hz, hzi, h₆⟩ := hsp i rfl hσi
        obtain rfl := h₂ z hz (h₆ σ hσ hσi)
        rw [ite_eq_left h₅]
        exact hb₁ hσi rfl
      · push Not at hσi
        rw [ite_eq_right fun h => hne h hσi, hσi]
    · rw [h₁, label_part_self hc]
      by_cases hσi : σ i ≠ S i
      · obtain ⟨z, h₅, hz, hzi, h₆⟩ := hsp i rfl hσi
        by_cases hyi : y i ≠ S i
        · have hzσ : z ≠ σ := by
            rintro rfl
            exact h₃ (eq_of_sub1 h₂ (h₆ y hy hyi))
          have hne' : siteNode S f ar i ≠ .part (f i) σ := by
            rw [h₅]
            intro h'
            exact hzσ (GNode.part.inj h').2
          rw [ite_eq_right hne']
          exact hb₂ hσi hyi
        · push Not at hyi
          have hzσ : z = σ := by
            by_contra hne'
            exact h₄ z hz (h₆ σ hσ hσi) hne' i hzi hyi
          rw [ite_eq_left (by rw [h₅, hzσ])]
          exact hb₁ hσi hyi
      · push Not at hσi
        have hyi : y i = S i := by
          by_contra h'
          exact h₂ i h' hσi
        rw [ite_eq_right fun h => hne h hσi, hσi, hyi]
  · have hne' : siteNode S f ar i ≠ .part c σ := by
      unfold siteNode
      split_ifs
      · split
        · intro h
          exact hi (GNode.part.inj h).1
        · simp
      · simp
    rw [ite_eq_right hne', hs.label_part_off hc hσr hi]
    rcases predNode_spec (S := S) hch c hσ with ⟨h₁, -⟩ | ⟨y, hy, h₁, -⟩
    · rw [h₁]
    · rw [h₁, hs.label_part_off hc (hrows y hy) hi]

omit har in
/-- The rows of the chains, on their component, are the end of the chain. -/
theorem label_endNode {c : Fin m} (hc : isNT f c = true) {X : List (Row m)} (hch : Ch S X) (hrows : ∀ y ∈ X, y ∈ rowsOf S M f c) (i : Fin m) :
    label S M f (endNode S c X) i = if f i = c then topAt S X i else label S M f (.top c) i := by
  rcases endNode_spec (S := S) hch c with ⟨h₁, h₂⟩ | ⟨y, hy, h₂, h₃⟩
  · rw [h₂]
    by_cases hi : f i = c
    · subst hi
      rw [ite_eq_left rfl, hs.label_top_self hc, h₁, topAt_nil]
    · rw [ite_eq_right hi]
  · rw [h₂]
    by_cases hi : f i = c
    · subst hi
      rw [ite_eq_left rfl, label_part_self hc, topAt_eq_of_max hy h₃]
    · rw [ite_eq_right hi, hs.label_part_off hc (hrows y hy) hi]

omit har in
/-- The nodes of a gall have the same nodes above. -/
theorem numAbove_part {c : Fin m} (hc : isNT f c = true) {σ τ : Row m} (hσ : σ ∈ rowsOf S M f c) (hτ : τ ∈ rowsOf S M f c) : numAbove S M f (.part c σ) = numAbove S M f (.part c τ) := by
  have hkey : ∀ {σ τ : Row m}, σ ∈ rowsOf S M f c → τ ∈ rowsOf S M f c → ∀ k ∈ cands S M f, Up S M f k (.part c σ) = true → Up S M f k (.part c τ) = true := by
    intro σ τ hσ hτ k hk h
    by_cases h₁ : k = .top c
    · rw [h₁]
      exact hs.top_up_part hc hτ
    by_cases h₂ : ∃ ρ, k = .part c ρ
    · obtain ⟨ρ, rfl⟩ := h₂
      rw [not_up_part_part hσ] at h
      exact absurd h (by simp)
    · push Not at h₂
      exact up_trans (hs.up_top_of_up_part hc hσ (valid_of_mem_cands hk) h₁ h₂ h) (hs.top_up_part hc hτ)
  refine le_antisymm (List.length_filter_le_length_filter fun k hk h => hkey hσ hτ k hk h) (List.length_filter_le_length_filter fun k hk h => hkey hτ hσ k hk h)

/-- **The network is acyclic**: the number of nodes above goes up along an arc, and along a gall the place on it does. -/
theorem rank_lt {a b : GNode m} (hb : Valid S M f b) (h : par S M f ar b = some a ∨ par₂ S ar b = some a) :
    numAbove S M f a * (m + 2) + galPos S ar m a < numAbove S M f b * (m + 2) + galPos S ar m b := by
  have hposle : ∀ v : GNode m, galPos S ar m v ≤ m + 1 := by
    intro v
    cases v with
    | part c σ =>
      simp only [galPos]
      split_ifs
      · exact le_rfl
      · have : card1 S σ ≤ (List.finRange m).length := List.length_filter_le _ _
        simp only [List.length_finRange] at this
        omega
    | root => simp [galPos]
    | top c => simp [galPos]
    | leaf ρ => simp [galPos]
  -- when `a` is above `b`
  have hup' : ∀ {a b : GNode m}, (∀ ρ, a ≠ .leaf ρ) → Valid S M f a → Up S M f a b = true → numAbove S M f a * (m + 2) + galPos S ar m a < numAbove S M f b * (m + 2) + galPos S ar m b := by
    intro a b hl ha hab
    have h₁ := numAbove_lt ha hl hab
    have h₂ : (numAbove S M f a + 1) * (m + 2) ≤ numAbove S M f b * (m + 2) := Nat.mul_le_mul_right _ h₁
    have h₃ := hposle a
    nlinarith
  cases b with
  | root => simp [par, par₂] at h
  | top c =>
    simp only [par₂, reduceCtorEq, or_false] at h
    obtain ⟨u', hu', hv', hl, hup'', -⟩ := hs.treePar_spec hb (by simp)
    have heq : a = u' := Option.some.inj ((show treePar S M f (.top c) = some a from h).symm.trans hu')
    subst heq
    exact hup' hl hv' hup''
  | leaf ρ =>
    simp only [par₂, reduceCtorEq, or_false] at h
    obtain ⟨u', hu', hv', hl, hup'', -⟩ := hs.treePar_spec hb (by simp)
    have heq : a = u' := Option.some.inj ((show treePar S M f (.leaf ρ) = some a from h).symm.trans hu')
    subst heq
    exact hup' hl hv' hup''
  | part c σ =>
    have hA := har c hb.1
    have hend : ∀ {X : List (Row m)}, Ch S X → (∀ y ∈ X, y ∈ rowsOf S M f c ∧ y ≠ (ar c).1) → (∀ y ∈ X, galPos S ar m (.part c y) < galPos S ar m (.part c σ)) → a = endNode S c X →
        numAbove S M f a * (m + 2) + galPos S ar m a < numAbove S M f (.part c σ) * (m + 2) + galPos S ar m (.part c σ) := by
      intro X hch hrows hlt hae
      rcases endNode_spec (S := S) hch c with ⟨-, h₁⟩ | ⟨y, hy, h₁, -⟩
      · rw [hae, h₁]
        exact hup' (by simp) (exists_of_isNT hb.1) (hs.top_up_part hb.1 hb.2)
      · rw [hae, h₁, numAbove_part hs hb.1 (hrows y hy).1 hb.2]
        have := hlt y hy
        omega
    have hcard : ∀ y : Row m, card1 S y ≤ m := fun y => by
      have : card1 S y ≤ (List.finRange m).length := List.length_filter_le _ _
      simpa using this
    have hpos : ∀ {y : Row m}, y ≠ (ar c).1 → galPos S ar m (.part c y) = card1 S y := fun {y} hy => by simp [galPos, hy]
    simp only [par, par₂] at h
    by_cases hσ : σ = (ar c).1
    · have hposσ : galPos S ar m (.part c σ) = m + 1 := by simp [galPos, hσ]
      simp only [hσ, ite_true, Option.some.injEq] at h
      rcases h with h | h
      · refine hend hA.chX hA.X_mem (fun y hy => ?_) h.symm
        rw [hposσ, hpos (hA.X_mem y hy).2]
        have := hcard y
        omega
      · refine hend hA.chY hA.Y_mem (fun y hy => ?_) h.symm
        rw [hposσ, hpos (hA.Y_mem y hy).2]
        have := hcard y
        omega
    · have hposσ := hpos hσ
      simp only [hσ, ite_false, reduceCtorEq, or_false] at h
      split_ifs at h with hσX
      · refine hend (hA.chX.filter _) (fun y hy => hA.X_mem y (List.mem_filter.1 hy).1) (fun y hy => ?_) (Option.some.inj h).symm
        rw [hposσ, hpos (hA.X_mem y (List.mem_filter.1 hy).1).2]
        simpa using (List.mem_filter.1 hy).2
      · refine hend (hA.chY.filter _) (fun y hy => hA.Y_mem y (List.mem_filter.1 hy).1) (fun y hy => ?_) (Option.some.inj h).symm
        rw [hposσ, hpos (hA.Y_mem y (List.mem_filter.1 hy).1).2]
        simpa using (List.mem_filter.1 hy).2

omit har in
/-- A node other than the root has a parent. -/
theorem exists_par {v : GNode m} (hv : Valid S M f v) (hne : v ≠ .root) : ∃ u, par S M f ar v = some u := by
  cases v with
  | root => exact absurd rfl hne
  | top c =>
    obtain ⟨u, hu, -⟩ := hs.treePar_spec hv hne
    exact ⟨u, hu⟩
  | leaf ρ =>
    obtain ⟨u, hu, -⟩ := hs.treePar_spec hv hne
    exact ⟨u, hu⟩
  | part c σ =>
    simp only [par]
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- **The labels along an arc that isn't into a recombination node.** -/
theorem label_step_all {v p : GNode m} (hv : Valid S M f v) (hp : par S M f ar v = some p) (hq : par₂ S ar v = none) (i : Fin m) :
    label S M f v i = if siteNode S f ar i = v then !label S M f p i else label S M f p i := by
  have htree : ∀ v, (∀ c σ, v ≠ GNode.part c σ) → Valid S M f v → v ≠ .root → treePar S M f v = some p → label S M f v i = if siteNode S f ar i = v then !label S M f p i else label S M f p i := by
    intro v hnp hv hne h
    obtain ⟨u, hu, hvu, -, hup, hlow⟩ := hs.treePar_spec hv hne
    obtain rfl : p = u := Option.some.inj (h.symm.trans hu)
    refine hs.label_tree_arc hv hvu hnp hup hlow i ar fun hc => ?_
    obtain ⟨z, hz, -⟩ := siteNode_spec (ar := ar) har hc
    rw [hz]
    exact (hnp _ _ · |>.elim) ∘ Eq.symm
  cases v with
  | root => simp [par] at hp
  | top c => exact htree _ (by simp) hv (by simp) hp
  | leaf ρ => exact htree _ (by simp) hv (by simp) hp
  | part c σ =>
    have hA := har c hv.1
    have hσs : σ ≠ (ar c).1 := by
      intro h
      simp [par₂, h] at hq
    simp only [par, hσs, ite_false] at hp
    have hsp : ∀ {X X' : List (Row m)}, ((X = (ar c).2.1 ∧ X' = (ar c).2.2) ∨ (X = (ar c).2.2 ∧ X' = (ar c).2.1)) → σ ∈ X → ∀ i, f i = c → σ i ≠ S i → ∃ z, siteNode S f ar i = .part c z ∧ z ∈ X ∧ z i ≠ S i ∧ ∀ a ∈ X, a i ≠ S i → Sub1 S z a := by
      intro X X' hXX hσX i hi hσi
      subst hi
      obtain ⟨z, h₁, h₂, h₃⟩ := siteNode_spec (ar := ar) har hv.1
      refine ⟨z, h₁, ?_, h₂, ?_⟩
      · rcases hXX with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases h₃ with ⟨h₄, -⟩ | ⟨h₄, -⟩
          · exact h₄
          · exact absurd (hA.disj σ hσX z h₄ i hσi) h₂
        · rcases h₃ with ⟨h₄, -⟩ | ⟨h₄, -⟩
          · exact absurd (hA.disj z h₄ σ hσX i h₂) hσi
          · exact h₄
      · rcases hXX with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases h₃ with ⟨-, h₄⟩ | ⟨h₄, -⟩
          · exact h₄
          · exact absurd (hA.disj σ hσX z h₄ i hσi) h₂
        · rcases h₃ with ⟨h₄, -⟩ | ⟨-, h₄⟩
          · exact absurd (hA.disj z h₄ σ hσX i h₂) hσi
          · exact h₄
    split_ifs at hp with hσX
    · rw [← Option.some.inj hp]
      exact label_chain_step hs har hv.1 hA.chX (fun y hy => (hA.X_mem y hy).1) hσX (hsp (Or.inl ⟨rfl, rfl⟩) hσX) i
    · have hσY : σ ∈ (ar c).2.2 := by
        rcases hA.all σ hv.2 with h | h | h
        · exact absurd h hσs
        · exact absurd h hσX
        · exact h
      rw [← Option.some.inj hp]
      exact label_chain_step hs har hv.1 hA.chY (fun y hy => (hA.Y_mem y hy).1) hσY (hsp (Or.inr ⟨rfl, rfl⟩) hσY) i

/-- **The recombination node.** Its label is that of the end of the second chain before the recombination point, and of the first after. -/
theorem label_recomb_all {c : Fin m} (hc : isNT f c = true) : ∃ n, ∀ i, label S M f (.part c (ar c).1) i = if i.val < n then label S M f (endNode S c (ar c).2.2) i else label S M f (endNode S c (ar c).2.1) i := by
  have hA := har c hc
  obtain ⟨n, hn⟩ := hA.point
  refine ⟨n, fun i => ?_⟩
  rw [label_endNode hs hc hA.chY (fun y hy => (hA.Y_mem y hy).1), label_endNode hs hc hA.chX (fun y hy => (hA.X_mem y hy).1)]
  by_cases hi : f i = c
  · subst hi
    rw [label_part_self hc, hn i rfl, ite_eq_left rfl, ite_eq_left rfl]
  · rw [ite_eq_right hi, ite_eq_right hi, hs.label_part_off hc hA.s_mem hi]
    split_ifs <;> rfl

end Net

/-! ### The network as a `PreNet` -/

section Assemble

open Gusfield2007.Network

variable {ar : Fin m → Arr m} (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c))

/-- **The reduced galled tree** as a `PreNet`: the nodes, the parents, the sites and the labels are the functions of the algorithm. -/
def gPreNet : PreNet (Fin m) (VNode S M f) where
  root := ⟨.root, trivial⟩
  par v := liftOpt (o := par S M f ar v.1) fun _ hu => par_valid hs har v.2 hu
  par₂ v := liftOpt (o := par₂ S ar v.1) fun _ hu => par₂_valid har v.2 hu
  site i := some ⟨siteNode S f ar i, site_valid har i⟩
  label v := label S M f v.1
  par_eq_none v := by
    rw [liftOpt_eq_none]
    constructor
    · intro h
      by_contra hne
      obtain ⟨u, hu⟩ := exists_par (ar := ar) hs v.2 fun h' => hne (Subtype.ext h')
      rw [hu] at h
      simp at h
    · intro h
      rw [h]
      rfl
  par₂_root := liftOpt_eq_none.2 rfl
  par₂_ne v q hq hp := by
    rw [liftOpt_eq_some] at hq hp
    obtain ⟨c, hc, hv, hq'⟩ := par₂_some v.2 hq
    rw [hv, par_recomb] at hp
    exact endNode_ne har hc ((Option.some.inj hp).trans hq')
  acyclic := Relation.not_transGen_self_of_forall_lt (fun v : VNode S M f => numAbove S M f v.1 * (m + 2) + galPos S ar m v.1) fun a b h => by
    refine rank_lt hs har b.2 ?_
    rcases h with h | h
    · exact Or.inl (liftOpt_eq_some.1 h)
    · exact Or.inr (liftOpt_eq_some.1 h)
  site_tree i v hv := by
    have hve : siteNode S f ar i = v.1 := congrArg Subtype.val (Option.some.inj hv)
    constructor
    · refine liftOpt_eq_none.2 ?_
      rw [← hve]
      by_cases hc : isNT f (f i) = true
      · obtain ⟨z, h, -, hz⟩ := siteNode_spec (ar := ar) har hc
        rw [h]
        have hzs : z ≠ (ar (f i)).1 := by
          rcases hz with ⟨hz, -⟩ | ⟨hz, -⟩
          · exact ((har _ hc).X_mem z hz).2
          · exact ((har _ hc).Y_mem z hz).2
        simp [par₂, hzs]
      · simp [siteNode, hc, par₂]
    · intro hroot
      have hv₁ : v.1 = .root := congrArg Subtype.val hroot
      rw [hv₁] at hve
      by_cases hc : isNT f (f i) = true
      · obtain ⟨z, h, -⟩ := siteNode_spec (ar := ar) har hc
        rw [h] at hve
        simp at hve
      · simp [siteNode, hc] at hve
  label_tree v p hp hq i := by
    have h₁ := label_step_all hs har v.2 (liftOpt_eq_some.1 hp) (liftOpt_eq_none.1 hq) i
    by_cases hsv : siteNode S f ar i = v.1
    · rw [ite_eq_left hsv] at h₁
      rw [ite_eq_left (congrArg some (Subtype.ext hsv))]
      exact h₁
    · rw [ite_eq_right hsv] at h₁
      rw [ite_eq_right fun h' => hsv (congrArg Subtype.val (Option.some.inj h'))]
      exact h₁
  label_recomb v p q hp hq i := by
    obtain ⟨c, hc, hv, hq'⟩ := par₂_some v.2 (liftOpt_eq_some.1 hq)
    have hp' := liftOpt_eq_some.1 hp
    rw [hv, par_recomb] at hp'
    obtain ⟨n, hn⟩ := label_recomb_all hs har hc
    have hv' : label S M f v.1 i = if i.val < n then label S M f (endNode S c (ar c).2.2) i else label S M f (endNode S c (ar c).2.1) i := by
      rw [hv]
      exact hn i
    have hpe : p.1 = endNode S c (ar c).2.1 := (Option.some.inj hp').symm
    change label S M f v.1 i = label S M f p.1 i ∨ label S M f v.1 i = label S M f q.1 i
    rw [hv', hpe, hq']
    by_cases hi : i.val < n
    · rw [ite_eq_left hi]
      exact Or.inr rfl
    · rw [ite_eq_right hi]
      exact Or.inl rfl

/-- The network of the algorithm. -/
noncomputable def gNet : Gusfield2007.Network (Fin m) (VNode S M f) ({v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none}) :=
  (gPreNet hs har).toNetwork fun _ => ⟨_, rfl⟩

/-- An arc goes from a parent. -/
theorem gNet_arc (e : {v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none}) :
    par S M f ar ((gNet hs har).tgt e).1 = some ((gNet hs har).src e).1 ∨ par₂ S ar ((gNet hs har).tgt e).1 = some ((gNet hs har).src e).1 := by
  rcases e with v | v
  · have h₁ : (gPreNet hs har).par v.1 = some ((gNet hs har).src (.inl v)) := (Option.some_get _).symm
    exact Or.inl (liftOpt_eq_some.1 h₁)
  · have h₁ : (gPreNet hs har).par₂ v.1 = some ((gNet hs har).src (.inr v)) := (Option.some_get _).symm
    exact Or.inr (liftOpt_eq_some.1 h₁)

/-- A parent gives an arc. -/
theorem gNet_exists_arc {v : VNode S M f} {u : GNode m} (h : par S M f ar v.1 = some u ∨ par₂ S ar v.1 = some u) :
    ∃ e, ((gNet hs har).src e).1 = u ∧ (gNet hs har).tgt e = v := by
  rcases h with h | h
  · have hne : (gPreNet hs har).par v ≠ none := fun h' => by
      rw [liftOpt_eq_none.1 h'] at h
      simp at h
    refine ⟨.inl ⟨v, hne⟩, ?_, rfl⟩
    have h₁ : (gPreNet hs har).par v = some ((gNet hs har).src (.inl ⟨v, hne⟩)) := (Option.some_get _).symm
    exact Option.some.inj ((liftOpt_eq_some.1 h₁).symm.trans h)
  · have hne : (gPreNet hs har).par₂ v ≠ none := fun h' => by
      rw [liftOpt_eq_none.1 h'] at h
      simp at h
    refine ⟨.inr ⟨v, hne⟩, ?_, rfl⟩
    have h₁ : (gPreNet hs har).par₂ v = some ((gNet hs har).src (.inr ⟨v, hne⟩)) := (Option.some_get _).symm
    exact Option.some.inj ((liftOpt_eq_some.1 h₁).symm.trans h)

/-- A recombination node of the network is the row at the recombination node of a gall. -/
theorem gNet_isRecomb {x : VNode S M f} (hx : (gNet hs har).IsRecomb x) : ∃ c, isNT f c = true ∧ x.1 = .part c (ar c).1 := by
  obtain ⟨e, g, heg, he, hg⟩ := hx
  have hq : ∃ q, par₂ S ar x.1 = some q := by
    rcases e with e | e
    · rcases g with g | g
      · exact absurd (congrArg Sum.inl (Subtype.ext (he.trans hg.symm))) heg
      · have hg' : g.1 = x := hg
        exact Option.ne_none_iff_exists'.1 fun h' => g.2 (by rw [hg']; exact liftOpt_eq_none.2 h')
    · have he' : e.1 = x := he
      exact Option.ne_none_iff_exists'.1 fun h' => e.2 (by rw [he']; exact liftOpt_eq_none.2 h')
  obtain ⟨q, hq⟩ := hq
  obtain ⟨c, hc, hv, -⟩ := par₂_some x.2 hq
  exact ⟨c, hc, hv⟩

theorem gNet_label (v : VNode S M f) : (gNet hs har).label v = label S M f v.1 := rfl

/-- The network has the ancestral sequence. -/
theorem gNet_ancestral : (gNet hs har).ancestral = S := funext label_root

/-- The network has single crossovers. -/
theorem gNet_obeys : (gNet hs har).Obeys .single := by
  intro x hx
  obtain ⟨c, hc, hxc⟩ := gNet_isRecomb hs har hx
  obtain ⟨e, he₁, he₂⟩ := gNet_exists_arc hs har (v := x) (u := endNode S c (ar c).2.2) (Or.inr (by rw [hxc]; exact par₂_recomb))
  obtain ⟨g, hg₁, hg₂⟩ := gNet_exists_arc hs har (v := x) (u := endNode S c (ar c).2.1) (Or.inl (by rw [hxc]; exact par_recomb))
  obtain ⟨n, hn⟩ := label_recomb_all hs har hc
  have hne : e ≠ g := by
    rintro rfl
    exact endNode_ne har hc (hg₁.symm.trans he₁)
  let L₀ : LowerSet (Fin m) := ⟨{i | i.val < n}, fun a b hba ha => lt_of_le_of_lt (show b.val ≤ a.val from hba) ha⟩
  refine ⟨e, g, hne, he₂, hg₂, L₀, fun i => ?_⟩
  rw [gNet_label, gNet_label, gNet_label, he₁, hg₁, hxc, hn i]
  by_cases hi : i.val < n
  · have hi' : i ∈ L₀ := hi
    rw [ite_eq_left hi, ite_eq_left hi']
  · have hi' : i ∉ L₀ := hi
    rw [ite_eq_right hi, ite_eq_right hi']

include hs in
/-- A parent isn't a leaf. -/
theorem par_not_leaf {v u : GNode m} (hv : Valid S M f v) (h : par S M f ar v = some u ∨ par₂ S ar v = some u) (ρ : Row m) : u ≠ .leaf ρ := by
  have hend : ∀ {c : Fin m} {X : List (Row m)}, u = endNode S c X → u ≠ .leaf ρ := by
    rintro c X rfl
    rcases endNode_cases (S := S) c X with h' | ⟨y, h'⟩ <;> rw [h'] <;> simp
  rcases h with h | h
  · cases v with
    | root => simp [par] at h
    | top c =>
      obtain ⟨u', hu', -, hl, -⟩ := hs.treePar_spec hv (by simp)
      have heq : u = u' := Option.some.inj ((show treePar S M f (.top c) = some u from h).symm.trans hu')
      rw [heq]
      exact hl ρ
    | leaf r =>
      obtain ⟨u', hu', -, hl, -⟩ := hs.treePar_spec hv (by simp)
      have heq : u = u' := Option.some.inj ((show treePar S M f (.leaf r) = some u from h).symm.trans hu')
      rw [heq]
      exact hl ρ
    | part c σ =>
      simp only [par] at h
      split_ifs at h
      · exact hend (Option.some.inj h).symm
      · exact hend (Option.some.inj h).symm
      · exact hend (Option.some.inj h).symm
  · obtain ⟨c, -, -, hq⟩ := par₂_some hv h
    exact hend hq

include hs har in
/-- **A node that isn't a leaf has a child**: the next node on the way to a row below it. -/
theorem exists_child {v : GNode m} (hv : Valid S M f v) (hnl : ∀ ρ, v ≠ .leaf ρ) : ∃ w, Valid S M f w ∧ (par S M f ar w = some v ∨ par₂ S ar w = some v) := by
  obtain ⟨r, hr, hrv⟩ := hs.nonempty_cl hv
  have hmem : (GNode.leaf r : GNode m) ∈ {w | Valid S M f w ∧ Up S M f v w = true ∧ w.cl S f r = true} := by
    refine ⟨hr, up_iff.2 ⟨hnl r, fun r' _ h' => ?_, fun _ => Or.inl ?_⟩, cl_leaf.2 rfl⟩
    · rw [cl_leaf.1 h']
      exact hrv
    · have hle := rank_le (f := f) v
      have hL : (GNode.leaf r : GNode m).rank f = 4 := rfl
      have hne4 : v.rank f ≠ 4 := by
        intro h4
        cases v with
        | root => simp [GNode.rank] at h4
        | leaf ρ => exact hnl ρ rfl
        | part _ _ => simp [GNode.rank] at h4
        | top c =>
          simp only [GNode.rank] at h4
          split_ifs at h4 <;> omega
      omega
  obtain ⟨w, ⟨hw, hvw, hrw⟩, hmin⟩ := (InvImage.wf (key S M f) Nat.lt_wfRel.wf).has_min _ ⟨_, hmem⟩
  have hlow : ∀ w', Valid S M f w' → Up S M f v w' = true → w'.cl S f r = true → ¬ key S M f w' < key S M f w := fun w' h₁ h₂ h₃ => hmin w' ⟨h₁, h₂, h₃⟩
  have htree : (∀ c σ, w ≠ GNode.part c σ) → w ≠ .root → par S M f ar w = treePar S M f w → ∃ w, Valid S M f w ∧ (par S M f ar w = some v ∨ par₂ S ar w = some v) := by
    intro _ hwr hpar
    obtain ⟨u, hu, hvu, -, hup, hl⟩ := hs.treePar_spec hw hwr
    refine ⟨w, hw, Or.inl ?_⟩
    rw [hpar, hu]
    rcases hl v hv hvw with h | h
    · rw [h]
    · exfalso
      exact hlow u hvu h ((up_iff.1 hup).2.1 r (by
        by_contra hrM
        exact hrM hr) hrw) (key_lt hup)
  cases w with
  | root =>
    exfalso
    obtain ⟨-, h₂, h₃⟩ := up_iff.1 hvw
    have ht := h₃ fun _ _ _ => rfl
    have hr₀ : (GNode.root : GNode m).rank f = 0 := rfl
    have hi₀ : (GNode.root : GNode m).idx = 0 := rfl
    unfold Tie at ht
    rw [hr₀, hi₀] at ht
    omega
  | top c => exact htree (by simp) (by simp) rfl
  | leaf ρ => exact htree (by simp) (by simp) rfl
  | part c τ =>
    have hτ : τ ∈ rowsOf S M f c := hw.2
    have hA := har c hw.1
    by_cases hvt : v = .top c
    · subst hvt
      -- the first node of the first chain, or the recombination node
      cases hX : (ar c).2.1.argmin (card1 S) with
      | none =>
        refine ⟨.part c (ar c).1, ⟨hw.1, hA.s_mem⟩, Or.inl ?_⟩
        rw [par_recomb, List.argmin_eq_none.1 hX]
        simp [endNode]
      | some y =>
        have hy := List.argmin_mem hX
        refine ⟨.part c y, ⟨hw.1, (hA.X_mem y hy).1⟩, Or.inl ?_⟩
        have hnil : ((ar c).2.1.filter fun z => decide (card1 S z < card1 S y)) = [] := by
          refine List.filter_eq_nil_iff.2 fun z hz hlt => ?_
          have := List.le_of_mem_argmin hz hX
          have hlt' : card1 S z < card1 S y := by simpa using hlt
          omega
        simp [par, (hA.X_mem y hy).2, hy, predNode, hnil, endNode]
    · have hvp : ∀ ρ, v ≠ .part c ρ := by
        rintro ρ rfl
        rw [not_up_part_part hτ] at hvw
        exact absurd hvw (by simp)
      exfalso
      have htv := hs.up_top_of_up_part hw.1 hτ hv hvt hvp hvw
      have htop := hs.top_up_part hw.1 hτ
      exact hlow (.top c) (exists_of_isNT hw.1) htv ((up_iff.1 htop).2.1 r hr hrw) (key_lt htop)

include hs har in
/-- Going back from a node of a gall, other than its coalescent node, stays on the gall. -/
theorem gNet_back {c : Fin m} (e : {v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none}) (h : InGall c ((gNet hs har).tgt e).1) (hne : ((gNet hs har).tgt e).1 ≠ .top c) : InGall c ((gNet hs har).src e).1 := by
  rcases h with h | ⟨σ, h⟩
  · exact absurd h hne
  have harc := gNet_arc hs har e
  rw [h] at harc
  rcases harc with h₁ | h₁
  · simp only [par] at h₁
    split_ifs at h₁
    · rw [← Option.some.inj h₁]
      exact inGall_endNode _ _
    · rw [← Option.some.inj h₁]
      exact inGall_endNode _ _
    · rw [← Option.some.inj h₁]
      exact inGall_endNode _ _
  · simp only [par₂] at h₁
    split_ifs at h₁
    rw [← Option.some.inj h₁]
    exact inGall_endNode _ _

include hs har in
theorem gNet_rk_lt (e : {v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none}) : rkN S M f ar ((gNet hs har).src e).1 < rkN S M f ar ((gNet hs har).tgt e).1 :=
  rank_lt hs har ((gNet hs har).tgt e).2 (gNet_arc hs har e)

include hs har in
theorem gNet_rk_le {a b : VNode S M f} (h : (gNet hs har).Reach a b) : rkN S M f ar a.1 ≤ rkN S M f ar b.1 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    obtain ⟨e, rfl, rfl⟩ := hbc
    exact ih.trans (gNet_rk_lt hs har e).le

/-- A path to a node of a gall stays on the gall, or comes through its coalescent node. -/
theorem gNet_path {c : Fin m} {l : List ({v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none})} {u : VNode S M f} : ∀ {v : VNode S M f}, (gNet hs har).IsPath u v l → InGall c v.1 →
    (InGall c u.1 ∧ ∀ e ∈ l, InGall c ((gNet hs har).tgt e).1) ∨ ∃ e ∈ l, ((gNet hs har).tgt e).1 = .top c := by
  induction l using List.reverseRecOn with
  | nil =>
    intro v h hv
    have huv : u = v := h
    exact Or.inl ⟨huv ▸ hv, by simp⟩
  | append_singleton l₀ e ih =>
    intro v h hv
    obtain ⟨y, h₁, h₂, h₃⟩ := Gusfield2007.Network.isPath_append.1 h
    have h₃' : (gNet hs har).tgt e = v := h₃
    have h₂' : (gNet hs har).src e = y := h₂
    by_cases het : ((gNet hs har).tgt e).1 = .top c
    · exact Or.inr ⟨e, by simp, het⟩
    · have hsrc := gNet_back hs har e (by rw [h₃']; exact hv) het
      rw [h₂'] at hsrc
      rcases ih h₁ hsrc with ⟨h₄, h₅⟩ | ⟨e', he', h₄⟩
      · refine Or.inl ⟨h₄, fun g hg => ?_⟩
        rcases List.mem_append.1 hg with hg | hg
        · exact h₅ g hg
        · rw [List.mem_singleton.1 hg, h₃']
          exact hv
      · exact Or.inr ⟨e', by simp [he'], h₄⟩

/-- **A recombination cycle of the network is on the gall of a component.** -/
theorem gNet_cycle {w x : VNode S M f} {p q : List ({v // (gPreNet hs har).par v ≠ none} ⊕ {v // (gPreNet hs har).par₂ v ≠ none})} (hc : (gNet hs har).IsCycleOn w x p q) :
    ∃ c, isNT f c = true ∧ x.1 = .part c (ar c).1 ∧ ∀ v ∈ (gNet hs har).blobVerts {e | e ∈ p ∨ e ∈ q}, InGall c v.1 := by
  obtain ⟨c, hc₁, hx⟩ := gNet_isRecomb hs har hc.1
  refine ⟨c, hc₁, hx, ?_⟩
  have hxg : InGall c x.1 := Or.inr ⟨_, hx⟩
  have hxne : x.1 ≠ .top c := by
    rw [hx]
    simp
  have hrev : ∀ {P : List _}, (gNet hs har).IsPath w x P → ∀ {e}, e ∈ P → ((gNet hs har).tgt e).1 = .top c → InGall c w.1 → False := by
    intro P hP e he hte hw
    have h₁ : rkN S M f ar w.1 ≤ rkN S M f ar ((gNet hs har).src e).1 := gNet_rk_le hs har (hP.reach_src_of_mem he)
    have h₂ := gNet_rk_lt hs har e
    rw [hte] at h₂
    rcases hw with h₃ | ⟨σ, h₃⟩
    · rw [h₃] at h₁
      omega
    · have hσ : σ ∈ rowsOf S M f c := by
        have := w.2
        rw [h₃] at this
        exact this.2
      have := rk_top_lt (ar := ar) hc₁ hs hσ
      rw [h₃] at h₁
      omega
  have hP := gNet_path hs har (c := c) hc.2.1 hxg
  have hQ := gNet_path hs har (c := c) hc.2.2.1 hxg
  rcases hP with ⟨hw, hP⟩ | ⟨e, he, hte⟩ <;> rcases hQ with ⟨hw', hQ⟩ | ⟨g, hg, htg⟩
  · have hall : ∀ e, (e ∈ p ∨ e ∈ q) → InGall c ((gNet hs har).tgt e).1 := by
      rintro e (h | h)
      · exact hP e h
      · exact hQ e h
    have hsrc : ∀ e, (e ∈ p ∨ e ∈ q) → InGall c ((gNet hs har).src e).1 := by
      have hv : ∀ {P : List _}, (gNet hs har).IsPath w x P → (∀ e ∈ P, InGall c ((gNet hs har).tgt e).1) → ∀ e ∈ P, InGall c ((gNet hs har).src e).1 := by
        intro P hPp hPt e he
        have hm := hPp.src_mem_pathVerts he
        rcases List.mem_cons.1 hm with h | h
        · rw [h]
          exact hw
        · obtain ⟨g, hg, hge⟩ := List.mem_map.1 h
          rw [← hge]
          exact hPt g hg
      rintro e (h | h)
      · exact hv hc.2.1 hP e h
      · exact hv hc.2.2.1 hQ e h
    rintro v (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact hsrc e he
    · exact hall e he
  · exact (hrev hc.2.2.1 hg htg hw).elim
  · exact (hrev hc.2.1 he hte hw').elim
  · exfalso
    have heq : (gNet hs har).tgt e = (gNet hs har).tgt g := Subtype.ext (hte.trans htg.symm)
    have := hc.2.2.2.2 e he g hg heq
    apply hxne
    rw [← this, hte]

instance : Finite (GNode m) := by
  refine Finite.of_injective (β := Option (Fin m ⊕ (Fin m × Row m) ⊕ Row m)) (fun v => match v with
    | .root => none
    | .top c => some (.inl c)
    | .part c σ => some (.inr (.inl (c, σ)))
    | .leaf r => some (.inr (.inr r))) ?_
  intro a b h
  cases a <;> cases b <;> simp_all

/-- **The network is a galled tree.** -/
theorem gNet_isGalledTree : IsGalledTree (gNet hs har) := by
  rintro Q ⟨w, x, p, q, hc, rfl⟩
  refine ⟨⟨w, x, p, q, hc, rfl⟩, ?_⟩
  rintro Q' ⟨w', x', p', q', hc', rfl⟩ hne
  rw [Set.disjoint_left]
  intro v hv hv'
  obtain ⟨c, hc₁, hx, hall⟩ := gNet_cycle hs har hc
  obtain ⟨c', -, hx', hall'⟩ := gNet_cycle hs har hc'
  obtain rfl := (hall v hv).unique (hall' v hv')
  have hxx : x' = x := Subtype.ext (hx'.trans hx.symm)
  subst hxx
  apply hne
  refine (cycle_unique hc hc' fun y hy hyv hr => hy ?_).symm
  obtain ⟨c₂, -, hy₂⟩ := gNet_isRecomb hs har hr
  have hg := hall y hyv
  obtain rfl := hg.unique (Or.inr ⟨_, hy₂⟩)
  exact Subtype.ext (hy₂.trans hx.symm)

/-- **The network derives the rows.** -/
theorem gNet_derives : (gNet hs har).Derives M.toFinset := by
  have hleaf : ∀ {v : VNode S M f}, (gNet hs har).IsLeaf v → ∃ r ∈ M, v.1 = .leaf r := by
    intro v hv
    by_contra hno
    push Not at hno
    have hnl : ∀ ρ, v.1 ≠ .leaf ρ := by
      intro ρ h
      have hρ : ρ ∈ M := by
        have := v.2
        rw [h] at this
        exact this
      exact hno ρ hρ h
    obtain ⟨w, hw, hwp⟩ := exists_child hs har v.2 hnl
    obtain ⟨e, he, -⟩ := gNet_exists_arc hs har (v := ⟨w, hw⟩) hwp
    exact hv e (Subtype.ext he)
  have hlab : ∀ (r : Row m) (h : Valid S M f (.leaf r)), (gNet hs har).label ⟨.leaf r, h⟩ = r := fun _ h => funext fun i => label_leaf hs h i
  refine ⟨fun v hv => ?_, fun u hu v hv huv => ?_, fun r hr => ?_⟩
  · obtain ⟨r, hr, h⟩ := hleaf hv
    have hve : v = ⟨.leaf r, hr⟩ := Subtype.ext h
    rw [hve, hlab r hr]
    exact Finset.mem_coe.2 (List.mem_toFinset.2 hr)
  · obtain ⟨r, hr, h⟩ := hleaf hu
    obtain ⟨r', hr', h'⟩ := hleaf hv
    have hue : u = ⟨.leaf r, hr⟩ := Subtype.ext h
    have hve : v = ⟨.leaf r', hr'⟩ := Subtype.ext h'
    rw [hue, hve, hlab r hr, hlab r' hr'] at huv
    rw [hue, hve]
    exact Subtype.ext (congrArg GNode.leaf huv)
  · have hrM : r ∈ M := List.mem_toFinset.1 hr
    refine ⟨⟨.leaf r, hrM⟩, fun e he => ?_, hlab r hrM⟩
    have harc := gNet_arc hs har e
    exact par_not_leaf hs ((gNet hs har).tgt e).2 harc r (by rw [he])

/-- The node below the arc of a site, in the network. -/
theorem gNet_tgt_site (i : Fin m) : ((gNet hs har).tgt ((gNet hs har).site i)).1 = siteNode S f ar i := by
  have h : (gPreNet hs har).site i = some (Exists.choose (⟨_, rfl⟩ : ∃ v, (gPreNet hs har).site i = some v)) := Exists.choose_spec (⟨_, rfl⟩ : ∃ v, (gPreNet hs har).site i = some v)
  exact (congrArg Subtype.val (Option.some.inj h)).symm

/-- The rows of `M + S` label nodes of the network. -/
theorem gNet_labels : ∀ r ∈ addRow M.toFinset S, ∃ v, (gNet hs har).label v = r := by
  intro r hr
  rcases mem_addRow.1 hr with rfl | hr
  · exact ⟨⟨.root, trivial⟩, funext label_root⟩
  · have hrM : r ∈ M := List.mem_toFinset.1 hr
    exact ⟨⟨.leaf r, hrM⟩, funext fun i => label_leaf hs hrM i⟩

/-- **The network is a reduced galled tree** (Definition 2.2 of the source). -/
theorem gNet_reduced : IsReducedGalledTree (gNet hs har) (conflictGraph S M.toFinset) := by
  rw [conflictGraph_eq_incompatGraph_addRow]
  have hG := gNet_isGalledTree hs har
  have hsiteOf : ∀ {c : Fin m} {i : Fin m}, isNT f c = true → f i = c → InGall c ((gNet hs har).tgt ((gNet hs har).site i)).1 := by
    intro c i hc hi
    subst hi
    obtain ⟨z, h, -⟩ := siteNode_spec (ar := ar) har hc
    rw [gNet_tgt_site, h]
    exact Or.inr ⟨z, rfl⟩
  refine ⟨hG, fun Q hQ => ?_, fun Q hQ i hi => ?_⟩
  · obtain ⟨w, x, p, q, hc, rfl⟩ := id hQ
    obtain ⟨c, hc₁, hx, hall⟩ := gNet_cycle hs har hc
    obtain ⟨a, ha⟩ := exists_of_isNT (f := f) hc₁
    obtain ⟨k, hk, hadj⟩ := hs.exists_adj_of_isNT hc₁ ha
    obtain ⟨Q₀, ⟨w₀, x₀, p₀, q₀, hc₀, rfl⟩, hsa, hsk⟩ := exists_isCycle_of_incompatible (gNet hs har) (gNet_labels hs har) hadj
    obtain ⟨c₀, -, hx₀, hall₀⟩ := gNet_cycle hs har hc₀
    have hin₀ := hall₀ _ (Or.inr ⟨_, hsa, rfl⟩)
    obtain rfl := hin₀.unique (hsiteOf hc₁ ha)
    have hxx : x₀ = x := Subtype.ext (hx₀.trans hx.symm)
    subst hxx
    have heq : {e | e ∈ p ∨ e ∈ q} = {e | e ∈ p₀ ∨ e ∈ q₀} := cycle_unique hc hc₀ fun y hy hyv hr => hy (by
      obtain ⟨c₂, -, hy₂⟩ := gNet_isRecomb hs har hr
      obtain rfl := (hall y hyv).unique (Or.inr ⟨_, hy₂⟩)
      exact Subtype.ext (hy₂.trans hx.symm))
    exact ⟨a, k, heq ▸ hsa, heq ▸ hsk, hadj⟩
  · obtain ⟨w, x, p, q, hc, rfl⟩ := id hQ
    obtain ⟨c, hc₁, -, hall⟩ := gNet_cycle hs har hc
    have hin := hall _ (Or.inr ⟨_, hi, rfl⟩)
    by_cases hci : isNT f (f i) = true
    · obtain rfl := hin.unique (hsiteOf hci rfl)
      obtain ⟨k, -, hk⟩ := hs.exists_adj_of_isNT hci rfl
      exact ⟨k, hk⟩
    · rw [gNet_tgt_site] at hin
      have hsn : siteNode S f ar i = .top (f i) := by simp [siteNode, hci]
      rw [hsn] at hin
      obtain rfl : f i = c := by
        rcases hin with h | ⟨σ, h⟩
        · exact GNode.top.inj h
        · simp at h
      exact absurd hc₁ hci

end Assemble

/-! ### The arrangement from the test -/

end Laminar

/-! ### The function -/

section Correct

open scoped Classical

open Gusfield2007 Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)}

/-- **The algorithm returns something exactly when there is a galled tree** (`ext:galled_build`), for the rows `M` and the ancestral sequence `S`, with the source's standing assumptions that there are rows and each column has a `1`. -/
theorem galledBuild_isSome_iff (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) :
    (galledBuild S M).isSome = true ↔ ∃ (a b : ℕ) (N : Network (Fin m) (Fin a) (Fin b)), IsGalledTree N ∧ N.Obeys .single ∧ N.Derives M.toFinset ∧ N.ancestral = S := by
  rw [← galledDecide_iff hM h1]
  unfold galledBuild
  by_cases h : (galledDecide S M).1 = true <;> simp [h]

/-- **What the algorithm returns is a reduced galled tree** (`ext:galled_build`), Gusfield et al. 2007, line 180. If `galledBuild` returns a table, it is the table of the network `gNet`: its nodes are those of the table (`mem_nodes`), its arcs go from the parents of the table (`gNet_arc`, `gNet_exists_arc`), its labels are those of the table (`gNet_label`), and the sites are on the arcs into the nodes the second list gives (`gNet_tgt_site`). That network is a reduced galled tree for `M`, with ancestral sequence `S` and single crossovers. -/
theorem galledBuild_correct (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) {t : GalledOut m} (ht : galledBuild S M = some t) :
    ∃ (f : Fin m → Fin m) (ar : Fin m → Arr m) (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c)), t = (gTable S M f ar, List.ofFn (siteNode S f ar)) ∧
      (gNet hs har).Obeys .single ∧ (gNet hs har).Derives M.toFinset ∧ (gNet hs har).ancestral = S ∧ IsReducedGalledTree (gNet hs har) (conflictGraph S M.toFinset) := by
  unfold galledBuild at ht
  split_ifs at ht with hdec
  have hs := std_of hM h1
  obtain ⟨a, b, N, hG, hc₁, hD, hSN⟩ := (galledDecide_iff hM h1).1 hdec
  have har₀ : ∀ c, isNT (labOf (edgesOps S M).1) c = true → ArrOK S M (labOf (edgesOps S M).1) c (arrOf S M (labOf (edgesOps S M).1) c) := fun c hc => arrOf_ok_of_galled h1 hG hc₁ hD hSN hc
  have har : (fun c : Fin m => (List.ofFn (arrOf S M (labOf (edgesOps S M).1))).getD c.val (S, [], [])) = arrOf S M (labOf (edgesOps S M).1) := by
    funext c
    simp [List.getD_eq_getElem?_getD]
  simp only [har] at ht
  exact ⟨_, _, hs, har₀, (Option.some.inj ht).symm, gNet_obeys hs har₀, gNet_derives hs har₀, gNet_ancestral hs har₀, gNet_reduced hs har₀⟩

end Correct

end External.GusfieldEtAl2004.Algorithm
