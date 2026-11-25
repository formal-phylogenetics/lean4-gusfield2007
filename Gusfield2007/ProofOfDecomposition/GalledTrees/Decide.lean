module

public import Gusfield2007.External.GusfieldEtAl2004.Algorithm
public import Gusfield2007.ProofOfDecomposition.GalledTrees.Existence

/-!
# Gusfield, Eddhu, Langley 2004: the decision procedure, from the existence of reduced galled trees

`galledDecide` accepts exactly when a galled tree exists, through the pieces of `GalledTreeExistence`.
-/

@[expose] public section

namespace External.GusfieldEtAl2004.Algorithm

variable {m : ℕ} {β : Type*}

section Sound

open scoped Classical

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)}

end Sound

/-! ### If there is a galled tree, the test passes -/

section Complete

open scoped Classical

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {V E : Type*} {N : Network (Fin m) V E} [Finite V] {M : List (Row m)}

end Complete

/-! ### The decision -/

section Decide

open scoped Classical

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)}

/-- **The decision is sound, with a reduced galled tree.** If `galledDecide` says `true`, there is a reduced galled tree for `M` with ancestral sequence `S` and single crossovers. The hypotheses are the source's: there are rows, and each column has a `1`. -/
theorem exists_reduced_of_decide (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) (h : (galledDecide S M).1 = true) :
    ∃ (a b : ℕ) (N : Network (Fin m) (Fin a) (Fin b)), N.Obeys .single ∧ N.Derives M.toFinset ∧ N.ancestral = S ∧ IsReducedGalledTree N (conflictGraph S M.toFinset) := by
  rw [conflictGraph_eq_incompatGraph_addRow]
  have hS : S ∈ addRow M.toFinset S := mem_addRow.2 (Or.inl rfl)
  have hC' : NoConstantColumn (addRow M.toFinset S) := fun i => by
    obtain ⟨r, hr, hri⟩ := h1 i
    exact ⟨r, mem_addRow.2 (Or.inr (List.mem_toFinset.2 hr)), S, hS, hri⟩
  by_cases hne : ∃ r ∈ addRow M.toFinset S, r ≠ S
  · have hpiece : ∀ C : Cent (incompatGraph (addRow M.toFinset S)), ∃ (a b : ℕ) (P : Network C.1.supp (Fin a) (Fin b)), P.Obeys .single ∧ P.ancestral = C.1.supp.domRestrict S ∧ P.Derives ((restrictRows C.1.supp (addRow M.toFinset S)).erase (C.1.supp.domRestrict S)) ∧ P.recombCount ≤ 1 := by
      rintro ⟨c, hnt⟩
      obtain ⟨k₀, rfl⟩ := c.exists_rep
      have hall : ∀ c₀ ∈ ((List.finRange m).map (labOf (edgesOps S M).1)).dedup, (labelTest S M (labOf (edgesOps S M).1) c₀).1 = true := by
        simpa [galledDecide, allOps] using h
      have ht := hall _ (List.mem_dedup.2 (List.mem_map.2 ⟨k₀, List.mem_finRange k₀, rfl⟩))
      have hlen := (one_lt_length_iff (S := S) (M := M) k₀).2 hnt
      have hnot : ¬ ((List.finRange m).filter (fun k => decide (labOf (edgesOps S M).1 k = labOf (edgesOps S M).1 k₀))).length ≤ 1 := by omega
      simp only [labelTest, hnot, ite_false] at ht
      exact exists_piece_of_compTest _ (mem_filter_lab k₀) ht
    choose a b P hob hanc hder hrec using hpiece
    exact exists_reduced_of_pieces .single hC' hne P hob hanc (fun C => by convert hder C) hrec
  · push Not at hne
    have hι : IsEmpty (Fin m) := ⟨fun i => by
      obtain ⟨r, hr, hri⟩ := h1 i
      exact hri (by rw [hne r (mem_addRow.2 (Or.inr (List.mem_toFinset.2 hr)))])⟩
    have hMne : M.toFinset.Nonempty := by
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil M hM
      exact ⟨r, List.mem_toFinset.2 hr⟩
    obtain ⟨a', b', N', hr, hd, hs, -⟩ := External.Gusfield1991.exists_network_of_no_conflict M.toFinset S hMne hC' (fun i => hι.elim i)
    have hinj := Network.tgt_injective_of_no_recomb hr
    have hcyc : ∀ Q, ¬ N'.IsCycle Q := Network.not_isCycle_of_tgt_injective hinj
    exact ⟨a', b', N', Network.obeys_of_tgt_injective hinj _, hd, hs, fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q)⟩

/-- **The decision** (`ext:galled_decide`), Sections 3.1, 3.2 and 7 of the source, and Theorem 3.2. `galledDecide S M` says `true` exactly when there is a galled tree for `M` with ancestral sequence `S` and single crossovers. The hypotheses are the source's standing assumptions that there are rows and that each column has a `1`.

Departure from the source: Section 7 decides by running the whole algorithm, Sections 3 to 6, and checking the galled tree it built. Here the decision needs only the arrangement of each component, and the gluing of Theorem 1 of Gusfield et al. 2007 shows that those arrangements fit together: so the decision doesn't build the part of the network outside the galls. -/
theorem galledDecide_iff (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) :
    (galledDecide S M).1 = true ↔ ∃ (a b : ℕ) (N : Network (Fin m) (Fin a) (Fin b)), IsGalledTree N ∧ N.Obeys .single ∧ N.Derives M.toFinset ∧ N.ancestral = S := by
  constructor
  · intro h
    obtain ⟨a, b, N, h₁, h₂, h₃, h₄⟩ := exists_reduced_of_decide hM h1 h
    exact ⟨a, b, N, h₄.galled, h₁, h₂, h₃⟩
  · rintro ⟨a, b, N, hG, hc₁, hD, rfl⟩
    simp only [galledDecide, allOps, List.all_eq_true]
    intro c₀ hc₀
    obtain ⟨k₀, -, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 hc₀)
    unfold labelTest
    dsimp only
    split_ifs with hlen
    · rfl
    · have hnt := (one_lt_length_iff (S := N.ancestral) (M := M) k₀).1 (by omega)
      exact compTest_of_gall hG hc₁ hD _ hnt (mem_filter_lab k₀)

/-! ### The count of the decision -/

end Decide

end External.GusfieldEtAl2004.Algorithm
