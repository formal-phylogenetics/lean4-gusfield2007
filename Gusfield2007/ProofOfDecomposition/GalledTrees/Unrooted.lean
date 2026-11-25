module

public import Gusfield2007.External.GusfieldEtAl2004.ReducedUnrooted
public import Gusfield2007.ProofOfDecomposition.GalledTrees.Existence

/-!
# Gusfield, Eddhu, Langley 2004: reduced galled trees exist without an ancestral sequence

The unrooted forms of `GalledTreeExistence`: a galled tree reduced for `G(M)`, and `R = ` the number of non-trivial
components of `G(M)` for a matrix with one.
-/

@[expose] public noncomputable section

open scoped Classical

namespace External.GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {ι V E : Type*}

/-! ### Turning round an arc out of the root -/

section Turn

variable {κ V' E' : Type*} [Finite V']

variable {P : Network κ V' E'} {a : E'} {h₁ : P.src a = P.root} {h₂ : ∀ f, P.tgt f = P.tgt a → f = a}

end Turn

/-! ### A leaf that avoids the recombination nodes -/

section Avoid

variable {N : Network ι V E} [Finite V] {w x : V} {p q : List E}

variable {M : Finset (ι → Bool)}

end Avoid

/-! ### The network of a component, rooted at a row -/

section PieceAt

variable {N : Network ι V E} [Finite V] {w x : V} {p q : List E} {L : Finset (ι → Bool)}

end PieceAt

/-! ### The results -/

section Results

variable [LinearOrder ι] [Finite ι] {N : Network ι V E} [Finite V] {M : Finset (ι → Bool)}

/-- **Gusfield et al. 2007, line 180** (`g:reduced_exists`). "When there is a galled-tree for `M`, there is a reduced galled-tree for `M`", for `G(M)`: with some ancestral sequence, a row of `M`, in the same crossover model. The standing assumption of Gusfield et al. 2007 on the columns is the hypothesis.
With a known ancestral sequence, this is Corollary 5.1 of Gusfield, Eddhu, Langley 2004 (`exists_isReducedGalledTree`). The head of this file says how this form is proved, and that the second reference of line 180 wasn't read. -/
theorem exists_isReducedGalledTree_incompatGraph (hG : IsGalledTree N) (hD : N.Derives M) (hC : NoConstantColumn M) {c : Crossover} (hc : N.Obeys c) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ IsReducedGalledTree N' (incompatGraph M) := by
  obtain ⟨y, hleaf, hy⟩ := exists_leaf_avoiding hG hD
  have hyM : N.label y ∈ M := Finset.mem_coe.1 (hD.mapsTo hleaf)
  have heq : addRow M (N.label y) = M := addRow_eq_of_mem hyM
  have hL : ∀ r ∈ addRow M (N.label y), ∃ v, N.label v = r := fun r hr => hD.displays r (heq ▸ hr)
  have hy' : ∀ w x p q, N.IsCycleOn w x p q → HasConflict N (addRow M (N.label y)) {e | e ∈ p ∨ e ∈ q} → ¬ N.Reach x y := by
    rw [heq]
    exact hy
  have hC' : NoConstantColumn (addRow M (N.label y)) := hC.addRow _
  by_cases hne : ∃ r ∈ addRow M (N.label y), r ≠ N.label y
  · choose a b P hob hanc hder hrec using fun C : Cent (incompatGraph (addRow M (N.label y))) => exists_gall_piece_at hG hL C hy'
    obtain ⟨a', b', N', h₁, h₂, -, h₄⟩ := exists_reduced_of_pieces c hC' hne P (fun C => hob C c hc) hanc hder hrec
    rw [heq] at h₄
    exact ⟨a', b', N', h₁, h₂, h₄⟩
  · push Not at hne
    have hι : IsEmpty ι := ⟨fun i => by
      obtain ⟨r, hr, r', hr', hrr⟩ := hC i
      rw [hne r (by rw [heq]; exact hr), hne r' (by rw [heq]; exact hr')] at hrr
      exact hrr rfl⟩
    obtain ⟨a', b', N', hr, hd, -, -⟩ := External.Gusfield1991.exists_network_of_no_conflict M (N.label y) hD.nonempty hC' (fun i => hι.elim i)
    have hinj := Network.tgt_injective_of_no_recomb hr
    have hcyc : ∀ Q, ¬ N'.IsCycle Q := Network.not_isCycle_of_tgt_injective hinj
    exact ⟨a', b', N', Network.obeys_of_tgt_injective hinj c, hd, fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q)⟩

/-- **Gusfield et al. 2007, line 381** (`g:line381_of_galled`). "The answer is yes when `M` can be derived on a galled-tree, even if the galled-tree must only use single-crossover recombinations, but any competing phylogenetic network is allowed to use multiple-crossovers": if `M` can be derived on a galled tree in the model `c`, then it is min decomposable, for `c` and for multiple crossovers. -/
theorem minDecomposable_of_isGalledTree (hG : IsGalledTree N) (hD : N.Derives M) (hC : NoConstantColumn M) {c : Crossover} (hc : N.Obeys c) :
    MinDecomposable c M ∧ MinDecomposable .multiple M := by
  obtain ⟨a, b, N', h₁, h₂, h₄⟩ := exists_isReducedGalledTree_incompatGraph hG hD hC hc
  exact line381 h₄ h₂ h₁

/-- **Gusfield et al. 2007, line 381**, the value (`g:line381_of_galled`): if `M` can be derived on a galled tree in the model `c`, then `R(M)`, for `c` and for multiple crossovers, is the number of non-trivial components of `G(M)`. -/
theorem R_eq_card_cent (hG : IsGalledTree N) (hD : N.Derives M) (hC : NoConstantColumn M) {c : Crossover} (hc : N.Obeys c) :
    R c M = Nat.card (Cent (incompatGraph M)) ∧ R .multiple M = Nat.card (Cent (incompatGraph M)) := by
  obtain ⟨a, b, N', h₁, h₂, h₄⟩ := exists_isReducedGalledTree_incompatGraph hG hD hC hc
  obtain ⟨h₅, h₆⟩ := reducedGalledTree_recombCount_eq_R h₄ h₂ h₁
  have h₇ := h₄.recombCount_eq_incompatGraph h₂
  exact ⟨h₅.symm.trans h₇, h₆.symm.trans h₇⟩

end Results

end External.GusfieldEtAl2004
