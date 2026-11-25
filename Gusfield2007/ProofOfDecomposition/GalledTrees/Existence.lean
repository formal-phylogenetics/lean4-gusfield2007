module

public import Gusfield2007.External.GusfieldEtAl2004.ReducedExists
public import Gusfield2007.ProofOfDecomposition.Decomposition

/-!
# Gusfield, Eddhu, Langley 2004: reduced galled trees exist, by the construction of the Decomposition Theorem

Corollary 5.1 of the source for galled trees (`External.GusfieldEtAl2004.exists_isReducedGalledTree`), Theorem 2.7 and the
counts `R_S = ` the number of non-trivial components, proved by gluing a gall for each component into `T̄`, as the proof of
Theorem 1 glues blobs (lines 299 to 303), rather than by the source's moves of sites. The statements are the source's, in
its namespace; they are in the paper's library because their proofs use its construction. The source's other results are in
`Gusfield2007/External/GusfieldEtAl2004/`.
-/

@[expose] public noncomputable section

open scoped Classical

namespace External.GusfieldEtAl2004

open Gusfield2007 Gusfield2007.Network Gusfield2007.Decomp

variable {ι V E : Type*}

/-! ### Blobs with one recombination node -/

section OneRecomb

variable {N : Network ι V E} {w x w' : V} {p q p' q' : List E}

/-- A fully decomposed network with as few recombination nodes as non-trivial components is a galled tree: each blob has a recombination node, and the blobs are node-disjoint, so each has just one, and is one cycle. -/
theorem isGalledTree_of_isFullyDecomposedFor [Finite V] [Finite ι] {G : SimpleGraph ι} (h : N.IsFullyDecomposedFor G)
    (hG : ∀ c : G.ConnectedComponent, c.supp.Nontrivial → ∃ B, N.IsBlob B ∧ ∀ i ∈ c.supp, N.site i ∈ B) (hcount : N.recombCount ≤ Nat.card (Cent G)) : IsGalledTree N := by
  obtain ⟨⟨f, -⟩, hd⟩ := (isFullyDecomposedFor_iff_correspondence N G hG).1 h
  -- the recombination node of a cycle of the blob
  have hrecOf : ∀ B : {B : Set E // N.IsBlob B}, ∃ x, N.IsRecomb x ∧ x ∈ N.blobVerts B.1 := by
    rintro ⟨B, hB⟩
    obtain ⟨Q, hQ, hBQ⟩ := id hB
    obtain ⟨w, x, p, q, hc, rfl⟩ := id hQ
    obtain ⟨a, -, ha, -, -, hax, -⟩ := cycle_last_arcs hc
    have haB : a ∈ B := by
      rw [hBQ]
      exact ⟨_, Relation.ReflTransGen.refl, Or.inl ha⟩
    exact ⟨x, hc.1, Or.inr ⟨a, haB, hax⟩⟩
  choose g hgr hgv using hrecOf
  have hdisj : ∀ {B B' : Set E}, N.IsBlob B → N.IsBlob B' → ∀ v, v ∈ N.blobVerts B → v ∈ N.blobVerts B' → B = B' := by
    intro B B' hB hB' v hv hv'
    by_contra hne
    exact Set.disjoint_left.1 (hd B B' hB hB' hne) hv hv'
  have hinj : Function.Injective fun B : {B : Set E // N.IsBlob B} => (⟨g B, hgr B⟩ : {x // N.IsRecomb x}) := by
    intro B B' hBB
    have hx : g B = g B' := congrArg Subtype.val hBB
    exact Subtype.ext (hdisj B.2 B'.2 _ (hgv B) (hx ▸ hgv B'))
  have hcard : Nat.card {x // N.IsRecomb x} ≤ Nat.card {B : Set E // N.IsBlob B} := by
    rw [← Nat.card_congr f]
    exact hcount
  have hsurj := (hinj.bijective_of_nat_card_le hcard).2
  -- a recombination node of a blob is its node
  have honly : ∀ {B : Set E} (hB : N.IsBlob B) (y : V), N.IsRecomb y → y ∈ N.blobVerts B → y = g ⟨B, hB⟩ := by
    intro B hB y hy hyv
    obtain ⟨B', hB'⟩ := hsurj ⟨y, hy⟩
    have hyB' : g B' = y := congrArg Subtype.val hB'
    have heq : B'.1 = B := hdisj B'.2 hB _ (hgv B') (hyB'.symm ▸ hyv)
    have : B' = ⟨B, hB⟩ := Subtype.ext heq
    rw [← hyB', this]
  -- each cycle is in a blob, and two cycles with a node in common are in one blob
  have hblobOf : ∀ {Q : Set E}, N.IsCycle Q → ∃ B, N.IsBlob B ∧ Q ⊆ B := by
    intro Q hQ
    refine ⟨_, ⟨Q, hQ, rfl⟩, fun e he => ⟨Q, Relation.ReflTransGen.refl, he⟩⟩
  have hvertsMono : ∀ {Q B : Set E}, Q ⊆ B → N.blobVerts Q ⊆ N.blobVerts B := by
    rintro Q B hQB v (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩)
    · exact Or.inl ⟨e, hQB he, rfl⟩
    · exact Or.inr ⟨e, hQB he, rfl⟩
  intro Q hQ
  refine ⟨hQ, fun Q' hQ' hne => ?_⟩
  rw [Set.disjoint_left]
  intro v hv hv'
  apply hne
  obtain ⟨B, hB, hQB⟩ := hblobOf hQ
  obtain ⟨B', hB', hQB'⟩ := hblobOf hQ'
  obtain rfl := hdisj hB hB' v (hvertsMono hQB hv) (hvertsMono hQB' hv')
  obtain ⟨w, x, p, q, hc, rfl⟩ := hQ
  obtain ⟨w', x', p', q', hc', rfl⟩ := hQ'
  have hmem : ∀ {w₀ x₀ : V} {p₀ q₀ : List E}, N.IsCycleOn w₀ x₀ p₀ q₀ → x₀ ∈ N.blobVerts {e | e ∈ p₀ ∨ e ∈ q₀} := by
    intro w₀ x₀ p₀ q₀ hc₀
    obtain ⟨a, -, ha, -, -, hax, -⟩ := cycle_last_arcs hc₀
    exact Or.inr ⟨a, Or.inl ha, hax⟩
  have hx : x = g ⟨B, hB⟩ := honly hB x hc.1 (hvertsMono hQB (hmem hc))
  have hx' : x' = g ⟨B, hB⟩ := honly hB x' hc'.1 (hvertsMono hQB' (hmem hc'))
  obtain rfl : x' = x := hx'.trans hx.symm
  refine (cycle_unique hc hc' fun y hy hyv hr => hy ?_).symm
  rw [hx]
  exact honly hB y hr (hvertsMono hQB hyv)

end OneRecomb

/-! ### The network of a gall -/

section Piece

variable {N : Network ι V E} [Finite V] {w x : V} {p q : List E}

variable {L : Finset (ι → Bool)}

end Piece

/-! ### Gluing -/

section Glue

variable [LinearOrder ι] [Finite ι] {N : Network ι V E} [Finite V] {M : Finset (ι → Bool)}

omit [LinearOrder ι] [Finite V] in
/-- The two facts on a network deriving `M`, fully decomposed, with as few recombination nodes as non-trivial components: it is a reduced galled tree. -/
theorem isReducedGalledTree_of_count [Finite V] {L : Finset (ι → Bool)} (hL : ∀ r ∈ L, ∃ v, N.label v = r) (hfd : N.IsFullyDecomposedFor (incompatGraph L)) (hcount : N.recombCount ≤ Nat.card (Cent (incompatGraph L))) :
    IsReducedGalledTree N (incompatGraph L) := by
  refine isReducedGalledTree_of_isFullyDecomposedFor (isGalledTree_of_isFullyDecomposedFor hfd (fun c' hc' => ?_) hcount) hfd
  obtain ⟨i, j, hi, hij⟩ := Cent.exists_adj (⟨c', hc'⟩ : Cent (incompatGraph L))
  obtain ⟨B, hB, hB', -⟩ := exists_isBlob_of_incompatible N hL hij
  refine ⟨B, hB, fun k hk => ?_⟩
  obtain ⟨c'', -, hc''⟩ := hfd.blob_component B hB
  have hic : i ∈ c''.supp := (hc'' i).1 hB'
  have hi' : i ∈ c'.supp := hi
  have hcc : c' = c'' := hi'.symm.trans hic
  exact (hc'' k).2 (hcc ▸ hk)

/-- **The gluing.** Networks with at most one recombination node for the non-trivial components of `G(M + S)`, on the rows of `M + S` other than `S`, glue to a reduced galled tree for `M` with ancestral sequence `S`: the construction of Theorem 1 of Gusfield et al. 2007, whose proof is `IsTBar.exists_glued`. -/
theorem exists_reduced_of_pieces (c : Crossover) {S : ι → Bool} (hC' : NoConstantColumn (addRow M S)) (hne : ∃ r ∈ addRow M S, r ≠ S) {a b : Cent (incompatGraph (addRow M S)) → ℕ}
    (P : ∀ C : Cent (incompatGraph (addRow M S)), Network C.1.supp (Fin (a C)) (Fin (b C))) (hob : ∀ C, (P C).Obeys c) (hanc : ∀ C, (P C).ancestral = C.1.supp.domRestrict S)
    (hder : ∀ C, (P C).Derives ((restrictRows C.1.supp (addRow M S)).erase (C.1.supp.domRestrict S))) (hrec : ∀ C, (P C).recombCount ≤ 1) :
    ∃ (a' b' : ℕ) (N' : Network ι (Fin a') (Fin b')), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = S ∧ IsReducedGalledTree N' (incompatGraph (addRow M S)) := by
  have hS : S ∈ addRow M S := mem_addRow.2 (Or.inl rfl)
  have hM' : (addRow M S).Nonempty := ⟨S, hS⟩
  have : Finite (incompatGraph (addRow M S)).ConnectedComponent := Finite.of_surjective (incompatGraph (addRow M S)).connectedComponentMk fun c => c.exists_rep
  have hP := fun C => piece_blob C (hanc C) (hder C) (hrec C)
  have hsum : ∑ᶠ C, (P C).recombCount ≤ Nat.card (Cent (incompatGraph (addRow M S))) := by
    have : Fintype (Cent (incompatGraph (addRow M S))) := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun C _ => hrec C
  obtain ⟨n, T, φ, edge, h⟩ := exists_isTBar (addRow M S) hM' hC'
  obtain ⟨V', E', hV, hE, N₁, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h.exists_glued P hS hC' hanc hder hne
  have hob' : N₁.Obeys c := h₁ c hob
  have hfd := h₅ hP
  -- the row `S` gets a new leaf, if it is one of `M`
  obtain ⟨V₂, E₂, hV₂, hE₂, N₂, h₂₁, h₂₂, h₂₃, h₂₄, h₂₅⟩ : ∃ (V₂ E₂ : Type _) (_ : Finite V₂) (_ : Finite E₂) (N₂ : Network ι V₂ E₂), N₂.Obeys c ∧ N₂.Derives M ∧ N₂.ancestral = S ∧
      N₂.IsFullyDecomposedFor (incompatGraph (addRow M S)) ∧ N₂.recombCount ≤ Nat.card (Cent (incompatGraph (addRow M S))) := by
    by_cases hSM : S ∈ M
    · have hl : N₁.label N₁.root = S := h₂
      refine ⟨Option V', Option E', inferInstance, inferInstance, Decomp.addLeaf N₁ N₁.root, Decomp.addLeaf_obeys hob', ?_, h₂, Decomp.addLeaf_fullyDecomposed hfd, Decomp.addLeaf_recombCount.trans_le (h₆ ▸ hsum)⟩
      have hd := Decomp.addLeaf_derives h₃ h₄ (by rw [hl]; simp)
      rwa [hl, addRow_eq_of_mem hSM, Finset.insert_erase hSM] at hd
    · have heq : (addRow M S).erase S = M := Finset.erase_insert hSM
      exact ⟨V', E', hV, hE, N₁, hob', heq ▸ h₃, h₂, hfd, h₆ ▸ hsum⟩
  obtain ⟨a', b', N', eV, eE, hiso⟩ := N₂.exists_fin_iso
  obtain ⟨i₁, i₂, i₃, i₄, i₅⟩ := hiso.invariants
  have hD' : N'.Derives M := (i₃ M).2 h₂₂
  have hanc' : N'.ancestral = S := i₄.trans h₂₃
  have hlab' : ∀ r ∈ addRow M S, ∃ v, N'.label v = r := hanc' ▸ labels_addRow hD'
  exact ⟨a', b', N', (i₂ c).2 h₂₁, hD', hanc', isReducedGalledTree_of_count hlab' ((i₅ _).2 h₂₄) (i₁.trans_le h₂₅)⟩

/-- **Corollary 5.1** (`ext:cor5_1`) of the source. "If there is a galled-tree for `M`, then there is a reduced galled-tree for `M`": with the same ancestral sequence and in the same crossover model. The hypothesis is the source's standing assumption that each column has a `1`.
See the head of this file for the difference from the source. The number of recombination nodes is `IsReducedGalledTree.recombCount_eq`, and that it is the minimum over galled trees is `corollary5_1_min`. Line 180 of Gusfield et al. 2007, unrooted, is `exists_isReducedGalledTree_incompatGraph`. -/
theorem exists_isReducedGalledTree (hG : IsGalledTree N) (hD : N.Derives M) (h1 : ∀ i, ∃ r ∈ M, r i ≠ N.ancestral i) {c : Crossover} (hc : N.Obeys c) :
    ∃ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), N'.Obeys c ∧ N'.Derives M ∧ N'.ancestral = N.ancestral ∧ IsReducedGalledTree N' (conflictGraph N.ancestral M) := by
  have hL : ∀ r ∈ addRow M N.ancestral, ∃ v, N.label v = r := labels_addRow hD
  have hS : N.ancestral ∈ addRow M N.ancestral := mem_addRow.2 (Or.inl rfl)
  have hC' : NoConstantColumn (addRow M N.ancestral) := fun i => by
    obtain ⟨r, hr, hri⟩ := h1 i
    exact ⟨r, mem_addRow.2 (Or.inr hr), _, hS, hri⟩
  have hM : M.Nonempty := hD.nonempty
  rw [conflictGraph_eq_incompatGraph_addRow]
  by_cases hne : ∃ r ∈ addRow M N.ancestral, r ≠ N.ancestral
  · choose a b P hob hanc hder hrec using fun C : Cent (incompatGraph (addRow M N.ancestral)) => exists_gall_piece hG hL C
    exact exists_reduced_of_pieces c hC' hne P (fun C => hob C c hc) hanc hder hrec
  · -- all the rows are `S`, and so there are no sites
    push Not at hne
    have hι : IsEmpty ι := ⟨fun i => by
      obtain ⟨r, hr, hri⟩ := h1 i
      exact hri (by rw [hne r (mem_addRow.2 (Or.inr hr))])⟩
    obtain ⟨a', b', N', hr, hd, hs, -⟩ := External.Gusfield1991.exists_network_of_no_conflict M N.ancestral hM hC' (fun i => hι.elim i)
    have hinj := Network.tgt_injective_of_no_recomb hr
    have hcyc : ∀ Q, ¬ N'.IsCycle Q := Network.not_isCycle_of_tgt_injective hinj
    exact ⟨a', b', N', Network.obeys_of_tgt_injective hinj c, hd, hs, fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q), fun Q hQ => absurd hQ (hcyc Q)⟩

/-- **Theorem 2.7** (`ext:thm2_7`) of the source, its first sentence. "If the conflict graph for `M` has `k` non-trivial connected components, and there is a galled-tree for `M`, then any galled-tree that minimizes the number of recombinations (over all galled-trees) uses exactly `k` recombinations." Here for the
galled trees with the ancestral sequence and in the crossover model of the given one. The source's hypothesis on the columns is needed: see the head of this file.

The source proves it by replacing a gall with no conflicted sites by a perfect phylogeny. Departure from the source: the minimum is compared with the reduced galled tree of `exists_isReducedGalledTree`, and the galled tree has a recombination node for each component by Theorem 2.6. The head of this file says why. -/
theorem theorem2_7 (hG : IsGalledTree N) (hD : N.Derives M) (h1 : ∀ i, ∃ r ∈ M, r i ≠ N.ancestral i) {c : Crossover} (hc : N.Obeys c)
    (hmin : ∀ (a b : ℕ) (N' : Network ι (Fin a) (Fin b)), IsGalledTree N' → N'.Obeys c → N'.Derives M → N'.ancestral = N.ancestral → N.recombCount ≤ N'.recombCount) :
    N.recombCount = Nat.card (Cent (conflictGraph N.ancestral M)) := by
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := exists_isReducedGalledTree hG hD h1 hc
  have h₄' : IsReducedGalledTree N' (conflictGraph N'.ancestral M) := by
    rw [h₃]
    exact h₄
  have h₅ := h₄'.recombCount_eq h₂
  rw [h₃] at h₅
  refine le_antisymm ((hmin a b N' h₄.galled h₁ h₂ h₃).trans_eq h₅) ?_
  rw [conflictGraph_eq_incompatGraph_addRow]
  exact card_cent_le_recombCount hG (labels_addRow hD)

/-- **Gusfield et al. 2007, line 381**, for any galled tree (`g:line381_of_galled`): "the answer is yes when `M` can be derived on a galled-tree". If `M` can be derived on a galled tree with ancestral sequence `S`, in the model `c`, then it is S-min decomposable for `c`, and for multiple crossovers: there is a fully decomposed network with the least possible number of recombination nodes. -/
theorem sMinDecomposable_of_isGalledTree (hG : IsGalledTree N) (hD : N.Derives M) (h1 : ∀ i, ∃ r ∈ M, r i ≠ N.ancestral i) {c : Crossover} (hc : N.Obeys c) :
    SMinDecomposable c N.ancestral M ∧ SMinDecomposable .multiple N.ancestral M := by
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := exists_isReducedGalledTree hG hD h1 hc
  rw [← h₃] at h₄ ⊢
  exact line381_rooted h₄ h₂ h₁

/-- **Corollary 5.1 and Theorem 8.3 of the source**, the value: if `M` can be derived on a galled tree with ancestral sequence `S`, in the model `c`, then `R_S(M)`, for `c` and for multiple crossovers, is the number of non-trivial components of `G_S(M)`. -/
theorem RS_eq_card_cent [Finite E] (hG : IsGalledTree N) (hD : N.Derives M) (h1 : ∀ i, ∃ r ∈ M, r i ≠ N.ancestral i) {c : Crossover} (hc : N.Obeys c) :
    RS c N.ancestral M = Nat.card (Cent (conflictGraph N.ancestral M)) ∧ RS .multiple N.ancestral M = Nat.card (Cent (conflictGraph N.ancestral M)) := by
  obtain ⟨a, b, N', h₁, h₂, h₃, h₄⟩ := exists_isReducedGalledTree hG hD h1 hc
  rw [← h₃] at h₄ ⊢
  obtain ⟨h₅, h₆⟩ := reducedGalledTree_recombCount_eq_RS h₄ h₂ h₁
  have h₇ := h₄.recombCount_eq h₂
  exact ⟨h₅.symm.trans h₇, h₆.symm.trans h₇⟩

end Glue

end External.GusfieldEtAl2004
