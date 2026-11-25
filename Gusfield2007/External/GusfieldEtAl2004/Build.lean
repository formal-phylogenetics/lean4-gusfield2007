module

public import Gusfield2007.External.GusfieldEtAl2004.Algorithm
public import Mathlib.Data.List.MinMax
public import Gusfield2007.Basic.Data.List

/-!
# The reduced galled tree, computed (Gusfield, Eddhu, Langley 2004, Sections 3 to 6)

See the `README.md` of this directory. `Algorithm.lean` decides. This module builds the network from the arrangements of the components, as functions on explicit nodes:

* the rows below a node are its cluster (`GNode.cl`): for a component with sites `C`, `top c` has the rows with a state other than the ancestral sequence's on `C`, and `part c σ` the rows equal to `σ` on `C`, one node of the gall for each;
* a node is below another when its cluster is inside the other's (`Up`), which is the source's ancestry of galls (Section 4) and its placing of the unconflicted sites and the leaves (Section 6) at once: Theorem 2 of Gusfield et al. 2007 says that the clusters are nested or disjoint (`trichotomy`);
* the nodes of a gall are chained as the arrangement says (Section 3.2).

`galledBuild S M` is the function: `none` when there is no galled tree (`galledBuild_isSome_iff`), and otherwise a table of nodes, parents and labels, which is a reduced galled tree (`galledBuild_correct`). Its count is in `BuildCount.lean`.

Departure from the source: its Sections 4 and 6 connect the galls by comparing the numbers of `1`s in columns, and walk the unconflicted sites up from the leaves, with cases, and its Section 7 then checks the result. Here one rule, inclusion of clusters, gives all the parents outside the galls, and the proof shows that no check is needed: Theorem 2 of Gusfield et al. 2007 is the ancestry of the galls. The recombination point isn't read from the bipartition of Lemma 3.1, but tried.
-/

@[expose] public section

namespace External.GusfieldEtAl2004.Algorithm

variable {m : ℕ}

/-- The nodes: the root, the top of a component (its coalescent node, or the node below the arc of a site alone in its component), a node of a gall for a sequence of the component, and a leaf for a row. -/
inductive GNode (m : ℕ) where
  | root : GNode m
  | top (c : Fin m) : GNode m
  | part (c : Fin m) (σ : Row m) : GNode m
  | leaf (r : Row m) : GNode m

instance : DecidableEq (GNode m)
  | .root, .root => isTrue rfl
  | .top a, .top b => if h : a = b then isTrue (by rw [h]) else isFalse (by simpa using h)
  | .part a σ, .part b τ => if h : a = b then (if h' : σ = τ then isTrue (by rw [h, h']) else isFalse (by simp [h'])) else isFalse (by simp [h])
  | .leaf a, .leaf b => if h : a = b then isTrue (by rw [h]) else isFalse (by simpa using h)
  | .root, .top _ | .root, .part _ _ | .root, .leaf _ | .top _, .root | .top _, .part _ _ | .top _, .leaf _
  | .part _ _, .root | .part _ _, .top _ | .part _ _, .leaf _ | .leaf _, .root | .leaf _, .top _ | .leaf _, .part _ _ => isFalse (by simp)

/-- An arrangement: the row at the recombination node, and the two chains, the second supplying the prefix. -/
abbrev Arr (m : ℕ) := Row m × List (Row m) × List (Row m)

section Core

variable (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (ar : Fin m → Arr m)

/-- The sites of a component. -/
def sitesOf (c : Fin m) : List (Fin m) := (List.finRange m).filter fun k => f k = c

/-- The component has conflicts. -/
def isNT (c : Fin m) : Bool := decide (1 < (sitesOf f c).length)

/-- The row on the sites of a component, and the ancestral sequence elsewhere. -/
def mkRow (c : Fin m) (r : Row m) : Row m := fun i => if f i = c then r i else S i

/-- The sequences of a component other than the ancestral one. -/
def rowsOf (c : Fin m) : List (Row m) := ((M.map (mkRow S f c)).dedup).filter fun σ => σ ≠ S

/-- Which rows are below a node. -/
def GNode.cl : GNode m → Row m → Bool
  | .root, _ => true
  | .top c, r => decide (mkRow S f c r ≠ S)
  | .part c σ, r => decide (mkRow S f c r = σ)
  | .leaf ρ, r => decide (r = ρ)

/-- The order of nodes with one cluster: a node of a gall, then a site alone, then a coalescent node, then a leaf. -/
def GNode.rank : GNode m → ℕ
  | .root => 0
  | .part _ _ => 1
  | .top c => if isNT f c then 3 else 2
  | .leaf _ => 4

/-- A number to break ties. -/
def GNode.idx : GNode m → ℕ
  | .top c => c.val
  | .part c _ => c.val
  | _ => 0

/-- `u` is above `v`, in the order of clusters. -/
def Up (u v : GNode m) : Bool :=
  decide (u ≠ v) && M.all (fun r => !v.cl S f r || u.cl S f r) &&
    (!(M.all fun r => !u.cl S f r || v.cl S f r) || decide (u.rank f < v.rank f) || (decide (u.rank f = v.rank f) && decide (u.idx < v.idx)))

/-- A number that goes up along `Up`. -/
def key (u : GNode m) : ℕ := (M.length - (M.filter (u.cl S f)).length) * (6 * (m + 1)) + u.rank f * (m + 1) + u.idx

/-- The labels of the components. -/
def reps : List (Fin m) := ((List.finRange m).map f).dedup

/-- The nodes that can be parents of a node by clusters. -/
def cands : List (GNode m) := .root :: (reps f).map .top ++ ((reps f).filter (isNT f)).flatMap fun c => (rowsOf S M f c).map (.part c)

/-- The parent of a node by clusters: the lowest node above it. -/
def treePar (v : GNode m) : Option (GNode m) := ((cands S M f).filter fun u => Up S M f u v).argmax (key S M f)

/-- The number of `1`s of a row. -/
def card1 (y : Row m) : ℕ := ((List.finRange m).filter fun i => y i != S i).length

/-- The end of a chain, or the coalescent node. -/
def endNode (c : Fin m) (X : List (Row m)) : GNode m :=
  match X.argmax (card1 S) with
  | some y => .part c y
  | none => .top c

/-- The node before a row on a chain, or the coalescent node. -/
def predNode (c : Fin m) (X : List (Row m)) (σ : Row m) : GNode m := endNode S c (X.filter fun y => card1 S y < card1 S σ)

/-- The parent of a node. -/
def par : GNode m → Option (GNode m)
  | .root => none
  | .part c σ =>
    if σ = (ar c).1 then some (endNode S c (ar c).2.1)
    else if σ ∈ (ar c).2.1 then some (predNode S c (ar c).2.1 σ) else some (predNode S c (ar c).2.2 σ)
  | v => treePar S M f v

/-- The other parent of a node: of the recombination node of a gall. -/
def par₂ : GNode m → Option (GNode m)
  | .part c σ => if σ = (ar c).1 then some (endNode S c (ar c).2.2) else none
  | _ => none

/-- The **arrangement** of a component, the first that the Site-Arrangement Algorithm accepts: the two chains are ordered so that the second supplies the prefix. -/
def arrOf (c : Fin m) : Arr m :=
  match (rowsOf S M f c).find? (fun s => (candidate S (sitesOf f c) (rowsOf S M f c) s).1) with
  | none => (S, [], [])
  | some s =>
    match (filterOps (rowsOf S M f c) fun r => (!(eqOn (sitesOf f c) r s).1, (eqOn (sitesOf f c) r s).2)).1 with
    | [] => (s, [], [])
    | seed :: tl =>
      if (List.range (m + 1)).any (fun n => (recombOk S (sitesOf f c) (filterOps (seed :: tl) (cmpOn S (sitesOf f c) seed)).1 (filterOps (seed :: tl) fun r => (!(cmpOn S (sitesOf f c) seed r).1, (cmpOn S (sitesOf f c) seed r).2)).1 s n).1) then
        (s, (filterOps (seed :: tl) (cmpOn S (sitesOf f c) seed)).1, (filterOps (seed :: tl) fun r => (!(cmpOn S (sitesOf f c) seed r).1, (cmpOn S (sitesOf f c) seed r).2)).1)
      else
        (s, (filterOps (seed :: tl) fun r => (!(cmpOn S (sitesOf f c) seed r).1, (cmpOn S (sitesOf f c) seed r).2)).1, (filterOps (seed :: tl) (cmpOn S (sitesOf f c) seed)).1)

/-- The node below the arc of a site. -/
def siteNode (i : Fin m) : GNode m :=
  if isNT f (f i) then
    match (((ar (f i)).2.1 ++ (ar (f i)).2.2).filter fun y => y i != S i).argmin (card1 S) with
    | some y => .part (f i) y
    | none => .root
  else .top (f i)

/-- The label of a node: on a site alone in its component, whether its arc is above; on a component, the sequence of the gall node above, or the node's own. -/
def label (v : GNode m) (i : Fin m) : Bool :=
  if isNT f (f i) then
    match v with
    | .part c σ => if c = f i then σ i else
      (match (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) with
        | some τ => τ i
        | none => S i)
    | _ =>
      (match (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) with
        | some τ => τ i
        | none => S i)
  else if v = .top (f i) || Up S M f (.top (f i)) v then !S i else S i

end Core

/-! ### The clusters are nested or disjoint -/

section Laminar

open scoped Classical

open Gusfield2007 Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)} {f : Fin m → Fin m}

/-- The components, as labels. -/
def IsLab (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) : Prop := ∀ k l, f k = f l ↔ (incompatGraph (addRow M.toFinset S)).Reachable k l

theorem mk_ne_iff {c : Fin m} {r : Row m} : mkRow S f c r ≠ S ↔ ∃ i, f i = c ∧ r i ≠ S i := by
  constructor
  · intro h
    by_contra hno
    push Not at hno
    refine h (funext fun i => ?_)
    by_cases hi : f i = c
    · simp only [mkRow, hi, ite_true]
      exact hno i hi
    · simp [mkRow, hi]
  · rintro ⟨i, hi, hri⟩ h
    apply hri
    have := congrFun h i
    simpa [mkRow, hi] using this

theorem mem_rowsOf {c : Fin m} {σ : Row m} : σ ∈ rowsOf S M f c ↔ (∃ r ∈ M, mkRow S f c r = σ) ∧ σ ≠ S := by
  simp [rowsOf]

theorem mk_mk {c : Fin m} {r : Row m} : mkRow S f c (mkRow S f c r) = mkRow S f c r := by
  funext i
  by_cases hi : f i = c <;> simp [mkRow, hi]

/-- The nodes of the network. -/
def Valid (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) : GNode m → Prop
  | .root => True
  | .top c => ∃ k, f k = c
  | .part c σ => isNT f c = true ∧ σ ∈ rowsOf S M f c
  | .leaf r => r ∈ M

/-- The rows below `u` are below `v`. -/
def SubCl (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (u v : GNode m) : Prop := ∀ r ∈ M, u.cl S f r = true → v.cl S f r = true

theorem SubCl.trans' {u v w : GNode m} (h₁ : SubCl S M f u v) (h₂ : SubCl S M f v w) : SubCl S M f u w := fun r hr h => h₂ r hr (h₁ r hr h)

/-- The order on nodes with one cluster. -/
def Tie (f : Fin m → Fin m) (u v : GNode m) : Prop := u.rank f < v.rank f ∨ (u.rank f = v.rank f ∧ u.idx < v.idx)

theorem up_iff {u v : GNode m} : Up S M f u v = true ↔ u ≠ v ∧ SubCl S M f v u ∧ (SubCl S M f u v → Tie f u v) := by
  have himp : ∀ a b : Bool, ((!a || b) = true) ↔ (a = true → b = true) := by decide
  have hall : ∀ {x y : GNode m}, M.all (fun r => !x.cl S f r || y.cl S f r) = true ↔ SubCl S M f x y := by
    intro x y
    simp only [List.all_eq_true, himp, SubCl]
  simp only [Up, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, hall]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨h₁, h₂, fun h₄ => ?_⟩
    have h₅ : M.all (fun r => !u.cl S f r || v.cl S f r) = true := hall.2 h₄
    rcases h₃ with (h₆ | h₆) | h₆
    · rw [h₅] at h₆
      exact absurd h₆ (by simp)
    · exact Or.inl h₆
    · exact Or.inr h₆
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨⟨h₁, h₂⟩, ?_⟩
    by_cases h₄ : SubCl S M f u v
    · rcases h₃ h₄ with h₅ | h₅
      · exact Or.inl (Or.inr h₅)
      · exact Or.inr h₅
    · refine Or.inl (Or.inl ?_)
      by_contra h₅
      exact h₄ (hall.1 (by simpa only [Bool.not_eq_false] using h₅))

variable {u v w : GNode m}

theorem up_irrefl : Up S M f u u = false := Bool.eq_false_iff.2 fun h => (up_iff.1 h).1 rfl

theorem Tie.trans' {a b c : GNode m} (h₁ : Tie f a b) (h₂ : Tie f b c) : Tie f a c := by
  unfold Tie at *
  omega

theorem Tie.irrefl' {a : GNode m} : ¬ Tie f a a := by
  unfold Tie
  omega

theorem up_trans (h₁ : Up S M f u v = true) (h₂ : Up S M f v w = true) : Up S M f u w = true := by
  obtain ⟨hne, hs, ht⟩ := up_iff.1 h₁
  obtain ⟨hne', hs', ht'⟩ := up_iff.1 h₂
  refine up_iff.2 ⟨?_, hs'.trans' hs, fun h => ?_⟩
  · rintro rfl
    exact Tie.irrefl' ((ht hs').trans' (ht' hs))
  · exact (ht (h.trans' hs')).trans' (ht' (hs.trans' h))

/-- The standing hypotheses on the rows and the labels. -/
structure Std (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) : Prop where
  lab : IsLab S M f
  ne : M ≠ []
  one : ∀ i, ∃ r ∈ M, r i ≠ S i

theorem Std.nonempty_cl (hs : Std S M f) (hv : Valid S M f v) : ∃ r ∈ M, v.cl S f r = true := by
  cases v with
  | root =>
    obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil M hs.ne
    exact ⟨r, hr, rfl⟩
  | top c =>
    obtain ⟨k, rfl⟩ := hv
    obtain ⟨r, hr, hri⟩ := hs.one k
    exact ⟨r, hr, decide_eq_true (mk_ne_iff.2 ⟨k, rfl, hri⟩)⟩
  | part c σ =>
    obtain ⟨⟨r, hr, h⟩, -⟩ := mem_rowsOf.1 hv.2
    exact ⟨r, hr, decide_eq_true h⟩
  | leaf ρ => exact ⟨ρ, hv, decide_eq_true rfl⟩

/-- A component with conflicts has two sequences off the ancestral one. -/
theorem Std.two_parts (hs : Std S M f) {c : Fin m} (hc : isNT f c = true) : ∃ r ∈ M, ∃ r' ∈ M, mkRow S f c r ≠ S ∧ mkRow S f c r' ≠ S ∧ mkRow S f c r ≠ mkRow S f c r' := by
  have hlen : 1 < (sitesOf f c).length := by simpa [isNT] using hc
  have hnd : (sitesOf f c).Nodup := (List.nodup_finRange m).filter _
  rw [← List.toFinset_card_of_nodup hnd, Finset.one_lt_card_iff] at hlen
  obtain ⟨a, b, ha, hb, hab⟩ := hlen
  have hfa : f a = c := by simpa [sitesOf] using ha
  have hfb : f b = c := by simpa [sitesOf] using hb
  obtain ⟨k, hk⟩ := SimpleGraph.Reachable.exists_adj_of_ne ((hs.lab a b).1 (hfa.trans hfb.symm)) hab
  have hkc : f k = c := ((hs.lab a k).2 (SimpleGraph.Adj.reachable hk)).symm.trans hfa
  have hne : (!S a) ≠ S a := by cases S a <;> simp
  have hrow : ∀ b' : Bool, ∃ r ∈ M, r a = !S a ∧ r k = b' := by
    intro b'
    obtain ⟨r, hr, h₁, h₂⟩ := hk (!S a) b'
    rcases mem_addRow.1 hr with rfl | hr'
    · exact absurd h₁.symm hne
    · exact ⟨r, List.mem_toFinset.1 hr', h₁, h₂⟩
  obtain ⟨r, hr, h₁, h₂⟩ := hrow true
  obtain ⟨r', hr', h₁', h₂'⟩ := hrow false
  refine ⟨r, hr, r', hr', mk_ne_iff.2 ⟨a, hfa, by rw [h₁]; exact hne⟩, mk_ne_iff.2 ⟨a, hfa, by rw [h₁']; exact hne⟩, fun h => ?_⟩
  have := congrFun h k
  simp [mkRow, hkc, h₂, h₂'] at this

theorem cl_top {c : Fin m} {r : Row m} : (GNode.top c).cl S f r = true ↔ mkRow S f c r ≠ S := by simp [GNode.cl]

theorem cl_part {c : Fin m} {σ r : Row m} : (GNode.part c σ).cl S f r = true ↔ mkRow S f c r = σ := by simp [GNode.cl]

theorem cl_leaf {ρ r : Row m} : (GNode.leaf ρ).cl S f r = true ↔ r = ρ := by simp [GNode.cl]

theorem exists_of_isNT {c : Fin m} (hc : isNT f c = true) : ∃ k, f k = c := by
  have hlen : 1 < (sitesOf f c).length := by simpa [isNT] using hc
  have hne : sitesOf f c ≠ [] := fun h => by
    rw [h] at hlen
    simp at hlen
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨a, by simpa [sitesOf] using ha⟩

theorem Tie.total {u v : GNode m} (hu : Valid S M f u) (hv : Valid S M f v) (hne : u ≠ v) (hr : ∃ r, u.cl S f r = true ∧ v.cl S f r = true) : Tie f u v ∨ Tie f v u := by
  have hval : ∀ {x y : ℕ}, x ≠ y → x < y ∨ y < x := fun h => Nat.lt_or_gt_of_ne h
  obtain ⟨r, h₁, h₂⟩ := hr
  have hsame : u.rank f = v.rank f → u.idx ≠ v.idx := by
    intro hrk hidx
    apply hne
    cases u <;> cases v <;> simp only [GNode.rank, GNode.idx] at hrk hidx
    · rfl
    · split_ifs at hrk
    · simp at hrk
    · simp at hrk
    · split_ifs at hrk
    · rw [Fin.ext hidx]
    · split_ifs at hrk <;> omega
    · split_ifs at hrk <;> omega
    · simp at hrk
    · split_ifs at hrk <;> omega
    · have hcc := Fin.ext hidx
      subst hcc
      rw [(cl_part.1 h₁).symm.trans (cl_part.1 h₂)]
    · simp at hrk
    · simp at hrk
    · split_ifs at hrk <;> omega
    · simp at hrk
    · rw [(cl_leaf.1 h₁).symm.trans (cl_leaf.1 h₂)]
  by_cases hrk : u.rank f = v.rank f
  · rcases hval (hsame hrk) with h | h
    · exact Or.inl (Or.inr ⟨hrk, h⟩)
    · exact Or.inr (Or.inr ⟨hrk.symm, h⟩)
  · rcases hval hrk with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)

/-- A leaf is above nothing. -/
theorem Std.not_up_leaf (hs : Std S M f) (hv : Valid S M f v) {ρ : Row m} : Up S M f (.leaf ρ) v = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  obtain ⟨hne, h₁, h₂⟩ := up_iff.1 h
  obtain ⟨r, hr, hrv⟩ := hs.nonempty_cl hv
  have hrρ : r = ρ := cl_leaf.1 (h₁ r hr hrv)
  subst hrρ
  have h₃ : SubCl S M f (.leaf r) v := fun r' _ h' => by
    rw [cl_leaf.1 h']
    exact hrv
  have hrk : ∀ w : GNode m, w.rank f ≤ 4 := by
    intro w
    cases w <;> simp only [GNode.rank]
    · omega
    · split_ifs <;> omega
    · omega
    · omega
  have h₄ := h₂ h₃
  have := hrk v
  have hidx0 : v.rank f = 4 → v.idx = 0 := by
    intro h₅
    cases v with
    | root => rfl
    | leaf _ => rfl
    | part _ _ => simp [GNode.rank] at h₅
    | top c =>
      simp only [GNode.rank] at h₅
      split_ifs at h₅ <;> omega
  have hL : (GNode.leaf r : GNode m).rank f = 4 := rfl
  have hLi : (GNode.leaf r : GNode m).idx = 0 := rfl
  unfold Tie at h₄
  rw [hL, hLi] at h₄
  rcases h₄ with h₅ | ⟨h₅, h₆⟩
  · omega
  · have := hidx0 h₅.symm
    omega

theorem rank_le (w : GNode m) : w.rank f ≤ 4 := by
  cases w <;> simp only [GNode.rank]
  · omega
  · split_ifs <;> omega
  · omega
  · omega

theorem idx_le (w : GNode m) : w.idx ≤ m := by
  cases w <;> simp only [GNode.idx]
  · omega
  · exact Nat.le_of_lt (Fin.is_lt _)
  · exact Nat.le_of_lt (Fin.is_lt _)
  · omega

/-- The key goes up along `Up`. -/
theorem key_lt {u v : GNode m} (h : Up S M f u v = true) : key S M f u < key S M f v := by
  obtain ⟨-, h₁, h₂⟩ := up_iff.1 h
  have hu := idx_le u
  have hv := idx_le v
  have hru := rank_le (f := f) u
  have hrv := rank_le (f := f) v
  have hbound : u.rank f * (m + 1) + u.idx ≤ 4 * (m + 1) + m := by nlinarith
  have hle : (M.filter (v.cl S f)).length ≤ (M.filter (u.cl S f)).length := List.length_filter_le_length_filter fun x hx => h₁ x hx
  have hleM : (M.filter (u.cl S f)).length ≤ M.length := List.length_filter_le _ _
  unfold key
  by_cases hsub : SubCl S M f u v
  · have heq : (M.filter (u.cl S f)).length = (M.filter (v.cl S f)).length := le_antisymm (List.length_filter_le_length_filter fun x hx => hsub x hx) hle
    rw [heq]
    rcases h₂ hsub with ht | ⟨ht, hi⟩
    · have : (u.rank f + 1) * (m + 1) ≤ v.rank f * (m + 1) := Nat.mul_le_mul_right _ ht
      nlinarith
    · rw [ht]
      omega
  · unfold SubCl at hsub
    push Not at hsub
    obtain ⟨r, hr, h₃, h₄⟩ := hsub
    have hlt : (M.filter (v.cl S f)).length < (M.filter (u.cl S f)).length := List.length_filter_lt_length_filter (fun x hx => h₁ x hx) ⟨r, hr, h₃, by simpa using h₄⟩
    obtain ⟨d, hd⟩ : ∃ d, M.length - (M.filter (v.cl S f)).length = M.length - (M.filter (u.cl S f)).length + 1 + d := ⟨M.length - (M.filter (v.cl S f)).length - (M.length - (M.filter (u.cl S f)).length) - 1, by omega⟩
    rw [hd]
    nlinarith [Nat.zero_le (d * (6 * (m + 1))), Nat.zero_le (v.rank f * (m + 1))]

theorem mem_reps {c : Fin m} : c ∈ reps f ↔ ∃ k, f k = c := by
  simp [reps]

theorem valid_of_mem_cands {u : GNode m} (h : u ∈ cands S M f) : Valid S M f u := by
  rcases List.mem_cons.1 h with rfl | h
  · trivial
  rcases List.mem_append.1 h with h | h
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
    exact mem_reps.1 hc
  · obtain ⟨c, hc, h'⟩ := List.mem_flatMap.1 h
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 h'
    exact ⟨(List.mem_filter.1 hc).2, hσ⟩

theorem mem_cands_of_valid {u : GNode m} (h : Valid S M f u) (hl : ∀ ρ, u ≠ .leaf ρ) : u ∈ cands S M f := by
  cases u with
  | root => exact List.mem_cons_self
  | top c => exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.2 ⟨c, mem_reps.2 h, rfl⟩))
  | part c σ => exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨c, List.mem_filter.2 ⟨mem_reps.2 (exists_of_isNT h.1), h.1⟩, List.mem_map.2 ⟨σ, h.2, rfl⟩⟩))
  | leaf ρ => exact absurd rfl (hl ρ)

/-- The root is above all the other nodes. -/
theorem up_root {v : GNode m} (hne : v ≠ .root) : Up S M f .root v = true := by
  refine up_iff.2 ⟨hne.symm, fun _ _ _ => rfl, fun _ => Or.inl ?_⟩
  cases v with
  | root => exact absurd rfl hne
  | top c =>
    simp only [GNode.rank]
    split_ifs <;> omega
  | part _ _ => simp [GNode.rank]
  | leaf _ => simp [GNode.rank]

theorem Std.top_up_part (hs : Std S M f) {c : Fin m} {σ : Row m} (hc : isNT f c = true) (hσ : σ ∈ rowsOf S M f c) : Up S M f (.top c) (.part c σ) = true := by
  refine up_iff.2 ⟨by simp, fun r _ h => cl_top.2 ?_, fun h => ?_⟩
  · rw [cl_part.1 h]
    exact (mem_rowsOf.1 hσ).2
  · exfalso
    obtain ⟨r, hr, r', hr', h₁, h₂, h₃⟩ := hs.two_parts hc
    exact h₃ ((cl_part.1 (h r hr (cl_top.2 h₁))).trans (cl_part.1 (h r' hr' (cl_top.2 h₂))).symm)

theorem not_up_part_part {c : Fin m} {σ τ : Row m} (hσ : σ ∈ rowsOf S M f c) : Up S M f (.part c τ) (.part c σ) = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  obtain ⟨h₁, h₂, -⟩ := up_iff.1 h
  obtain ⟨⟨r, hr, hrσ⟩, -⟩ := mem_rowsOf.1 hσ
  have := cl_part.1 (h₂ r hr (cl_part.2 hrσ))
  apply h₁
  rw [← this, hrσ]

theorem Std.not_up_part_top (hs : Std S M f) {c : Fin m} {τ : Row m} (hc : isNT f c = true) : Up S M f (.part c τ) (.top c) = false := by
  refine Bool.eq_false_iff.2 fun h => ?_
  obtain ⟨-, h₂, -⟩ := up_iff.1 h
  obtain ⟨r, hr, r', hr', h₃, h₄, h₅⟩ := hs.two_parts hc
  exact h₅ ((cl_part.1 (h₂ r hr (cl_top.2 h₃))).trans (cl_part.1 (h₂ r' hr' (cl_top.2 h₄))).symm)

theorem rank_top_ge {c : Fin m} : 2 ≤ (GNode.top c : GNode m).rank f := by
  simp only [GNode.rank]
  split_ifs <;> omega

theorem not_tie_top {c : Fin m} {v : GNode m} (hv : v.rank f < 2) : ¬ Tie f (.top c) v := by
  have := rank_top_ge (f := f) (c := c)
  unfold Tie
  omega

/-- The `1`s of `x` are `1`s of `y`. -/
def Sub1 (S x y : Row m) : Prop := ∀ i, x i ≠ S i → y i ≠ S i

theorem Sub1.refl' (x : Row m) : Sub1 S x x := fun _ h => h

theorem Sub1.trans' {x y z : Row m} (h₁ : Sub1 S x y) (h₂ : Sub1 S y z) : Sub1 S x z := fun i hi => h₂ i (h₁ i hi)

theorem card1_le {x y : Row m} (h : Sub1 S x y) : card1 S x ≤ card1 S y :=
  List.length_filter_le_length_filter fun i _ hi => by simpa using h i (by simpa using hi)

theorem eq_of_sub1 {x y : Row m} (h : Sub1 S x y) (h' : Sub1 S y x) : x = y := by
  funext i
  have h₁ := h i
  have h₂ := h' i
  revert h₁ h₂
  cases x i <;> cases y i <;> cases S i <;> simp

theorem card1_lt {x y : Row m} (h : Sub1 S x y) (hne : x ≠ y) : card1 S x < card1 S y := by
  have hi : ∃ i, y i ≠ S i ∧ x i = S i := by
    by_contra hno
    push Not at hno
    exact hne (eq_of_sub1 h fun i hi => hno i hi)
  obtain ⟨i, h₁, h₂⟩ := hi
  exact List.length_filter_lt_length_filter (fun j _ hj => by simpa using h j (by simpa using hj)) ⟨i, List.mem_finRange i, by simpa using h₁, by simpa using h₂⟩

/-- A chain of rows. -/
def Ch (S : Row m) (X : List (Row m)) : Prop := ∀ x ∈ X, ∀ y ∈ X, Sub1 S x y ∨ Sub1 S y x

theorem Ch.sub_of_le {X : List (Row m)} (h : Ch S X) {x y : Row m} (hx : x ∈ X) (hy : y ∈ X) (hle : card1 S x ≤ card1 S y) : Sub1 S x y := by
  rcases h x hx y hy with h' | h'
  · exact h'
  · by_cases hne : y = x
    · rw [hne]
      exact Sub1.refl' x
    · have := card1_lt h' hne
      omega

theorem Ch.filter {X : List (Row m)} (h : Ch S X) (p : Row m → Bool) : Ch S (X.filter p) := fun x hx y hy =>
  h x (List.mem_filter.1 hx).1 y (List.mem_filter.1 hy).1

/-- The end of a chain. -/
theorem endNode_spec {X : List (Row m)} (hX : Ch S X) (c : Fin m) : (X = [] ∧ endNode S c X = .top c) ∨ ∃ y ∈ X, endNode S c X = .part c y ∧ ∀ a ∈ X, Sub1 S a y := by
  cases hm : X.argmax (card1 S) with
  | none =>
    refine Or.inl ⟨List.argmax_eq_none.1 hm, ?_⟩
    simp [endNode, hm]
  | some y =>
    have hy := List.argmax_mem hm
    refine Or.inr ⟨y, hy, by simp [endNode, hm], fun a ha => hX.sub_of_le ha hy (List.le_of_mem_argmax ha hm)⟩

theorem topAt_eq_of_max {X : List (Row m)} {y : Row m} (hy : y ∈ X) (hmax : ∀ a ∈ X, Sub1 S a y) (i : Fin m) : topAt S X i = y i := by
  have hb : ∀ {a b c : Bool}, (a ≠ c ↔ b ≠ c) → a = b := by decide
  refine hb (c := S i) (topAt_ne_iff.trans ⟨?_, fun h => ⟨y, hy, h⟩⟩)
  rintro ⟨r, hr, hri⟩
  exact hmax r hr i hri

theorem topAt_nil (i : Fin m) : topAt S [] i = S i := by simp [topAt]

/-- The node before a row of a chain. -/
theorem predNode_spec {X : List (Row m)} (hX : Ch S X) (c : Fin m) {σ : Row m} (hσ : σ ∈ X) :
    (predNode S c X σ = .top c ∧ ∀ a ∈ X, Sub1 S a σ → a = σ) ∨ ∃ y ∈ X, predNode S c X σ = .part c y ∧ Sub1 S y σ ∧ y ≠ σ ∧ card1 S y < card1 S σ ∧ ∀ a ∈ X, Sub1 S a σ → a ≠ σ → Sub1 S a y := by
  rcases endNode_spec (hX.filter fun y => decide (card1 S y < card1 S σ)) c with ⟨h₁, h₂⟩ | ⟨y, hy, h₂, h₃⟩
  · refine Or.inl ⟨h₂, fun a ha hsub => ?_⟩
    by_contra hne
    have : a ∈ X.filter fun y => decide (card1 S y < card1 S σ) := List.mem_filter.2 ⟨ha, by simpa using card1_lt hsub hne⟩
    rw [h₁] at this
    simp at this
  · obtain ⟨hyX, hyl⟩ := List.mem_filter.1 hy
    have hlt : card1 S y < card1 S σ := by simpa using hyl
    refine Or.inr ⟨y, hyX, h₂, hX.sub_of_le hyX hσ hlt.le, ?_, hlt, fun a ha hsub hne => h₃ a (List.mem_filter.2 ⟨ha, by simpa using card1_lt hsub hne⟩)⟩
    rintro rfl
    omega

/-- What the arrangement of a component gives. -/
structure ArrOK (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (c : Fin m) (a : Arr m) : Prop where
  s_mem : a.1 ∈ rowsOf S M f c
  X_mem : ∀ y ∈ a.2.1, y ∈ rowsOf S M f c ∧ y ≠ a.1
  Y_mem : ∀ y ∈ a.2.2, y ∈ rowsOf S M f c ∧ y ≠ a.1
  all : ∀ σ ∈ rowsOf S M f c, σ = a.1 ∨ σ ∈ a.2.1 ∨ σ ∈ a.2.2
  chX : Ch S a.2.1
  chY : Ch S a.2.2
  disj : ∀ x ∈ a.2.1, ∀ y ∈ a.2.2, ∀ i, x i ≠ S i → y i = S i
  cover : ∀ i, f i = c → (∃ y ∈ a.2.1, y i ≠ S i) ∨ ∃ y ∈ a.2.2, y i ≠ S i
  point : ∃ n, ∀ i, f i = c → a.1 i = if i.val < n then topAt S a.2.2 i else topAt S a.2.1 i

/-! ### The labels -/

section Labels

variable (hs : Std S M f)

include hs

theorem Std.part_unique {c : Fin m} {τ τ' : Row m} {v : GNode m} (hv : Valid S M f v) (h : Up S M f (.part c τ) v = true) (h' : Up S M f (.part c τ') v = true) : τ = τ' := by
  obtain ⟨r, hr, hrv⟩ := hs.nonempty_cl hv
  exact (cl_part.1 ((up_iff.1 h).2.1 r hr hrv)).symm.trans (cl_part.1 ((up_iff.1 h').2.1 r hr hrv))

omit hs in
theorem label_part_self {i : Fin m} (hc : isNT f (f i) = true) (σ : Row m) : label S M f (.part (f i) σ) i = σ i := by
  simp [label, hc]

/-- The label at a site of a component, from the gall node above. -/
theorem Std.label_of_up {i : Fin m} (hc : isNT f (f i) = true) {τ : Row m} (hτ : τ ∈ rowsOf S M f (f i)) {v : GNode m} (hv : Valid S M f v) (hvo : ∀ σ, v ≠ .part (f i) σ) (h : Up S M f (.part (f i) τ) v = true) : label S M f v i = τ i := by
  have hfind : (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) = some τ := by
    cases hf : (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) with
    | none =>
      have := List.find?_eq_none.1 hf τ hτ
      rw [h] at this
      exact absurd this (by simp)
    | some τ' =>
      have h' := List.find?_some hf
      rw [hs.part_unique hv h' h]
  cases v with
  | part c' σ =>
    have hne : c' ≠ f i := by
      rintro rfl
      exact hvo σ rfl
    simp [label, hc, hne, hfind]
  | root => simp [label, hc, hfind]
  | top c' => simp [label, hc, hfind]
  | leaf ρ => simp [label, hc, hfind]

omit hs in
/-- The label at a site of a component, with no gall node above. -/
theorem label_of_not {i : Fin m} (hc : isNT f (f i) = true) {v : GNode m} (hvo : ∀ σ, v ≠ .part (f i) σ) (h : ∀ τ ∈ rowsOf S M f (f i), Up S M f (.part (f i) τ) v = false) : label S M f v i = S i := by
  have hfind : (rowsOf S M f (f i)).find? (fun τ => Up S M f (.part (f i) τ) v) = none := List.find?_eq_none.2 fun τ hτ => by simp [h τ hτ]
  cases v with
  | part c' σ =>
    have hne : c' ≠ f i := by
      rintro rfl
      exact hvo σ rfl
    simp [label, hc, hne, hfind]
  | root => simp [label, hc, hfind]
  | top c' => simp [label, hc, hfind]
  | leaf ρ => simp [label, hc, hfind]

omit hs in
/-- The label at a site alone in its component. -/
theorem label_trivial {i : Fin m} (hc : ¬ isNT f (f i) = true) (v : GNode m) : label S M f v i = if v = .top (f i) ∨ Up S M f (.top (f i)) v = true then !S i else S i := by
  simp [label, hc]

/-- The label of the coalescent node on its own component is the ancestral sequence. -/
theorem Std.label_top_self {i : Fin m} (hc : isNT f (f i) = true) : label S M f (.top (f i)) i = S i :=
  label_of_not hc (by simp) fun _ _ => hs.not_up_part_top hc

/-- **Along a tree arc**, the label changes at the sites of the arc. -/
theorem Std.label_tree_arc {v u : GNode m} (hv : Valid S M f v) (hu : Valid S M f u) (hnp : ∀ c σ, v ≠ .part c σ) (hup : Up S M f u v = true)
    (hlow : ∀ u', Valid S M f u' → Up S M f u' v = true → u' = u ∨ Up S M f u' u = true) (i : Fin m) (ar : Fin m → Arr m) (hsite : isNT f (f i) = true → siteNode S f ar i ≠ v) :
    label S M f v i = if siteNode S f ar i = v then !label S M f u i else label S M f u i := by
  by_cases hc : isNT f (f i) = true
  · rw [ite_eq_right (hsite hc)]
    by_cases hex : ∃ τ ∈ rowsOf S M f (f i), Up S M f (.part (f i) τ) v = true
    · obtain ⟨τ, hτ, hτv⟩ := hex
      rw [hs.label_of_up hc hτ hv (fun σ => hnp _ σ) hτv]
      rcases hlow _ (show Valid S M f (.part (f i) τ) from ⟨hc, hτ⟩) hτv with rfl | h
      · exact (label_part_self hc τ).symm
      · by_cases hown : ∃ σ, u = .part (f i) σ
        · obtain ⟨σ, rfl⟩ := hown
          have hσ : σ ∈ rowsOf S M f (f i) := hu.2
          rw [not_up_part_part hσ] at h
          exact absurd h (by simp)
        · push Not at hown
          exact (hs.label_of_up hc hτ hu hown h).symm
    · push Not at hex
      rw [label_of_not hc (fun σ => hnp _ σ) fun τ hτ => by simpa using hex τ hτ]
      by_cases hown : ∃ σ, u = .part (f i) σ
      · obtain ⟨σ, rfl⟩ := hown
        exact absurd hup (hex σ hu.2)
      · push Not at hown
        exact (label_of_not hc hown fun τ hτ => Bool.eq_false_iff.2 fun h => hex τ hτ (up_trans h hup)).symm
  · rw [label_trivial hc, label_trivial hc]
    have hs₁ : siteNode S f ar i = .top (f i) := by simp [siteNode, hc]
    rw [hs₁]
    by_cases hvt : v = .top (f i)
    · have hun : ¬ (u = .top (f i) ∨ Up S M f (.top (f i)) u = true) := by
        rintro (rfl | h)
        · rw [hvt, up_irrefl] at hup
          exact absurd hup (by simp)
        · rw [hvt] at hup
          have h' := up_trans h hup
          rw [up_irrefl] at h'
          exact absurd h' (by simp)
      simp [hvt, hun]
    · have hiff : (v = .top (f i) ∨ Up S M f (.top (f i)) v = true) ↔ (u = .top (f i) ∨ Up S M f (.top (f i)) u = true) := by
        constructor
        · rintro (h | h)
          · exact absurd h hvt
          · rcases hlow _ (show Valid S M f (.top (f i)) from ⟨i, rfl⟩) h with h' | h'
            · exact Or.inl h'.symm
            · exact Or.inr h'
        · rintro (rfl | h)
          · exact Or.inr hup
          · exact Or.inr (up_trans h hup)
      have hne : (GNode.top (f i) : GNode m) ≠ v := fun h => hvt h.symm
      simp only [hne, ite_false]
      by_cases h' : u = .top (f i) ∨ Up S M f (.top (f i)) u = true
      · rw [ite_eq_left (hiff.2 h'), ite_eq_left h']
      · rw [ite_eq_right (fun h'' => h' (hiff.1 h'')), ite_eq_right h']

end Labels

/-! ### The network -/

section Net

variable {ar : Fin m → Arr m} (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c))

include hs har

omit hs in
/-- The first row of the chain with a site is below the arc of the site. -/
theorem siteNode_spec {i : Fin m} (hc : isNT f (f i) = true) :
    ∃ z, siteNode S f ar i = .part (f i) z ∧ z i ≠ S i ∧ ((z ∈ (ar (f i)).2.1 ∧ ∀ a ∈ (ar (f i)).2.1, a i ≠ S i → Sub1 S z a) ∨ (z ∈ (ar (f i)).2.2 ∧ ∀ a ∈ (ar (f i)).2.2, a i ≠ S i → Sub1 S z a)) := by
  have hA := har _ hc
  obtain ⟨y₀, hy₀, hy₀i⟩ : ∃ y ∈ (ar (f i)).2.1 ++ (ar (f i)).2.2, y i ≠ S i := by
    rcases hA.cover i rfl with ⟨y, hy, h⟩ | ⟨y, hy, h⟩
    · exact ⟨y, List.mem_append_left _ hy, h⟩
    · exact ⟨y, List.mem_append_right _ hy, h⟩
  have hmem : y₀ ∈ ((ar (f i)).2.1 ++ (ar (f i)).2.2).filter fun y => y i != S i := List.mem_filter.2 ⟨hy₀, by simpa using hy₀i⟩
  have hnone : (((ar (f i)).2.1 ++ (ar (f i)).2.2).filter fun y => y i != S i).argmin (card1 S) ≠ none := by
    rw [Ne, List.argmin_eq_none]
    intro h
    rw [h] at hmem
    simp at hmem
  obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.1 hnone
  obtain ⟨hzm, hzi⟩ := List.mem_filter.1 (List.argmin_mem hz)
  have hzi' : z i ≠ S i := by simpa using hzi
  have hle : ∀ a ∈ (ar (f i)).2.1 ++ (ar (f i)).2.2, a i ≠ S i → card1 S z ≤ card1 S a := fun a ha hai =>
    List.le_of_mem_argmin (List.mem_filter.2 ⟨ha, by simpa using hai⟩) hz
  have hsn : siteNode S f ar i = .part (f i) z := by
    unfold siteNode
    rw [ite_eq_left hc, hz]
  refine ⟨z, hsn, hzi', ?_⟩
  rcases List.mem_append.1 hzm with h | h
  · exact Or.inl ⟨h, fun a ha hai => hA.chX.sub_of_le h ha (hle a (List.mem_append_left _ ha) hai)⟩
  · exact Or.inr ⟨h, fun a ha hai => hA.chY.sub_of_le h ha (hle a (List.mem_append_right _ ha) hai)⟩

omit hs har in
theorem endNode_valid {c : Fin m} (hc : isNT f c = true) {X : List (Row m)} (hX : Ch S X) (hrows : ∀ y ∈ X, y ∈ rowsOf S M f c) : Valid S M f (endNode S c X) := by
  rcases endNode_spec hX c with ⟨-, h⟩ | ⟨y, hy, h, -⟩
  · rw [h]
    exact exists_of_isNT hc
  · rw [h]
    exact ⟨hc, hrows y hy⟩

omit hs in
theorem par₂_valid {v u : GNode m} (hv : Valid S M f v) (h : par₂ S ar v = some u) : Valid S M f u := by
  cases v with
  | part c σ =>
    have hA := har c hv.1
    simp only [par₂] at h
    split_ifs at h
    rw [← Option.some.inj h]
    exact endNode_valid hv.1 hA.chY fun y hy => (hA.Y_mem y hy).1
  | root => simp [par₂] at h
  | top c => simp [par₂] at h
  | leaf ρ => simp [par₂] at h

omit hs in
theorem site_valid (i : Fin m) : Valid S M f (siteNode S f ar i) := by
  by_cases hc : isNT f (f i) = true
  · obtain ⟨z, h, -, hz⟩ := siteNode_spec (ar := ar) har hc
    rw [h]
    refine ⟨hc, ?_⟩
    rcases hz with ⟨hz, -⟩ | ⟨hz, -⟩
    · exact ((har _ hc).X_mem z hz).1
    · exact ((har _ hc).Y_mem z hz).1
  · have : siteNode S f ar i = .top (f i) := by simp [siteNode, hc]
    rw [this]
    exact ⟨i, rfl⟩

/-- The number of nodes above a node. -/
def numAbove (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (v : GNode m) : ℕ := ((cands S M f).filter fun u => Up S M f u v).length

/-- The place of a node on its gall. -/
def galPos (S : Row m) (ar : Fin m → Arr m) (m' : ℕ) : GNode m → ℕ
  | .part c σ => if σ = (ar c).1 then m' + 1 else card1 S σ
  | _ => 0

omit hs har in
theorem numAbove_lt {u v : GNode m} (hu : Valid S M f u) (hul : ∀ ρ, u ≠ .leaf ρ) (h : Up S M f u v = true) : numAbove S M f u < numAbove S M f v :=
  List.length_filter_lt_length_filter (fun _ _ hk => up_trans hk h) ⟨u, mem_cands_of_valid hu hul, h, up_irrefl⟩

omit hs in
/-- The two ends of the chains of a gall are different nodes. -/
theorem endNode_ne {c : Fin m} (hc : isNT f c = true) : endNode S c (ar c).2.1 ≠ endNode S c (ar c).2.2 := by
  have hA := har c hc
  obtain ⟨k, hk⟩ := exists_of_isNT (f := f) hc
  rcases endNode_spec (S := S) hA.chX c with ⟨h₁, h₂⟩ | ⟨y, hy, h₂, -⟩ <;> rcases endNode_spec (S := S) hA.chY c with ⟨h₃, h₄⟩ | ⟨z, hz, h₄, -⟩
  · exfalso
    rcases hA.cover k hk with ⟨y, hy, -⟩ | ⟨y, hy, -⟩
    · rw [h₁] at hy
      simp at hy
    · rw [h₃] at hy
      simp at hy
  · rw [h₂, h₄]
    simp
  · rw [h₂, h₄]
    simp
  · rw [h₂, h₄]
    intro h
    obtain rfl : y = z := (GNode.part.inj h).2
    have hyS := (mem_rowsOf.1 (hA.X_mem y hy).1).2
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ S i := by
      by_contra hno
      push Not at hno
      exact hyS (funext hno)
    exact hi (hA.disj y hy y hz i hi)

omit har in
/-- The label of a leaf is its row. -/
theorem label_leaf {r : Row m} (hr : r ∈ M) (i : Fin m) : label S M f (.leaf r) i = r i := by
  have hv : Valid S M f (.leaf r) := hr
  have hmk : mkRow S f (f i) r i = r i := by simp [mkRow]
  by_cases hc : isNT f (f i) = true
  · by_cases hne : mkRow S f (f i) r = S
    · rw [label_of_not hc (by simp) fun τ hτ => Bool.eq_false_iff.2 fun h => ?_]
      · rw [← hmk, hne]
      · have := cl_part.1 ((up_iff.1 h).2.1 r hr (cl_leaf.2 rfl))
        exact (mem_rowsOf.1 hτ).2 (this.symm.trans hne)
    · have hτ : mkRow S f (f i) r ∈ rowsOf S M f (f i) := mem_rowsOf.2 ⟨⟨r, hr, rfl⟩, hne⟩
      rw [hs.label_of_up hc hτ hv (by simp) (up_iff.2 ⟨by simp, fun r' _ h' => ?_, fun _ => Or.inl (by simp [GNode.rank])⟩), hmk]
      rw [cl_leaf.1 h']
      exact cl_part.2 rfl
  · rw [label_trivial hc]
    have hsingle : ∀ j, f j = f i → j = i := by
      intro j hj
      have hlen : ¬ 1 < (sitesOf f (f i)).length := by simpa [isNT] using hc
      have hnd : (sitesOf f (f i)).Nodup := (List.nodup_finRange m).filter _
      rw [← List.toFinset_card_of_nodup hnd, Finset.one_lt_card_iff] at hlen
      push Not at hlen
      exact hlen j i (by simp [sitesOf, hj]) (by simp [sitesOf])
    have hup : Up S M f (.top (f i)) (.leaf r) = true ↔ r i ≠ S i := by
      constructor
      · intro h
        obtain ⟨j, hj, hrj⟩ := mk_ne_iff.1 (cl_top.1 ((up_iff.1 h).2.1 r hr (cl_leaf.2 rfl)))
        rwa [hsingle j hj] at hrj
      · intro h
        refine up_iff.2 ⟨by simp, fun r' _ h' => ?_, fun _ => Or.inl ?_⟩
        · rw [cl_leaf.1 h']
          exact cl_top.2 (mk_ne_iff.2 ⟨i, rfl, h⟩)
        · have h₁ : (GNode.top (f i) : GNode m).rank f ≤ 3 := by
            simp only [GNode.rank]
            split_ifs
            omega
          have h₂ : (GNode.leaf r : GNode m).rank f = 4 := rfl
          omega
    have hb : ∀ {u v : Bool}, u ≠ v → (!v) = u := by decide
    by_cases hri : r i ≠ S i
    · rw [ite_eq_left (Or.inr (hup.2 hri))]
      exact hb hri
    · push Not at hri
      rw [ite_eq_right, hri]
      rintro (h | h)
      · simp at h
      · exact absurd hri (hup.1 h)

omit hs har in
/-- The label of the root is the ancestral sequence. -/
theorem label_root (i : Fin m) : label S M f .root i = S i := by
  have hnot : ∀ {u : GNode m}, u.rank f ≠ 0 → Up S M f u .root = false := by
    intro u hu
    refine Bool.eq_false_iff.2 fun h => ?_
    obtain ⟨-, -, h₂⟩ := up_iff.1 h
    have ht := h₂ fun _ _ _ => rfl
    have hr : (GNode.root : GNode m).rank f = 0 := rfl
    unfold Tie at ht
    rw [hr] at ht
    omega
  by_cases hc : isNT f (f i) = true
  · exact label_of_not hc (by simp) fun τ _ => hnot (by simp [GNode.rank])
  · rw [label_trivial hc, ite_eq_right]
    rintro (h | h)
    · simp at h
    · rw [hnot (by have := rank_top_ge (f := f) (c := f i); omega)] at h
      exact absurd h (by simp)

end Net

/-! ### The network as a `PreNet` -/

section Assemble

open Gusfield2007.Network

variable {ar : Fin m → Arr m} (hs : Std S M f) (har : ∀ c, isNT f c = true → ArrOK S M f c (ar c))

/-- The nodes as a type. -/
abbrev VNode (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) : Type := {v : GNode m // Valid S M f v}

/-- An option of a node, on the nodes as a type. -/
def liftOpt {o : Option (GNode m)} (h : ∀ u, o = some u → Valid S M f u) : Option (VNode S M f) := o.pmap Subtype.mk h

theorem liftOpt_eq_some {o : Option (GNode m)} {h : ∀ u, o = some u → Valid S M f u} {q : VNode S M f} : liftOpt h = some q ↔ o = some q.1 := by
  cases o with
  | none => simp [liftOpt]
  | some a =>
    simp only [liftOpt, Option.pmap_some, Option.some.injEq]
    exact ⟨fun h' => by rw [← h'], fun h' => Subtype.ext h'⟩

theorem liftOpt_eq_none {o : Option (GNode m)} {h : ∀ u, o = some u → Valid S M f u} : liftOpt h = none ↔ o = none := by
  cases o <;> simp [liftOpt]

/-- The second parent is the end of the second chain, at the recombination node. -/
theorem par₂_some {v q : GNode m} (hv : Valid S M f v) (h : par₂ S ar v = some q) : ∃ c, isNT f c = true ∧ v = .part c (ar c).1 ∧ q = endNode S c (ar c).2.2 := by
  cases v with
  | part c σ =>
    simp only [par₂] at h
    split_ifs at h with h₁
    exact ⟨c, hv.1, by rw [h₁], (Option.some.inj h).symm⟩
  | root => simp [par₂] at h
  | top c => simp [par₂] at h
  | leaf ρ => simp [par₂] at h

theorem par_recomb {c : Fin m} : par S M f ar (.part c (ar c).1) = some (endNode S c (ar c).2.1) := by
  simp [par]

theorem par₂_recomb {c : Fin m} : par₂ S ar (.part c (ar c).1) = some (endNode S c (ar c).2.2) := by
  simp [par₂]

theorem endNode_cases (c : Fin m) (X : List (Row m)) : endNode S c X = .top c ∨ ∃ y, endNode S c X = .part c y := by
  unfold endNode
  split
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-- The nodes of the gall of a component. -/
def InGall (c : Fin m) (v : GNode m) : Prop := v = .top c ∨ ∃ σ, v = .part c σ

theorem inGall_endNode (c : Fin m) (X : List (Row m)) : InGall c (endNode S c X) := by
  rcases endNode_cases (S := S) c X with h | ⟨y, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨y, h⟩

theorem InGall.unique {c c' : Fin m} {v : GNode m} (h : InGall c v) (h' : InGall c' v) : c = c' := by
  rcases h with rfl | ⟨σ, rfl⟩ <;> rcases h' with h' | ⟨τ, h'⟩
  · exact GNode.top.inj h'
  · simp at h'
  · simp at h'
  · exact (GNode.part.inj h').1

/-- The measure that goes up along the arcs. -/
def rkN (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (ar : Fin m → Arr m) (v : GNode m) : ℕ := numAbove S M f v * (m + 2) + galPos S ar m v

theorem rk_top_lt {c : Fin m} {σ : Row m} (hc : isNT f c = true) (hs : Std S M f) (hσ : σ ∈ rowsOf S M f c) : rkN S M f ar (.top c) < rkN S M f ar (.part c σ) := by
  have h₁ := numAbove_lt (S := S) (M := M) (f := f) (u := .top c) (v := .part c σ) (exists_of_isNT hc) (by simp) (hs.top_up_part hc hσ)
  have h₂ : (numAbove S M f (.top c) + 1) * (m + 2) ≤ numAbove S M f (.part c σ) * (m + 2) := Nat.mul_le_mul_right _ h₁
  have h₃ : galPos S ar m (.top c) = 0 := rfl
  unfold rkN
  rw [h₃]
  nlinarith

include hs in
/-- A component with conflicts has an edge at each site. -/
theorem Std.exists_adj_of_isNT {c : Fin m} (hc : isNT f c = true) {i : Fin m} (hi : f i = c) : ∃ k, f k = c ∧ (incompatGraph (addRow M.toFinset S)).Adj i k := by
  have hlen : 1 < (sitesOf f c).length := by simpa [isNT] using hc
  have hnd : (sitesOf f c).Nodup := (List.nodup_finRange m).filter _
  rw [← List.toFinset_card_of_nodup hnd, Finset.one_lt_card_iff] at hlen
  obtain ⟨a, b, ha, hb, hab⟩ := hlen
  have hfa : f a = c := by simpa [sitesOf] using ha
  have hfb : f b = c := by simpa [sitesOf] using hb
  obtain ⟨j, hj, hji⟩ : ∃ j, f j = c ∧ j ≠ i := by
    by_cases h : a = i
    · exact ⟨b, hfb, fun h' => hab (h.trans h'.symm)⟩
    · exact ⟨a, hfa, h⟩
  obtain ⟨k, hk⟩ := SimpleGraph.Reachable.exists_adj_of_ne ((hs.lab i j).1 (hi.trans hj.symm)) (Ne.symm hji)
  exact ⟨k, ((hs.lab i k).2 (SimpleGraph.Adj.reachable hk)).symm.trans hi, hk⟩

end Assemble

/-! ### The arrangement from the test -/

theorem mem_sitesOf {c i : Fin m} : i ∈ sitesOf f c ↔ f i = c := by
  simp [sitesOf]

theorem off_rowsOf {c : Fin m} {σ : Row m} (hσ : σ ∈ rowsOf S M f c) {i : Fin m} (hi : f i ≠ c) : σ i = S i := by
  obtain ⟨⟨r, -, rfl⟩, -⟩ := mem_rowsOf.1 hσ
  simp [mkRow, hi]

theorem arrOf_ok {c : Fin m} (hex : ∃ s ∈ rowsOf S M f c, (candidate S (sitesOf f c) (rowsOf S M f c) s).1 = true) : ArrOK S M f c (arrOf S M f c) := by
  obtain ⟨s₀, hs₀, hs₀c⟩ := hex
  have hnone : (rowsOf S M f c).find? (fun s => (candidate S (sitesOf f c) (rowsOf S M f c) s).1) ≠ none := by
    intro h
    have := List.find?_eq_none.1 h s₀ hs₀
    rw [hs₀c] at this
    exact absurd this (by simp)
  obtain ⟨s, hfind⟩ := Option.ne_none_iff_exists'.1 hnone
  have hsc' := List.find?_some hfind
  have hsc : (candidate S (sitesOf f c) (rowsOf S M f c) s).1 = true := hsc'
  have hs : s ∈ rowsOf S M f c := List.mem_of_find?_eq_some hfind
  unfold arrOf
  rw [hfind]
  dsimp only
  have hcand := hsc
  unfold candidate at hcand
  dsimp only at hcand
  have heqOn : ∀ {a b : Row m}, a ∈ rowsOf S M f c → b ∈ rowsOf S M f c → (∀ i ∈ sitesOf f c, a i = b i) → a = b := by
    intro a b ha hb h
    funext i
    by_cases hi : f i = c
    · exact h i (mem_sitesOf.2 hi)
    · rw [off_rowsOf ha hi, off_rowsOf hb hi]
  have hrest : ∀ {r}, r ∈ (filterOps (rowsOf S M f c) fun r => (!(eqOn (sitesOf f c) r s).1, (eqOn (sitesOf f c) r s).2)).1 ↔ r ∈ rowsOf S M f c ∧ r ≠ s := by
    intro r
    constructor
    · intro hr
      obtain ⟨h₁, h₂⟩ := List.mem_filter.1 hr
      refine ⟨h₁, fun h₃ => ?_⟩
      have : (eqOn (sitesOf f c) r s).1 = true := eqOn_iff.2 fun i _ => by rw [h₃]
      simp [this] at h₂
    · rintro ⟨h₁, h₂⟩
      refine List.mem_filter.2 ⟨h₁, ?_⟩
      have : ¬ (eqOn (sitesOf f c) r s).1 = true := fun h' => h₂ (heqOn h₁ hs (eqOn_iff.1 h'))
      simpa using this
  split
  · rename_i hnil
    rw [hnil] at hcand
    simp at hcand
  · rename_i seed tl hRR
    rw [hRR] at hcand hrest
    have hrestM : ∀ {r}, r ∈ seed :: tl → r ∈ rowsOf S M f c ∧ r ≠ s := hrest.1
    dsimp only at hcand
    generalize hA : (filterOps (seed :: tl) (cmpOn S (sitesOf f c) seed)).1 = A at hcand ⊢
    generalize hB : (filterOps (seed :: tl) fun r => (!(cmpOn S (sitesOf f c) seed r).1, (cmpOn S (sitesOf f c) seed r).2)).1 = B at hcand ⊢
    have hAm : ∀ {y}, y ∈ A → y ∈ rowsOf S M f c ∧ y ≠ s := fun {y} hy => hrestM (by
      rw [← hA] at hy
      exact (List.mem_filter.1 hy).1)
    have hBm : ∀ {y}, y ∈ B → y ∈ rowsOf S M f c ∧ y ≠ s := fun {y} hy => hrestM (by
      rw [← hB] at hy
      exact (List.mem_filter.1 hy).1)
    have hsplit : ∀ {σ}, σ ∈ rowsOf S M f c → σ = s ∨ σ ∈ A ∨ σ ∈ B := by
      intro σ hσ
      by_cases hσs : σ = s
      · exact Or.inl hσs
      have hσr : σ ∈ seed :: tl := hrest.2 ⟨hσ, hσs⟩
      by_cases hcmp : (cmpOn S (sitesOf f c) seed σ).1 = true
      · exact Or.inr (Or.inl (by rw [← hA]; exact List.mem_filter.2 ⟨hσr, hcmp⟩))
      · exact Or.inr (Or.inr (by rw [← hB]; exact List.mem_filter.2 ⟨hσr, by simpa using hcmp⟩))
    have hsub : ∀ {a b : Row m}, a ∈ rowsOf S M f c → (∀ i ∈ sitesOf f c, a i ≠ S i → b i ≠ S i) → Sub1 S a b := by
      intro a b ha h i hi
      by_cases hic : f i = c
      · exact h i (mem_sitesOf.2 hic) hi
      · exact absurd (off_rowsOf ha hic) hi
    have hch : ∀ {X : List (Row m)}, (∀ {y}, y ∈ X → y ∈ rowsOf S M f c ∧ y ≠ s) → (∀ a ∈ X, ∀ b ∈ X, (cmpOn S (sitesOf f c) a b).1 = true) → Ch S X := by
      intro X hX h a ha b hb
      rcases cmpOn_iff.1 (h a ha b hb) with h' | h'
      · exact Or.inl (hsub (hX ha).1 h')
      · exact Or.inr (hsub (hX hb).1 h')
    simp only [Bool.and_eq_true, allOps, anyOps, List.all_eq_true, List.any_eq_true, Bool.or_eq_true] at hcand
    obtain ⟨⟨⟨⟨hchA, hchB⟩, hdj⟩, hcov⟩, n, hn, hrc⟩ := hcand
    have hdisj : ∀ x ∈ A, ∀ y ∈ B, ∀ i, x i ≠ S i → y i = S i := by
      intro x hx y hy i hi
      by_cases hic : f i = c
      · exact disjOn_iff.1 (hdj x hx y hy) i (mem_sitesOf.2 hic) hi
      · exact off_rowsOf (hBm hy).1 hic
    have hdisj' : ∀ x ∈ B, ∀ y ∈ A, ∀ i, x i ≠ S i → y i = S i := by
      intro x hx y hy i hi
      by_contra hne
      exact hi (hdisj y hy x hx i hne)
    have hcover : ∀ i, f i = c → (∃ y ∈ A, y i ≠ S i) ∨ ∃ y ∈ B, y i ≠ S i := by
      intro i hi
      rcases hcov i (mem_sitesOf.2 hi) with ⟨y, hy, hyi⟩ | ⟨y, hy, hyi⟩
      · exact Or.inl ⟨y, hy, by simpa [flipAt] using hyi⟩
      · exact Or.inr ⟨y, hy, by simpa [flipAt] using hyi⟩
    have hpt : ∀ {X Y : List (Row m)} {n' : ℕ}, (recombOk S (sitesOf f c) X Y s n').1 = true → ∃ n, ∀ i, f i = c → s i = if i.val < n then topAt S Y i else topAt S X i := by
      intro X Y n' h
      simp only [recombOk, allOps, List.all_eq_true, beq_iff_eq] at h
      exact ⟨n', fun i hi => h i (mem_sitesOf.2 hi)⟩
    split_ifs with hany
    · obtain ⟨n', -, hn'⟩ := List.any_eq_true.1 hany
      exact ⟨hs, fun y hy => hAm hy, fun y hy => hBm hy, fun σ hσ => hsplit hσ, hch hAm hchA, hch hBm hchB, hdisj, hcover, hpt hn'⟩
    · rcases hrc with h | h
      · exact absurd (List.any_eq_true.2 ⟨n, hn, h⟩) hany
      · exact ⟨hs, fun y hy => hBm hy, fun y hy => hAm hy, fun σ hσ => (hsplit hσ).imp_right Or.symm, hch hBm hchB, hch hAm hchA, hdisj', fun i hi => (hcover i hi).symm, hpt h⟩

end Laminar

/-! ### The function -/

/-- The table of the network: for each node, its parents and its label. -/
def gTable (S : Row m) (M : List (Row m)) (f : Fin m → Fin m) (ar : Fin m → Arr m) : List (GNode m × Option (GNode m) × Option (GNode m) × List Bool) :=
  (cands S M f ++ M.map GNode.leaf).map fun v => (v, par S M f ar v, par₂ S ar v, List.ofFn (label S M f v))

/-- What the algorithm returns: the table of the nodes, and the node below the arc of each site. -/
abbrev GalledOut (m : ℕ) := List (GNode m × Option (GNode m) × Option (GNode m) × List Bool) × List (GNode m)

/-- **The algorithm** (`ext:galled_build`), Sections 3 to 7 of the source: decide, and when there is a galled tree, return a reduced one as a table. -/
def galledBuild (S : Row m) (M : List (Row m)) : Option (GalledOut m) :=
  if (galledDecide S M).1 then
    let f := labOf (edgesOps S M).1
    let t := List.ofFn (arrOf S M f)
    let ar : Fin m → Arr m := fun c => t.getD c.val (S, [], [])
    some (gTable S M f ar, List.ofFn (siteNode S f ar))
  else none

section Correct

open scoped Classical

open Gusfield2007 Gusfield2007.Decomp

variable {S : Row m} {M : List (Row m)}

theorem mem_nodes {f : Fin m → Fin m} {v : GNode m} : v ∈ cands S M f ++ M.map GNode.leaf ↔ Valid S M f v := by
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact valid_of_mem_cands h
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 h
      exact hr
  · intro h
    by_cases hl : ∀ ρ, v ≠ .leaf ρ
    · exact List.mem_append_left _ (mem_cands_of_valid h hl)
    · push Not at hl
      obtain ⟨ρ, rfl⟩ := hl
      exact List.mem_append_right _ (List.mem_map.2 ⟨ρ, h, rfl⟩)

theorem std_of (hM : M ≠ []) (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) : Std S M (labOf (edgesOps S M).1) := ⟨lab_iff, hM, h1⟩

/-- A galled tree gives the arrangements (Theorem 3.2 of the source). -/
theorem arrOf_ok_of_galled (h1 : ∀ i, ∃ r ∈ M, r i ≠ S i) {V E : Type*} [Finite V] {N : Network (Fin m) V E} (hG : IsGalledTree N) (hc₁ : N.Obeys .single) (hD : N.Derives M.toFinset) (hS : N.ancestral = S) {c : Fin m}
    (hc : isNT (labOf (edgesOps S M).1) c = true) : ArrOK S M (labOf (edgesOps S M).1) c (arrOf S M (labOf (edgesOps S M).1) c) := by
  subst hS
  obtain ⟨k₀, rfl⟩ := exists_of_isNT hc
  refine arrOf_ok ?_
  have hnt := (one_lt_length_iff (S := N.ancestral) (M := M) k₀).1 (of_decide_eq_true hc)
  have hCl : ∀ i, i ∈ sitesOf (labOf (edgesOps N.ancestral M).1) (labOf (edgesOps N.ancestral M).1 k₀) ↔ i ∈ ((incompatGraph (addRow M.toFinset N.ancestral)).connectedComponentMk k₀).supp := mem_filter_lab k₀
  refine exists_candidate_of_gall hG hc₁ hD _ hnt hCl (fun r hr => ?_) (fun r hr h => ?_) (fun ρ hρ hne => ?_)
  · obtain ⟨⟨ρ, hρ, rfl⟩, -⟩ := mem_rowsOf.1 hr
    exact ⟨ρ, hρ, fun i hi => by simp [mkRow, mem_sitesOf.1 hi]⟩
  · obtain ⟨⟨ρ, hρ, rfl⟩, hne⟩ := mem_rowsOf.1 hr
    apply hne
    funext i
    by_cases hi : labOf (edgesOps N.ancestral M).1 i = labOf (edgesOps N.ancestral M).1 k₀
    · exact h i (mem_sitesOf.2 hi)
    · simp [mkRow, hi]
  · refine ⟨mkRow N.ancestral (labOf (edgesOps N.ancestral M).1) (labOf (edgesOps N.ancestral M).1 k₀) ρ, mem_rowsOf.2 ⟨⟨ρ, hρ, rfl⟩, fun h => hne fun i hi => ?_⟩, fun i hi => by simp [mkRow, mem_sitesOf.1 hi]⟩
    have := congrFun h i
    simpa [mkRow, mem_sitesOf.1 hi] using this

end Correct

end External.GusfieldEtAl2004.Algorithm
