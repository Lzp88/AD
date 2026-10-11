import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Tactic
import PaperVerifier.PrincipalMomentAudit.Basic

/-!
# Guarded pruning on actual finite simple graphs

The graph keeps the entire original vertex type; removed vertices become
isolated. This matches public arXiv:2607.21494v1 Section 3.2, rather than
assuming an abstract pruning geometry.
-/

namespace PrincipalMomentAudit.ForestPruning

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Mask edges to an active finite vertex set, keeping inactive vertices isolated. -/
def mask (G : SimpleGraph V) (S : Finset V) : SimpleGraph V where
  Adj u v := u ∈ S ∧ v ∈ S ∧ G.Adj u v
  symm := ⟨fun _ _ h => ⟨h.2.1, h.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.2.2⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    DecidableRel (mask G S).Adj := fun u v =>
  inferInstanceAs (Decidable (u ∈ S ∧ v ∈ S ∧ G.Adj u v))

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mask_adj (G : SimpleGraph V) (S : Finset V) (u v : V) :
    (mask G S).Adj u v ↔ u ∈ S ∧ v ∈ S ∧ G.Adj u v := Iff.rfl

omit [Fintype V] [DecidableEq V] in
theorem mask_le (G : SimpleGraph V) (S : Finset V) : mask G S ≤ G :=
  fun _ _ h => h.2.2

omit [Fintype V] [DecidableEq V] in
/-- Actual acyclicity is retained by every masking step. -/
theorem mask_isAcyclic (G : SimpleGraph V) (hG : G.IsAcyclic) (S : Finset V) :
    (mask G S).IsAcyclic := hG.anti (mask_le G S)

omit [Fintype V] in
theorem mask_mask (G : SimpleGraph V) (S T : Finset V) :
    mask (mask G S) T = mask G (S ∩ T) := by
  ext u v
  simp only [mask_adj, Finset.mem_inter]
  tauto

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem mask_compl_neighborFinset (W : Finset V) {v : V} (hv : v ∉ W) :
    (mask G Wᶜ).neighborFinset v = G.neighborFinset v \ W := by
  ext u
  simp [SimpleGraph.mem_neighborFinset, hv, and_comm]

theorem mask_degree_zero_of_not_mem (S : Finset V) {v : V} (hv : v ∉ S) :
    (mask G S).degree v = 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have h : (mask G S).neighborFinset v = ∅ := by
    ext u
    simp [SimpleGraph.mem_neighborFinset, hv]
  simp [h]

/-- The number of incident edges deleted at an unremoved vertex. -/
def removedNeighbors (W : Finset V) (v : V) : ℕ :=
  (G.neighborFinset v ∩ W).card

theorem removedNeighbors_eq_filter (W : Finset V) (v : V) :
    removedNeighbors G W v = (W.filter (G.Adj v)).card := by
  unfold removedNeighbors
  congr 1
  ext u
  simp [SimpleGraph.mem_neighborFinset, and_comm]

/-- Exact degree bookkeeping, before any forest assumption. -/
theorem mask_compl_degree_add (W : Finset V) {v : V} (hv : v ∉ W) :
    (mask G Wᶜ).degree v + removedNeighbors G W v = G.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, mask_compl_neighborFinset G W hv]
  exact Finset.card_sdiff_add_card_inter (G.neighborFinset v) W

theorem mask_compl_degree (W : Finset V) (v : V) :
    (mask G Wᶜ).degree v =
      if v ∈ W then 0 else G.degree v - removedNeighbors G W v := by
  split_ifs with hv
  · exact mask_degree_zero_of_not_mem G Wᶜ (by simpa)
  · exact Nat.eq_sub_of_add_eq (mask_compl_degree_add G W hv)

/-- Guarded leaf: degree one, with the sole neighbor outside the degree-one set.
Thus endpoints of an isolated K₂ are protected, as in the paper.
-/
def peelable : Finset V := by
  classical
  exact Finset.univ.filter (fun v => G.degree v = 1 ∧ ∃ u, G.Adj v u ∧ G.degree u ≠ 1)

omit [DecidableEq V] in
theorem mem_peelable (v : V) :
    v ∈ peelable G ↔ G.degree v = 1 ∧ ∃ u, G.Adj v u ∧ G.degree u ≠ 1 := by
  classical
  simp [peelable]

omit [DecidableEq V] in
theorem peelable_degree {v : V} (hv : v ∈ peelable G) : G.degree v = 1 :=
  ((mem_peelable G v).mp hv).1

omit [DecidableEq V] in
/-- No two guarded leaves are adjacent; the guard is proved to protect K₂ endpoints. -/
theorem peelable_neighbor_not_mem {v u : V} (hv : v ∈ peelable G) (hvu : G.Adj v u) :
    u ∉ peelable G := by
  obtain ⟨hvdeg, x, hvx, hxdeg⟩ := (mem_peelable G v).mp hv
  obtain ⟨a, ha, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hvdeg
  have hux : u = x := (huniq u hvu).trans (huniq x hvx).symm
  intro hu
  exact hxdeg (hux ▸ peelable_degree G hu)

theorem removedNeighbors_peelable_zero {v : V} (hv : v ∈ peelable G) :
    removedNeighbors G (peelable G) v = 0 := by
  rw [removedNeighbors_eq_filter]
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro u hu hAdj
  exact peelable_neighbor_not_mem G hv hAdj hu

/-- One guarded leaf deletion step on the original vertex type. -/
def step : SimpleGraph V := mask G (peelable G)ᶜ

instance : DecidableRel (step G).Adj :=
  inferInstanceAs (DecidableRel (mask G (peelable G)ᶜ).Adj)

theorem step_isAcyclic (hG : G.IsAcyclic) : (step G).IsAcyclic :=
  mask_isAcyclic G hG _

/-- The paper's scalar degree update, with the removed-leaf correction. -/
theorem step_degree_update (v : V) :
    ((step G).degree v : ℤ) = (G.degree v : ℤ) -
      (if v ∈ peelable G then 1 else 0) - removedNeighbors G (peelable G) v := by
  by_cases hv : v ∈ peelable G
  · have hd := peelable_degree G hv
    have hr := removedNeighbors_peelable_zero G hv
    have hs : (step G).degree v = 0 :=
      mask_degree_zero_of_not_mem G (peelable G)ᶜ (by simpa)
    simp [hv, hd, hr, hs]
  · have h := mask_compl_degree_add G (peelable G) hv
    change (step G).degree v + removedNeighbors G (peelable G) v = G.degree v at h
    have hz := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [Nat.cast_add] at hz
    simp only [hv, if_false]
    omega

omit [DecidableEq V] in
theorem leaf_neighbor_unique {v u w : V} (hv : G.degree v = 1)
    (hvu : G.Adj v u) (hvw : G.Adj v w) : u = w := by
  obtain ⟨a, ha, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  exact (huniq u hvu).trans (huniq w hvw).symm

/-- The literal degree-one selector set in the current actual graph. -/
def leaves : Finset V := Finset.univ.filter (fun v => G.degree v = 1)

omit [DecidableEq V] in
@[simp] theorem mem_leaves (v : V) : v ∈ leaves G ↔ G.degree v = 1 := by
  simp [leaves]

/-- A leaf has exactly one selected neighbor precisely when its sole neighbor is selected. -/
theorem leaf_selected_neighbor_count_one_iff (W : Finset V) {v : V}
    (hv : G.degree v = 1) :
    removedNeighbors G W v = 1 ↔ ∃ u, G.Adj v u ∧ u ∈ W := by
  rw [removedNeighbors_eq_filter, Finset.card_eq_one_iff_existsUnique]
  constructor
  · rintro ⟨u, hu, _⟩
    exact ⟨u, (Finset.mem_filter.mp hu).2, (Finset.mem_filter.mp hu).1⟩
  · rintro ⟨u, hvu, hu⟩
    refine ⟨u, Finset.mem_filter.mpr ⟨hu, hvu⟩, ?_⟩
    intro w hw
    exact leaf_neighbor_unique G hv (Finset.mem_filter.mp hw).2 hvu

/-- On a leaf, the degree-one neighbor count detects exactly the protected leaf-pair case. -/
theorem leaf_neighbor_count_one_iff {v : V} (hv : G.degree v = 1) :
    removedNeighbors G (leaves G) v = 1 ↔
      ∃ u, G.Adj v u ∧ G.degree u = 1 := by
  rw [leaf_selected_neighbor_count_one_iff G (leaves G) hv]
  simp only [mem_leaves]

/-- The paper's guard is the negation of the literal degree-one neighbor count selector. -/
theorem mem_peelable_iff_leaf_count (v : V) :
    v ∈ peelable G ↔ G.degree v = 1 ∧ removedNeighbors G (leaves G) v ≠ 1 := by
  rw [mem_peelable]
  constructor
  · rintro ⟨hv, u, hvu, hu⟩
    refine ⟨hv, ?_⟩
    intro hc
    obtain ⟨w, hvw, hw⟩ := (leaf_neighbor_count_one_iff G hv).mp hc
    exact hu (leaf_neighbor_unique G hv hvu hvw ▸ hw)
  · rintro ⟨hv, hc⟩
    obtain ⟨u, hvu, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    refine ⟨hv, u, hvu, ?_⟩
    intro hu
    exact hc ((leaf_neighbor_count_one_iff G hv).mpr ⟨u, hvu, hu⟩)

/-- Guarded leaves equal all leaves minus the leaf-pair endpoints detected by the count diagonal. -/
theorem peelable_eq_leaves_sdiff :
    peelable G = leaves G \ (leaves G).filter
      (fun v => removedNeighbors G (leaves G) v = 1) := by
  ext v
  simp only [mem_peelable_iff_leaf_count, Finset.mem_sdiff, Finset.mem_filter, mem_leaves]
  tauto

omit [DecidableEq V] in
/-- An edge between two leaves is the entire connected component, proved using actual walks. -/
theorem reachable_leaf_pair {v u z : V} (hv : G.degree v = 1) (hu : G.degree u = 1)
    (hvu : G.Adj v u) (hz : G.Reachable v z) : z = v ∨ z = u := by
  have closed : ∀ a b, (a = v ∨ a = u) → G.Adj a b → (b = v ∨ b = u) := by
    intro a b ha hab
    rcases ha with rfl | rfl
    · exact Or.inr (leaf_neighbor_unique G hv hab hvu)
    · exact Or.inl (leaf_neighbor_unique G hu hab hvu.symm)
  have hwalk : ∀ {a b}, (p : G.Walk a b) → (a = v ∨ a = u) → (b = v ∨ b = u) := by
    intro a b p
    induction p with
    | nil => exact id
    | @cons a b c hab p ih => exact fun ha => ih (closed a b ha hab)
  obtain ⟨p⟩ := hz
  exact hwalk p (Or.inl rfl)

omit [DecidableEq V] in
/-- A nonterminal actual finite tree has a guarded leaf. No pruning geometry is assumed. -/
theorem tree_exists_peelable (hTree : G.IsTree) {r : V} (hr : 2 ≤ G.degree r) :
    ∃ v, v ∈ peelable G := by
  let : Nontrivial V := SimpleGraph.nontrivial_of_degree_ne_zero (by omega : G.degree r ≠ 0)
  obtain ⟨v, hv⟩ := hTree.exists_vert_degree_one_of_nontrivial
  obtain ⟨u, hvu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  refine ⟨v, (mem_peelable G v).mpr ⟨hv, u, hvu, ?_⟩⟩
  intro hu
  rcases reachable_leaf_pair G hv hu hvu (hTree.connected v r) with hrv | hru
  · rw [hrv, hv] at hr
    omega
  · rw [hru, hu] at hr
    omega

omit [DecidableEq V] in
/-- Component degrees equal the original graph degrees; no external component vertices are adjacent. -/
theorem component_degree (C : G.ConnectedComponent)
    [Fintype C] [DecidableRel C.toSimpleGraph.Adj] (v : C) :
    C.toSimpleGraph.degree v = G.degree v := by
  let e : C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val :=
    { toFun := fun u => ⟨u.val.val, u.property⟩
      invFun := fun u => ⟨⟨u.val, C.mem_supp_of_adj_mem_supp v.property u.property⟩, u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr e

omit [DecidableEq V] in
/-- A nonterminal actual finite forest has a guarded leaf in a nonterminal component. -/
theorem forest_exists_peelable (hForest : G.IsAcyclic) {r : V} (hr : 2 ≤ G.degree r) :
    ∃ v, v ∈ peelable G := by
  classical
  let C := G.connectedComponentMk r
  let : Fintype C := Fintype.ofFinite C
  let : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  let rC : C := ⟨r, rfl⟩
  have hdeg : ∀ v : C, C.toSimpleGraph.degree v = G.degree v := component_degree G C
  have hrC : 2 ≤ C.toSimpleGraph.degree rC := by rw [hdeg]; exact hr
  obtain ⟨v, hv⟩ := tree_exists_peelable C.toSimpleGraph
    (hForest.isTree_connectedComponent C) hrC
  obtain ⟨hvdeg, u, hvu, hudeg⟩ := (mem_peelable C.toSimpleGraph v).mp hv
  refine ⟨v.val, (mem_peelable G v.val).mpr ⟨?_, u.val, hvu, ?_⟩⟩
  · simpa only [hdeg] using hvdeg
  · simpa only [hdeg] using hudeg

omit [DecidableEq V] in
/-- Terminal forests are exactly disjoint unions of isolated vertices and leaf pairs.
The degree formulation is equivalent to “every component is K₁ or K₂”.
-/
theorem forest_terminal_iff (hForest : G.IsAcyclic) :
    peelable G = ∅ ↔ ∀ v, G.degree v ≤ 1 := by
  constructor
  · intro hempty v
    by_contra hv
    have hhigh : 2 ≤ G.degree v := by omega
    obtain ⟨w, hw⟩ := forest_exists_peelable G hForest hhigh
    simp [hempty] at hw
  · intro hdeg
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvdeg, u, hvu, hudeg⟩ := (mem_peelable G v).mp hv
    have hpos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨v, hvu.symm⟩
    have hle := hdeg u
    omega

/-- Inactive vertices are isolated, so every peeled vertex is active. -/
theorem peelable_subset_active (S : Finset V) : peelable (mask G S) ⊆ S := by
  intro v hv
  by_contra hnot
  have hzero := mask_degree_zero_of_not_mem G S hnot
  have hone := peelable_degree (mask G S) hv
  omega

def nextActive (S : Finset V) : Finset V := S \ peelable (mask G S)

theorem nextActive_subset (S : Finset V) : nextActive G S ⊆ S := Finset.sdiff_subset

theorem nextActive_card_lt (S : Finset V) (hne : peelable (mask G S) ≠ ∅) :
    (nextActive G S).card < S.card := by
  have hsub := peelable_subset_active G S
  have hpos : 0 < (peelable (mask G S)).card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  unfold nextActive
  rw [Finset.card_sdiff_of_subset hsub]
  have hle := Finset.card_le_card hsub
  omega

/-- Actual active-set iteration, including its state update, rather than a supplied schedule. -/
def activeFrom : Finset V → ℕ → Finset V
  | S, 0 => S
  | S, n + 1 => activeFrom (nextActive G S) n

@[simp] theorem activeFrom_zero (S : Finset V) : activeFrom G S 0 = S := rfl

@[simp] theorem activeFrom_succ (S : Finset V) (n : ℕ) :
    activeFrom G S (n + 1) = activeFrom G (nextActive G S) n := rfl

/-- A genuine finite forest reaches only isolated vertices and K₂ components
in at most the original number of active vertices.
-/
theorem forest_pruning_terminates (hForest : G.IsAcyclic) (S : Finset V) :
    ∃ n, n ≤ S.card ∧ ∀ v, (mask G (activeFrom G S n)).degree v ≤ 1 := by
  have aux : ∀ k : ℕ, ∀ S : Finset V, S.card = k →
      ∃ n, n ≤ k ∧ ∀ v, (mask G (activeFrom G S n)).degree v ≤ 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro S hcard
      by_cases hempty : peelable (mask G S) = ∅
      · refine ⟨0, Nat.zero_le _, ?_⟩
        change ∀ v, (mask G S).degree v ≤ 1
        exact (forest_terminal_iff (mask G S) (mask_isAcyclic G hForest S)).mp hempty
      · have hlt : (nextActive G S).card < k := by
          rw [← hcard]
          exact nextActive_card_lt G S hempty
        obtain ⟨n, hn, hterm⟩ := ih (nextActive G S).card hlt (nextActive G S) rfl
        refine ⟨n + 1, by omega, ?_⟩
        change ∀ v, (mask G (activeFrom G (nextActive G S) n)).degree v ≤ 1
        exact hterm
  exact aux S.card S rfl

/-- Actual terminal components are K₁ or K₂, not merely an abstract degree promise. -/
theorem terminal_component_shape (hdeg : ∀ v, G.degree v ≤ 1) (C : G.ConnectedComponent) :
    (∃ v, C.supp = {v}) ∨ (∃ v u, G.Adj v u ∧ C.supp = {v, u}) := by
  obtain ⟨v, hv⟩ := C.nonempty_supp
  by_cases hvzero : G.degree v = 0
  · left
    refine ⟨v, ?_⟩
    ext z
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hz
      by_contra hne
      exact SimpleGraph.not_reachable_of_left_degree_zero (Ne.symm hne) hvzero
        (C.reachable_of_mem_supp hv hz)
    · rintro rfl
      exact hv
  · have hvone : G.degree v = 1 := by have h := hdeg v; omega
    obtain ⟨u, hvu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hvone
    have huone : G.degree u = 1 := by
      have hpos := (G.degree_pos_iff_exists_adj u).mpr ⟨v, hvu.symm⟩
      have hle := hdeg u
      omega
    right
    refine ⟨v, u, hvu, ?_⟩
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro hz
      exact reachable_leaf_pair G hvone huone hvu (C.reachable_of_mem_supp hv hz)
    · rintro (rfl | rfl)
      · exact hv
      · exact C.mem_supp_of_adj_mem_supp hv hvu

/-- Removing any set of actual leaves preserves every connection between surviving vertices. -/
theorem reachable_after_leaf_deletion (W : Finset V)
    (hLeaves : ∀ w ∈ W, G.degree w = 1) {u v : V} (hu : u ∉ W) (hv : v ∉ W)
    (hReach : G.Reachable u v) : (mask G Wᶜ).Reachable u v := by
  refine hReach.elim_path (fun p => ?_)
  have hkeep : ∀ w ∈ (p : G.Walk u v).support, w ∈ ((W : Set V)ᶜ) := by
    intro w hwp
    change w ∉ W
    intro hw
    have hss : (G.neighborSet w).Subsingleton := by
      intro x hx y hy
      exact leaf_neighbor_unique G (hLeaves w hw) hx hy
    exact p.isTrail.not_mem_support_of_subsingleton_neighborSet
      (by intro hwu; exact hu (hwu ▸ hw)) (by intro hwv; exact hv (hwv ▸ hw)) hss hwp
  let f : G.induce ((W : Set V)ᶜ) →g mask G Wᶜ :=
    { toFun := fun x => x.val
      map_rel' := by
        intro x y hxy
        exact ⟨Finset.mem_compl.mpr x.property, Finset.mem_compl.mpr y.property, hxy⟩ }
  exact (((p : G.Walk u v).induce ((W : Set V)ᶜ) hkeep).map f).reachable

theorem guarded_step_preserves_reachable {u v : V}
    (hu : u ∉ peelable G) (hv : v ∉ peelable G) (hReach : G.Reachable u v) :
    (step G).Reachable u v :=
  reachable_after_leaf_deletion G (peelable G) (fun _ hw => peelable_degree G hw) hu hv hReach

omit [DecidableRel G.Adj] [DecidableEq V] in
@[simp] theorem mask_univ : mask G Finset.univ = G := by
  ext u v
  simp

/-- The active-set update and the full-vertex graph update describe the same graph. -/
theorem mask_nextActive_eq_step (S : Finset V) :
    mask G (nextActive G S) = step (mask G S) := by
  ext u v
  simp only [nextActive, step, mask_adj, Finset.mem_sdiff, Finset.mem_compl]
  tauto

theorem nextActive_meets_component (S : Finset V) (C : G.ConnectedComponent)
    (h : ∃ v, v ∈ S ∧ v ∈ C.supp) : ∃ v, v ∈ nextActive G S ∧ v ∈ C.supp := by
  obtain ⟨v, hvS, hvC⟩ := h
  by_cases hvPeel : v ∈ peelable (mask G S)
  · obtain ⟨_, u, hvu, _⟩ := (mem_peelable (mask G S) v).mp hvPeel
    refine ⟨u, Finset.mem_sdiff.mpr ⟨hvu.2.1, ?_⟩, ?_⟩
    · exact peelable_neighbor_not_mem (mask G S) hvPeel hvu
    · exact C.mem_supp_of_adj_mem_supp hvC hvu.2.2
  · exact ⟨v, Finset.mem_sdiff.mpr ⟨hvS, hvPeel⟩, hvC⟩

theorem activeFrom_subset (S : Finset V) (n : ℕ) : activeFrom G S n ⊆ S := by
  induction n generalizing S with
  | zero => exact Finset.Subset.refl _
  | succ n ih => exact (ih (nextActive G S)).trans (nextActive_subset G S)

/-- Guarding ensures that no original component disappears during any number of rounds. -/
theorem activeFrom_meets_component (S : Finset V) (n : ℕ) (C : G.ConnectedComponent)
    (h : ∃ v, v ∈ S ∧ v ∈ C.supp) : ∃ v, v ∈ activeFrom G S n ∧ v ∈ C.supp := by
  induction n generalizing S with
  | zero => exact h
  | succ n ih => exact ih (nextActive G S) (nextActive_meets_component G S C h)

/-- Every connection between surviving active vertices is preserved through all rounds. -/
theorem activeFrom_preserves_reachable (S : Finset V) (n : ℕ) {u v : V}
    (hu : u ∈ activeFrom G S n) (hv : v ∈ activeFrom G S n)
    (hReach : (mask G S).Reachable u v) :
    (mask G (activeFrom G S n)).Reachable u v := by
  induction n generalizing S with
  | zero => exact hReach
  | succ n ih =>
    have huNext : u ∈ nextActive G S := activeFrom_subset G (nextActive G S) n hu
    have hvNext : v ∈ nextActive G S := activeFrom_subset G (nextActive G S) n hv
    have hStep := guarded_step_preserves_reachable (mask G S)
      (Finset.mem_sdiff.mp huNext).2 (Finset.mem_sdiff.mp hvNext).2 hReach
    rw [← mask_nextActive_eq_step] at hStep
    exact ih (nextActive G S) hu hv hStep

/-- The final connected component is exactly the surviving part of its original component. -/
theorem surviving_component_iff (n : ℕ) (C : G.ConnectedComponent) {v z : V}
    (hv : v ∈ activeFrom G Finset.univ n) (hvC : v ∈ C.supp) :
    z ∈ ((mask G (activeFrom G Finset.univ n)).connectedComponentMk v).supp ↔
      z ∈ activeFrom G Finset.univ n ∧ z ∈ C.supp := by
  let S := activeFrom G Finset.univ n
  let H := mask G S
  change z ∈ (H.connectedComponentMk v).supp ↔ z ∈ S ∧ z ∈ C.supp
  constructor
  · intro hz
    have hReach : H.Reachable v z :=
      (H.connectedComponentMk v).reachable_of_mem_supp (by rfl) hz
    have hOrig : G.Reachable v z := hReach.mono (mask_le G S)
    have hzC : z ∈ C.supp := by
      change G.connectedComponentMk z = C
      exact (SimpleGraph.ConnectedComponent.sound hOrig).symm.trans hvC
    refine ⟨?_, hzC⟩
    by_cases hzv : z = v
    · exact hzv ▸ hv
    · have hzpos : 0 < H.degree z := hReach.degree_pos_right (Ne.symm hzv)
      obtain ⟨w, hzw⟩ := (H.degree_pos_iff_exists_adj z).mp hzpos
      exact hzw.1
  · rintro ⟨hz, hzC⟩
    have hOrig : (mask G Finset.univ).Reachable v z := by
      rw [mask_univ]
      exact C.reachable_of_mem_supp hvC hzC
    have hReach := activeFrom_preserves_reachable G Finset.univ n hv hz hOrig
    exact (SimpleGraph.ConnectedComponent.sound hReach).symm

/-- The guarded algorithm leaves one vertex or one edge in each original forest
component. This proves the terminal-core geometry used by the paper.
-/
theorem forest_pruning_terminal_core (hForest : G.IsAcyclic) :
    ∃ n, n ≤ Fintype.card V ∧ ∀ C : G.ConnectedComponent,
      (∃ v, ∀ z, (z ∈ activeFrom G Finset.univ n ∧ z ∈ C.supp) ↔ z = v) ∨
      (∃ v u, G.Adj v u ∧
        ∀ z, (z ∈ activeFrom G Finset.univ n ∧ z ∈ C.supp) ↔ z = v ∨ z = u) := by
  obtain ⟨n, hn, hdeg⟩ := forest_pruning_terminates G hForest Finset.univ
  refine ⟨n, by simpa using hn, ?_⟩
  intro C
  obtain ⟨r, hr⟩ := C.nonempty_supp
  obtain ⟨v, hv, hvC⟩ := activeFrom_meets_component G Finset.univ n C
    ⟨r, Finset.mem_univ _, hr⟩
  let H := mask G (activeFrom G Finset.univ n)
  let D := H.connectedComponentMk v
  have hComp : ∀ z, z ∈ D.supp ↔ z ∈ activeFrom G Finset.univ n ∧ z ∈ C.supp :=
    fun z => surviving_component_iff G n C hv hvC
  rcases terminal_component_shape H hdeg D with ⟨a, ha⟩ | ⟨a, b, hab, habSupp⟩
  · left
    refine ⟨a, fun z => ?_⟩
    rw [← hComp z, ha]
    rfl
  · right
    refine ⟨a, b, hab.2.2, fun z => ?_⟩
    rw [← hComp z, habSupp]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- The simultaneous ordinary leaf core used for induction on a tree of order > 2. -/
def leafCore : Finset V := Finset.univ.filter (fun v => G.degree v ≠ 1)

omit [DecidableEq V] in
@[simp] theorem mem_leafCore (v : V) : v ∈ leafCore G ↔ G.degree v ≠ 1 := by
  simp [leafCore]

theorem connected_leaf_pair_card_le_two (hconn : G.Connected) {v u : V}
    (hv : G.degree v = 1) (hu : G.degree u = 1) (hvu : G.Adj v u) :
    Fintype.card V ≤ 2 := by
  have hsub : (Finset.univ : Finset V) ⊆ {v, u} := by
    intro z _
    have hz := reachable_leaf_pair G hv hu hvu (hconn v z)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hcard := Finset.card_le_card hsub
  have hpair : ({v, u} : Finset V).card ≤ 2 := by
    simpa only [Finset.card_singleton] using (Finset.card_insert_le v {u})
  exact (by simpa only [Finset.card_univ] using hcard : Fintype.card V ≤ ({v, u} : Finset V).card).trans hpair

/-- For a genuine tree with more than two vertices, every leaf's sole neighbor is in the core. -/
theorem leaf_neighbor_mem_core (hTree : G.IsTree) (hcard : 2 < Fintype.card V)
    {v u : V} (hv : G.degree v = 1) (hvu : G.Adj v u) : u ∈ leafCore G := by
  rw [mem_leafCore]
  intro hu
  exact (Nat.not_le_of_gt hcard) (connected_leaf_pair_card_le_two G hTree.connected hv hu hvu)

theorem leafCore_nonempty (hTree : G.IsTree) (hcard : 2 < Fintype.card V) :
    (leafCore G).Nonempty := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < Fintype.card V)
  obtain ⟨v, hv⟩ := hTree.exists_vert_degree_one_of_nontrivial
  obtain ⟨u, hvu, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  exact ⟨u, leaf_neighbor_mem_core G hTree hcard hv hvu⟩

omit [DecidableEq V] in
theorem leafCore_card_lt (hTree : G.IsTree) (hcard : 2 < Fintype.card V) :
    (leafCore G).card < Fintype.card V := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < Fintype.card V)
  obtain ⟨v, hv⟩ := hTree.exists_vert_degree_one_of_nontrivial
  have hstrict : leafCore G ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    have hvmem : v ∈ leafCore G := by rw [heq]; exact Finset.mem_univ _
    exact (mem_leafCore G v).mp hvmem hv
  simpa only [Finset.card_univ] using Finset.card_lt_card hstrict

/-- Deleting all leaves from an actual tree of order > 2 produces a smaller nonempty actual tree. -/
theorem leafCore_isTree (hTree : G.IsTree) (hcard : 2 < Fintype.card V) :
    (G.induce (leafCore G : Set V)).IsTree := by
  obtain ⟨v, hv⟩ := leafCore_nonempty G hTree hcard
  let : Nonempty (leafCore G : Set V) := ⟨⟨v, hv⟩⟩
  refine ⟨?_, hTree.isAcyclic.induce _⟩
  refine ⟨hTree.preconnected.induce_of_degree_eq_one ?_⟩
  intro w hw
  have hwleaf : G.degree w = 1 := by
    by_contra hnot
    exact hw ((mem_leafCore G w).mpr hnot)
  intro x hx y hy
  exact leaf_neighbor_unique G hwleaf hx hy

/-- Predicate-subtype form, avoiding a dependent conversion of the vertex
type when the reconstruction induction uses degree predicates directly. -/
theorem nonleaf_predicate_core_isTree (hTree : G.IsTree) (hcard : 2 < Fintype.card V) :
    (G.induce {u | G.degree u ≠ 1}).IsTree := by
  obtain ⟨v, hv⟩ := leafCore_nonempty G hTree hcard
  let : Nonempty ({u | G.degree u ≠ 1} : Set V) := ⟨⟨v, (mem_leafCore G v).mp hv⟩⟩
  refine ⟨⟨hTree.preconnected.induce_of_degree_eq_one ?_⟩, hTree.isAcyclic.induce _⟩
  intro w hw
  have hwleaf : G.degree w = 1 := not_not.mp hw
  intro x hx y hy
  exact leaf_neighbor_unique G hwleaf hx hy

theorem leafCore_eq_leaves_compl : leafCore G = (leaves G)ᶜ := by
  ext v
  simp only [mem_leafCore, Finset.mem_compl, mem_leaves]

/-- On a tree of order > 2 the guard removes every leaf; only the small terminal bases need it. -/
theorem peelable_eq_leaves_of_tree (hTree : G.IsTree) (hcard : 2 < Fintype.card V) :
    peelable G = leaves G := by
  ext v
  rw [mem_peelable, mem_leaves]
  constructor
  · exact fun h => h.1
  · intro hv
    obtain ⟨u, hvu, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
    exact ⟨hv, u, hvu, (mem_leafCore G u).mp (leaf_neighbor_mem_core G hTree hcard hv hvu)⟩

/-- The induced active graph and full-vertex masked graph have the same active degrees. -/
theorem induce_degree_eq_mask_degree (S : Finset V) (v : (S : Set V)) :
    (G.induce (S : Set V)).degree v = (mask G S).degree v.val := by
  let e : (G.induce (S : Set V)).neighborSet v ≃ (mask G S).neighborSet v.val :=
    { toFun := fun u => ⟨u.val.val, v.property, u.val.property, u.property⟩
      invFun := fun u => ⟨⟨u.val, u.property.2.1⟩, u.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr e

/-- Exact degree update in the smaller tree used by the reconstruction induction. -/
theorem leafCore_degree_add (v : (leafCore G : Set V)) :
    (G.induce (leafCore G : Set V)).degree v +
      removedNeighbors G (leaves G) v.val = G.degree v.val := by
  rw [induce_degree_eq_mask_degree]
  have hmask := congrArg (fun S : Finset V => (mask G S).degree v.val)
    (leafCore_eq_leaves_compl G)
  rw [hmask]
  exact mask_compl_degree_add G (leaves G) (by
    intro hv
    exact (mem_leafCore G v.val).mp v.property ((mem_leaves G v.val).mp hv))

end

end PrincipalMomentAudit.ForestPruning
