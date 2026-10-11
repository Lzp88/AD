import Mathlib

/-!
Actual rooted components of a simple tree. A branch at child c of parent p
is the connected component of c after all edges incident to p are removed.
The separation and boundary lemmas below follow from IsTree/IsAcyclic and
the bridge property; they are not supplied as quotient assumptions.
-/

namespace PrincipalMomentAudit.RootedOrbit

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The actual component below a child, with its parent isolated. -/
def branch (p c : V) : Set V := {x | (G.deleteIncidenceSet p).Reachable c x}

theorem child_mem_branch (p c : V) : c ∈ branch G p c := Reachable.rfl

private theorem isolated_parent (p : V) :
    (G.deleteIncidenceSet p).neighborSet p = ∅ := by
  ext x
  simp [neighborSet, deleteIncidenceSet_adj]

theorem parent_not_mem_branch {p c : V} (hpc : G.Adj p c) : p ∉ branch G p c := by
  exact not_reachable_of_neighborSet_right_eq_empty hpc.ne.symm (isolated_parent G p)

private theorem delete_parent_le_delete_child_edge {p c : V} (hpc : G.Adj p c) :
    G.deleteIncidenceSet p ≤ G.deleteEdges {s(p, c)} := by
  apply deleteEdges_anti
  apply Set.singleton_subset_iff.mpr
  simp [hpc]

/-- A child component in an acyclic graph can meet the parent at only its
specified root c. This is the tree fact needed for a branch graft or swap. -/
theorem branch_parent_neighbor_unique (hG : G.IsAcyclic) {p c x : V}
    (hpc : G.Adj p c) (hx : x ∈ branch G p c) (hpx : G.Adj p x) : x = c := by
  by_contra hxc
  have hcx : (G.deleteEdges {s(p, c)}).Reachable c x :=
    hx.mono (delete_parent_le_delete_child_edge G hpc)
  have hxpadj : (G.deleteEdges {s(p, c)}).Adj x p := by
    apply deleteEdges_adj.mpr
    refine ⟨hpx.symm, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    intro h
    rcases h with h | h
    · exact hpx.ne (h.1.symm)
    · exact hxc h.1
  have hbridge := isAcyclic_iff_forall_adj_isBridge.mp hG hpc
  exact hbridge ((hcx.trans hxpadj.reachable).symm)

/-- A branch has no outside edges except its root-parent edge. The statement
is an equivalence, making it usable directly when gluing rooted isomorphisms. -/
theorem branch_boundary (hG : G.IsAcyclic) {p c x y : V}
    (hpc : G.Adj p c) (hx : x ∈ branch G p c) (hy : y ∉ branch G p c) :
    G.Adj x y ↔ x = c ∧ y = p := by
  constructor
  · intro hxy
    have hyp : y = p := by
      by_contra hn
      have hxp : x ≠ p := by
        intro h
        subst x
        exact parent_not_mem_branch G hpc hx
      have hdel : (G.deleteIncidenceSet p).Adj x y :=
        deleteIncidenceSet_adj.mpr ⟨hxy, hxp, hn⟩
      exact hy (hx.trans hdel.reachable)
    subst y
    exact ⟨branch_parent_neighbor_unique G hG hpc hx hxy.symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact hpc.symm

/-- Distinct children of a parent lie in disjoint actual components. -/
theorem sibling_branches_disjoint (hG : G.IsAcyclic) {p c d : V}
    (hpc : G.Adj p c) (hpd : G.Adj p d) (hcd : c ≠ d) :
    Disjoint (branch G p c) (branch G p d) := by
  apply Set.disjoint_left.mpr
  intro x hcx hdx
  have hcdreach : (G.deleteIncidenceSet p).Reachable c d := hcx.trans hdx.symm
  exact hcd (branch_parent_neighbor_unique G hG hpc hcdreach hpd).symm

private theorem reachable_without_parent {u v : V} (w : G.Walk u v) (p : V)
    (havoids : p ∉ w.support) : (G.deleteIncidenceSet p).Reachable u v := by
  revert havoids
  induction w with
  | nil =>
    intro _
    exact Reachable.rfl
  | @cons u z v huz w ih =>
    intro ha
    have hparts : p ≠ u ∧ p ∉ w.support := by simpa using ha
    have hz : z ≠ p := by
      intro h
      exact hparts.2 (h ▸ w.start_mem_support)
    have hu : u ≠ p := Ne.symm hparts.1
    exact (deleteIncidenceSet_adj.mpr ⟨huz, hu, hz⟩).reachable.trans (ih hparts.2)

/-- Every nonparent vertex of an actual connected tree belongs to a child
component. A shortest simple path supplies the child and avoids the parent
after its first step. -/
theorem exists_child_branch (hG : G.IsTree) {p x : V} (hxp : x ≠ p) :
    ∃ c, G.Adj p c ∧ x ∈ branch G p c := by
  obtain ⟨w, hw, _⟩ := hG.connected.exists_path_of_dist p x
  cases w with
  | nil => exact (hxp rfl).elim
  | cons hpz w =>
    have hparts : p ∉ w.support ∧ w.support.Nodup := by
      simpa only [Walk.support_cons, List.nodup_cons] using hw.support_nodup
    exact ⟨_, hpz, reachable_without_parent G w p hparts.1⟩

/-- The actual child components partition the complement of the parent. -/
theorem child_branch_unique (hG : G.IsTree) {p x : V} (hxp : x ≠ p) :
    ∃! c, G.Adj p c ∧ x ∈ branch G p c := by
  obtain ⟨c, hpc, hcx⟩ := exists_child_branch G hG hxp
  refine ⟨c, ⟨hpc, hcx⟩, ?_⟩
  intro d hd
  by_contra hdc
  exact Set.disjoint_left.mp (sibling_branches_disjoint G hG.isAcyclic hpc hd.1
    (Ne.symm hdc)) hcx hd.2

noncomputable section

/-- Exchange two disjoint sets through an actual equivalence and fix their
complement. This is the underlying permutation used to swap tree branches. -/
def swapMap (S T : Set V) (e : S ≃ T) (x : V) : V := by
  classical
  exact if hx : x ∈ S then (e ⟨x, hx⟩ : V)
    else if hx : x ∈ T then (e.symm ⟨x, hx⟩ : V) else x

theorem swapMap_left {S T : Set V} (e : S ≃ T) {x : V} (hx : x ∈ S) :
    swapMap S T e x = (e ⟨x, hx⟩ : V) := by
  classical
  simp [swapMap, hx]

theorem swapMap_right {S T : Set V} (e : S ≃ T) (hST : Disjoint S T)
    {x : V} (hx : x ∈ T) : swapMap S T e x = (e.symm ⟨x, hx⟩ : V) := by
  classical
  have hn : x ∉ S := fun hs => Set.disjoint_left.mp hST hs hx
  simp [swapMap, hn, hx]

theorem swapMap_out {S T : Set V} (e : S ≃ T) {x : V}
    (hxS : x ∉ S) (hxT : x ∉ T) : swapMap S T e x = x := by
  classical
  simp [swapMap, hxS, hxT]

theorem swapMap_involutive {S T : Set V} (e : S ≃ T) (hST : Disjoint S T) :
    Function.Involutive (swapMap S T e) := by
  classical
  intro x
  by_cases hxS : x ∈ S
  · rw [swapMap_left e hxS, swapMap_right e hST (e ⟨x, hxS⟩).property]
    simp
  · by_cases hxT : x ∈ T
    · rw [swapMap_right e hST hxT, swapMap_left e (e.symm ⟨x, hxT⟩).property]
      simp
    · rw [swapMap_out e hxS hxT, swapMap_out e hxS hxT]

/-- A rooted branch isomorphism is an isomorphism of the actual induced
components, preserving the child roots. It contains no global automorphism. -/
def RootedBranchIso (p c d : V) : Prop :=
  ∃ e : G.induce (branch G p c) ≃g G.induce (branch G p d),
    e ⟨c, child_mem_branch G p c⟩ = ⟨d, child_mem_branch G p d⟩

private theorem branch_swap_adj (hG : G.IsAcyclic) {p c d : V}
    (hpc : G.Adj p c) (hpd : G.Adj p d) (hcd : c ≠ d)
    (e : G.induce (branch G p c) ≃g G.induce (branch G p d))
    (he : e ⟨c, child_mem_branch G p c⟩ = ⟨d, child_mem_branch G p d⟩)
    {x y : V} (hxy : G.Adj x y) :
    G.Adj (swapMap (branch G p c) (branch G p d) e.toEquiv x)
      (swapMap (branch G p c) (branch G p d) e.toEquiv y) := by
  classical
  let S := branch G p c
  let T := branch G p d
  have hST : Disjoint S T := sibling_branches_disjoint G hG hpc hpd hcd
  have hpS : p ∉ S := parent_not_mem_branch G hpc
  have hpT : p ∉ T := parent_not_mem_branch G hpd
  have hpfix : swapMap S T e.toEquiv p = p := swapMap_out e.toEquiv hpS hpT
  have heval : (e ⟨c, child_mem_branch G p c⟩ : V) = d :=
    congrArg Subtype.val he
  have hesymm : e.symm ⟨d, child_mem_branch G p d⟩ = ⟨c, child_mem_branch G p c⟩ := by
    rw [← he]
    exact e.symm_apply_apply _
  have heinv : (e.symm ⟨d, child_mem_branch G p d⟩ : V) = c :=
    congrArg Subtype.val hesymm
  have left_case {u v : V} (hu : u ∈ S) (huv : G.Adj u v) :
      G.Adj (swapMap S T e.toEquiv u) (swapMap S T e.toEquiv v) := by
    by_cases hv : v ∈ S
    · rw [swapMap_left e.toEquiv hu, swapMap_left e.toEquiv hv]
      exact e.map_adj_iff.mpr huv
    · obtain ⟨huc, hvp⟩ := (branch_boundary G hG hpc hu hv).mp huv
      rw [huc, hvp]
      rw [swapMap_left e.toEquiv (child_mem_branch G p c), hpfix]
      change G.Adj (e ⟨c, child_mem_branch G p c⟩ : V) p
      rw [heval]
      exact hpd.symm
  have right_case {u v : V} (hu : u ∈ T) (huv : G.Adj u v) :
      G.Adj (swapMap S T e.toEquiv u) (swapMap S T e.toEquiv v) := by
    by_cases hv : v ∈ T
    · rw [swapMap_right e.toEquiv hST hu, swapMap_right e.toEquiv hST hv]
      exact e.symm.map_adj_iff.mpr huv
    · obtain ⟨hud, hvp⟩ := (branch_boundary G hG hpd hu hv).mp huv
      rw [hud, hvp]
      rw [swapMap_right e.toEquiv hST (child_mem_branch G p d), hpfix]
      change G.Adj (e.symm ⟨d, child_mem_branch G p d⟩ : V) p
      rw [heinv]
      exact hpc.symm
  by_cases hxS : x ∈ S
  · exact left_case hxS hxy
  · by_cases hxT : x ∈ T
    · exact right_case hxT hxy
    · by_cases hyS : y ∈ S
      · exact (left_case hyS hxy.symm).symm
      · by_cases hyT : y ∈ T
        · exact (right_case hyT hxy.symm).symm
        · rw [swapMap_out e.toEquiv hxS hxT, swapMap_out e.toEquiv hyS hyT]
          exact hxy

/-- In an actual acyclic graph, isomorphic rooted sibling branches can be
swapped by a graph automorphism fixing their parent and every outside vertex.
This constructs the automorphism; its existence is not an assumption. -/
theorem sibling_branch_iso_gives_automorphism (hG : G.IsAcyclic) {p c d : V}
    (hpc : G.Adj p c) (hpd : G.Adj p d) (hiso : RootedBranchIso G p c d) :
    ∃ α : G ≃g G, α p = p ∧ α c = d ∧
      ∀ x, x ∉ branch G p c → x ∉ branch G p d → α x = x := by
  classical
  by_cases hcd : c = d
  · subst d
    exact ⟨Iso.refl, rfl, rfl, fun _ _ _ => rfl⟩
  obtain ⟨e, he⟩ := hiso
  let S := branch G p c
  let T := branch G p d
  have hST : Disjoint S T := sibling_branches_disjoint G hG hpc hpd hcd
  let f := swapMap S T e.toEquiv
  have hf : Function.Involutive f := swapMap_involutive e.toEquiv hST
  let α : G ≃g G :=
    { toEquiv := hf.toPerm f
      map_rel_iff' := by
        intro x y
        constructor
        · intro hxy
          have h := branch_swap_adj G hG hpc hpd hcd e he hxy
          change G.Adj (f (f x)) (f (f y)) at h
          simpa only [hf x, hf y] using h
        · exact branch_swap_adj G hG hpc hpd hcd e he }
  refine ⟨α, ?_, ?_, ?_⟩
  · exact swapMap_out e.toEquiv (parent_not_mem_branch G hpc) (parent_not_mem_branch G hpd)
  · change swapMap S T e.toEquiv c = d
    rw [swapMap_left e.toEquiv (child_mem_branch G p c)]
    exact congrArg Subtype.val he
  · intro x hxS hxT
    exact swapMap_out e.toEquiv hxS hxT

end

#print axioms branch_parent_neighbor_unique
#print axioms branch_boundary
#print axioms sibling_branches_disjoint
#print axioms exists_child_branch
#print axioms child_branch_unique
#print axioms sibling_branch_iso_gives_automorphism

end PrincipalMomentAudit.RootedOrbit
