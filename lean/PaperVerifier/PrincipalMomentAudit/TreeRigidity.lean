import PaperVerifier.PrincipalMomentAudit.TreeReconstruction
import PaperVerifier.PrincipalMomentAudit.ForestPruning
import PaperVerifier.PrincipalMomentAudit.LeafGrafting

/-!
Actual finite-tree reconstruction from equal weighted equitable data.
The proof is the written Theorem 5.1 argument: strip leaves, reconstruct
the smaller core, and attach child multisets with their prescribed counts.
It proves a stronger statement for common equitable labels, so that the
old orbit cells need not be recomputed after a leaf-stripping round.
-/

namespace PrincipalMomentAudit.TreeReconstruction
noncomputable section
open SimpleGraph

universe u v w
variable {V : Type u} {W : Type v} {α : Type w} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]
variable (c : V → α) (d : W → α)

local instance : DecidableEq α := Classical.decEq _

theorem nonleaf_core_isTree (hG : G.IsTree) (hcard : 2 < Fintype.card V) :
    (G.induce {u | G.degree u ≠ 1}).IsTree := by
  classical
  have hset : (ForestPruning.leafCore G : Set V) = {u | G.degree u ≠ 1} := by
    ext v
    simp
  have ht := ForestPruning.leafCore_isTree G hG hcard
  rw [hset] at ht
  exact ht

theorem nonleaf_core_card_lt (hG : G.IsTree) (hcard : 2 < Fintype.card V) :
    Fintype.card {u : V // G.degree u ≠ 1} < Fintype.card V := by
  classical
  simpa [Fintype.card_subtype, ForestPruning.leafCore] using
    ForestPruning.leafCore_card_lt G hG hcard

theorem leaf_unique_core_parent (hG : G.IsTree) (hcard : 2 < Fintype.card V) :
    ∀ l, ¬ (G.degree l ≠ 1) → ∃! u : {v // G.degree v ≠ 1}, G.Adj u l := by
  classical
  intro l hl
  have hleaf : G.degree l = 1 := not_not.mp hl
  obtain ⟨p, hp, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hleaf
  have hpcore : G.degree p ≠ 1 := by
    simpa using ForestPruning.leaf_neighbor_mem_core G hG hcard hleaf hp
  refine ⟨⟨p, hpcore⟩, hp.symm, ?_⟩
  intro q hq
  apply Subtype.ext
  exact huniq q hq.symm

theorem leaves_not_adj (hG : G.IsTree) (hcard : 2 < Fintype.card V) :
    ∀ l m, ¬ (G.degree l ≠ 1) → ¬ (G.degree m ≠ 1) → ¬ G.Adj l m := by
  classical
  intro l m hl hm hadj
  have hcore := ForestPruning.leaf_neighbor_mem_core G hG hcard (not_not.mp hl) hadj
  exact hm (by simpa using hcore)

def core_neighbor_fiber_equiv (u : {u : V // G.degree u ≠ 1}) (k : α) :
    {z : {z : G.neighborSet (u : V) // c z = k} // G.degree z ≠ 1} ≃
      {z : (G.induce {u | G.degree u ≠ 1}).neighborSet u // c z = k} where
  toFun z := ⟨⟨⟨z.val.val, z.property⟩, z.val.val.property⟩, z.val.property⟩
  invFun z := ⟨⟨⟨z.val.val, z.val.property⟩, z.property⟩, z.val.val.property⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl

def child_neighbor_fiber_equiv (u : {u : V // G.degree u ≠ 1}) (k : α) :
    {z : {z : G.neighborSet (u : V) // c z = k} // ¬ (G.degree z ≠ 1)} ≃
      LeafGrafting.ChildFiber G (fun v => G.degree v ≠ 1) c u k where
  toFun z := ⟨z.val.val, z.property, z.val.val.property, z.val.property⟩
  invFun z := ⟨⟨⟨z.val, z.property.2.1⟩, z.property.2.2⟩, z.property.1⟩
  left_inv z := by ext; rfl
  right_inv z := by ext; rfl

theorem leaf_child_count (u : {u : V // G.degree u ≠ 1}) (k : α) :
    Fintype.card (LeafGrafting.ChildFiber G (fun v => G.degree v ≠ 1) c u k) =
      neighborCount G c u k -
        neighborCount (G.induce {u | G.degree u ≠ 1}) (fun u => c u) u k := by
  classical
  rw [← Fintype.card_congr (child_neighbor_fiber_equiv G c u k), Fintype.card_subtype_compl]
  rw [Fintype.card_congr (core_neighbor_fiber_equiv G c u k)]
  rfl

theorem leaf_child_counts_equal
    (hsize : ∀ k, cellSize c k = cellSize d k)
    (hcount : ∀ u v, c u = d v → ∀ k, neighborCount G c u k = neighborCount H d v k)
    (u : {u : V // G.degree u ≠ 1}) (v : {v : W // H.degree v ≠ 1})
    (huv : c u = d v) (k : α) :
    Fintype.card (LeafGrafting.ChildFiber G (fun v => G.degree v ≠ 1) c u k) =
      Fintype.card (LeafGrafting.ChildFiber H (fun v => H.degree v ≠ 1) d v k) := by
  rw [leaf_child_count, leaf_child_count, hcount u v huv k,
    core_neighbor_counts_equal G H c d hsize hcount u v huv k]

theorem colored_tree_rigidity_aux (n : ℕ) :
    ∀ {V : Type u} {W : Type v} [Fintype V] [Fintype W]
      (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]
      (c : V → α) (d : W → α),
      Fintype.card V = n → G.IsTree → H.IsTree →
      (∀ k, cellSize c k = cellSize d k) →
      (∀ u v, c u = d v → ∀ k, neighborCount G c u k = neighborCount H d v k) →
      ∃ f : G ≃g H, ∀ u, d (f u) = c u := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V W _ _ G H _ _ c d hn hG hH hsize hcount
    by_cases hsmall : Fintype.card V ≤ 2
    · exact small_colored_tree_iso G H c d hG hH hsize hsmall
    have hlarge : 2 < Fintype.card V := by omega
    have hlargeH : 2 < Fintype.card W := by
      rw [← Fintype.card_congr (colorEquiv c d hsize)]
      exact hlarge
    let CoreG := {u : V // G.degree u ≠ 1}
    let CoreH := {v : W // H.degree v ≠ 1}
    let Gcore := G.induce {u | G.degree u ≠ 1}
    let Hcore := H.induce {v | H.degree v ≠ 1}
    have hlt : Fintype.card CoreG < n := by
      rw [← hn]
      exact nonleaf_core_card_lt G hG hlarge
    obtain ⟨f, hf⟩ := ih (Fintype.card CoreG) hlt Gcore Hcore
      (fun u => c u) (fun v => d v) rfl
      (nonleaf_core_isTree G hG hlarge) (nonleaf_core_isTree H hH hlargeH)
      (core_cell_sizes_equal G H c d hsize hcount)
      (fun u v huv k => core_neighbor_counts_equal G H c d hsize hcount u v huv k)
    let fibers : ∀ u : CoreG, ∀ k,
        LeafGrafting.ChildFiber G (fun v => G.degree v ≠ 1) c u k ≃
          LeafGrafting.ChildFiber H (fun v => H.degree v ≠ 1) d (f u) k :=
      fun u k => Fintype.equivOfCardEq
        (leaf_child_counts_equal G H c d hsize hcount u (f u) (hf u).symm k)
    obtain ⟨whole, _, hlabels⟩ := LeafGrafting.graft_colored_iso G H
      (fun v => G.degree v ≠ 1) (fun v => H.degree v ≠ 1) c d f fibers
      (leaf_unique_core_parent G hG hlarge) (leaf_unique_core_parent H hH hlargeH)
      (leaves_not_adj G hG hlarge) (leaves_not_adj H hH hlargeH) hf
    exact ⟨whole, hlabels⟩

/-- Actual colored finite trees are determined by weighted equitable data.
Only actual tree, cell-cardinality, and neighbor-count hypotheses remain. -/
theorem colored_tree_rigidity (hG : G.IsTree) (hH : H.IsTree)
    (hsize : ∀ k, cellSize c k = cellSize d k)
    (hcount : ∀ u v, c u = d v → ∀ k, neighborCount G c u k = neighborCount H d v k) :
    ∃ f : G ≃g H, ∀ u, d (f u) = c u :=
  colored_tree_rigidity_aux (Fintype.card V) G H c d rfl hG hH hsize hcount

#print axioms colored_tree_rigidity
end
end PrincipalMomentAudit.TreeReconstruction
