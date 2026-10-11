import Mathlib

/-!
Supporting lemmas for public arXiv:2607.21494v1 Theorem 5.1.
The reconstruction uses the written leaf-stripping and child-multiset argument.
Labels may be any common equitable partition; they need not remain automorphism
orbits after deleting leaves. No tree-isomorphism conclusion is assumed here.
The complete recursive theorem is added only after its actual graph obligations
have been proved.
-/

namespace PrincipalMomentAudit.TreeReconstruction
noncomputable section
open SimpleGraph

variable {V W α : Type*} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]
variable (c : V → α) (d : W → α)

def cellSize (c : V → α) (k : α) : ℕ := by
  classical
  exact Fintype.card {v // c v = k}

def neighborCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → α) (u : V) (k : α) : ℕ := by
  classical
  exact Fintype.card {v : G.neighborSet u // c v = k}

/-- An arbitrary label-preserving bijection from equal actual fiber cardinalities. -/
def colorEquiv (hsize : ∀ k, cellSize c k = cellSize d k) : V ≃ W := by
  classical
  exact Equiv.ofFiberEquiv (fun k => Fintype.equivOfCardEq (hsize k))

theorem colorEquiv_map (hsize : ∀ k, cellSize c k = cellSize d k) (u : V) :
    d (colorEquiv c d hsize u) = c u := by
  exact Equiv.ofFiberEquiv_map _ _

theorem degree_eq_of_colored_neighbor_counts (u : V) (v : W)
    (hcount : ∀ k, neighborCount G c u k = neighborCount H d v k) :
    G.degree u = H.degree v := by
  classical
  let e : G.neighborSet u ≃ H.neighborSet v :=
    Equiv.ofFiberEquiv (fun k => Fintype.equivOfCardEq (hcount k))
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using Fintype.card_congr e

theorem same_label_degree_eq
    (hsize : ∀ k, cellSize c k = cellSize d k)
    (hcount : ∀ u v, c u = d v → ∀ k, neighborCount G c u k = neighborCount H d v k)
    {u u' : V} (hu : c u = c u') : G.degree u = G.degree u' := by
  let v := colorEquiv c d hsize u
  have hv : d v = c u := colorEquiv_map c d hsize u
  exact (degree_eq_of_colored_neighbor_counts G H c d u v (hcount u v hv.symm)).trans
    (degree_eq_of_colored_neighbor_counts G H c d u' v (hcount u' v (hu.symm.trans hv.symm))).symm

/-- A degree-preserving bijection restricts to the actual non-leaf core. -/
def coreEquiv
    (hsize : ∀ k, cellSize c k = cellSize d k)
    (hcount : ∀ u v, c u = d v → ∀ k, neighborCount G c u k = neighborCount H d v k) :
    {u : V // G.degree u ≠ 1} ≃ {v : W // H.degree v ≠ 1} := by
  classical
  apply Equiv.subtypeEquiv (colorEquiv c d hsize)
  intro u
  have hdeg := degree_eq_of_colored_neighbor_counts G H c d u (colorEquiv c d hsize u)
    (hcount u _ (colorEquiv_map c d hsize u).symm)
  simp only [hdeg]

theorem coreEquiv_map
    (hsize : ∀ k, cellSize c k = cellSize d k)
    (hcount : ∀ u v, c u = d v → ∀ k, neighborCount G c u k = neighborCount H d v k)
    (u : {u : V // G.degree u ≠ 1}) :
    d (coreEquiv G H c d hsize hcount u) = c u := by
  exact colorEquiv_map c d hsize u

theorem core_cell_sizes_equal
    (hsize : ∀ k, cellSize c k = cellSize d k)
    (hcount : ∀ u v, c u = d v → ∀ k, neighborCount G c u k = neighborCount H d v k) (k : α) :
    cellSize (fun u : {u : V // G.degree u ≠ 1} => c u) k =
      cellSize (fun v : {v : W // H.degree v ≠ 1} => d v) k := by
  classical
  let e := coreEquiv G H c d hsize hcount
  have he : ∀ u, d (e u) = c u := coreEquiv_map G H c d hsize hcount
  exact Fintype.card_congr (Equiv.subtypeEquiv e (fun u => by
    change c u = k ↔ d (e u) = k
    rw [he u]))

section InducedFibers

variable (P : V → Prop) [DecidablePred P]

/-- If a whole color cell survives, deleting other cells does not change its
neighbor count at a surviving vertex. This is an actual subtype equivalence. -/
def induced_neighbor_fiber_equiv (u : {v // P v}) (k : α)
    (hcell : ∀ v, c v = k → P v) :
    {v : (G.induce {v | P v}).neighborSet u // c v = k} ≃
      {v : G.neighborSet (u : V) // c v = k} where
  toFun v := ⟨⟨v.val.val, v.val.property⟩, v.property⟩
  invFun v := ⟨⟨⟨v.val.val, hcell v.val.val v.property⟩, v.val.property⟩, v.property⟩
  left_inv v := by ext; rfl
  right_inv v := by ext; rfl

theorem surviving_color_neighbor_count (u : {v // P v}) (k : α)
    (hcell : ∀ v, c v = k → P v) :
    neighborCount (G.induce {v | P v}) (fun v => c v) u k = neighborCount G c u k := by
  classical
  exact Fintype.card_congr (induced_neighbor_fiber_equiv G c P u k hcell)

theorem deleted_color_neighbor_count (u : {v // P v}) (k : α)
    (hcell : ∀ v, c v = k → ¬ P v) :
    neighborCount (G.induce {v | P v}) (fun v => c v) u k = 0 := by
  classical
  let : IsEmpty {v : (G.induce {v | P v}).neighborSet u // c v = k} :=
    ⟨fun v => hcell v.val.val.val v.property v.val.val.property⟩
  exact Fintype.card_eq_zero

end InducedFibers

theorem core_neighbor_counts_equal
    (hsize : ∀ k, cellSize c k = cellSize d k)
    (hcount : ∀ u v, c u = d v → ∀ k, neighborCount G c u k = neighborCount H d v k)
    (u : {u : V // G.degree u ≠ 1}) (v : {v : W // H.degree v ≠ 1})
    (huv : c u = d v) (k : α) :
    neighborCount (G.induce {u | G.degree u ≠ 1}) (fun u => c u) u k =
      neighborCount (H.induce {v | H.degree v ≠ 1}) (fun v => d v) v k := by
  classical
  by_cases hk : ∃ a, c a = k ∧ G.degree a ≠ 1
  · obtain ⟨a, hak, ha⟩ := hk
    have hGcell : ∀ b, c b = k → G.degree b ≠ 1 := by
      intro b hb
      rw [same_label_degree_eq G H c d hsize hcount (hb.trans hak.symm)]
      exact ha
    have hHcell : ∀ b, d b = k → H.degree b ≠ 1 := by
      intro b hb
      have hdeg := degree_eq_of_colored_neighbor_counts G H c d a b
        (hcount a b (hak.trans hb.symm))
      rwa [← hdeg]
    rw [surviving_color_neighbor_count G c _ u k hGcell,
      surviving_color_neighbor_count H d _ v k hHcell]
    exact hcount u v huv k
  · have hGcell : ∀ b, c b = k → ¬ (G.degree b ≠ 1) := by
      intro b hb hn
      exact hk ⟨b, hb, hn⟩
    have hHcell : ∀ b, d b = k → ¬ (H.degree b ≠ 1) := by
      intro b hb hn
      obtain ⟨a, ha⟩ := (colorEquiv c d hsize).surjective b
      have hac : c a = k := (colorEquiv_map c d hsize a).symm.trans (by rw [ha, hb])
      have hdeg := degree_eq_of_colored_neighbor_counts G H c d a b
        (hcount a b (hac.trans hb.symm))
      exact hk ⟨a, hac, by rwa [hdeg]⟩
    rw [deleted_color_neighbor_count G c _ u k hGcell,
      deleted_color_neighbor_count H d _ v k hHcell]

/-- The terminal K₁/K₂ cases are actual graph isomorphisms, not codes. -/
theorem small_connected_adj_iff_ne (hconn : G.Connected) (hcard : Fintype.card V ≤ 2)
    (u v : V) : G.Adj u v ↔ u ≠ v := by
  classical
  constructor
  · exact fun h => h.ne
  · intro huv
    have hpos := (hconn u v).degree_pos_left huv
    obtain ⟨w, huw⟩ := (G.degree_pos_iff_exists_adj u).mp hpos
    by_contra hnon
    have hwv : w ≠ v := fun h => hnon (h ▸ huw)
    have hthree : ({u, v, w} : Finset V).card = 3 := by
      simp [huv, huw.ne, Ne.symm hwv]
    have hle : ({u, v, w} : Finset V).card ≤ Fintype.card V := Finset.card_le_univ _
    omega

theorem small_colored_tree_iso (hG : G.IsTree) (hH : H.IsTree)
    (hsize : ∀ k, cellSize c k = cellSize d k) (hcard : Fintype.card V ≤ 2) :
    ∃ f : G ≃g H, ∀ u, d (f u) = c u := by
  classical
  let e := colorEquiv c d hsize
  have hcardH : Fintype.card W ≤ 2 := by
    rw [← Fintype.card_congr e]
    exact hcard
  let f : G ≃g H := {
    toEquiv := e
    map_rel_iff' := by
      intro u v
      rw [small_connected_adj_iff_ne H hH.connected hcardH,
        small_connected_adj_iff_ne G hG.connected hcard, e.injective.ne_iff] }
  exact ⟨f, colorEquiv_map c d hsize⟩

#print axioms degree_eq_of_colored_neighbor_counts
#print axioms core_cell_sizes_equal
#print axioms core_neighbor_counts_equal
#print axioms small_colored_tree_iso

end
end PrincipalMomentAudit.TreeReconstruction
