import PaperVerifier.PrincipalMomentAudit.OrbitQuotient
import PaperVerifier.PrincipalMomentAudit.TreeRigidity

/-!
arXiv:2607.21494v1, Theorem 5.1: the actual weighted automorphism-orbit
quotient determines a finite tree. Both graphs are actual SimpleGraph.IsTree.
The only comparison data are an orbit relabeling, equal actual cell sizes,
and equal actual neighbor counts. No reconstruction oracle is a hypothesis.
-/

namespace PrincipalMomentAudit.WeightedQuotientRigidity
noncomputable section
open PrincipalMomentAudit.OrbitQuotient PrincipalMomentAudit.TreeReconstruction

variable {V W α β : Type*} [Fintype V] [Fintype W]
variable [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem cellSize_orbit (i : Orbit G) : cellSize (classOf G) i = orbitSize G i := by
  classical
  simp [cellSize, orbitSize, orbitVertices, Fintype.card_subtype]

omit [DecidableEq V] in
theorem neighborCount_orbit (u : V) (i : Orbit G) :
    neighborCount G (classOf G) u i = (orbitNeighbors G u i).card := by
  classical
  let e : {x : G.neighborSet u // classOf G x = i} ≃
      {x : V // G.Adj u x ∧ classOf G x = i} := {
    toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
    invFun := fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩
    left_inv := by intro x; ext; rfl
    right_inv := by intro x; ext; rfl }
  rw [neighborCount, Fintype.card_congr e]
  simp [orbitNeighbors, Fintype.card_subtype]

omit [DecidableEq V] in
theorem cellSize_relabel (c : V → α) (e : α ≃ β) (i : α) :
    cellSize (fun v => e (c v)) (e i) = cellSize c i := by
  classical
  exact Fintype.card_congr (Equiv.subtypeEquiv (Equiv.refl V) (fun _ => e.injective.eq_iff))

omit [DecidableEq V] in
theorem neighborCount_relabel (c : V → α) (e : α ≃ β) (u : V) (i : α) :
    neighborCount G (fun v => e (c v)) u (e i) = neighborCount G c u i := by
  classical
  exact Fintype.card_congr
    (Equiv.subtypeEquiv (Equiv.refl (G.neighborSet u)) (fun _ => e.injective.eq_iff))

omit [DecidableEq V] [DecidableEq W] in
/-- Public arXiv:2607.21494v1 Theorem 5.1, with literal actual graph and quotient semantics. -/
theorem actual_weighted_orbit_quotient_determines_tree
    (hG : G.IsTree) (hH : H.IsTree) (e : Orbit G ≃ Orbit H)
    (hs : ∀ i, orbitSize G i = orbitSize H (e i))
    (hB : ∀ i j, quotientEntry G i j = quotientEntry H (e i) (e j)) :
    Nonempty (G ≃g H) := by
  classical
  let c := classOf G
  let d := fun v => e.symm (classOf H v)
  have hsize : ∀ i, cellSize c i = cellSize d i := by
    intro i
    change cellSize (classOf G) i = cellSize (fun v => e.symm (classOf H v)) i
    rw [cellSize_orbit, hs i]
    have hrel := cellSize_relabel (classOf H) e.symm (e i)
    simpa only [Equiv.symm_apply_apply, cellSize_orbit] using hrel.symm
  have hcount : ∀ u v, c u = d v → ∀ i,
      neighborCount G c u i = neighborCount H d v i := by
    intro u v huv i
    have he : e (classOf G u) = classOf H v := by
      exact e.symm.injective (by simpa only [Equiv.symm_apply_apply] using huv)
    change neighborCount G (classOf G) u i =
      neighborCount H (fun v => e.symm (classOf H v)) v i
    have hrel := neighborCount_relabel H (classOf H) e.symm v (e i)
    rw [neighborCount_orbit, ← quotientEntry_at_vertex, hB, he]
    simpa only [Equiv.symm_apply_apply, neighborCount_orbit, quotientEntry_at_vertex]
      using hrel.symm
  obtain ⟨f, _⟩ := colored_tree_rigidity G H c d hG hH hsize hcount
  exact ⟨f⟩

#print axioms actual_weighted_orbit_quotient_determines_tree
end
end PrincipalMomentAudit.WeightedQuotientRigidity
