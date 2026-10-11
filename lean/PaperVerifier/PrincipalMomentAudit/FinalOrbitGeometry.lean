import PaperVerifier.PrincipalMomentAudit.SharedVectorFamily
import PaperVerifier.PrincipalMomentAudit.StageOrbitLifting
import PaperVerifier.PrincipalMomentAudit.PeeledOrbitGeometry
import PaperVerifier.PrincipalMomentAudit.SharedFamilyMomentRigidity

/-!
# Actual original-orbit classification of the literal seed and child sets

The finite sets in `ActualOrbitGeometry` are proved to be genuine original
automorphism orbits. Terminal coloured automorphisms are constructed on the
true active induced graph and then lifted chronologically to the original
graph. No orbit classification or selector existence is supplied as a paper
hypothesis.
-/

namespace PrincipalMomentAudit.FinalOrbitGeometry

open Matrix Finset SimpleGraph PrincipalMomentAudit.Transport PrincipalMomentAudit.SelectorEvaluation
open PrincipalMomentAudit.ForestPruning PrincipalMomentAudit.OrbitQuotient PrincipalMomentAudit.SharedVectorFamily
open PrincipalMomentAudit.StageGeometry PrincipalMomentAudit.StageOrbitLifting PrincipalMomentAudit.TerminalOrbits

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem literal_set_orbit_invariant (p : Expression) (W : Finset V)
    (hp : matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = PrincipalMomentAudit.vertexSelector W)
    (u v : V) (huv : classOf G u = classOf G v) : u ∈ W ↔ v ∈ W := by
  have hm := PrincipalMomentAudit.PrincipalExpressions.literal_selector_indicator_mem G p W hp
  have hc := principal_le_orbitConstantModule G hm
  have he := hc u v huv
  change (if u ∈ W then (1 : ℝ) else 0) = (if v ∈ W then (1 : ℝ) else 0) at he
  by_cases hu : u ∈ W <;> by_cases hv : v ∈ W <;> simp_all

omit [DecidableRel G.Adj] in
theorem invariant_transitive_set (W : Finset V)
    (hinv : ∀ u v, classOf G u = classOf G v → u ∈ W → v ∈ W)
    (htrans : ∀ u ∈ W, ∀ v ∈ W, classOf G u = classOf G v) :
    W = ∅ ∨ ∃ i : Orbit G, W = orbitVertices G i := by
  classical
  by_cases hz : W = ∅
  · exact Or.inl hz
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    right
    refine ⟨classOf G v, ?_⟩
    ext u
    simp only [orbitVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hu => (htrans v hv u hu).symm, fun hu => hinv v u hu.symm hv⟩

theorem terminal_vertex_transitive (r : StageType (Fintype.card V) (Fintype.card V))
    (v w : V)
    (hv : v ∈ typeCell (centerVertexSet (mask G (stageActive G (Fintype.card V)))
      (stageActive G (Fintype.card V))) (stageLabel G (Fintype.card V)) r)
    (hw : w ∈ typeCell (centerVertexSet (mask G (stageActive G (Fintype.card V)))
      (stageActive G (Fintype.card V))) (stageLabel G (Fintype.card V)) r) :
    classOf G v = classOf G w := by
  classical
  obtain ⟨hvset, hvl⟩ := (mem_typeCell _ _ _ _).mp hv
  obtain ⟨hwset, hwl⟩ := (mem_typeCell _ _ _ _).mp hw
  obtain ⟨hvactive, hvdeg⟩ := Finset.mem_filter.mp hvset
  obtain ⟨hwactive, hwdeg⟩ := Finset.mem_filter.mp hwset
  let vS : StageVertices G (Fintype.card V) := ⟨v, hvactive⟩
  let wS : StageVertices G (Fintype.card V) := ⟨w, hwactive⟩
  have hvd : (stageGraph G (Fintype.card V)).degree vS = 0 :=
    (active_degree_eq_mask G _ vS).trans hvdeg
  have hwd : (stageGraph G (Fintype.card V)).degree wS = 0 :=
    (active_degree_eq_mask G _ wS).trans hwdeg
  obtain ⟨a, ha, hcolor⟩ := isolated_same_label_orbit (stageGraph G (Fintype.card V))
    (stageColor G (Fintype.card V)) hvd hwd (hvl.trans hwl.symm)
  obtain ⟨α, hα⟩ := stage_aut_lifts G (Fintype.card V) a hcolor
  exact (classOf_eq_iff G v w).mpr ⟨α, (hα vS).trans (congrArg Subtype.val ha)⟩

theorem terminal_edge_transitive (r q : StageType (Fintype.card V) (Fintype.card V))
    (v w : V)
    (hv : v ∈ centerEdgeTypeSet (mask G (stageActive G (Fintype.card V)))
      (stageActive G (Fintype.card V)) (stageLabel G (Fintype.card V)) r q)
    (hw : w ∈ centerEdgeTypeSet (mask G (stageActive G (Fintype.card V)))
      (stageActive G (Fintype.card V)) (stageLabel G (Fintype.card V)) r q) :
    classOf G v = classOf G w := by
  classical
  obtain ⟨hvtype, hvcenter, u, hvu, hutype, hucenter⟩ := (mem_centerEdgeTypeSet _ _ _ _ _ _).mp hv
  obtain ⟨hwtype, hwcenter, z, hwz, hztype, hzcenter⟩ := (mem_centerEdgeTypeSet _ _ _ _ _ _).mp hw
  obtain ⟨hvactive, hvl⟩ := (mem_typeCell _ _ _ _).mp hvtype
  obtain ⟨huactive, hul⟩ := (mem_typeCell _ _ _ _).mp hutype
  obtain ⟨hwactive, hwl⟩ := (mem_typeCell _ _ _ _).mp hwtype
  obtain ⟨hzactive, hzl⟩ := (mem_typeCell _ _ _ _).mp hztype
  let vS : StageVertices G (Fintype.card V) := ⟨v, hvactive⟩
  let uS : StageVertices G (Fintype.card V) := ⟨u, huactive⟩
  let wS : StageVertices G (Fintype.card V) := ⟨w, hwactive⟩
  let zS : StageVertices G (Fintype.card V) := ⟨z, hzactive⟩
  have hdegree (x : StageVertices G (Fintype.card V))
      (hx : x.val ∈ centerEdgeSet (mask G (stageActive G (Fintype.card V)))) :
      (stageGraph G (Fintype.card V)).degree x = 1 :=
    (active_degree_eq_mask G _ x).trans ((mem_leafSet _ _).mp (Finset.mem_filter.mp hx).1)
  obtain ⟨a, ha, hcolor⟩ := leaf_pair_same_labels_orbit (stageGraph G (Fintype.card V))
    (stageColor G (Fintype.card V)) (hdegree vS hvcenter) (hdegree uS hucenter)
    (hdegree wS hwcenter) (hdegree zS hzcenter) hvu.2.2 hwz.2.2
    (hvl.trans hwl.symm) (hul.trans hzl.symm)
  obtain ⟨α, hα⟩ := stage_aut_lifts G (Fintype.card V) a hcolor
  exact (classOf_eq_iff G v w).mpr ⟨α, (hα vS).trans (congrArg Subtype.val ha)⟩

theorem terminal_vertex_classification (r : StageType (Fintype.card V) (Fintype.card V)) :
    typeCell (centerVertexSet (mask G (stageActive G (Fintype.card V)))
      (stageActive G (Fintype.card V))) (stageLabel G (Fintype.card V)) r = ∅ ∨
    ∃ i : Orbit G, typeCell (centerVertexSet (mask G (stageActive G (Fintype.card V)))
      (stageActive G (Fintype.card V))) (stageLabel G (Fintype.card V)) r = orbitVertices G i := by
  apply invariant_transitive_set
  · intro u v huv hu
    exact (literal_set_orbit_invariant G _ _
      (centerVertexType_matrixEval _ _ _ G _ _ (all_stages_realizes G _) r) u v huv).mp hu
  · intro u hu v hv
    exact terminal_vertex_transitive G r u v hu hv

theorem terminal_edge_classification (r q : StageType (Fintype.card V) (Fintype.card V)) :
    centerEdgeTypeSet (mask G (stageActive G (Fintype.card V)))
      (stageActive G (Fintype.card V)) (stageLabel G (Fintype.card V)) r q = ∅ ∨
    ∃ i : Orbit G, centerEdgeTypeSet (mask G (stageActive G (Fintype.card V)))
      (stageActive G (Fintype.card V)) (stageLabel G (Fintype.card V)) r q = orbitVertices G i := by
  apply invariant_transitive_set
  · intro u v huv hu
    exact (literal_set_orbit_invariant G _ _
      (centerEdgeType_matrixEval _ _ _ G _ _ (all_stages_realizes G _) r q) u v huv).mp hu
  · intro u hu v hv
    exact terminal_edge_transitive G r q u v hu hv

theorem child_fiber_invariant (t : ℕ) (r : StageType (Fintype.card V) t) (i : Orbit G)
    (u v : V) (huv : classOf G u = classOf G v) :
    u ∈ childFiber G (mask G (stageActive G t)) (peeledCell G (stageActive G t) (stageLabel G t) r) i ↔
    v ∈ childFiber G (mask G (stageActive G t)) (peeledCell G (stageActive G t) (stageLabel G t) r) i := by
  classical
  have hmap : ∀ a b, classOf G a = classOf G b →
      a ∈ childFiber G (mask G (stageActive G t)) (peeledCell G (stageActive G t) (stageLabel G t) r) i →
      b ∈ childFiber G (mask G (stageActive G t)) (peeledCell G (stageActive G t) (stageLabel G t) r) i := by
    intro a b hab ha
    obtain ⟨hW, x, hax, hx⟩ := Finset.mem_filter.mp ha
    obtain ⟨α, hα⟩ := (classOf_eq_iff G a b).mp hab
    apply Finset.mem_filter.mpr
    refine ⟨(literal_set_orbit_invariant G _ _
      (peeledType_matrixEval _ _ _ G _ _ (all_stages_realizes G t) r) a b hab).mp hW, α x, ?_, ?_⟩
    · refine ⟨(stage_active_orbit_invariant G t a b hab).mp hax.1, ?_, ?_⟩
      · exact (stage_active_orbit_invariant G t x (α x) (classOf_aut G α x).symm).mp hax.2.1
      · have he := α.map_adj_iff.mpr hax.2.2
        simpa only [hα] using he
    · exact (classOf_aut G α x).trans hx
  exact ⟨hmap u v huv, hmap v u huv.symm⟩

theorem child_fiber_transitive (t : ℕ) (r : StageType (Fintype.card V) t) (i : Orbit G)
    (l m : V)
    (hl : l ∈ childFiber G (mask G (stageActive G t))
      (peeledCell G (stageActive G t) (stageLabel G t) r) i)
    (hm : m ∈ childFiber G (mask G (stageActive G t))
      (peeledCell G (stageActive G t) (stageLabel G t) r) i) : classOf G l = classOf G m := by
  obtain ⟨hlW, p, hlp, hp⟩ := Finset.mem_filter.mp hl
  obtain ⟨hmW, q, hmq, hq⟩ := Finset.mem_filter.mp hm
  exact PrincipalMomentAudit.PeeledOrbitGeometry.peeled_same_type_parent_class G t r l m p q
    hlW hmW hlp hmq (hp.trans hq.symm)

theorem child_fiber_classification (t : ℕ) (r : StageType (Fintype.card V) t) (i : Orbit G) :
    childFiber G (mask G (stageActive G t)) (peeledCell G (stageActive G t) (stageLabel G t) r) i = ∅ ∨
    ∃ j : Orbit G, childFiber G (mask G (stageActive G t))
      (peeledCell G (stageActive G t) (stageLabel G t) r) i = orbitVertices G j := by
  apply invariant_transitive_set
  · intro u v huv hu
    exact (child_fiber_invariant G t r i u v huv).mp hu
  · intro u hu v hv
    exact child_fiber_transitive G t r i u v hu hv

/-- The three set classifications are proved for the actual original graph.
This discharges every field of the family lemma's geometry input. -/
theorem actual_orbit_geometry : ActualOrbitGeometry G := by
  constructor
  · exact terminal_vertex_classification G
  · exact terminal_edge_classification G
  · intro t _ r i _
    exact child_fiber_classification G t r i

/-- No classification or recovery premise remains for a genuine finite forest. -/
theorem forest_family_sound (hForest : G.IsAcyclic) :
    PrincipalMomentAudit.SharedFamilyMomentRigidity.FamilySound G (vectorFamily (Fintype.card V)) := by
  exact vector_family_sound_expression G hForest (actual_orbit_geometry G)

theorem forest_family_covers (hForest : G.IsAcyclic) :
    PrincipalMomentAudit.SharedFamilyMomentRigidity.FamilyCovers G (vectorFamily (Fintype.card V)) := by
  exact vector_family_cover_expression G hForest (actual_orbit_geometry G)

#print axioms terminal_vertex_classification
#print axioms terminal_edge_classification
#print axioms child_fiber_invariant
#print axioms actual_orbit_geometry
#print axioms forest_family_sound
#print axioms forest_family_covers

end

end PrincipalMomentAudit.FinalOrbitGeometry
