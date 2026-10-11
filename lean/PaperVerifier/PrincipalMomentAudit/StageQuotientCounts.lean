import PaperVerifier.PrincipalMomentAudit.PeeledOrbitGeometry
import PaperVerifier.PrincipalMomentAudit.OrbitRepresentation
import PaperVerifier.PrincipalMomentAudit.Quotient

/-!
The actual current adjacency quotient on the fixed original automorphism
orbits. Guarded peeled orbit rows have a unique parent and entry one there.
The reverse product's single support and its positive integer weight are
derived from genuine vertex adjacency and pointed automorphism lifting.
-/

namespace PrincipalMomentAudit.StageQuotientCounts

noncomputable section
open Matrix Finset SimpleGraph
open PrincipalMomentAudit.ForestPruning PrincipalMomentAudit.SelectorEvaluation
open PrincipalMomentAudit.OrbitQuotient PrincipalMomentAudit.SharedVectorFamily
open PrincipalMomentAudit.PeeledOrbitGeometry PrincipalMomentAudit.OrbitRepresentation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def currentNeighbors (t : ℕ) (u : V) (j : Orbit G) : Finset V :=
  Finset.univ.filter (fun v => (mask G (stageActive G t)).Adj u v ∧ classOf G v = j)

def currentCounts (t : ℕ) : Matrix (Orbit G) (Orbit G) ℕ :=
  fun i j => (currentNeighbors G t i.out j).card

def typedOrbits (t : ℕ) (r : StageType (Fintype.card V) t) : Finset (Orbit G) :=
  Finset.univ.filter (fun i => i.out ∈ peeledCell G (stageActive G t) (stageLabel G t) r)

def activeOrbits (t : ℕ) : Finset (Orbit G) :=
  Finset.univ.filter (fun i => i.out ∈ stageActive G t)

theorem current_adj_aut_iff (t : ℕ) (a : G ≃g G) (u v : V) :
    (mask G (stageActive G t)).Adj (a u) (a v) ↔
      (mask G (stageActive G t)).Adj u v := by
  change (a u ∈ stageActive G t ∧ a v ∈ stageActive G t ∧ G.Adj (a u) (a v)) ↔ _
  rw [← stage_active_orbit_invariant G t u (a u) (classOf_aut G a u).symm,
    ← stage_active_orbit_invariant G t v (a v) (classOf_aut G a v).symm,
    a.map_adj_iff]
  rfl

theorem currentNeighbors_aut_card (t : ℕ) (a : G ≃g G) (u : V) (j : Orbit G) :
    (currentNeighbors G t (a u) j).card = (currentNeighbors G t u j).card := by
  symm
  apply Finset.card_bij (fun v _ => a v)
  · intro v hv
    simp only [currentNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨(current_adj_aut_iff G t a u v).mpr hv.1,
      (classOf_aut G a v).trans hv.2⟩
  · intro u hu v hv h; exact a.injective h
  · intro v hv
    refine ⟨a.symm v, ?_, by simp⟩
    simp only [currentNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    refine ⟨?_, (classOf_aut G a.symm v).trans hv.2⟩
    have h := (current_adj_aut_iff G t a.symm (a u) v).mpr hv.1
    simpa using h

theorem currentCounts_at_vertex (t : ℕ) (u : V) (j : Orbit G) :
    currentCounts G t (classOf G u) j = (currentNeighbors G t u j).card := by
  obtain ⟨a, ha⟩ := (classOf_eq_iff G (classOf G u).out u).mp (Quotient.out_eq _)
  change (currentNeighbors G t (classOf G u).out j).card = _
  have h := currentNeighbors_aut_card G t a (classOf G u).out j
  rw [ha] at h
  exact h.symm

theorem currentCounts_pos_iff (t : ℕ) (i j : Orbit G) :
    0 < currentCounts G t i j ↔
      ∃ v, (mask G (stageActive G t)).Adj i.out v ∧ classOf G v = j := by
  rw [currentCounts, Finset.card_pos]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨v, (Finset.mem_filter.mp hv).2⟩
  · rintro ⟨v, hv⟩
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩

theorem currentCounts_reverse_pos (t : ℕ) (i j : Orbit G)
    (h : 0 < currentCounts G t i j) : 0 < currentCounts G t j i := by
  obtain ⟨v, hv, hclass⟩ := (currentCounts_pos_iff G t i j).mp h
  obtain ⟨a, ha⟩ := (classOf_eq_iff G j.out v).mp ((Quotient.out_eq j).trans hclass.symm)
  apply (currentCounts_pos_iff G t j i).mpr
  refine ⟨a.symm i.out, ?_, (classOf_aut G a.symm i.out).trans (Quotient.out_eq i)⟩
  have he := (current_adj_aut_iff G t a.symm v i.out).mpr hv.symm
  rw [← ha, a.symm_apply_apply] at he
  exact he

theorem currentCounts_reverse_zero (t : ℕ) (i j : Orbit G)
    (h : currentCounts G t i j = 0) : currentCounts G t j i = 0 := by
  by_contra hn
  have hp : 0 < currentCounts G t j i := Nat.pos_of_ne_zero hn
  have hi := currentCounts_reverse_pos G t j i hp
  omega

theorem count_bound (t : ℕ) (i j : Orbit G) : currentCounts G t i j ≤ Fintype.card V :=
  (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)

def parentVertex (t : ℕ) (i : Orbit G) : V :=
  if h : (mask G (stageActive G t)).degree i.out = 1 then
    Classical.choose (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp h)
  else i.out

def parentOrbit (t : ℕ) (i : Orbit G) : Orbit G := classOf G (parentVertex G t i)

theorem parentVertex_spec (t : ℕ) (i : Orbit G)
    (hi : (mask G (stageActive G t)).degree i.out = 1) :
    (mask G (stageActive G t)).Adj i.out (parentVertex G t i) ∧
      ∀ v, (mask G (stageActive G t)).Adj i.out v → v = parentVertex G t i := by
  unfold parentVertex
  rw [dif_pos hi]
  exact Classical.choose_spec (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hi)

theorem selected_degree (t : ℕ) (r : StageType (Fintype.card V) t)
    (i : Orbit G) (hi : i ∈ typedOrbits G t r) :
    (mask G (stageActive G t)).degree i.out = 1 := by
  have hp := Finset.mem_filter.mp hi
  exact peelable_degree _ ((mem_typeCell _ _ _ _).mp hp.2).1

theorem selected_row (t : ℕ) (r : StageType (Fintype.card V) t)
    (i : Orbit G) (hi : i ∈ typedOrbits G t r) (j : Orbit G) :
    currentCounts G t i j = if j = parentOrbit G t i then 1 else 0 := by
  have hs := parentVertex_spec G t i (selected_degree G t r i hi)
  have he : currentNeighbors G t i.out j =
      if j = parentOrbit G t i then {parentVertex G t i} else ∅ := by
    ext v
    simp only [currentNeighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j = parentOrbit G t i
    · simp only [hj, ite_true, Finset.mem_singleton]
      exact ⟨fun h => hs.2 v h.1, fun h => h ▸ ⟨hs.1, rfl⟩⟩
    · simp only [hj, ite_false, Finset.notMem_empty]
      refine ⟨?_, False.elim⟩
      intro hv
      have hvp := hs.2 v hv.1
      exact hj (hv.2.symm.trans (congrArg (classOf G) hvp))
  rw [currentCounts, he]
  split <;> simp

theorem selected_sumcounts (t : ℕ) (r : StageType (Fintype.card V) t)
    (i : Orbit G) (hi : i ∈ typedOrbits G t r) : ∑ j, currentCounts G t i j = 1 := by
  simp_rw [selected_row G t r i hi]
  simp

theorem selected_parent_positive (t : ℕ) (r : StageType (Fintype.card V) t)
    (i : Orbit G) (hi : i ∈ typedOrbits G t r) :
    0 < currentCounts G t i (parentOrbit G t i) := by
  rw [selected_row G t r i hi]
  simp

theorem parent_active_next (t : ℕ) (r : StageType (Fintype.card V) t)
    (i : Orbit G) (hi : i ∈ typedOrbits G t r) :
    (parentOrbit G t i).out ∈ stageActive G (t + 1) := by
  have hpeel := ((mem_typeCell _ _ _ _).mp (Finset.mem_filter.mp hi).2).1
  have hs := (parentVertex_spec G t i (selected_degree G t r i hi)).1
  have hp : parentVertex G t i ∈ stageActive G (t + 1) :=
    Finset.mem_sdiff.mpr ⟨hs.2.1, peelable_neighbor_not_mem _ hpeel hs⟩
  exact (stage_active_orbit_invariant G (t + 1) (parentVertex G t i)
    (parentOrbit G t i).out (Quotient.out_eq _).symm).mp hp

theorem parent_fibre_unique (t : ℕ) (r : StageType (Fintype.card V) t)
    (i : Orbit G) (hi : i ∈ typedOrbits G t r)
    (j : Orbit G) (hj : j ∈ typedOrbits G t r)
    (hparent : parentOrbit G t i = parentOrbit G t j) : i = j := by
  have h := peeled_same_type_parent_class G t r i.out j.out
    (parentVertex G t i) (parentVertex G t j)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    (parentVertex_spec G t i (selected_degree G t r i hi)).1
    (parentVertex_spec G t j (selected_degree G t r j hj)).1 hparent
  exact (Quotient.out_eq i).symm.trans (h.trans (Quotient.out_eq j))

theorem reverse_coordinate (t : ℕ) (r : StageType (Fintype.card V) t)
    (c : Orbit G) (hc : c ∈ typedOrbits G t r) :
    PrincipalMomentAudit.Quotient.positiveSelector (Fintype.card V)
      (PrincipalMomentAudit.Quotient.reverseProduct (fun i j => (currentCounts G t i j : ℝ))
        (typedOrbits G t r) (parentOrbit G t c)) = PrincipalMomentAudit.Quotient.coordinate c := by
  let B : Matrix (Orbit G) (Orbit G) ℝ := fun i j => currentCounts G t i j
  have hrow : ∀ i ∈ typedOrbits G t r, ∀ j, j ≠ parentOrbit G t i → B i j = 0 := by
    intro i hi j hj
    simp [B, selected_row G t r i hi, hj]
  have hz : ∀ i j, B i j = 0 → B j i = 0 := by
    intro i j hij
    change (currentCounts G t i j : ℝ) = 0 at hij
    have h : currentCounts G t i j = 0 := by exact_mod_cast hij
    have h' := currentCounts_reverse_zero G t i j h
    simp [B, h']
  have hcol := PrincipalMomentAudit.Quotient.column_parent_support_of_undirected
    B (typedOrbits G t r) (parentOrbit G t) hrow hz
  have hone : currentCounts G t c (parentOrbit G t c) = 1 := by
    simp [selected_row G t r c hc]
  have hpos := currentCounts_reverse_pos G t c (parentOrbit G t c)
    (selected_parent_positive G t r c hc)
  apply PrincipalMomentAudit.Quotient.extract_unique_child B (typedOrbits G t r) (parentOrbit G t)
    (parentOrbit G t c) c (Fintype.card V) (currentCounts G t (parentOrbit G t c) c)
    hrow hcol (parent_fibre_unique G t r) hc rfl
  · simp [B, hone]
  · exact count_bound G t _ _
  · exact hpos

theorem selected_row_zero (t : ℕ) (r : StageType (Fintype.card V) t)
    (i : Orbit G) (hi : i ∈ typedOrbits G t r) (j : Orbit G)
    (hj : j ≠ parentOrbit G t i) : (currentCounts G t i j : ℝ) = 0 := by
  simp [selected_row G t r i hi, hj]

theorem selected_column_zero (t : ℕ) (r : StageType (Fintype.card V) t)
    (i : Orbit G) (hi : i ∈ typedOrbits G t r) (j : Orbit G)
    (hj : j ≠ parentOrbit G t i) : (currentCounts G t j i : ℝ) = 0 := by
  have hz : currentCounts G t i j = 0 := by simp [selected_row G t r i hi, hj]
  simp [currentCounts_reverse_zero G t i j hz]

theorem backward_count_positive (t : ℕ) (r : StageType (Fintype.card V) t)
    (c : Orbit G) (hc : c ∈ typedOrbits G t r) (p : Orbit G)
    (hpc : parentOrbit G t c = p) : 0 < currentCounts G t p c := by
  rw [← hpc]
  exact currentCounts_reverse_pos G t c _ (selected_parent_positive G t r c hc)

theorem reverse_product_value (t : ℕ) (r : StageType (Fintype.card V) t)
    (p c : Orbit G) (hc : c ∈ typedOrbits G t r) (hpc : parentOrbit G t c = p) :
    PrincipalMomentAudit.Quotient.reverseProduct (fun i j => (currentCounts G t i j : ℝ))
      (typedOrbits G t r) p =
      (currentCounts G t p c : ℝ) • PrincipalMomentAudit.Quotient.coordinate c := by
  rw [PrincipalMomentAudit.Quotient.reverseProduct_eq_coordinate
    (fun i j => (currentCounts G t i j : ℝ)) (typedOrbits G t r) (parentOrbit G t) p c
    (selected_row_zero G t r) (selected_column_zero G t r) (parent_fibre_unique G t r) hc hpc]
  have hone : currentCounts G t c p = 1 := by simp [selected_row G t r c hc, hpc]
  simp [hone]

theorem reverse_product_empty (t : ℕ) (r : StageType (Fintype.card V) t)
    (p : Orbit G) (hempty : ∀ i ∈ typedOrbits G t r, parentOrbit G t i ≠ p) :
    PrincipalMomentAudit.Quotient.reverseProduct (fun i j => (currentCounts G t i j : ℝ))
      (typedOrbits G t r) p = 0 :=
  PrincipalMomentAudit.Quotient.reverseProduct_empty _ _ _ _
    (selected_row_zero G t r) (selected_column_zero G t r) hempty

/-- Every literal quotient matrix entry is the actual vertex-space operator
applied to an original orbit indicator, evaluated at an actual representative. -/
theorem quotient_eval_entry (p : PrincipalMomentAudit.Transport.Expression) (i j : Orbit G) :
    matrixEval (adjacencyQuotient G) (degreeQuotient G) p i j =
      (matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p *ᵥ
        (fun v => (Pi.single j (1 : ℝ) : Orbit G → ℝ) (classOf G v))) i.out := by
  have h := congrArg (fun x : EuclideanSpace ℝ V => x i.out)
    (matrixEval_quotient_compatibility G p (Pi.single j 1))
  change ((matrixEval (adjacencyQuotient G) (degreeQuotient G) p) *ᵥ
    Pi.single j 1) (classOf G i.out) = _ at h
  rw [show classOf G i.out = i from Quotient.out_eq i, Matrix.mulVec_single_one] at h
  exact h

theorem current_adjacency_matrixEval (t : ℕ) :
    matrixEval (adjacencyQuotient G) (degreeQuotient G)
      (literalState (Fintype.card V) t).adjacency =
        (fun i j => (currentCounts G t i j : ℝ)) := by
  ext i j
  rw [quotient_eval_entry, (all_stages_realizes G t).adjacency,
    SimpleGraph.adjMatrix_mulVec_apply]
  have hf : ((mask G (stageActive G t)).neighborFinset i.out).filter
      (fun v => classOf G v = j) = currentNeighbors G t i.out j := by
    ext v
    simp [currentNeighbors, SimpleGraph.mem_neighborFinset]
  have hpi : (fun v => (Pi.single j (1 : ℝ) : Orbit G → ℝ) (classOf G v)) =
      (fun v => if classOf G v = j then (1 : ℝ) else 0) := by
    funext v
    simp [Pi.single_apply, eq_comm]
  rw [hpi]
  have hsum : (∑ v ∈ (mask G (stageActive G t)).neighborFinset i.out,
      if classOf G v = j then (1 : ℝ) else 0) =
      ((((mask G (stageActive G t)).neighborFinset i.out).filter
        (fun v => classOf G v = j)).card : ℝ) := by simp
  rw [hsum, hf]
  rfl

theorem selector_quotient_matrixEval (p : PrincipalMomentAudit.Transport.Expression) (W : Finset V)
    (hp : matrixEval (G.adjMatrix ℝ) (G.degMatrix ℝ) p = PrincipalMomentAudit.vertexSelector W) :
    matrixEval (adjacencyQuotient G) (degreeQuotient G) p =
      PrincipalMomentAudit.Quotient.selectedDiagonal (Finset.univ.filter (fun i : Orbit G => i.out ∈ W)) := by
  ext i j
  rw [quotient_eval_entry, hp, PrincipalMomentAudit.vertexSelector, Matrix.mulVec_diagonal]
  have hout : classOf G i.out = i := Quotient.out_eq i
  by_cases hij : i = j
  · subst j
    simp [PrincipalMomentAudit.Quotient.selectedDiagonal, hout]
  · simp [PrincipalMomentAudit.Quotient.selectedDiagonal, hout, hij]

theorem typed_selector_matrixEval (t : ℕ) (r : StageType (Fintype.card V) t) :
    matrixEval (adjacencyQuotient G) (degreeQuotient G)
      ((literalState (Fintype.card V) t).peeledType (Fintype.card V) r) =
      PrincipalMomentAudit.Quotient.selectedDiagonal (typedOrbits G t r) := by
  exact selector_quotient_matrixEval G _ _
    (peeledType_matrixEval _ _ _ G _ _ (all_stages_realizes G t) r)

theorem active_selector_matrixEval (t : ℕ) :
    matrixEval (adjacencyQuotient G) (degreeQuotient G)
      (literalState (Fintype.card V) t).active =
      PrincipalMomentAudit.Quotient.selectedDiagonal (activeOrbits G t) := by
  exact selector_quotient_matrixEval G _ _
    (active_matrixEval _ _ _ G _ _ (all_stages_realizes G t))

#print axioms currentCounts_at_vertex
#print axioms currentCounts_reverse_zero
#print axioms selected_row
#print axioms parent_fibre_unique
#print axioms parent_active_next
#print axioms reverse_coordinate
#print axioms reverse_product_value
#print axioms reverse_product_empty
#print axioms current_adjacency_matrixEval
#print axioms typed_selector_matrixEval

end
end PrincipalMomentAudit.StageQuotientCounts
