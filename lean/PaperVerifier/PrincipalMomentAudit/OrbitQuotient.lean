import Mathlib
import PaperVerifier.PrincipalMomentAudit.GraphSemantics

/-!
Actual automorphism orbits of a finite simple graph and their weighted quotient.
The partition is defined using genuine graph isomorphisms, not supplied as an
equitable partition or inferred from a matrix. Quotient entries count actual
neighbors in an actual orbit. The inner-product formulas are the formulas
used in public arXiv:2607.21494v1, Lemma 5.3.
-/

namespace PrincipalMomentAudit.OrbitQuotient
noncomputable section
open Matrix
open scoped InnerProductSpace

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def orbitSetoid : Setoid V where
  r u v := ∃ e : G ≃g G, e u = v
  iseqv := {
    refl := fun u => ⟨SimpleGraph.Iso.refl, rfl⟩
    symm := by
      rintro u v ⟨e, rfl⟩
      exact ⟨e.symm, by simp⟩
    trans := by
      rintro u v w ⟨e, he⟩ ⟨f, hf⟩
      exact ⟨e.trans f, by simpa using (congrArg f he).trans hf⟩ }

abbrev Orbit := Quotient (orbitSetoid G)
def classOf (v : V) : Orbit G := Quotient.mk (orbitSetoid G) v

instance : Fintype (Orbit G) := by classical exact Quotient.fintype _
instance : DecidableEq (Orbit G) := Classical.decEq _

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem classOf_eq_iff (u v : V) :
    classOf G u = classOf G v ↔ ∃ e : G ≃g G, e u = v :=
  Quotient.eq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem classOf_aut (e : G ≃g G) (v : V) : classOf G (e v) = classOf G v := by
  apply Quotient.sound
  exact ⟨e.symm, by simp⟩

def orbitVertices (i : Orbit G) : Finset V := Finset.univ.filter (fun v => classOf G v = i)
def orbitNeighbors (u : V) (j : Orbit G) : Finset V :=
  Finset.univ.filter (fun v => G.Adj u v ∧ classOf G v = j)

omit [DecidableEq V] in
theorem orbitNeighbors_aut_card (e : G ≃g G) (u : V) (j : Orbit G) :
    (orbitNeighbors G (e u) j).card = (orbitNeighbors G u j).card := by
  symm
  apply Finset.card_bij (fun v _ => e v)
  · intro v hv
    simp only [orbitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨e.map_adj_iff.mpr hv.1, (classOf_aut G e v).trans hv.2⟩
  · intro a ha b hb hab
    exact e.injective hab
  · intro v hv
    refine ⟨e.symm v, ?_, by simp⟩
    simp only [orbitNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    constructor
    · simpa using e.symm.map_adj_iff.mpr hv.1
    · exact (classOf_aut G e.symm v).trans hv.2

omit [DecidableEq V] in
theorem orbitNeighbors_card_eq_of_same_orbit {u v : V}
    (huv : classOf G u = classOf G v) (j : Orbit G) :
    (orbitNeighbors G u j).card = (orbitNeighbors G v j).card := by
  obtain ⟨e, rfl⟩ := (classOf_eq_iff G u v).mp huv
  exact (orbitNeighbors_aut_card G e u j).symm

def quotientEntry (i j : Orbit G) : ℕ := (orbitNeighbors G i.out j).card
def orbitSize (i : Orbit G) : ℕ := (orbitVertices G i).card

omit [DecidableEq V] in
theorem quotientEntry_at_vertex (u : V) (j : Orbit G) :
    quotientEntry G (classOf G u) j = (orbitNeighbors G u j).card := by
  apply orbitNeighbors_card_eq_of_same_orbit
  exact Quotient.out_eq _

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem orbitSize_pos (i : Orbit G) : 0 < orbitSize G i := by
  apply Finset.card_pos.mpr
  refine ⟨i.out, ?_⟩
  simp only [orbitVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Quotient.out_eq i

def indicator (i : Orbit G) : EuclideanSpace ℝ V :=
  WithLp.toLp 2 (fun v => if classOf G v = i then (1 : ℝ) else 0)

theorem adjacency_indicator_apply (i : Orbit G) (u : V) :
    (GraphSemantics.generators G false (indicator G i)) u =
      ((orbitNeighbors G u i).card : ℝ) := by
  change (G.adjMatrix ℝ *ᵥ (fun v => if classOf G v = i then 1 else 0)) u = _
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hset : (G.neighborFinset u).filter (fun v => classOf G v = i) =
      orbitNeighbors G u i := by
    ext v
    simp [orbitNeighbors, SimpleGraph.mem_neighborFinset]
  rw [← hset]
  simp

omit [DecidableEq V] [DecidableRel G.Adj] in
theorem indicator_norm_square (i : Orbit G) :
    ⟪indicator G i, indicator G i⟫_ℝ = (orbitSize G i : ℝ) := by
  rw [PiLp.inner_apply]
  simp [indicator, orbitSize, orbitVertices]

theorem adjacency_gram (i j : Orbit G) :
    ⟪indicator G i, GraphSemantics.generators G false (indicator G j)⟫_ℝ =
      (orbitSize G i : ℝ) * (quotientEntry G i j : ℝ) := by
  rw [PiLp.inner_apply]
  have hterm (u : V) :
      inner ℝ ((indicator G i) u)
        ((GraphSemantics.generators G false (indicator G j)) u) =
      if classOf G u = i then (quotientEntry G i j : ℝ) else 0 := by
    rw [adjacency_indicator_apply]
    by_cases hu : classOf G u = i
    · have hq := quotientEntry_at_vertex G u j
      rw [hu] at hq
      simp [indicator, hu, hq]
    · simp [indicator, hu]
  simp_rw [hterm]
  simp [orbitSize, orbitVertices, ← Finset.sum_filter]

/-- The paper's b_ij=q_ij/s_i, with positivity proved from actual orbit nonemptiness. -/
theorem quotient_recovery (i j : Orbit G) :
    ⟪indicator G i, GraphSemantics.generators G false (indicator G j)⟫_ℝ /
      ⟪indicator G i, indicator G i⟫_ℝ = (quotientEntry G i j : ℝ) := by
  rw [adjacency_gram, indicator_norm_square]
  have hs : (orbitSize G i : ℝ) ≠ 0 := by exact_mod_cast (orbitSize_pos G i).ne'
  exact mul_div_cancel_left₀ _ hs

theorem edge_balance (i j : Orbit G) :
    (orbitSize G i : ℝ) * (quotientEntry G i j : ℝ) =
      (orbitSize G j : ℝ) * (quotientEntry G j i : ℝ) := by
  rw [← adjacency_gram, ← adjacency_gram]
  rw [← (GraphSemantics.generators_symmetric G false) (indicator G i) (indicator G j)]
  exact real_inner_comm _ _

/-- The actual orbit-constant subspace U_G of the paper. -/
def orbitConstantModule : Submodule ℝ (EuclideanSpace ℝ V) where
  carrier := {x | ∀ u v, classOf G u = classOf G v → x u = x v}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy u v huv
    change x u + y u = x v + y v
    rw [hx u v huv, hy u v huv]
  smul_mem' := by
    intro r x hx u v huv
    change r * x u = r * x v
    rw [hx u v huv]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem one_mem_orbitConstantModule :
    GraphSemantics.oneSeed (V := V) ∈ orbitConstantModule G := by
  intro u v huv
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem indicator_mem_orbitConstantModule (i : Orbit G) :
    indicator G i ∈ orbitConstantModule G := by
  intro u v huv
  simp [indicator, huv]

theorem orbitConstantModule_invariant (b : Bool) (x : EuclideanSpace ℝ V)
    (hx : x ∈ orbitConstantModule G) :
    GraphSemantics.generators G b x ∈ orbitConstantModule G := by
  intro u v huv
  obtain ⟨e, rfl⟩ := (classOf_eq_iff G u v).mp huv
  cases b
  · change (G.adjMatrix ℝ *ᵥ (WithLp.ofLp x)) u =
      (G.adjMatrix ℝ *ᵥ (WithLp.ofLp x)) (e u)
    rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.adjMatrix_mulVec_apply]
    apply Finset.sum_bij (fun a _ => e a)
    · intro a ha
      simpa only [SimpleGraph.mem_neighborFinset] using
        e.map_adj_iff.mpr ((SimpleGraph.mem_neighborFinset G _ _).mp ha)
    · intro a ha b hb hab
      exact e.injective hab
    · intro a ha
      refine ⟨e.symm a, ?_, by simp⟩
      apply (SimpleGraph.mem_neighborFinset G _ _).mpr
      simpa using e.symm.map_adj_iff.mpr ((SimpleGraph.mem_neighborFinset G _ _).mp ha)
    · intro a ha
      exact hx a (e a) (classOf_aut G e a).symm
  · change (G.degMatrix ℝ *ᵥ (WithLp.ofLp x)) u =
      (G.degMatrix ℝ *ᵥ (WithLp.ofLp x)) (e u)
    rw [SimpleGraph.degMatrix_mulVec_apply, SimpleGraph.degMatrix_mulVec_apply,
      e.degree_eq, hx u (e u) (classOf_aut G e u).symm]

/-- M_G ⊆ U_G for every finite graph; the reverse inclusion requires the forest proof. -/
theorem principal_le_orbitConstantModule :
    principal (GraphSemantics.generators G) (GraphSemantics.oneSeed (V := V)) ≤
      orbitConstantModule G := by
  rw [principal_eq_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact one_mem_orbitConstantModule G
  | cons b w ih => exact orbitConstantModule_invariant G b _ ih

#print axioms orbitNeighbors_card_eq_of_same_orbit
#print axioms quotient_recovery
#print axioms principal_le_orbitConstantModule

end
end PrincipalMomentAudit.OrbitQuotient
