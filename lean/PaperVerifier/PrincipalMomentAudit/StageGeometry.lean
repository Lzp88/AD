import PaperVerifier.PrincipalMomentAudit.ForestPruning

/-!
# Actual active-stage graphs

The ambient masked graph keeps earlier removed vertices isolated, as the
paper's matrices do. The combinatorial reconstruction instead uses the
genuine induced graph on the active subtype. This module proves the exact
bridge, so earlier inactive isolated vertices cannot enter a stage orbit.
-/

namespace PrincipalMomentAudit.StageGeometry

noncomputable section
open SimpleGraph PrincipalMomentAudit.ForestPruning

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The genuine active graph, whose vertex type contains exactly active vertices. -/
abbrev activeGraph (S : Finset V) : SimpleGraph (S : Set V) := G.induce (S : Set V)

/-- Degrees in the true active graph equal the degrees of the same vertices
in the full-vertex masked matrix graph. -/
theorem active_degree_eq_mask (S : Finset V) (u : (S : Set V)) :
    (activeGraph G S).degree u = (mask G S).degree u.val :=
  induce_degree_eq_mask_degree G S u

/-- Guarded peeling on the active subtype is exactly ambient guarded peeling
at its corresponding active vertex. -/
theorem mem_active_peelable_iff (S : Finset V) (u : (S : Set V)) :
    u ∈ peelable (activeGraph G S) ↔ u.val ∈ peelable (mask G S) := by
  classical
  rw [mem_peelable, mem_peelable]
  constructor
  · rintro ⟨hu, v, huv, hv⟩
    refine ⟨(active_degree_eq_mask G S u).symm.trans hu, v.val,
      ⟨u.property, v.property, huv⟩, ?_⟩
    exact fun h => hv ((active_degree_eq_mask G S v).trans h)
  · rintro ⟨hu, v, huv, hv⟩
    let vS : (S : Set V) := ⟨v, huv.2.1⟩
    refine ⟨(active_degree_eq_mask G S u).trans hu, vS, huv.2.2, ?_⟩
    exact fun h => hv ((active_degree_eq_mask G S vS).symm.trans h)

/-- Ambient peelable vertices really are active, so the bridge loses no vertices. -/
theorem ambient_peelable_is_active (S : Finset V) {u : V}
    (hu : u ∈ peelable (mask G S)) : u ∈ S :=
  peelable_subset_active G S hu

/-- A retained stage vertex is an active vertex which the active graph does not peel. -/
abbrev Retained (S : Finset V) :=
  {u : (S : Set V) // u ∉ peelable (activeGraph G S)}

/-- The genuine retained subtype equals the next actual active subtype as
an equivalence that preserves each ambient vertex. -/
def retainedEquiv (S : Finset V) : Retained G S ≃ (nextActive G S : Set V) where
  toFun u := ⟨u.val.val, Finset.mem_sdiff.mpr
    ⟨u.val.property, fun h => u.property ((mem_active_peelable_iff G S u.val).mpr h)⟩⟩
  invFun u := ⟨⟨u.val, (Finset.mem_sdiff.mp u.property).1⟩,
    fun h => (Finset.mem_sdiff.mp u.property).2
      ((mem_active_peelable_iff G S ⟨u.val, (Finset.mem_sdiff.mp u.property).1⟩).mp h)⟩
  left_inv _u := rfl
  right_inv _u := rfl

@[simp] theorem retainedEquiv_val (S : Finset V) (u : Retained G S) :
    (retainedEquiv G S u).val = u.val.val := rfl

@[simp] theorem retainedEquiv_symm_val (S : Finset V)
    (u : (nextActive G S : Set V)) :
    ((retainedEquiv G S).symm u).val.val = u.val := rfl

/-- Deleting the actual active peelable vertices yields precisely the next
actual active induced graph, with an actual graph isomorphism. -/
def retainedIso (S : Finset V) :
    (activeGraph G S).induce {u | u ∉ peelable (activeGraph G S)} ≃g
      activeGraph G (nextActive G S) where
  toEquiv := retainedEquiv G S
  map_rel_iff' := by
    intro u v
    rfl

@[simp] theorem retainedIso_val (S : Finset V) (u : Retained G S) :
    (retainedIso G S u).val = u.val.val := rfl

/-- Retained stage cardinality is the literal next active-set cardinality. -/
theorem retained_card (S : Finset V) :
    Fintype.card (Retained G S) = (nextActive G S).card := by
  rw [Fintype.card_congr (retainedEquiv G S)]
  simp

/-- The recursion can equivalently be read as one genuine stage after the
previous stage, which is convenient for reverse orbit induction. -/
theorem activeFrom_succ_right (S : Finset V) (n : ℕ) :
    activeFrom G S (n + 1) = nextActive G (activeFrom G S n) := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
      change activeFrom G (nextActive G S) (n + 1) =
        nextActive G (activeFrom G (nextActive G S) n)
      exact ih (nextActive G S)

#print axioms active_degree_eq_mask
#print axioms mem_active_peelable_iff
#print axioms retainedIso
#print axioms retained_card
#print axioms activeFrom_succ_right

end

end PrincipalMomentAudit.StageGeometry
