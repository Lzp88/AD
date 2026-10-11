import PaperVerifier.PrincipalMomentAudit.StageGeometry

/-! Exact actual-subtype versus ambient finite-filter child counts. -/

namespace PrincipalMomentAudit.StageCounts

noncomputable section
open PrincipalMomentAudit.ForestPruning PrincipalMomentAudit.StageGeometry

variable {V ρ : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (S : Finset V) (label : V → ρ)

local instance : DecidableEq ρ := Classical.decEq _

/-- Actual selected active leaf-neighbors and their ambient finite-filter
representatives have exactly the same underlying vertices. -/
def peeledNeighborEquiv (r : ρ) (u : (S : Set V)) :
    {l : (S : Set V) // l ∈ peelable (activeGraph G S) ∧
      (activeGraph G S).Adj u l ∧ label l.val = r} ≃
    {l : V // l ∈ ((peelable (mask G S)).filter (fun l => label l = r)).filter
      ((mask G S).Adj u.val)} where
  toFun l := ⟨l.val.val, Finset.mem_filter.mpr
    ⟨Finset.mem_filter.mpr
      ⟨(mem_active_peelable_iff G S l.val).mp l.property.1, l.property.2.2⟩,
      ⟨u.property, l.val.property, l.property.2.1⟩⟩⟩
  invFun l :=
    let hp := Finset.mem_filter.mp (Finset.mem_filter.mp l.property).1
    let hadj := (Finset.mem_filter.mp l.property).2
    ⟨⟨l.val, hadj.2.1⟩,
      ⟨(mem_active_peelable_iff G S ⟨l.val, hadj.2.1⟩).mpr hp.1, hadj.2.2, hp.2⟩⟩
  left_inv _l := rfl
  right_inv _l := rfl

/-- The actual stage's finite child-fibre cardinality is exactly the
ambient masked graph's selected-neighbor diagonal entry. -/
theorem actual_peeled_neighbor_count (r : ρ) (u : (S : Set V)) :
    Nat.card {l : (S : Set V) // l ∈ peelable (activeGraph G S) ∧
      (activeGraph G S).Adj u l ∧ label l.val = r} =
      removedNeighbors (mask G S)
        ((peelable (mask G S)).filter (fun l => label l = r)) u.val := by
  classical
  rw [Nat.card_congr (peeledNeighborEquiv G S label r u), Nat.card_eq_fintype_card,
    removedNeighbors_eq_filter]
  exact Fintype.card_of_subtype _ (fun _ => Iff.rfl)

#print axioms actual_peeled_neighbor_count

end

end PrincipalMomentAudit.StageCounts
