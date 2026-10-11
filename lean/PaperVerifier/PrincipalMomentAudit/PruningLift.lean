import PaperVerifier.PrincipalMomentAudit.LeafGrafting
import PaperVerifier.PrincipalMomentAudit.ForestPruning

/-!
The constructive one-step completeness of the paper's lower-type refinement.
The retained graph is the actual induced complement of guarded leaves. If
its core isomorphism preserves old labels and all typed peeled-neighbour
counts, it lifts to an old-label preserving isomorphism of the actual graphs.
No branch-type completeness or global graph isomorphism is assumed.
-/

namespace PrincipalMomentAudit.PruningLift

noncomputable section

open SimpleGraph PrincipalMomentAudit.ForestPruning PrincipalMomentAudit.LeafGrafting

variable {V W K : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

def Retained (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Prop :=
  v ∉ peelable G

/-- Actual count of peeled children having the specified old lower type. -/
def peeledCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (label : V → K) (k : K) (v : V) : ℕ :=
  Nat.card {l : V // l ∈ peelable G ∧ G.Adj v l ∧ label l = k}

/-- The refinement used in the paper, with unbounded natural count values
for its combinatorial interpretation. Literal AD expressions use the same
values embedded into Fin(N+1), justified by the order bound. -/
def refinedLabel (G : SimpleGraph V) [DecidableRel G.Adj]
    (label : V → K) (v : V) : K × (K → ℕ) :=
  (label v, fun k => peeledCount G label k v)

omit [DecidableEq V] in
theorem peeled_unique_parent (l : V) (hl : ¬ Retained G l) :
    ∃! u : {v // Retained G v}, G.Adj u l := by
  classical
  have hleaf : l ∈ peelable G := by simpa only [Retained, not_not] using hl
  obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp (peelable_degree G hleaf)
  have hcore : Retained G u := peelable_neighbor_not_mem G hleaf hu
  refine ⟨⟨u, hcore⟩, hu.symm, ?_⟩
  intro v hv
  exact Subtype.ext (huniq v hv.symm)

omit [DecidableEq V] in
theorem peeled_no_adj (l m : V) (hl : ¬ Retained G l) (hm : ¬ Retained G m) :
    ¬ G.Adj l m := by
  classical
  have hleaf : l ∈ peelable G := by simpa only [Retained, not_not] using hl
  have hother : m ∈ peelable G := by simpa only [Retained, not_not] using hm
  exact fun h => peelable_neighbor_not_mem G hleaf h hother

omit [DecidableEq V] in
theorem childFiber_card (label : V → K) (u : {v // Retained G v}) (k : K) :
    Nat.card (ChildFiber G (Retained G) label u k) = peeledCount G label k u := by
  classical
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro l
  simp only [Retained, not_not]

omit [DecidableEq V] [DecidableEq W] in
/-- A genuine core isomorphism preserving the next refinement lifts through
this exact guarded pruning round. The whole isomorphism is constructed by
matching finite labelled child fibres and the core, not supplied as a premise. -/
theorem label_iso_lift (labelG : V → K) (labelH : W → K)
    (coreIso : G.induce {v | Retained G v} ≃g H.induce {w | Retained H w})
    (hprofile : ∀ u : {v // Retained G v},
      refinedLabel H labelH (coreIso u) = refinedLabel G labelG u) :
    ∃ wholeIso : G ≃g H,
      (∀ u : {v // Retained G v}, wholeIso u = (coreIso u : W)) ∧
      ∀ v, labelH (wholeIso v) = labelG v := by
  have hlabels : ∀ u : {v // Retained G v}, labelH (coreIso u) = labelG u :=
    fun u => congrArg Prod.fst (hprofile u)
  have hcounts : ∀ u : {v // Retained G v}, ∀ k : K,
      peeledCount G labelG k u = peeledCount H labelH k (coreIso u) := by
    intro u k
    exact (congrArg (fun z : K × (K → ℕ) => z.2 k) (hprofile u)).symm
  apply graft_colored_iso_of_card G H (Retained G) (Retained H) labelG labelH coreIso
  · intro u k
    rw [childFiber_card G, childFiber_card H]
    exact hcounts u k
  · exact peeled_unique_parent G
  · exact peeled_unique_parent H
  · exact peeled_no_adj G
  · exact peeled_no_adj H
  · exact hlabels

#print axioms peeled_unique_parent
#print axioms childFiber_card
#print axioms label_iso_lift

end

end PrincipalMomentAudit.PruningLift
