import PaperVerifier.PrincipalMomentAudit.PruningOrbits
import PaperVerifier.PrincipalMomentAudit.StageCounts
import PaperVerifier.PrincipalMomentAudit.SelectorEvaluation

/-!
Actual coloured automorphisms of an induced active graph lift through every
previous guarded peeling round to actual automorphisms of the original
graph. Earlier inactive isolated vertices are excluded from every stage.
The refinement profile is proved equal to the literal algorithm's next
stage label, using actual typed neighbour counts.
-/

namespace PrincipalMomentAudit.StageOrbitLifting

noncomputable section

open SimpleGraph PrincipalMomentAudit.ForestPruning PrincipalMomentAudit.SelectorEvaluation
open PrincipalMomentAudit.StageGeometry PrincipalMomentAudit.PruningLift PrincipalMomentAudit.PruningOrbits

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev StageVertices (t : ℕ) := (stageActive G t : Set V)
abbrev stageGraph (t : ℕ) : SimpleGraph (StageVertices G t) :=
  activeGraph G (stageActive G t)

def stageColor (t : ℕ) (u : StageVertices G t) : StageType (Fintype.card V) t :=
  stageLabel G t u.val

def stageRetainedIso (t : ℕ) :
    (stageGraph G t).induce {u | PruningLift.Retained (stageGraph G t) u} ≃g
      stageGraph G (t + 1) :=
  retainedIso G (stageActive G t)

/-- Exact equality between actual induced-stage refinement and the shared
literal next label after forgetting the Fin(N+1) bound on its counts. -/
theorem stage_profile (t : ℕ) (u : StageVertices G t) :
    refinedLabel (stageGraph G t) (stageColor G t) u =
      ((stageLabel G (t + 1) u.val).1,
        fun r => ((stageLabel G (t + 1) u.val).2 r).val) := by
  apply Prod.ext
  · rfl
  · funext r
    have h := PrincipalMomentAudit.StageCounts.actual_peeled_neighbor_count G (stageActive G t)
      (stageLabel G t) r u
    change peeledCount (stageGraph G t) (stageColor G t) r u =
      childCount G (stageActive G t) (stageLabel G t) r u.val
    change Nat.card {l : (stageActive G t : Set V) //
      l ∈ peelable (activeGraph G (stageActive G t)) ∧
      (activeGraph G (stageActive G t)).Adj u l ∧ stageLabel G t l.val = r} = _
    rw [h]
    rfl

/-- One true induced active-stage automorphism lifts to the preceding true
active stage, preserving its actual old labels and all retained images. -/
theorem previous_stage_aut (t : ℕ)
    (a : stageGraph G (t + 1) ≃g stageGraph G (t + 1))
    (hcolor : ∀ u : StageVertices G (t + 1),
      stageColor G (t + 1) (a u) = stageColor G (t + 1) u) :
    ∃ b : stageGraph G t ≃g stageGraph G t,
      (∀ u : {u : StageVertices G t // PruningLift.Retained (stageGraph G t) u},
        b u.val = ((stageRetainedIso G t).symm (a (stageRetainedIso G t u))).val) ∧
      ∀ u, stageColor G t (b u) = stageColor G t u := by
  let e := stageRetainedIso G t
  let coreAut := e.trans (a.trans e.symm)
  have hprofile : ∀ u : {u : StageVertices G t // PruningLift.Retained (stageGraph G t) u},
      refinedLabel (stageGraph G t) (stageColor G t) (coreAut u) =
        refinedLabel (stageGraph G t) (stageColor G t) u := by
    intro u
    rw [stage_profile, stage_profile]
    have he : ((coreAut u).val.val) = (a (e u)).val := rfl
    have heu : (e u).val = u.val.val := rfl
    rw [he, ← heu]
    have hc := hcolor (e u)
    exact congrArg (fun z : StageType (Fintype.card V) (t + 1) =>
      (z.1, fun r => (z.2 r).val)) hc
  exact core_aut_lift (stageGraph G t) (stageColor G t) coreAut hprofile

def stageZeroIso : stageGraph G 0 ≃g G where
  toEquiv :=
    { toFun := fun u => u.val
      invFun := fun u => ⟨u, Finset.mem_univ u⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  map_rel_iff' := by intro u v; rfl

/-- Every coloured active-stage automorphism is the restriction of an actual
original graph automorphism. This closes the chronological lifting bridge. -/
theorem stage_aut_lifts (t : ℕ) (a : stageGraph G t ≃g stageGraph G t)
    (hcolor : ∀ u : StageVertices G t, stageColor G t (a u) = stageColor G t u) :
    ∃ α : G ≃g G, ∀ u : StageVertices G t, α u.val = (a u).val := by
  induction t with
  | zero =>
    let e := stageZeroIso G
    let α := e.symm.trans (a.trans e)
    exact ⟨α, fun _ => rfl⟩
  | succ t ih =>
    obtain ⟨b, hretained, hbcolor⟩ := previous_stage_aut G t a hcolor
    obtain ⟨α, hα⟩ := ih b hbcolor
    refine ⟨α, ?_⟩
    intro u
    let v := (stageRetainedIso G t).symm u
    have hv : v.val.val = u.val := rfl
    rw [← hv, hα v.val, hretained v]
    rfl

#print axioms stage_profile
#print axioms previous_stage_aut
#print axioms stage_aut_lifts

end

end PrincipalMomentAudit.StageOrbitLifting
