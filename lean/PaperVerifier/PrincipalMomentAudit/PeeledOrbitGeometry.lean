import PaperVerifier.PrincipalMomentAudit.StageOrbitLifting
import PaperVerifier.PrincipalMomentAudit.SharedVectorFamily

/-!
Actual original-orbit classification for the reverse typed child step.
An original automorphism taking one retained parent to another restricts to
a refined next-stage automorphism. A pointed leaf graft prescribes the child
image, and chronological stage lifting returns an actual original graph
automorphism. No original child orbit or branch completeness is assumed.
-/

namespace PrincipalMomentAudit.PeeledOrbitGeometry

noncomputable section

open SimpleGraph PrincipalMomentAudit.ForestPruning PrincipalMomentAudit.SelectorEvaluation
open PrincipalMomentAudit.OrbitQuotient PrincipalMomentAudit.SharedVectorFamily
open PrincipalMomentAudit.StageGeometry PrincipalMomentAudit.StageOrbitLifting
open PrincipalMomentAudit.PruningLift PrincipalMomentAudit.PruningOrbits PrincipalMomentAudit.TerminalOrbits

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Literal active-type indicators show that current labels are invariant
under original automorphisms at all active vertices. -/
theorem stage_label_orbit_invariant (t : ℕ) (u v : V)
    (hu : u ∈ stageActive G t) (hclass : classOf G u = classOf G v) :
    stageLabel G t u = stageLabel G t v := by
  let r := stageLabel G t u
  let W := typeCell (stageActive G t) (stageLabel G t) r
  have hm := PrincipalMomentAudit.PrincipalExpressions.literal_selector_indicator_mem G
    ((literalState (Fintype.card V) t).typeSelector r) W
    ((all_stages_realizes G t).typeSelector r)
  have he := principal_le_orbitConstantModule G hm u v hclass
  have huW : u ∈ W := by simp [W, r, hu]
  change (if u ∈ W then (1 : ℝ) else 0) = (if v ∈ W then 1 else 0) at he
  have hvW : v ∈ W := by
    by_contra hn
    simp [huW, hn] at he
  exact ((mem_typeCell _ _ _ _).mp hvW).2.symm

/-- Restriction of a genuine original automorphism to the actual active
subtype. There are no inactive isolated vertices in its vertex type. -/
def originalStageAut (t : ℕ) (α : G ≃g G) : stageGraph G t ≃g stageGraph G t where
  toEquiv :=
    { toFun := fun u => ⟨α u.val, (stage_active_orbit_invariant G t u.val (α u.val)
        (classOf_aut G α u.val).symm).mp u.property⟩
      invFun := fun u => ⟨α.symm u.val, (stage_active_orbit_invariant G t u.val (α.symm u.val)
        (classOf_aut G α.symm u.val).symm).mp u.property⟩
      left_inv := by intro u; apply Subtype.ext; exact α.symm_apply_apply u.val
      right_inv := by intro u; apply Subtype.ext; exact α.apply_symm_apply u.val }
  map_rel_iff' := by intro u v; exact α.map_adj_iff

theorem originalStageAut_color (t : ℕ) (α : G ≃g G) (u : StageVertices G t) :
    stageColor G t (originalStageAut G t α u) = stageColor G t u :=
  (stage_label_orbit_invariant G t u.val (α u.val) u.property (classOf_aut G α u.val).symm).symm

/-- The exact reverse-classification implication required by Lemmas 3.2 and
4.3: selected peeled children of the same actual stage type, with parents
in one original automorphism orbit, are in one original automorphism orbit. -/
theorem peeled_same_type_parent_class (t : ℕ) (r : StageType (Fintype.card V) t)
    (l m p q : V)
    (hl : l ∈ peeledCell G (stageActive G t) (stageLabel G t) r)
    (hm : m ∈ peeledCell G (stageActive G t) (stageLabel G t) r)
    (hlp : (mask G (stageActive G t)).Adj l p)
    (hmq : (mask G (stageActive G t)).Adj m q)
    (hparent : classOf G p = classOf G q) : classOf G l = classOf G m := by
  have hlparts := (mem_typeCell _ _ _ _).mp hl
  have hmparts := (mem_typeCell _ _ _ _).mp hm
  have hlactive := ambient_peelable_is_active G (stageActive G t) hlparts.1
  have hmactive := ambient_peelable_is_active G (stageActive G t) hmparts.1
  have hpnext : p ∈ stageActive G (t + 1) :=
    Finset.mem_sdiff.mpr ⟨hlp.2.1, peelable_neighbor_not_mem _ hlparts.1 hlp⟩
  have hqnext : q ∈ stageActive G (t + 1) :=
    Finset.mem_sdiff.mpr ⟨hmq.2.1, peelable_neighbor_not_mem _ hmparts.1 hmq⟩
  obtain ⟨α, hαp⟩ := (classOf_eq_iff G p q).mp hparent
  let a := originalStageAut G (t + 1) α
  let e := stageRetainedIso G t
  let coreAut := e.trans (a.trans e.symm)
  have hprofile : ∀ u : {u : StageVertices G t // PruningLift.Retained (stageGraph G t) u},
      refinedLabel (stageGraph G t) (stageColor G t) (coreAut u) =
        refinedLabel (stageGraph G t) (stageColor G t) u := by
    intro u
    rw [stage_profile, stage_profile]
    have he : (coreAut u).val.val = (a (e u)).val := rfl
    have heu : (e u).val = u.val.val := rfl
    rw [he, ← heu]
    exact congrArg (fun z : StageType (Fintype.card V) (t + 1) =>
      (z.1, fun s => (z.2 s).val)) (originalStageAut_color G (t + 1) α (e u))
  let lS : StageVertices G t := ⟨l, hlactive⟩
  let mS : StageVertices G t := ⟨m, hmactive⟩
  let pNext : StageVertices G (t + 1) := ⟨p, hpnext⟩
  let u := e.symm pNext
  have hlret : ¬ PruningLift.Retained (stageGraph G t) lS := by
    intro hn
    exact hn ((mem_active_peelable_iff G _ lS).mpr hlparts.1)
  have hmret : ¬ PruningLift.Retained (stageGraph G t) mS := by
    intro hn
    exact hn ((mem_active_peelable_iff G _ mS).mpr hmparts.1)
  have hul : (stageGraph G t).Adj u.val lS := hlp.2.2.symm
  have hum : (stageGraph G t).Adj (coreAut u).val mS := by
    change G.Adj (coreAut u).val.val m
    have hq : (coreAut u).val.val = q := by
      change α p = q
      exact hαp
    rw [hq]
    exact hmq.2.2.symm
  have hleafcolor : stageColor G t lS = stageColor G t mS :=
    hlparts.2.trans hmparts.2.symm
  obtain ⟨b, hbpoint, hbcolors⟩ := peeled_pair_core_aut_orbit
    (stageGraph G t) (stageColor G t) coreAut hprofile u lS mS hlret hmret hul hum hleafcolor
  obtain ⟨β, hβ⟩ := stage_aut_lifts G t b hbcolors
  apply (classOf_eq_iff G l m).mpr
  exact ⟨β, (hβ lS).trans (congrArg Subtype.val hbpoint)⟩

#print axioms stage_label_orbit_invariant
#print axioms originalStageAut_color
#print axioms peeled_same_type_parent_class

end

end PrincipalMomentAudit.PeeledOrbitGeometry
