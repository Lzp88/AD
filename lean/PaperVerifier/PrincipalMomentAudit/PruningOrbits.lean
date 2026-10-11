import PaperVerifier.PrincipalMomentAudit.PruningLift
import PaperVerifier.PrincipalMomentAudit.TerminalOrbits
import PaperVerifier.PrincipalMomentAudit.PointedGrafting

/-!
Constructive coloured orbit propagation through one real guarded peeling
round. The hypotheses name an actual automorphism of the refined retained
graph; they do not assume an original whole-graph orbit classification.
The pointed leaf graft extends that automorphism and prescribes the desired
same-type child image.
-/

namespace PrincipalMomentAudit.PruningOrbits

noncomputable section

open SimpleGraph PrincipalMomentAudit.PruningLift PrincipalMomentAudit.LeafGrafting
open PrincipalMomentAudit.PointedGrafting PrincipalMomentAudit.TerminalOrbits

variable {V K : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → K)

omit [DecidableEq V] in
/-- An actual refined-core automorphism lifts to the preceding labelled graph. -/
theorem core_aut_lift
    (coreAut : G.induce {v | Retained G v} ≃g G.induce {v | Retained G v})
    (hprofile : ∀ u : {v // Retained G v},
      refinedLabel G label (coreAut u) = refinedLabel G label u) :
    ∃ wholeAut : G ≃g G,
      (∀ u : {v // Retained G v}, wholeAut u = (coreAut u : V)) ∧
      ∀ v, label (wholeAut v) = label v :=
  label_iso_lift G G label label coreAut hprofile

omit [DecidableEq V] in
/-- Same old leaf label and the same refined core-parent orbit suffice for
one actual coloured leaf orbit. The automorphism is constructed by adjusting
an actual finite child-fibre equivalence at the designated leaf. -/
theorem peeled_pair_core_aut_orbit
    (coreAut : G.induce {v | Retained G v} ≃g G.induce {v | Retained G v})
    (hprofile : ∀ u : {v // Retained G v},
      refinedLabel G label (coreAut u) = refinedLabel G label u)
    (u : {v // Retained G v}) (l m : V)
    (hl : ¬ Retained G l) (hm : ¬ Retained G m)
    (hul : G.Adj u l) (hum : G.Adj (coreAut u) m)
    (hlabel : label l = label m) : ColoredOrbit G label l m := by
  classical
  have hlabels : ∀ a : {v // Retained G v}, label (coreAut a) = label a :=
    fun a => congrArg Prod.fst (hprofile a)
  have hcard : ∀ a k,
      Nat.card (ChildFiber G (Retained G) label a k) =
        Nat.card (ChildFiber G (Retained G) label (coreAut a) k) := by
    intro a k
    rw [childFiber_card G, childFiber_card G]
    exact (congrArg (fun z : K × (K → ℕ) => z.2 k) (hprofile a)).symm
  let x : ChildFiber G (Retained G) label u (label l) := ⟨l, hl, hul, rfl⟩
  let y : ChildFiber G (Retained G) label (coreAut u) (label l) := ⟨m, hm, hum, hlabel.symm⟩
  obtain ⟨wholeAut, _, hwholeLabels, hwholePoint⟩ :=
    graft_colored_iso_givenleaf G G (Retained G) (Retained G) label label coreAut
      (peeled_unique_parent G) (peeled_unique_parent G) (peeled_no_adj G) (peeled_no_adj G)
      hlabels (fun a k => by simpa only [← Nat.card_eq_fintype_card] using hcard a k)
      u (label l) x y
  exact ⟨wholeAut, hwholePoint, hwholeLabels⟩

#print axioms core_aut_lift
#print axioms peeled_pair_core_aut_orbit

end

end PrincipalMomentAudit.PruningOrbits
