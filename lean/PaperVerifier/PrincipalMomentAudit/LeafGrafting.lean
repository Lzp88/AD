import Mathlib

/-!
Grafting actual labelled leaves onto an actual core graph isomorphism.
The input geometry is exactly the leaf partition: every outside vertex has
a unique adjacent core parent, and outside vertices have no mutual edges.
The theorem constructs the whole graph isomorphism from actual child-fibre
equivalences. It assumes neither a whole graph isomorphism nor a recursive
tree rigidity assertion. IsTree implies the needed peeling geometry in the
separate ForestPruning development.
-/

namespace PrincipalMomentAudit.LeafGrafting

open SimpleGraph

variable {V W K : Type*}

abbrev ChildFiber (G : SimpleGraph V) (Core : V → Prop) (label : V → K)
    (u : {v // Core v}) (k : K) :=
  {l : V // ¬ Core l ∧ G.Adj u l ∧ label l = k}

abbrev Location (G : SimpleGraph V) (Core : V → Prop) (label : V → K) :=
  {v // Core v} ⊕ (Σ u : {v // Core v}, Σ k : K, ChildFiber G Core label u k)

def locationValue (G : SimpleGraph V) (Core : V → Prop) (label : V → K) :
    Location G Core label → V
  | .inl u => u
  | .inr ⟨_, _, l⟩ => l

theorem locationValue_bijective (G : SimpleGraph V) (Core : V → Prop) (label : V → K)
    (hparent : ∀ l, ¬ Core l → ∃! u : {v // Core v}, G.Adj u l) :
    Function.Bijective (locationValue G Core label) := by
  constructor
  · rintro (u | ⟨u, k, l⟩) (v | ⟨v, j, m⟩) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · change (u : V) = (m : V) at h
      exact (m.property.1 (h ▸ u.property)).elim
    · change (l : V) = (v : V) at h
      exact (l.property.1 (h.symm ▸ v.property)).elim
    · change (l : V) = (m : V) at h
      have huv : u = v := (hparent l l.property.1).unique l.property.2.1
        (h.symm ▸ m.property.2.1)
      have hkj : k = j := l.property.2.2.symm.trans (h.symm ▸ m.property.2.2)
      subst v
      subst j
      have hlm : l = m := Subtype.ext h
      subst m
      rfl
  · intro l
    classical
    by_cases hl : Core l
    · exact ⟨.inl ⟨l, hl⟩, rfl⟩
    · obtain ⟨u, hu, _⟩ := hparent l hl
      exact ⟨.inr ⟨u, label l, ⟨l, hl, hu, rfl⟩⟩, rfl⟩

noncomputable def locationEquiv (G : SimpleGraph V) (Core : V → Prop) (label : V → K)
    (hparent : ∀ l, ¬ Core l → ∃! u : {v // Core v}, G.Adj u l) :
    Location G Core label ≃ V :=
  Equiv.ofBijective (locationValue G Core label) (locationValue_bijective G Core label hparent)

/-- The parent of an actual child fibre is recovered from adjacency, not
from a separate coordinate oracle. -/
theorem core_child_adj_iff (G : SimpleGraph V) (Core : V → Prop) (label : V → K)
    (hparent : ∀ l, ¬ Core l → ∃! u : {v // Core v}, G.Adj u l)
    (u v : {v // Core v}) (k : K) (l : ChildFiber G Core label v k) :
    G.Adj u l ↔ u = v := by
  constructor
  · intro h
    exact (hparent l l.property.1).unique h l.property.2.1
  · rintro rfl
    exact l.property.2.1

section TwoGraphs

variable (G : SimpleGraph V) (H : SimpleGraph W)
variable (CoreG : V → Prop) (CoreH : W → Prop)
variable (labelG : V → K) (labelH : W → K)
variable (coreIso : G.induce {v | CoreG v} ≃g H.induce {w | CoreH w})
variable (fibers : ∀ u : {v // CoreG v}, ∀ k : K,
  ChildFiber G CoreG labelG u k ≃ ChildFiber H CoreH labelH (coreIso u) k)

/-- Exact matching of core vertices and of labelled leaf fibres. -/
def locationMatch : Location G CoreG labelG ≃ Location H CoreH labelH :=
  Equiv.sumCongr coreIso.toEquiv
    (Equiv.sigmaCongr coreIso.toEquiv (fun u =>
      Equiv.sigmaCongrRight (fibers u)))

theorem locationMatch_label
    (hCoreLabel : ∀ u : {v // CoreG v}, labelH (coreIso u) = labelG u)
    (x : Location G CoreG labelG) :
    labelH (locationValue H CoreH labelH (locationMatch G H CoreG CoreH labelG labelH coreIso fibers x)) =
      labelG (locationValue G CoreG labelG x) := by
  rcases x with u | ⟨u, k, l⟩
  · exact hCoreLabel u
  · exact (fibers u k l).property.2.2.trans l.property.2.2.symm

/-- The actual adjacency check for the matching permutation. The only
outside-edge hypotheses are unique core parent and absence of leaf-leaf edges. -/
theorem locationMatch_adj
    (hparentG : ∀ l, ¬ CoreG l → ∃! u : {v // CoreG v}, G.Adj u l)
    (hparentH : ∀ l, ¬ CoreH l → ∃! u : {w // CoreH w}, H.Adj u l)
    (hleavesG : ∀ l m, ¬ CoreG l → ¬ CoreG m → ¬ G.Adj l m)
    (hleavesH : ∀ l m, ¬ CoreH l → ¬ CoreH m → ¬ H.Adj l m)
    (x y : Location G CoreG labelG) :
    H.Adj
      (locationValue H CoreH labelH (locationMatch G H CoreG CoreH labelG labelH coreIso fibers x))
      (locationValue H CoreH labelH (locationMatch G H CoreG CoreH labelG labelH coreIso fibers y)) ↔
    G.Adj (locationValue G CoreG labelG x) (locationValue G CoreG labelG y) := by
  rcases x with u | ⟨u, k, l⟩ <;> rcases y with v | ⟨v, j, m⟩
  · exact coreIso.map_adj_iff
  · change H.Adj (coreIso u) (fibers v j m) ↔ G.Adj u m
    rw [core_child_adj_iff H CoreH labelH hparentH,
      core_child_adj_iff G CoreG labelG hparentG]
    exact coreIso.toEquiv.injective.eq_iff
  · change H.Adj (fibers u k l) (coreIso v) ↔ G.Adj l v
    rw [H.adj_comm, G.adj_comm, core_child_adj_iff H CoreH labelH hparentH,
      core_child_adj_iff G CoreG labelG hparentG]
    exact coreIso.toEquiv.injective.eq_iff
  · exact iff_of_false
      (hleavesH _ _ (fibers u k l).property.1 (fibers v j m).property.1)
      (hleavesG _ _ l.property.1 m.property.1)

include fibers in
/-- Grafting finite labelled leaf fibres onto a core isomorphism gives a
whole graph isomorphism preserving labels. Finiteness is unnecessary for the
glue itself; in the tree application finite equal fibre-cardinalities supply
the actual equivalences accepted here. -/
theorem graft_colored_iso
    (hparentG : ∀ l, ¬ CoreG l → ∃! u : {v // CoreG v}, G.Adj u l)
    (hparentH : ∀ l, ¬ CoreH l → ∃! u : {w // CoreH w}, H.Adj u l)
    (hleavesG : ∀ l m, ¬ CoreG l → ¬ CoreG m → ¬ G.Adj l m)
    (hleavesH : ∀ l m, ¬ CoreH l → ¬ CoreH m → ¬ H.Adj l m)
    (hCoreLabel : ∀ u : {v // CoreG v}, labelH (coreIso u) = labelG u) :
    ∃ wholeIso : G ≃g H,
      (∀ u : {v // CoreG v}, wholeIso u = (coreIso u : W)) ∧
      ∀ v, labelH (wholeIso v) = labelG v := by
  let eG := locationEquiv G CoreG labelG hparentG
  let eH := locationEquiv H CoreH labelH hparentH
  let eM := locationMatch G H CoreG CoreH labelG labelH coreIso fibers
  let e := eG.symm.trans (eM.trans eH)
  let wholeIso : G ≃g H :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        have h := locationMatch_adj G H CoreG CoreH labelG labelH coreIso fibers
          hparentG hparentH hleavesG hleavesH (eG.symm x) (eG.symm y)
        change H.Adj (eH (eM (eG.symm x))) (eH (eM (eG.symm y))) ↔
          G.Adj (eG (eG.symm x)) (eG (eG.symm y)) at h
        change H.Adj (eH (eM (eG.symm x))) (eH (eM (eG.symm y))) ↔ G.Adj x y
        simpa only [eG.apply_symm_apply x, eG.apply_symm_apply y] using h }
  refine ⟨wholeIso, ?_, ?_⟩
  · intro u
    have hg : eG.symm (u : V) = .inl u := by
      apply eG.injective
      simp [eG, locationEquiv, locationValue]
    change eH (eM (eG.symm u)) = _
    rw [hg]
    rfl
  · intro v
    change labelH (eH (eM (eG.symm v))) = labelG v
    have h := locationMatch_label G H CoreG CoreH labelG labelH coreIso fibers hCoreLabel
      (eG.symm v)
    change labelH (eH (eM (eG.symm v))) = labelG (eG (eG.symm v)) at h
    simpa only [eG.apply_symm_apply v] using h

/-- In the finite case, equality of actual labelled child-fibre cardinalities
supplies all the equivalences used by the graft. This wrapper exposes only
count data, unique-parent geometry, and a core isomorphism. -/
theorem graft_colored_iso_of_card [Finite V] [Finite W]
    (hcard : ∀ u : {v // CoreG v}, ∀ k : K,
      Nat.card (ChildFiber G CoreG labelG u k) =
        Nat.card (ChildFiber H CoreH labelH (coreIso u) k))
    (hparentG : ∀ l, ¬ CoreG l → ∃! u : {v // CoreG v}, G.Adj u l)
    (hparentH : ∀ l, ¬ CoreH l → ∃! u : {w // CoreH w}, H.Adj u l)
    (hleavesG : ∀ l m, ¬ CoreG l → ¬ CoreG m → ¬ G.Adj l m)
    (hleavesH : ∀ l m, ¬ CoreH l → ¬ CoreH m → ¬ H.Adj l m)
    (hCoreLabel : ∀ u : {v // CoreG v}, labelH (coreIso u) = labelG u) :
    ∃ wholeIso : G ≃g H,
      (∀ u : {v // CoreG v}, wholeIso u = (coreIso u : W)) ∧
      ∀ v, labelH (wholeIso v) = labelG v := by
  let es : ∀ u : {v // CoreG v}, ∀ k : K,
      ChildFiber G CoreG labelG u k ≃ ChildFiber H CoreH labelH (coreIso u) k := by
    intro u k
    letI := Fintype.ofFinite (ChildFiber G CoreG labelG u k)
    letI := Fintype.ofFinite (ChildFiber H CoreH labelH (coreIso u) k)
    apply Fintype.equivOfCardEq
    simpa only [Nat.card_eq_fintype_card] using hcard u k
  exact graft_colored_iso G H CoreG CoreH labelG labelH coreIso es
    hparentG hparentH hleavesG hleavesH hCoreLabel

end TwoGraphs

#print axioms locationValue_bijective
#print axioms core_child_adj_iff
#print axioms locationMatch_adj
#print axioms graft_colored_iso
#print axioms graft_colored_iso_of_card

end PrincipalMomentAudit.LeafGrafting
