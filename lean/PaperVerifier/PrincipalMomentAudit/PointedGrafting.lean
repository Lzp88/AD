import PaperVerifier.PrincipalMomentAudit.LeafGrafting
import PaperVerifier.PrincipalMomentAudit.PointedSupport

/-!
# Exact child images in actual leaf grafting

The graph isomorphism is constructed from the given core isomorphism and
actual child-fibre equivalences. The conclusion exposes both core images
and every child image, so prescribing one fibre image proves the pointed
version without assuming a whole-graph pointed isomorphism.
-/

namespace PrincipalMomentAudit.PointedGrafting

noncomputable section

open SimpleGraph PrincipalMomentAudit.LeafGrafting

variable {V W K : Type*}
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable (CoreG : V → Prop) (CoreH : W → Prop)
variable (labelG : V → K) (labelH : W → K)
variable (coreIso : G.induce {v | CoreG v} ≃g H.induce {w | CoreH w})
variable (fibers : ∀ u : {v // CoreG v}, ∀ k : K,
  ChildFiber G CoreG labelG u k ≃ ChildFiber H CoreH labelH (coreIso u) k)

/-- Adjust a family of actual equivalences at one dependent index. -/
noncomputable def pointAdjustedFamily {ι : Type*} (X Y : ι → Type*)
    (e : ∀ i, X i ≃ Y i) (i₀ : ι) (x : X i₀) (y : Y i₀) : ∀ i, X i ≃ Y i := by
  classical
  intro i
  by_cases hi : i = i₀
  · subst i
    exact PrincipalMomentAudit.PointedSupport.pointAdjustedEquiv (e i₀) x y
  · exact e i

@[simp] theorem pointAdjustedFamily_apply {ι : Type*} (X Y : ι → Type*)
    (e : ∀ i, X i ≃ Y i) (i₀ : ι) (x : X i₀) (y : Y i₀) :
    pointAdjustedFamily X Y e i₀ x y i₀ x = y := by
  classical
  simp [pointAdjustedFamily]

include fibers in
/-- Actual grafting with the complete coordinate specification exposed. -/
theorem graft_colored_iso_with_fiber_images
    (hparentG : ∀ l, ¬ CoreG l → ∃! u : {v // CoreG v}, G.Adj u l)
    (hparentH : ∀ l, ¬ CoreH l → ∃! u : {w // CoreH w}, H.Adj u l)
    (hleavesG : ∀ l m, ¬ CoreG l → ¬ CoreG m → ¬ G.Adj l m)
    (hleavesH : ∀ l m, ¬ CoreH l → ¬ CoreH m → ¬ H.Adj l m)
    (hCoreLabel : ∀ u : {v // CoreG v}, labelH (coreIso u) = labelG u) :
    ∃ wholeIso : G ≃g H,
      (∀ u : {v // CoreG v}, wholeIso u = (coreIso u : W)) ∧
      (∀ u k (l : ChildFiber G CoreG labelG u k),
        wholeIso l = (fibers u k l : W)) ∧
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
  refine ⟨wholeIso, ?_, ?_, ?_⟩
  · intro u
    have hg : eG.symm (u : V) = .inl u := by
      apply eG.injective
      simp [eG, locationEquiv, locationValue]
    change eH (eM (eG.symm u)) = _
    rw [hg]
    rfl
  · intro u k l
    have hg : eG.symm (l : V) = .inr ⟨u, k, l⟩ := by
      apply eG.injective
      simp [eG, locationEquiv, locationValue]
    change eH (eM (eG.symm l)) = _
    rw [hg]
    rfl
  · intro v
    change labelH (eH (eM (eG.symm v))) = labelG v
    have h := locationMatch_label G H CoreG CoreH labelG labelH coreIso fibers hCoreLabel
      (eG.symm v)
    change labelH (eH (eM (eG.symm v))) = labelG (eG (eG.symm v)) at h
    simpa only [eG.apply_symm_apply v] using h

include fibers in
/-- Prescribing one actual child-fibre image produces the corresponding
pointed whole-graph isomorphism, while preserving the core and all labels. -/
theorem graft_colored_iso_pointed_child
    (hparentG : ∀ l, ¬ CoreG l → ∃! u : {v // CoreG v}, G.Adj u l)
    (hparentH : ∀ l, ¬ CoreH l → ∃! u : {w // CoreH w}, H.Adj u l)
    (hleavesG : ∀ l m, ¬ CoreG l → ¬ CoreG m → ¬ G.Adj l m)
    (hleavesH : ∀ l m, ¬ CoreH l → ¬ CoreH m → ¬ H.Adj l m)
    (hCoreLabel : ∀ u : {v // CoreG v}, labelH (coreIso u) = labelG u)
    (u : {v // CoreG v}) (k : K)
    (x : ChildFiber G CoreG labelG u k)
    (y : ChildFiber H CoreH labelH (coreIso u) k)
    (hxy : fibers u k x = y) :
    ∃ wholeIso : G ≃g H,
      (∀ a : {v // CoreG v}, wholeIso a = (coreIso a : W)) ∧
      (∀ v, labelH (wholeIso v) = labelG v) ∧ wholeIso x = (y : W) := by
  obtain ⟨wholeIso, hcore, hchild, hlabel⟩ :=
    graft_colored_iso_with_fiber_images G H CoreG CoreH labelG labelH coreIso fibers
      hparentG hparentH hleavesG hleavesH hCoreLabel
  exact ⟨wholeIso, hcore, hlabel, (hchild u k x).trans (congrArg Subtype.val hxy)⟩

section FiniteFibers

variable [Fintype V] [Fintype W]

local instance : DecidablePred CoreG := Classical.decPred _
local instance : DecidablePred CoreH := Classical.decPred _
local instance : DecidableRel G.Adj := Classical.decRel _
local instance : DecidableRel H.Adj := Classical.decRel _
local instance : DecidableEq K := Classical.decEq _

/-- Equal actual finite child-fibre cardinalities are enough to graft a
label-preserving isomorphism with a prescribed child image. The fibre
bijections are constructed here and adjusted only at the designated fibre. -/
theorem graft_colored_iso_givenleaf
    (hparentG : ∀ l, ¬ CoreG l → ∃! u : {v // CoreG v}, G.Adj u l)
    (hparentH : ∀ l, ¬ CoreH l → ∃! u : {w // CoreH w}, H.Adj u l)
    (hleavesG : ∀ l m, ¬ CoreG l → ¬ CoreG m → ¬ G.Adj l m)
    (hleavesH : ∀ l m, ¬ CoreH l → ¬ CoreH m → ¬ H.Adj l m)
    (hCoreLabel : ∀ u : {v // CoreG v}, labelH (coreIso u) = labelG u)
    (hcard : ∀ u k,
      Fintype.card (ChildFiber G CoreG labelG u k) =
        Fintype.card (ChildFiber H CoreH labelH (coreIso u) k))
    (u : {v // CoreG v}) (k : K)
    (x : ChildFiber G CoreG labelG u k)
    (y : ChildFiber H CoreH labelH (coreIso u) k) :
    ∃ wholeIso : G ≃g H,
      (∀ a : {v // CoreG v}, wholeIso a = (coreIso a : W)) ∧
      (∀ v, labelH (wholeIso v) = labelG v) ∧ wholeIso x = (y : W) := by
  classical
  let X := fun i : {v // CoreG v} × K => ChildFiber G CoreG labelG i.1 i.2
  let Y := fun i : {v // CoreG v} × K => ChildFiber H CoreH labelH (coreIso i.1) i.2
  let e : ∀ i, X i ≃ Y i := fun i => Fintype.equivOfCardEq (hcard i.1 i.2)
  let es := pointAdjustedFamily X Y e (u, k) x y
  let fs := fun a j => es (a, j)
  have hxy : fs u k x = y := pointAdjustedFamily_apply X Y e (u, k) x y
  exact graft_colored_iso_pointed_child G H CoreG CoreH labelG labelH coreIso fs
    hparentG hparentH hleavesG hleavesH hCoreLabel u k x y hxy

end FiniteFibers

#print axioms graft_colored_iso_with_fiber_images
#print axioms graft_colored_iso_pointed_child
#print axioms graft_colored_iso_givenleaf

end

end PrincipalMomentAudit.PointedGrafting
