import PaperVerifier.PrincipalMomentAudit.TreeReconstruction

/-!
# Pointed support for actual coloured-tree reconstruction

These lemmas identify an actual leaf's neighbour-colour counts and adjust
finite fibre equivalences to send a specified source point to a specified
target point. They do not assume any tree rigidity or orbit-completeness
conclusion.
-/

namespace PrincipalMomentAudit.PointedSupport

noncomputable section
open SimpleGraph PrincipalMomentAudit.TreeReconstruction

variable {V W α : Type*} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]
variable (c : V → α) (d : W → α)

local instance : DecidableEq α := Classical.decEq _

/-- At an actual leaf, each neighbour-colour count is the indicator of its
unique parent's colour. -/
theorem leaf_neighborCount {x p : V} (hx : G.degree x = 1) (hxp : G.Adj x p)
    (k : α) : neighborCount G c x k = if c p = k then 1 else 0 := by
  classical
  have hunique : ∀ q, G.Adj x q → q = p := by
    obtain ⟨r, hr, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hx
    exact fun q hq => (huniq q hq).trans (huniq p hxp).symm
  by_cases hpk : c p = k
  · let : Unique {q : G.neighborSet x // c q = k} :=
      { default := ⟨⟨p, hxp⟩, hpk⟩
        uniq := fun q => Subtype.ext (Subtype.ext (hunique q q.val.property)) }
    simp only [if_pos hpk]
    exact Fintype.card_unique
  · let : IsEmpty {q : G.neighborSet x // c q = k} :=
      ⟨fun q => hpk ((hunique q q.val.property) ▸ q.property)⟩
    simp only [if_neg hpk]
    exact Fintype.card_eq_zero

/-- Equal actual colour counts at two leaves force their actual parents
to have the same colour. -/
theorem leaf_parents_same_color {x p : V} {y q : W}
    (hx : G.degree x = 1) (hy : H.degree y = 1)
    (hxp : G.Adj x p) (hyq : H.Adj y q)
    (hcounts : ∀ k, neighborCount G c x k = neighborCount H d y k) :
    c p = d q := by
  classical
  by_contra hne
  have hG : neighborCount G c x (c p) = 1 := by
    simpa using leaf_neighborCount G c hx hxp (c p)
  have hH : neighborCount H d y (c p) = 0 := by
    simpa [Ne.symm hne] using leaf_neighborCount H d hy hyq (c p)
  exact Nat.one_ne_zero (hG.symm.trans ((hcounts (c p)).trans hH))

/-- The same statement for the actual non-leaf-core parents used by the
tree induction. Their membership is supplied by the actual geometric theorem. -/
theorem same_color_leaf_core_parents
    (hcount : ∀ x y, c x = d y → ∀ k,
      neighborCount G c x k = neighborCount H d y k)
    {x : V} {y : W} (hxy : c x = d y)
    (hx : G.degree x = 1) (hy : H.degree y = 1)
    (p : {v : V // G.degree v ≠ 1}) (q : {v : W // H.degree v ≠ 1})
    (hpx : G.Adj p x) (hqy : H.Adj q y) : c p = d q :=
  leaf_parents_same_color G H c d hx hy hpx.symm hqy.symm (hcount x y hxy)

section EquivalenceAdjustment

variable {X Y K : Type*}

local instance : DecidableEq Y := Classical.decEq _

/-- Postcompose any equivalence with a transposition to prescribe one image.
This works for actual finite child fibres, without replacing them by counts. -/
def pointAdjustedEquiv (e : X ≃ Y) (x : X) (y : Y) : X ≃ Y := by
  classical
  exact e.trans (Equiv.swap (e x) y)

@[simp] theorem pointAdjustedEquiv_apply (e : X ≃ Y) (x : X) (y : Y) :
    pointAdjustedEquiv e x y x = y := by
  classical
  simp [pointAdjustedEquiv]

/-- Swapping two vertices with the same label preserves every label. -/
theorem swap_preserves_label (label : Y → K) (a b : Y)
    (hab : label a = label b) (z : Y) :
    label (Equiv.swap a b z) = label z := by
  classical
  by_cases hza : z = a
  · subst z
    simpa only [Equiv.swap_apply_left] using hab.symm
  · by_cases hzb : z = b
    · subst z
      simpa only [Equiv.swap_apply_right] using hab
    · rw [Equiv.swap_apply_of_ne_of_ne hza hzb]

/-- The image adjustment preserves labels when the prescribed source and
target points have the same label. -/
theorem pointAdjustedEquiv_preserves_label (e : X ≃ Y)
    (labelX : X → K) (labelY : Y → K)
    (he : ∀ z, labelY (e z) = labelX z)
    (x : X) (y : Y) (hxy : labelX x = labelY y) (z : X) :
    labelY (pointAdjustedEquiv e x y z) = labelX z := by
  classical
  exact (swap_preserves_label labelY (e x) y ((he x).trans hxy) (e z)).trans (he z)

/-- Equal actual finite fibre cardinalities yield a bijection with a
prescribed point image. -/
def pointedEquivOfCardEq [Fintype X] [Fintype Y]
    (hcard : Fintype.card X = Fintype.card Y) (x : X) (y : Y) : X ≃ Y :=
  pointAdjustedEquiv (Fintype.equivOfCardEq hcard) x y

@[simp] theorem pointedEquivOfCardEq_apply [Fintype X] [Fintype Y]
    (hcard : Fintype.card X = Fintype.card Y) (x : X) (y : Y) :
    pointedEquivOfCardEq hcard x y x = y :=
  pointAdjustedEquiv_apply _ x y

end EquivalenceAdjustment

/-- A whole-vertex colour bijection with a prescribed same-colour image. -/
def colorEquivPointed (hsize : ∀ k, cellSize c k = cellSize d k)
    (x : V) (y : W) : V ≃ W :=
  pointAdjustedEquiv (colorEquiv c d hsize) x y

@[simp] theorem colorEquivPointed_apply
    (hsize : ∀ k, cellSize c k = cellSize d k) (x : V) (y : W) :
    colorEquivPointed c d hsize x y x = y :=
  pointAdjustedEquiv_apply _ x y

theorem colorEquivPointed_map
    (hsize : ∀ k, cellSize c k = cellSize d k)
    (x : V) (y : W) (hxy : c x = d y) (z : V) :
    d (colorEquivPointed c d hsize x y z) = c z :=
  pointAdjustedEquiv_preserves_label _ c d (colorEquiv_map c d hsize) x y hxy z

/-- The order-one/order-two induction bases also admit the prescribed image. -/
theorem small_colored_tree_iso_pointed (hG : G.IsTree) (hH : H.IsTree)
    (hsize : ∀ k, cellSize c k = cellSize d k) (hcard : Fintype.card V ≤ 2)
    (x : V) (y : W) (hxy : c x = d y) :
    ∃ f : G ≃g H, (∀ z, d (f z) = c z) ∧ f x = y := by
  classical
  let e := colorEquivPointed c d hsize x y
  have hcardH : Fintype.card W ≤ 2 := by
    rw [← Fintype.card_congr e]
    exact hcard
  let f : G ≃g H :=
    { toEquiv := e
      map_rel_iff' := by
        intro u v
        rw [small_connected_adj_iff_ne H hH.connected hcardH,
          small_connected_adj_iff_ne G hG.connected hcard, e.injective.ne_iff] }
  exact ⟨f, colorEquivPointed_map c d hsize x y hxy, colorEquivPointed_apply c d hsize x y⟩

#print axioms leaf_neighborCount
#print axioms leaf_parents_same_color
#print axioms same_color_leaf_core_parents
#print axioms pointAdjustedEquiv_preserves_label
#print axioms small_colored_tree_iso_pointed

end

end PrincipalMomentAudit.PointedSupport
