import PaperVerifier.PrincipalMomentAudit.RootedOrbit
import PaperVerifier.PrincipalMomentAudit.PruningLift

/-!
Actual coloured automorphisms at the terminal guarded forest core.
The isolated-point and oriented K2 endpoint classes are proved to be
transitive by constructing graph automorphisms, not by assuming type/orbit
classification. Closed induced-component isomorphisms are extended below.
-/

namespace PrincipalMomentAudit.TerminalOrbits

open SimpleGraph PrincipalMomentAudit.RootedOrbit

variable {V K : Type*}

def ColoredOrbit (G : SimpleGraph V) (label : V → K) (v w : V) : Prop :=
  ∃ α : G ≃g G, α v = w ∧ ∀ x, label (α x) = label x

def Closed (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∉ S, ¬ G.Adj x y

noncomputable section

theorem closed_component_aut_extend (G : SimpleGraph V) (label : V → K)
    (S : Set V) (hclosed : Closed G S) (e : G.induce S ≃g G.induce S)
    (hlabel : ∀ x : S, label (e x) = label x) :
    ∃ α : G ≃g G, (∀ x : S, α x = (e x : V)) ∧
      (∀ x, x ∉ S → α x = x) ∧ ∀ x, label (α x) = label x := by
  classical
  let d := Equiv.Set.sumCompl S
  let m := Equiv.sumCongr e.toEquiv (Equiv.refl (Sᶜ : Set V))
  have hAdj (x y : S ⊕ (Sᶜ : Set V)) : G.Adj (d (m x)) (d (m y)) ↔ G.Adj (d x) (d y) := by
    rcases x with x | x <;> rcases y with y | y
    · exact e.map_adj_iff
    · exact iff_of_false (hclosed _ (e x).property _ y.property)
        (hclosed _ x.property _ y.property)
    · exact iff_of_false (fun h => hclosed _ (e y).property _ x.property h.symm)
        (fun h => hclosed _ y.property _ x.property h.symm)
    · rfl
  let f := d.symm.trans (m.trans d)
  let α : G ≃g G :=
    { toEquiv := f
      map_rel_iff' := by
        intro x y
        have h := hAdj (d.symm x) (d.symm y)
        change G.Adj (d (m (d.symm x))) (d (m (d.symm y))) ↔
          G.Adj (d (d.symm x)) (d (d.symm y)) at h
        change G.Adj (d (m (d.symm x))) (d (m (d.symm y))) ↔ G.Adj x y
        simpa only [d.apply_symm_apply] using h }
  have hS (x : S) : α x = (e x : V) := by
    change d (m (d.symm x)) = _
    rw [Equiv.Set.sumCompl_symm_apply_of_mem x.property]
    rfl
  have hout (x : V) (hx : x ∉ S) : α x = x := by
    change d (m (d.symm x)) = _
    rw [Equiv.Set.sumCompl_symm_apply_of_notMem hx]
    rfl
  refine ⟨α, hS, hout, ?_⟩
  intro x
  by_cases hx : x ∈ S
  · rw [hS ⟨x, hx⟩]
    exact hlabel ⟨x, hx⟩
  · rw [hout x hx]

theorem closed_components_iso_swap (G : SimpleGraph V) (label : V → K)
    (S T : Set V) (hST : Disjoint S T) (hclosedS : Closed G S) (hclosedT : Closed G T)
    (e : G.induce S ≃g G.induce T) (hlabel : ∀ x : S, label (e x) = label x) :
    ∃ α : G ≃g G, (∀ x : S, α x = (e x : V)) ∧
      ∀ x, label (α x) = label x := by
  classical
  let f := swapMap S T e.toEquiv
  have hf : Function.Involutive f := swapMap_involutive e.toEquiv hST
  have hmap {x y : V} (hxy : G.Adj x y) : G.Adj (f x) (f y) := by
    change G.Adj (swapMap S T e.toEquiv x) (swapMap S T e.toEquiv y)
    by_cases hxS : x ∈ S
    · by_cases hyS : y ∈ S
      · rw [swapMap_left e.toEquiv hxS, swapMap_left e.toEquiv hyS]
        exact e.map_adj_iff.mpr hxy
      · exact (hclosedS x hxS y hyS hxy).elim
    · by_cases hxT : x ∈ T
      · by_cases hyT : y ∈ T
        · rw [swapMap_right e.toEquiv hST hxT, swapMap_right e.toEquiv hST hyT]
          exact e.symm.map_adj_iff.mpr hxy
        · exact (hclosedT x hxT y hyT hxy).elim
      · by_cases hyS : y ∈ S
        · exact (hclosedS y hyS x hxS hxy.symm).elim
        · by_cases hyT : y ∈ T
          · exact (hclosedT y hyT x hxT hxy.symm).elim
          · rw [swapMap_out e.toEquiv hxS hxT, swapMap_out e.toEquiv hyS hyT]
            exact hxy
  let α : G ≃g G :=
    { toEquiv := hf.toPerm f
      map_rel_iff' := by
        intro x y
        constructor
        · intro h
          have h' := hmap h
          change G.Adj (f (f x)) (f (f y)) at h'
          simpa only [hf x, hf y] using h'
        · exact hmap }
  refine ⟨α, ?_, ?_⟩
  · intro x
    exact swapMap_left e.toEquiv x.property
  · intro x
    change label (swapMap S T e.toEquiv x) = label x
    by_cases hxS : x ∈ S
    · rw [swapMap_left e.toEquiv hxS]
      exact hlabel ⟨x, hxS⟩
    · by_cases hxT : x ∈ T
      · rw [swapMap_right e.toEquiv hST hxT]
        let y : S := e.toEquiv.symm ⟨x, hxT⟩
        have hy : (e y : V) = x := congrArg Subtype.val (e.toEquiv.apply_symm_apply ⟨x, hxT⟩)
        exact (hlabel y).symm.trans (congrArg label hy)
      · rw [swapMap_out e.toEquiv hxS hxT]

section Finite

variable [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → K)

omit [DecidableEq V] in
theorem degree_one_neighbors_eq {v u z : V} (hv : G.degree v = 1)
    (hvu : G.Adj v u) (hvz : G.Adj v z) : u = z := by
  obtain ⟨a, _, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  exact (huniq u hvu).trans (huniq z hvz).symm

omit [DecidableEq V] in
theorem pair_closed {v u : V} (hv : G.degree v = 1) (hu : G.degree u = 1)
    (hvu : G.Adj v u) : Closed G ({v, u} : Set V) := by
  intro x hx y hy hxy
  rcases hx with rfl | hx
  · have he : y = u := degree_one_neighbors_eq G hv hxy hvu
    exact hy (Or.inr he)
  · have hx' : x = u := hx
    subst x
    have he : y = v := degree_one_neighbors_eq G hu hxy hvu.symm
    exact hy (Or.inl he)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem pair_adj_iff {v u : V} (hvu : G.Adj v u) (x y : ({v, u} : Set V)) :
    G.Adj x y ↔ x ≠ y := by
  have hx : (x : V) = v ∨ (x : V) = u := x.property
  have hy : (y : V) = v ∨ (y : V) = u := y.property
  simp only [ne_eq, Subtype.ext_iff]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp [hx, hy, hvu, hvu.symm, hvu.ne, hvu.ne.symm]

omit [Fintype V] in
def pairMatch (v u w z : V) (hvu : v ≠ u) (hwz : w ≠ z) :
    ({v, u} : Set V) ≃ ({w, z} : Set V) where
  toFun x := if (x : V) = v then ⟨w, Or.inl rfl⟩ else ⟨z, Or.inr rfl⟩
  invFun y := if (y : V) = w then ⟨v, Or.inl rfl⟩ else ⟨u, Or.inr rfl⟩
  left_inv x := by
    apply Subtype.ext
    by_cases hx : (x : V) = v
    · simp [hx]
    · have hxu : (x : V) = u := x.property.resolve_left hx
      simp [hxu, hvu.symm, hwz.symm]
  right_inv y := by
    apply Subtype.ext
    by_cases hy : (y : V) = w
    · simp [hy]
    · have hyz : (y : V) = z := y.property.resolve_left hy
      simp [hyz, hwz.symm, hvu.symm]

omit [Fintype V] [DecidableRel G.Adj] in
def pairIso {v u w z : V} (hvu : G.Adj v u) (hwz : G.Adj w z) :
    G.induce ({v, u} : Set V) ≃g G.induce ({w, z} : Set V) where
  toEquiv := pairMatch v u w z hvu.ne hwz.ne
  map_rel_iff' := by
    intro x y
    change G.Adj (pairMatch v u w z hvu.ne hwz.ne x : V)
      (pairMatch v u w z hvu.ne hwz.ne y : V) ↔ G.Adj x y
    rw [pair_adj_iff G hwz, pair_adj_iff G hvu]
    exact not_congr (pairMatch v u w z hvu.ne hwz.ne).injective.eq_iff

omit [Fintype V] [DecidableRel G.Adj] in
theorem pairIso_root {v u w z : V} (hvu : G.Adj v u) (hwz : G.Adj w z) :
    (pairIso G hvu hwz ⟨v, Or.inl rfl⟩ : V) = w := by
  simp [pairIso, pairMatch]

omit [Fintype V] [DecidableRel G.Adj] in
theorem pairIso_label {v u w z : V} (hvu : G.Adj v u) (hwz : G.Adj w z)
    (hvlabel : label v = label w) (hulabel : label u = label z)
    (x : ({v, u} : Set V)) : label (pairIso G hvu hwz x) = label x := by
  by_cases hx : (x : V) = v
  · simp [pairIso, pairMatch, hx, hvlabel]
  · have hxu : (x : V) = u := x.property.resolve_left hx
    simp [pairIso, pairMatch, hxu, hvu.ne.symm, hulabel]

/-- Actual isolated vertices of the same colour are in one coloured orbit. -/
theorem isolated_same_label_orbit {v w : V} (hv : G.degree v = 0) (hw : G.degree w = 0)
    (hlabel : label v = label w) : ColoredOrbit G label v w := by
  classical
  by_cases hvw : v = w
  · exact ⟨Iso.refl, hvw, fun _ => rfl⟩
  have hnv : G.IsIsolated v := IsIsolated.of_degree_eq_zero G v hv
  have hnw : G.IsIsolated w := IsIsolated.of_degree_eq_zero G w hw
  let S : Set V := {v}
  let T : Set V := {w}
  let se : S ≃ T :=
    { toFun := fun _ => ⟨w, by simp [T]⟩
      invFun := fun _ => ⟨v, by simp [S]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact x.property.symm
      right_inv := by
        intro x
        apply Subtype.ext
        exact x.property.symm }
  let e : G.induce S ≃g G.induce T :=
    { toEquiv := se
      map_rel_iff' := by
        intro x y
        have hx : (x : V) = v := x.property
        have hn : ¬ G.Adj x y := by simpa only [hx] using hnv (y : V)
        exact iff_of_false (hnw w) hn }
  have hST : Disjoint S T := by simp [S, T, hvw]
  have hSclosed : Closed G S := by
    intro x hx y _
    have hxe : x = v := hx
    simpa only [hxe] using hnv y
  have hTclosed : Closed G T := by
    intro x hx y _
    have hxe : x = w := hx
    simpa only [hxe] using hnw y
  have helabel : ∀ x : S, label (e x) = label x := by
    intro x
    have hx : (x : V) = v := x.property
    change label w = label x
    rw [hx]
    exact hlabel.symm
  obtain ⟨α, hα, hαlabel⟩ := closed_components_iso_swap G label S T hST hSclosed hTclosed e helabel
  refine ⟨α, ?_, hαlabel⟩
  exact hα ⟨v, rfl⟩

/-- Actual isolated-edge endpoints with the same ordered pair of colours are
in one coloured orbit. Distinct edge components are exchanged; equal-colour
endpoints in one component are reflected. All permutations are constructed. -/
theorem leaf_pair_same_labels_orbit {v u w z : V}
    (hv : G.degree v = 1) (hu : G.degree u = 1)
    (hw : G.degree w = 1) (hz : G.degree z = 1)
    (hvu : G.Adj v u) (hwz : G.Adj w z)
    (hvlabel : label v = label w) (hulabel : label u = label z) :
    ColoredOrbit G label v w := by
  classical
  by_cases hvw : v = w
  · exact ⟨Iso.refl, hvw, fun _ => rfl⟩
  by_cases huw : u = w
  · have hvulabel : label v = label u := by simpa only [← huw] using hvlabel
    let S : Set V := {v, u}
    let av : S := ⟨v, Or.inl rfl⟩
    let au : S := ⟨u, Or.inr rfl⟩
    let se : S ≃ S := Equiv.swap av au
    let e : G.induce S ≃g G.induce S :=
      { toEquiv := se
        map_rel_iff' := by
          intro x y
          change G.Adj (se x : V) (se y : V) ↔ G.Adj x y
          rw [pair_adj_iff G hvu, pair_adj_iff G hvu]
          exact not_congr se.injective.eq_iff }
    have hconst (x : S) : label x = label v := by
      rcases x.property with hx | hx
      · rw [hx]
      · rw [hx]
        exact hvulabel.symm
    obtain ⟨α, hα, _, hαlabel⟩ := closed_component_aut_extend G label S
      (pair_closed G hv hu hvu) e (fun x => (hconst (e x)).trans (hconst x).symm)
    refine ⟨α, ?_, hαlabel⟩
    have h := hα av
    change α v = ((Equiv.swap av au) av : V) at h
    rw [Equiv.swap_apply_left] at h
    exact h.trans huw
  · have hzv : z ≠ v := by
      intro h
      have hwu : w = u := degree_one_neighbors_eq G hv (by simpa only [h] using hwz.symm) hvu
      exact huw hwu.symm
    have hzu : z ≠ u := by
      intro h
      have hwv : w = v := degree_one_neighbors_eq G hu (by simpa only [h] using hwz.symm) hvu.symm
      exact hvw hwv.symm
    have hST : Disjoint ({v, u} : Set V) ({w, z} : Set V) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact hvw (hx.symm.trans hy)
      · exact hzv (hy.symm.trans hx)
      · exact huw (hx.symm.trans hy)
      · exact hzu (hy.symm.trans hx)
    obtain ⟨α, hα, hαlabel⟩ := closed_components_iso_swap G label {v, u} {w, z} hST
      (pair_closed G hv hu hvu) (pair_closed G hw hz hwz) (pairIso G hvu hwz)
      (pairIso_label G label hvu hwz hvlabel hulabel)
    refine ⟨α, ?_, hαlabel⟩
    exact (hα ⟨v, Or.inl rfl⟩).trans (pairIso_root G hvu hwz)

/-- Exact coloured orbit classification of the terminal isolated-vertex seeds. -/
theorem isolated_orbit_iff {v w : V} (hv : G.degree v = 0) (hw : G.degree w = 0) :
    ColoredOrbit G label v w ↔ label v = label w := by
  constructor
  · rintro ⟨α, hα, hc⟩
    exact (hc v).symm.trans (congrArg label hα)
  · exact isolated_same_label_orbit G label hv hw

/-- Exact coloured orbit classification of the terminal oriented-edge seeds. -/
theorem leaf_pair_orbit_iff {v u w z : V}
    (hv : G.degree v = 1) (hu : G.degree u = 1)
    (hw : G.degree w = 1) (hz : G.degree z = 1)
    (hvu : G.Adj v u) (hwz : G.Adj w z) :
    ColoredOrbit G label v w ↔ label v = label w ∧ label u = label z := by
  constructor
  · rintro ⟨α, hα, hc⟩
    have hvcolor : label v = label w := (hc v).symm.trans (congrArg label hα)
    have hau : G.Adj w (α u) := by
      have h := α.map_adj_iff.mpr hvu
      simpa only [hα] using h
    have hneighbor : α u = z := degree_one_neighbors_eq G hw hau hwz
    exact ⟨hvcolor, (hc u).symm.trans (congrArg label hneighbor)⟩
  · rintro ⟨hvcolor, hucolor⟩
    exact leaf_pair_same_labels_orbit G label hv hu hw hz hvu hwz hvcolor hucolor

omit [DecidableEq V] in
theorem terminal_neighbor_degree_one (hterminal : ∀ x, G.degree x ≤ 1) {v u : V}
    (hvu : G.Adj v u) : G.degree u = 1 := by
  have hpos : 0 < G.degree u := (G.degree_pos_iff_exists_adj u).mpr ⟨v, hvu.symm⟩
  have hle := hterminal u
  omega

/-- The endpoint version used by the literal terminal-seed classifier: the
sole-neighbour degrees follow from actual terminality. -/
theorem terminal_edge_orbit_iff (hterminal : ∀ x, G.degree x ≤ 1) {v u w z : V}
    (hvu : G.Adj v u) (hwz : G.Adj w z) :
    ColoredOrbit G label v w ↔ label v = label w ∧ label u = label z := by
  exact leaf_pair_orbit_iff G label
    (terminal_neighbor_degree_one G hterminal hvu.symm)
    (terminal_neighbor_degree_one G hterminal hvu)
    (terminal_neighbor_degree_one G hterminal hwz.symm)
    (terminal_neighbor_degree_one G hterminal hwz) hvu hwz

end Finite

end

#print axioms closed_component_aut_extend
#print axioms closed_components_iso_swap
#print axioms isolated_same_label_orbit
#print axioms leaf_pair_same_labels_orbit
#print axioms isolated_orbit_iff
#print axioms terminal_edge_orbit_iff

end PrincipalMomentAudit.TerminalOrbits
