import PaperVerifier.ADComplete.SpiderGeometry

/-! Geometry of the actual closed graph walks used by the spider obstruction. -/
namespace ADComplete.SpiderGraph
noncomputable section

def arm {L : Fin 3 → ℕ} : Vertex L → Option (Fin 3)
  | none => none
  | some y => some y.1

theorem vertex_eq_of_arm_height {L : Fin 3 → ℕ} {x z : Vertex L}
    (ha : arm x = arm z) (hh : height x = height z) : x = z := by
  cases x with
  | none =>
      cases z with
      | none => rfl
      | some y => simp [arm] at ha
  | some y =>
      cases z with
      | none => simp [arm] at ha
      | some q =>
          rcases y with ⟨a, i⟩
          rcases q with ⟨b, j⟩
          have hab : a = b := Option.some_injective _ ha
          subst b
          have hij : i = j := Fin.ext (by simpa only [height, Nat.add_right_cancel_iff] using hh)
          subst j
          rfl

theorem adjacent_arm_eq (L : Fin 3 → ℕ) {x z : Vertex L}
    (h : (graph L).Adj x z) (hx : x ≠ none) (hz : z ≠ none) : arm x = arm z := by
  cases x with
  | none => exact (hx rfl).elim
  | some y =>
      cases z with
      | none => exact (hz rfl).elim
      | some q =>
          rcases y with ⟨a, i⟩
          rcases q with ⟨b, j⟩
          have hab := ((some_adj_some L a b i j).mp h).1
          exact congrArg Option.some hab

theorem no_center_walk_arm_constant (L : Fin 3 → ℕ) {x z : Vertex L}
    (p : (graph L).Walk x z) (hc : none ∉ p.support) :
    ∀ y ∈ p.support, arm y = arm x := by
  induction p with
  | nil => simp
  | @cons u v z h p ih =>
      have hu : u ≠ none := by intro he; subst u; exact hc (by simp)
      have hv : v ≠ none := by
        intro he; subst v
        exact hc (by simp)
      have hp : none ∉ p.support := by
        intro he
        exact hc (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons]; exact Or.inr he)
      intro y hy
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · rfl
      · exact (ih hp y hy).trans (adjacent_arm_eq L h hu hv).symm

theorem closed_walk_height_difference (L : Fin 3 → ℕ) {x y z : Vertex L}
    (p : (graph L).Walk x x) (hy : y ∈ p.support) (hz : z ∈ p.support) :
    2 * (height z - height y) ≤ p.length := by
  let q := p.rotate y hy
  have hz' : z ∈ q.support :=
    (SimpleGraph.Walk.mem_support_rotate_iff p y hy).mpr hz
  have h₀ := walk_height_le L (q.takeUntil z hz')
  have h₁ := walk_height_le L ((q.dropUntil z hz').reverse)
  rw [SimpleGraph.Walk.length_reverse] at h₁
  have hlen := congrArg SimpleGraph.Walk.length (q.take_spec hz')
  rw [SimpleGraph.Walk.length_append] at hlen
  have hq : q.length = p.length := SimpleGraph.Walk.length_rotate p y hy
  omega

theorem short_closed_height_span (L : Fin 3 → ℕ) (m : ℕ) {x y z : Vertex L}
    (p : (graph L).Walk x x) (hp : p.length < 2 * m)
    (hy : y ∈ p.support) (hz : z ∈ p.support) : height z - height y < m := by
  have h := closed_walk_height_difference L p hy hz
  omega

theorem short_word_height_span (L : Fin 3 → ℕ) (m : ℕ) (w : List Bool)
    (hw : ADClosedWalks.adjacencyCount w < 2 * m) (u : Vertex L)
    (x : Fin w.length → Vertex L) (h : ADClosedWalks.valid (graph L) w u u x)
    (i j : Fin (w.length + 1)) :
    height ((Fin.cons u x : Fin (w.length + 1) → Vertex L) j) -
      height ((Fin.cons u x : Fin (w.length + 1) → Vertex L) i) < m := by
  let p := ADClosedWalks.toWalk (graph L) w u u x h
  have hp : p.length < 2 * m := by
    simpa only [p, ADClosedWalks.toWalk_length] using hw
  exact short_closed_height_span L m p hp
    (ADClosedWalks.positions_mem_support (graph L) w u u x h i)
    (ADClosedWalks.positions_mem_support (graph L) w u u x h j)

#print axioms no_center_walk_arm_constant
#print axioms short_word_height_span
end
end ADComplete.SpiderGraph
