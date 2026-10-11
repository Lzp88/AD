import PaperVerifier.ADComplete.SpiderDegrees

/-! Actual graph distances of the spider arms and their preservation by relabeling. -/
namespace ADComplete.SpiderGraph
noncomputable section

theorem adjacent_height_le (L : Fin 3 → ℕ) {x z : Vertex L} (h : (graph L).Adj x z) :
    height z ≤ height x + 1 := by
  obtain ⟨y, hy | hy⟩ := (graph_adj L x z).mp h
  · rw [hy.1, hy.2]
    exact (parent_height L y).ge
  · rw [hy.1, hy.2]
    have hp := parent_height L y
    omega

theorem walk_height_le (L : Fin 3 → ℕ) {x z : Vertex L} (p : (graph L).Walk x z) :
    height z ≤ height x + p.length := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      have hh := adjacent_height_le L h
      rw [SimpleGraph.Walk.length_cons]
      omega

theorem root_walk_of_height (L : Fin 3 → ℕ) (x : Vertex L) :
    ∃ p : (graph L).Walk none x, p.length = height x := by
  cases x with
  | none => exact ⟨.nil, rfl⟩
  | some y =>
      rcases y with ⟨a, i⟩
      have hr (k : ℕ) (hk : k < L a) : ∃ p : (graph L).Walk none
          (some ⟨a, ⟨k, hk⟩⟩), p.length = k + 1 := by
        induction k with
        | zero =>
            have hp : (graph L).Adj none (some ⟨a, ⟨0, hk⟩⟩) :=
              (root_adj_some L _).mpr rfl
            exact ⟨hp.toWalk, rfl⟩
        | succ k ih =>
            obtain ⟨p, hp⟩ := ih (by omega)
            have ha : (graph L).Adj (some ⟨a, ⟨k, by omega⟩⟩)
                (some ⟨a, ⟨k + 1, hk⟩⟩) :=
              (some_adj_some L a a _ _).mpr ⟨rfl, Or.inl rfl⟩
            exact ⟨p.concat ha, by rw [SimpleGraph.Walk.length_concat, hp]⟩
      exact hr i.val i.isLt

theorem root_dist (L : Fin 3 → ℕ) (x : Vertex L) : (graph L).dist none x = height x := by
  obtain ⟨p, hp⟩ := root_walk_of_height L x
  apply le_antisymm
  · simpa only [hp] using (graph L).dist_le p
  · obtain ⟨q, _, hq⟩ := (connected L).exists_path_of_dist none x
    have h := walk_height_le L q
    simpa only [height, zero_add, hq] using h

theorem iso_preserves_distance {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (e : G ≃g H)
    {x y : V} (hxy : G.Reachable x y) : H.dist (e x) (e y) = G.dist x y := by
  obtain ⟨p, _, hp⟩ := hxy.exists_path_of_dist
  have hr : H.Reachable (e x) (e y) := (p.map e.toHom).reachable
  obtain ⟨q, _, hq⟩ := hr.exists_path_of_dist
  apply le_antisymm
  · have h := H.dist_le (p.map e.toHom)
    change H.dist (e x) (e y) ≤ (p.map e.toHom).length at h
    simpa only [SimpleGraph.Walk.length_map, hp] using h
  · have h := G.dist_le (q.map e.symm.toHom)
    change G.dist (e.symm (e x)) (e.symm (e y)) ≤ (q.map e.symm.toHom).length at h
    simpa only [SimpleGraph.Walk.length_map, hq, e.symm_apply_apply] using h

#print axioms root_dist
#print axioms iso_preserves_distance
end
end ADComplete.SpiderGraph
