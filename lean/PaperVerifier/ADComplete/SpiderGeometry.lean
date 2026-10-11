import PaperVerifier.ADComplete.SpiderDistances
import PaperVerifier.ADComplete.ADClosedWalks

/-! Closed-walk geometry and a genuine nonisomorphic pair of finite spider trees. -/
namespace ADComplete.SpiderGraph
noncomputable section
open scoped BigOperators

theorem closed_walk_distance_bound {V : Type*} (G : SimpleGraph V)
    {x y : V} (p : G.Walk x x) (hy : y ∈ p.support) :
    2 * G.dist x y ≤ p.length := by
  classical
  have h₀ := G.dist_le (p.takeUntil y hy)
  have h₁ := G.dist_le (p.dropUntil y hy)
  rw [G.dist_comm] at h₁
  have hlen := congrArg SimpleGraph.Walk.length (p.take_spec hy)
  rw [SimpleGraph.Walk.length_append] at hlen
  omega

theorem closed_walk_root_height_bound (L : Fin 3 → ℕ) {x z : Vertex L}
    (p : (graph L).Walk x x) (hc : none ∈ p.support) (hz : z ∈ p.support) :
    2 * height z ≤ p.length := by
  have hz' : z ∈ (p.rotate none hc).support :=
    (SimpleGraph.Walk.mem_support_rotate_iff p none hc).mpr hz
  have h := closed_walk_distance_bound (graph L) (p.rotate none hc) hz'
  simpa only [root_dist, SimpleGraph.Walk.length_rotate] using h

theorem short_center_walk_height (L : Fin 3 → ℕ) (m : ℕ) {x : Vertex L}
    (p : (graph L).Walk x x) (hp : p.length < 2 * m) (hc : none ∈ p.support)
    (z : Vertex L) (hz : z ∈ p.support) : height z < m := by
  have h := closed_walk_root_height_bound L p hc hz
  omega

theorem degree_three_iff (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) (x : Vertex L) :
    (graph L).degree x = 3 ↔ x = none := by
  cases x with
  | none => simp [root_degree L hL]
  | some y => rw [arm_degree]; split_ifs <;> simp

def leaf (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) (a : Fin 3) : Vertex L :=
  some ⟨a, ⟨L a - 1, by have := hL a; omega⟩⟩

theorem leaf_height (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) (a : Fin 3) :
    height (leaf L hL a) = L a := by
  simp only [leaf, height]
  have := hL a
  omega

theorem leaf_degree (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) (a : Fin 3) :
    (graph L).degree (leaf L hL a) = 1 := by
  rw [leaf, arm_degree]
  have := hL a
  simp [show L a - 1 + 1 = L a by omega]

def LeafAt (L : Fin 3 → ℕ) (k : ℕ) :=
  {x : Vertex L // (graph L).degree x = 1 ∧ (graph L).dist none x = k}

instance (L : Fin 3 → ℕ) (k : ℕ) : Fintype (LeafAt L k) := by
  classical
  unfold LeafAt
  infer_instance

def shortArmLeafEquiv (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) (k : ℕ) :
    {a : Fin 3 // L a = k} ≃ LeafAt L k :=
  Equiv.ofBijective (fun a => ⟨leaf L hL a.val,
    leaf_degree L hL a.val, by rw [root_dist, leaf_height, a.property]⟩) (by
    constructor
    · intro a b hab
      apply Subtype.ext
      exact congrArg Sigma.fst (Option.some_injective _ (congrArg Subtype.val hab))
    · rintro ⟨x, hx⟩
      cases x with
      | none => have h := root_degree L hL; omega
      | some y =>
          rcases y with ⟨a, i⟩
          have hi : i.val + 1 = L a := by
            have h := hx.1
            rw [arm_degree] at h
            split_ifs at h with hi
            · exact hi
            · omega
          have hk : L a = k := by
            have h := hx.2
            rw [root_dist] at h
            change i.val + 1 = k at h
            omega
          refine ⟨⟨a, hk⟩, ?_⟩
          apply Subtype.ext
          change some (⟨a, ⟨L a - 1, _⟩⟩ : ArmVertex L) = some ⟨a, i⟩
          have hfin : (⟨L a - 1, by have := hL a; omega⟩ : Fin (L a)) = i :=
            Fin.ext (by change L a - 1 = i.val; omega)
          simp only [hfin])

theorem leafAt_card (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) (k : ℕ) :
    Fintype.card (LeafAt L k) = Fintype.card {a : Fin 3 // L a = k} :=
  (Fintype.card_congr (shortArmLeafEquiv L hL k)).symm

def isoLeafAtEquiv (L K : Fin 3 → ℕ) (hL : ∀ a, 0 < L a)
    (hK : ∀ a, 0 < K a) (e : graph L ≃g graph K) (k : ℕ) :
    LeafAt L k ≃ LeafAt K k := by
  have he : e none = none :=
    (degree_three_iff K hK (e none)).mp (by rw [e.degree_eq, root_degree L hL])
  have hes : e.symm none = none := by rw [← he, e.symm_apply_apply]
  refine
    { toFun := fun x => ⟨e x.val, ?_, ?_⟩
      invFun := fun x => ⟨e.symm x.val, ?_, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simpa only [e.degree_eq] using x.property.1
  · rw [← he, iso_preserves_distance (graph L) (graph K) e (root_reachable L x.val)]
    exact x.property.2
  · simpa only [e.symm.degree_eq] using x.property.1
  · rw [← hes, iso_preserves_distance (graph K) (graph L) e.symm (root_reachable K x.val)]
    exact x.property.2
  · intro x; apply Subtype.ext; exact e.symm_apply_apply x.val
  · intro x; apply Subtype.ext; exact e.apply_symm_apply x.val

theorem left_positive (m : ℕ) (hm : 2 ≤ m) : ∀ a, 0 < leftLengths m a := by
  intro a
  fin_cases a <;> simp [leftLengths] <;> omega

theorem right_positive (m : ℕ) (hm : 2 ≤ m) : ∀ a, 0 < rightLengths m a := by
  intro a
  fin_cases a
  · simpa [rightLengths] using (by omega : 0 < m)
  · simp [rightLengths]
  · simp [rightLengths]

theorem short_left_count (m : ℕ) :
    Fintype.card {a : Fin 3 // leftLengths m a = m} = 2 := by
  classical
  rw [Fintype.card_subtype]
  have hp : (fun a : Fin 3 => leftLengths m a = m) = (fun a => a = 0 ∨ a = 1) := by
    funext a
    apply propext
    fin_cases a <;> simp [leftLengths]
  simpa only [hp] using (by decide :
    (Finset.univ.filter (fun a : Fin 3 => a = 0 ∨ a = 1)).card = 2)

theorem short_right_count (m : ℕ) :
    Fintype.card {a : Fin 3 // rightLengths m a = m} = 1 := by
  classical
  rw [Fintype.card_subtype]
  have hp : (fun a : Fin 3 => rightLengths m a = m) = (fun a => a = 0) := by
    funext a
    apply propext
    fin_cases a <;> simp [rightLengths]
  simpa only [hp] using (by decide :
    (Finset.univ.filter (fun a : Fin 3 => a = 0)).card = 1)

theorem witness_nonisomorphic (m : ℕ) (hm : 2 ≤ m) :
    ¬ Nonempty (graph (leftLengths m) ≃g graph (rightLengths m)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr
    (isoLeafAtEquiv (leftLengths m) (rightLengths m)
      (left_positive m hm) (right_positive m hm) e m)
  rw [leafAt_card _ (left_positive m hm), leafAt_card _ (right_positive m hm),
    short_left_count, short_right_count] at h
  omega

#print axioms closed_walk_root_height_bound
#print axioms witness_nonisomorphic
end
end ADComplete.SpiderGraph
