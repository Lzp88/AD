import Mathlib

/-! The actual finite three-arm spiders used for the trace-degree obstruction. -/
namespace ADComplete.SpiderGraph
noncomputable section
open scoped BigOperators

abbrev ArmVertex (L : Fin 3 → ℕ) := (a : Fin 3) × Fin (L a)
abbrev Vertex (L : Fin 3 → ℕ) := Option (ArmVertex L)

def height {L : Fin 3 → ℕ} : Vertex L → ℕ
  | none => 0
  | some y => y.2.val + 1

def parent (L : Fin 3 → ℕ) (y : ArmVertex L) : Vertex L :=
  if hy : y.2.val = 0 then none else
    some ⟨y.1, ⟨y.2.val - 1, by omega⟩⟩

theorem parent_height (L : Fin 3 → ℕ) (y : ArmVertex L) :
    height (parent L y) + 1 = height (some y) := by
  unfold parent
  split_ifs with hy
  · simp [height, hy]
  · simp only [height]
    omega

theorem parent_ne (L : Fin 3 → ℕ) (y : ArmVertex L) : parent L y ≠ some y := by
  intro h
  have hh := parent_height L y
  rw [h] at hh
  omega

def childEdge (L : Fin 3 → ℕ) (y : ArmVertex L) : Sym2 (Vertex L) :=
  s(parent L y, some y)

theorem childEdge_injective (L : Fin 3 → ℕ) : Function.Injective (childEdge L) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Option.some_injective _ h.2
  · have hx := parent_height L x
    have hy := parent_height L y
    have h₁ := congrArg height h.1
    have h₂ := congrArg height h.2
    omega

def graph (L : Fin 3 → ℕ) : SimpleGraph (Vertex L) :=
  SimpleGraph.fromEdgeSet (Set.range (childEdge L))

instance (L : Fin 3 → ℕ) : DecidableRel (graph L).Adj := Classical.decRel _

theorem graph_edgeSet (L : Fin 3 → ℕ) : (graph L).edgeSet = Set.range (childEdge L) := by
  rw [graph, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · intro he
    exact he.1
  · rintro ⟨y, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    intro hy
    exact parent_ne L y (Sym2.mk_isDiag_iff.mp hy)

def edgeEquiv (L : Fin 3 → ℕ) : ArmVertex L ≃ (graph L).edgeSet :=
  Equiv.ofBijective (fun y => ⟨childEdge L y, graph_edgeSet L ▸ ⟨y, rfl⟩⟩) (by
    constructor
    · intro x y h
      exact childEdge_injective L (congrArg Subtype.val h)
    · rintro ⟨e, he⟩
      rw [graph_edgeSet] at he
      obtain ⟨y, rfl⟩ := he
      exact ⟨y, rfl⟩)

theorem parent_adj (L : Fin 3 → ℕ) (y : ArmVertex L) :
    (graph L).Adj (parent L y) (some y) := by
  exact ⟨⟨y, rfl⟩, parent_ne L y⟩

theorem graph_adj (L : Fin 3 → ℕ) (x z : Vertex L) :
    (graph L).Adj x z ↔ ∃ y : ArmVertex L,
      (x = parent L y ∧ z = some y) ∨ (x = some y ∧ z = parent L y) := by
  constructor
  · rintro ⟨⟨y, hy⟩, _⟩
    refine ⟨y, ?_⟩
    rcases Sym2.eq_iff.mp hy with h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.2.symm, h.1.symm⟩
  · rintro ⟨y, h | h⟩
    · rw [h.1, h.2]
      exact parent_adj L y
    · rw [h.1, h.2]
      exact (parent_adj L y).symm

theorem parent_eq_none (L : Fin 3 → ℕ) (y : ArmVertex L) :
    parent L y = none ↔ y.2.val = 0 := by
  unfold parent
  split_ifs <;> simp_all

theorem parent_eq_some (L : Fin 3 → ℕ) (a b : Fin 3) (i : Fin (L a)) (j : Fin (L b)) :
    parent L ⟨a, i⟩ = some ⟨b, j⟩ ↔ a = b ∧ i.val = j.val + 1 := by
  by_cases hi : i.val = 0
  · simp [parent, hi]
  · constructor
    · intro h
      have hf := congrArg (fun x : Vertex L => x.map Sigma.fst) h
      have hh := congrArg height h
      simp only [parent, dif_neg hi, Option.map_some] at hf
      simp only [parent, dif_neg hi, height] at hh
      exact ⟨Option.some_injective _ hf, by omega⟩
    · rintro ⟨rfl, hval⟩
      simp only [parent, dif_neg hi]
      congr 2
      apply Fin.ext
      change i.val - 1 = j.val
      omega

theorem root_adj_some (L : Fin 3 → ℕ) (y : ArmVertex L) :
    (graph L).Adj none (some y) ↔ y.2.val = 0 := by
  rw [graph_adj]
  constructor
  · rintro ⟨z, h | h⟩
    · have hz : y = z := Option.some_injective _ h.2
      subst z
      exact (parent_eq_none L y).mp h.1.symm
    · cases h.1
  · intro hy
    exact ⟨y, Or.inl ⟨((parent_eq_none L y).mpr hy).symm, rfl⟩⟩

theorem some_adj_some (L : Fin 3 → ℕ) (a b : Fin 3) (i : Fin (L a)) (j : Fin (L b)) :
    (graph L).Adj (some ⟨a, i⟩) (some ⟨b, j⟩) ↔
      a = b ∧ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  rw [graph_adj]
  constructor
  · rintro ⟨z, h | h⟩
    · have hz : (⟨b, j⟩ : ArmVertex L) = z := Option.some_injective _ h.2
      subst z
      obtain ⟨ha, hv⟩ := (parent_eq_some L b a j i).mp h.1.symm
      exact ⟨ha.symm, Or.inl hv.symm⟩
    · have hz : (⟨a, i⟩ : ArmVertex L) = z := Option.some_injective _ h.1
      subst z
      obtain ⟨ha, hv⟩ := (parent_eq_some L a b i j).mp h.2.symm
      exact ⟨ha, Or.inr hv.symm⟩
  · rintro ⟨ha, hv | hv⟩
    · exact ⟨⟨b, j⟩, Or.inl ⟨((parent_eq_some L b a j i).mpr ⟨ha.symm, hv.symm⟩).symm, rfl⟩⟩
    · exact ⟨⟨a, i⟩, Or.inr ⟨rfl, ((parent_eq_some L a b i j).mpr ⟨ha, hv.symm⟩).symm⟩⟩

def rootNeighborEquiv (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) :
    Fin 3 ≃ (graph L).neighborSet none :=
  Equiv.ofBijective (fun a => ⟨some ⟨a, ⟨0, hL a⟩⟩,
    (root_adj_some L _).mpr rfl⟩) (by
    constructor
    · intro a b h
      exact congrArg Sigma.fst (Option.some_injective _ (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      cases x with
      | none => exact ((graph L).irrefl hx).elim
      | some y =>
          rcases y with ⟨a, i⟩
          have hi := (root_adj_some L ⟨a, i⟩).mp hx
          change i.val = 0 at hi
          have heq : i = ⟨0, hL a⟩ := Fin.ext hi
          subst i
          refine ⟨a, ?_⟩
          rfl)

theorem root_degree (L : Fin 3 → ℕ) (hL : ∀ a, 0 < L a) :
    (graph L).degree none = 3 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr (rootNeighborEquiv L hL)).symm

theorem root_reachable (L : Fin 3 → ℕ) (x : Vertex L) :
    (graph L).Reachable none x := by
  cases x with
  | none => exact SimpleGraph.Reachable.refl _
  | some y =>
      rcases y with ⟨a, i⟩
      have hr (k : ℕ) (hk : k < L a) :
          (graph L).Reachable none (some ⟨a, ⟨k, hk⟩⟩) := by
        induction k with
        | zero =>
            have hp : (graph L).Adj none (some ⟨a, ⟨0, hk⟩⟩) := by
              simpa [parent] using parent_adj L ⟨a, ⟨0, hk⟩⟩
            exact hp.reachable
        | succ k ih =>
            have hp : (graph L).Adj (some ⟨a, ⟨k, by omega⟩⟩) (some ⟨a, ⟨k + 1, hk⟩⟩) := by
              simpa [parent] using parent_adj L ⟨a, ⟨k + 1, hk⟩⟩
            exact (ih (by omega)).trans hp.reachable
      exact hr i.val i.isLt

theorem connected (L : Fin 3 → ℕ) : (graph L).Connected :=
  ⟨fun x y => (root_reachable L x).symm.trans (root_reachable L y)⟩

theorem card_vertices (L : Fin 3 → ℕ) : Fintype.card (Vertex L) = 1 + ∑ a, L a := by
  simp [Vertex, ArmVertex, Fintype.card_sigma, Nat.add_comm]

theorem isTree (L : Fin 3 → ℕ) : (graph L).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨connected L, ?_⟩
  rw [Nat.card_congr (edgeEquiv L).symm]
  simp [Vertex, Nat.card_eq_fintype_card]

def leftLengths (m : ℕ) : Fin 3 → ℕ := ![m, m, m + 2]
def rightLengths (m : ℕ) : Fin 3 → ℕ := ![m, m + 1, m + 1]

theorem witness_card_left (m : ℕ) : Fintype.card (Vertex (leftLengths m)) = 3 * m + 3 := by
  rw [card_vertices]
  simp [leftLengths, Fin.sum_univ_succ]
  omega

theorem witness_card_right (m : ℕ) : Fintype.card (Vertex (rightLengths m)) = 3 * m + 3 := by
  rw [card_vertices]
  simp [rightLengths, Fin.sum_univ_succ]
  omega

#print axioms isTree
#print axioms witness_card_left
#print axioms witness_card_right
end
end ADComplete.SpiderGraph
