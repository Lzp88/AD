import PaperVerifier.ADComplete.SpiderGraph

/-! Exact neighbor sets and degree labels of the actual finite spiders. -/
namespace ADComplete.SpiderGraph
noncomputable section

theorem adjacent_parent_or_child (L : Fin 3 → ℕ) (y : ArmVertex L) (z : Vertex L) :
    (graph L).Adj (some y) z ↔ z = parent L y ∨
      ∃ w : ArmVertex L, parent L w = some y ∧ z = some w := by
  rw [graph_adj]
  constructor
  · rintro ⟨w, h | h⟩
    · exact Or.inr ⟨w, h.1.symm, h.2⟩
    · have heq : y = w := Option.some_injective _ h.1
      subst w
      exact Or.inl h.2
  · rintro (h | ⟨w, hp, hz⟩)
    · exact ⟨y, Or.inr ⟨rfl, h⟩⟩
    · exact ⟨w, Or.inl ⟨hp.symm, hz⟩⟩

theorem children_unique (L : Fin 3 → ℕ) (y z w : ArmVertex L)
    (hz : parent L z = some y) (hw : parent L w = some y) : z = w := by
  rcases y with ⟨a, i⟩
  rcases z with ⟨b, j⟩
  rcases w with ⟨c, k⟩
  obtain ⟨hb, hj⟩ := (parent_eq_some L b a j i).mp hz
  obtain ⟨hc, hk⟩ := (parent_eq_some L c a k i).mp hw
  subst b
  subst c
  exact Sigma.ext rfl (heq_of_eq (Fin.ext (hj.trans hk.symm)))

def child (L : Fin 3 → ℕ) (y : ArmVertex L) (hy : y.2.val + 1 < L y.1) : ArmVertex L :=
  ⟨y.1, ⟨y.2.val + 1, hy⟩⟩

theorem parent_child (L : Fin 3 → ℕ) (y : ArmVertex L) (hy : y.2.val + 1 < L y.1) :
    parent L (child L y hy) = some y := by
  rcases y with ⟨a, i⟩
  exact (parent_eq_some L a a ⟨i.val + 1, hy⟩ i).mpr ⟨rfl, rfl⟩

theorem no_child_at_leaf (L : Fin 3 → ℕ) (y : ArmVertex L)
    (hy : y.2.val + 1 = L y.1) (z : ArmVertex L) : parent L z ≠ some y := by
  rcases y with ⟨a, i⟩
  rcases z with ⟨b, j⟩
  intro h
  obtain ⟨hb, hj⟩ := (parent_eq_some L b a j i).mp h
  subst b
  have hlt := j.isLt
  change i.val + 1 = L a at hy
  omega

def leafNeighborEquiv (L : Fin 3 → ℕ) (y : ArmVertex L) (hy : y.2.val + 1 = L y.1) :
    Unit ≃ (graph L).neighborSet (some y) :=
  Equiv.ofBijective (fun _ => ⟨parent L y, (parent_adj L y).symm⟩) (by
    constructor
    · exact fun x z _ => Subsingleton.elim x z
    · rintro ⟨z, hz⟩
      rcases (adjacent_parent_or_child L y z).mp hz with h | ⟨w, hw, _⟩
      · exact ⟨(), Subtype.ext h.symm⟩
      · exact (no_child_at_leaf L y hy w hw).elim)

def internalNeighborEquiv (L : Fin 3 → ℕ) (y : ArmVertex L)
    (hy : y.2.val + 1 < L y.1) : Bool ≃ (graph L).neighborSet (some y) :=
  Equiv.ofBijective (fun b => if b then
      ⟨some (child L y hy), by
        change (graph L).Adj (some y) (some (child L y hy))
        rw [← parent_child L y hy]
        exact parent_adj L (child L y hy)⟩
    else ⟨parent L y, (parent_adj L y).symm⟩) (by
    constructor
    · intro b c h
      have hv := congrArg (fun z : (graph L).neighborSet (some y) => height (z : Vertex L)) h
      have hh := parent_height L y
      simp only [height] at hh
      cases b <;> cases c <;> simp only [Bool.false_eq_true,
        if_false, if_true, height, child] at hv ⊢
      all_goals omega
    · rintro ⟨z, hz⟩
      rcases (adjacent_parent_or_child L y z).mp hz with h | ⟨w, hw, hz⟩
      · exact ⟨false, Subtype.ext h.symm⟩
      · have heq := children_unique L y w (child L y hy) hw (parent_child L y hy)
        exact ⟨true, Subtype.ext (by simpa only [if_true, heq] using hz.symm)⟩)

theorem arm_degree (L : Fin 3 → ℕ) (y : ArmVertex L) :
    (graph L).degree (some y) = if y.2.val + 1 = L y.1 then 1 else 2 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  by_cases hy : y.2.val + 1 = L y.1
  · rw [if_pos hy]
    exact (Fintype.card_congr (leafNeighborEquiv L y hy)).symm
  · rw [if_neg hy]
    have hlt : y.2.val + 1 < L y.1 := by have := y.2.isLt; omega
    exact (Fintype.card_congr (internalNeighborEquiv L y hlt)).symm

#print axioms arm_degree
end
end ADComplete.SpiderGraph
