import Mathlib

/-! Exact finite translation counts and a leaf-status-preserving bijection. -/
namespace ADComplete.SpiderGraph
noncomputable section
open scoped BigOperators

def Placement (L : Fin 3 → ℕ) (w : ℕ) := (a : Fin 3) × Fin (L a - w)

instance (L : Fin 3 → ℕ) (w : ℕ) : Fintype (Placement L w) := by
  unfold Placement
  infer_instance

abbrev atLeaf {L : Fin 3 → ℕ} {w : ℕ} (p : Placement L w) : Prop :=
  p.2.val + 1 = L p.1 - w

instance (L : Fin 3 → ℕ) (w : ℕ) : DecidablePred (@atLeaf L w) := by
  intro p
  unfold atLeaf
  infer_instance

def leafPlacementEquiv (L : Fin 3 → ℕ) (w : ℕ) (hL : ∀ a, w < L a) :
    Fin 3 ≃ {p : Placement L w // atLeaf p} :=
  { toFun := fun a => ⟨⟨a, ⟨L a - w - 1, by have := hL a; omega⟩⟩,
      by change L a - w - 1 + 1 = L a - w; have := hL a; omega⟩
    invFun := fun p => p.val.1
    left_inv := by intro a; rfl
    right_inv := by
      rintro ⟨⟨a, t⟩, ht⟩
      apply Subtype.ext
      change (⟨a, ⟨L a - w - 1, _⟩⟩ : Placement L w) = ⟨a, t⟩
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Fin.ext
        change L a - w - 1 = t.val
        change t.val + 1 = L a - w at ht
        omega }

def interiorPlacementEquiv (L : Fin 3 → ℕ) (w : ℕ) :
    ((a : Fin 3) × Fin (L a - w - 1)) ≃ {p : Placement L w // ¬ atLeaf p} :=
  { toFun := fun p => ⟨⟨p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩⟩,
      by have := p.2.isLt; change p.2.val + 1 ≠ L p.1 - w; omega⟩
    invFun := fun p => ⟨p.val.1, ⟨p.val.2.val, by
      have ht := p.val.2.isLt
      have hn := p.property
      change p.val.2.val + 1 ≠ L p.val.1 - w at hn
      omega⟩⟩
    left_inv := by rintro ⟨a, t⟩; rfl
    right_inv := by rintro ⟨⟨a, t⟩, ht⟩; rfl }

theorem leafPlacement_card (L : Fin 3 → ℕ) (w : ℕ) (hL : ∀ a, w < L a) :
    Fintype.card {p : Placement L w // atLeaf p} = 3 :=
  (Fintype.card_congr (leafPlacementEquiv L w hL)).symm

theorem interiorPlacement_card (L : Fin 3 → ℕ) (w : ℕ) :
    Fintype.card {p : Placement L w // ¬ atLeaf p} = ∑ a, (L a - w - 1) := by
  rw [← Fintype.card_congr (interiorPlacementEquiv L w), Fintype.card_sigma]
  simp only [Fintype.card_fin]

theorem interiorPlacement_card_eq (L K : Fin 3 → ℕ) (w : ℕ)
    (hL : ∀ a, w < L a) (hK : ∀ a, w < K a) (hs : (∑ a, L a) = ∑ a, K a) :
    Fintype.card {p : Placement L w // ¬ atLeaf p} =
      Fintype.card {p : Placement K w // ¬ atLeaf p} := by
  rw [interiorPlacement_card, interiorPlacement_card]
  have hl₀ := hL 0
  have hl₁ := hL 1
  have hl₂ := hL 2
  have hk₀ := hK 0
  have hk₁ := hK 1
  have hk₂ := hK 2
  simp [Fin.sum_univ_succ] at hs ⊢
  omega

def placementLeafEquiv (L K : Fin 3 → ℕ) (w : ℕ)
    (hL : ∀ a, w < L a) (hK : ∀ a, w < K a) :
    {p : Placement L w // atLeaf p} ≃ {p : Placement K w // atLeaf p} :=
  Fintype.equivOfCardEq (by rw [leafPlacement_card L w hL, leafPlacement_card K w hK])

def placementInteriorEquiv (L K : Fin 3 → ℕ) (w : ℕ)
    (hL : ∀ a, w < L a) (hK : ∀ a, w < K a) (hs : (∑ a, L a) = ∑ a, K a) :
    {p : Placement L w // ¬ atLeaf p} ≃ {p : Placement K w // ¬ atLeaf p} :=
  Fintype.equivOfCardEq (interiorPlacement_card_eq L K w hL hK hs)

def placementEquiv (L K : Fin 3 → ℕ) (w : ℕ)
    (hL : ∀ a, w < L a) (hK : ∀ a, w < K a) (hs : (∑ a, L a) = ∑ a, K a) :
    Placement L w ≃ Placement K w :=
  (Equiv.sumCompl (@atLeaf L w)).symm.trans
    ((Equiv.sumCongr (placementLeafEquiv L K w hL hK)
      (placementInteriorEquiv L K w hL hK hs)).trans (Equiv.sumCompl (@atLeaf K w)))

theorem placementEquiv_preserves_leaf (L K : Fin 3 → ℕ) (w : ℕ)
    (hL : ∀ a, w < L a) (hK : ∀ a, w < K a) (hs : (∑ a, L a) = ∑ a, K a)
    (p : Placement L w) : atLeaf (placementEquiv L K w hL hK hs p) ↔ atLeaf p := by
  by_cases hp : atLeaf p
  · have ht := (placementLeafEquiv L K w hL hK ⟨p, hp⟩).property
    have he : atLeaf (placementEquiv L K w hL hK hs p) := by
      simpa only [placementEquiv, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hp,
        Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl] using ht
    exact iff_of_true he hp
  · have ht := (placementInteriorEquiv L K w hL hK hs ⟨p, hp⟩).property
    have he : ¬ atLeaf (placementEquiv L K w hL hK hs p) := by
      simpa only [placementEquiv, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hp,
        Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr] using ht
    exact iff_of_false he hp

#print axioms interiorPlacement_card_eq
#print axioms placementEquiv_preserves_leaf
end
end ADComplete.SpiderGraph
