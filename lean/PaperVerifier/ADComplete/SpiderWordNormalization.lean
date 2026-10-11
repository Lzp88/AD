import PaperVerifier.ADComplete.NormalizedArmTuples

/-! The tuple normalization preserves the literal A/D transition and closure tests. -/
namespace ADComplete.SpiderGraph
noncomputable section
open ADClosedWalks

def natCoordAdj (i j : ℕ) : Prop := i + 1 = j ∨ j + 1 = i

theorem coordinate_shift_closed_iff {l m : ℕ} (w : List Bool)
    (x : Fin (w.length + 1) → Fin m) (y : Fin (w.length + 1) → Fin l)
    (t : ℕ) (hy : ∀ i, (y i).val = t + (x i).val) :
    (lineValid (@coordAdj l) w y ∧ finish w y = y 0) ↔
      (lineValid (@coordAdj m) w x ∧ finish w x = x 0) := by
  have hf : (fun i : Fin (w.length + 1) => (y i).val) =
      (fun z : ℕ => t + z) ∘ (fun i => (x i).val) := funext hy
  have hadd : Function.Injective (fun z : ℕ => t + z) := by
    intro i j hij
    change t + i = t + j at hij
    omega
  have hrel (i j : ℕ) : natCoordAdj (t + i) (t + j) ↔ natCoordAdj i j := by
    change (t + i + 1 = t + j ∨ t + j + 1 = t + i) ↔ (i + 1 = j ∨ j + 1 = i)
    omega
  calc
    _ ↔ (lineValid natCoordAdj w (Fin.val ∘ y) ∧
        finish w (Fin.val ∘ y) = (Fin.val ∘ y) 0) :=
      (flatClosed_embedding_iff (@coordAdj l) natCoordAdj Fin.val Fin.val_injective
        (fun _ _ => Iff.rfl) w y).symm
    _ ↔ (lineValid natCoordAdj w (Fin.val ∘ x) ∧
        finish w (Fin.val ∘ x) = (Fin.val ∘ x) 0) := by
      change (lineValid natCoordAdj w (fun i => (y i).val) ∧
          finish w (fun i => (y i).val) = (y 0).val) ↔ _
      change (lineValid natCoordAdj w (fun i => (y i).val) ∧
          finish w (fun i => (y i).val) = (fun i => (y i).val) 0) ↔ _
      rw [hf]
      exact flatClosed_embedding_iff natCoordAdj natCoordAdj (fun z => t + z)
        hadd hrel w (Fin.val ∘ x)
    _ ↔ _ := flatClosed_embedding_iff (@coordAdj m) natCoordAdj Fin.val Fin.val_injective
      (fun _ _ => Iff.rfl) w x

def shapeWordValid (m : ℕ) (w : List Bool) (f : NormalizedTuple m w.length) : Prop :=
  lineValid (@coordAdj m) w f.val ∧ finish w f.val = f.val 0

def boundedWordValid (L : Fin 3 → ℕ) (m : ℕ) (w : List Bool)
    (p : BoundedArmTuple L m w.length) : Prop :=
  lineValid (@coordAdj (L p.1)) w p.2.val ∧ finish w p.2.val = p.2.val 0

theorem shifted_word_valid_iff (L : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m) (w : List Bool)
    (p : ShiftedArmTuple L m w.length) :
    boundedWordValid L m w (shiftedTupleMap L m w.length hm p) ↔ shapeWordValid m w p.1 :=
  coordinate_shift_closed_iff w p.1.val _ p.2.2.val (fun _ => rfl)

theorem arm_chain_span (L : Fin 3 → ℕ) (m : ℕ) (w : List Bool)
    (hw : adjacencyCount w < 2 * m) (p : ArmChain L w) (i j : Fin (w.length + 1)) :
    (p.2.val i).val - (p.2.val j).val < m := by
  let y : Fin (w.length + 1) → Vertex L := armEmbed L p.1 ∘ p.2.val
  have hv : lineValid (graph L).Adj w y ∧ finish w y = y 0 :=
    (flatClosed_embedding_iff _ _ _ (armEmbed_injective L p.1)
      (armEmbed_adj L p.1) w p.2.val).mpr p.2.property
  have hx : valid (graph L) w (y 0) (y 0) (Fin.tail y) :=
    (valid_flat _ _ _ _ _).mpr (by simpa only [Fin.cons_self_tail] using hv)
  have h := short_word_height_span L m w hw (y 0) (Fin.tail y) hx j i
  rw [Fin.cons_self_tail] at h
  change ((p.2.val i).val + 1) - ((p.2.val j).val + 1) < m at h
  simpa only [Nat.add_sub_add_right] using h

def armBoundedWordEquiv (L : Fin 3 → ℕ) (m : ℕ) (w : List Bool)
    (hw : adjacencyCount w < 2 * m) :
    ArmChain L w ≃ {p : BoundedArmTuple L m w.length // boundedWordValid L m w p} :=
  { toFun := fun p => ⟨⟨p.1, ⟨p.2.val, arm_chain_span L m w hw p⟩⟩, p.2.property⟩
    invFun := fun p => ⟨p.val.1, ⟨p.val.2.val, p.property⟩⟩
    left_inv := by rintro ⟨a, ⟨q, hq⟩⟩; rfl
    right_inv := by rintro ⟨⟨a, ⟨q, hs⟩⟩, hv⟩; rfl }

def ShiftedWord (L : Fin 3 → ℕ) (m : ℕ) (w : List Bool) :=
  {p : ShiftedArmTuple L m w.length // shapeWordValid m w p.1}

instance (L : Fin 3 → ℕ) (m : ℕ) (w : List Bool) : Fintype (ShiftedWord L m w) := by
  classical
  unfold ShiftedWord
  infer_instance

def shiftedWordArmEquiv (L : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m) (w : List Bool)
    (hw : adjacencyCount w < 2 * m) : ShiftedWord L m w ≃ ArmChain L w :=
  (Equiv.subtypeEquiv (shiftedTupleEquiv L m w.length hm)
    (fun p => (shifted_word_valid_iff L m hm w p).symm)).trans
      (armBoundedWordEquiv L m w hw).symm

#print axioms shiftedWordArmEquiv
end
end ADComplete.SpiderGraph
