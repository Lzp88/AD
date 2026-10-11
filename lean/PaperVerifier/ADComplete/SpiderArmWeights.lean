import PaperVerifier.ADComplete.SpiderWordNormalization
import PaperVerifier.ADComplete.SpiderPlacements

/-! The normalization gives an actual degree-weight-preserving arm-chain bijection. -/
namespace ADComplete.SpiderGraph
noncomputable section
open ADClosedWalks
open scoped BigOperators

def armDegree (L : Fin 3 → ℕ) (a : Fin 3) (i : Fin (L a)) : ℤ :=
  if i.val + 1 = L a then 1 else 2

theorem armEmbed_degree (L : Fin 3 → ℕ) (a : Fin 3) (i : Fin (L a)) :
    ((graph L).degree (armEmbed L a i) : ℤ) = armDegree L a i := by
  rw [armEmbed, arm_degree]
  unfold armDegree
  split_ifs <;> rfl

def armChainWeight (L : Fin 3 → ℕ) (w : List Bool) (p : ArmChain L w) : ℤ :=
  lineWeight (armDegree L p.1) w p.2.val

theorem armChainMap_weight (L : Fin 3 → ℕ) (w : List Bool) (p : ArmChain L w) :
    lineWeight (fun v => (graph L).degree v) w (armChainMap L w p).val.val =
      armChainWeight L w p :=
  lineWeight_transport _ _ (armEmbed L p.1) (armEmbed_degree L p.1) w p.2.val

theorem shiftedWordArm_coordinate (L : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m)
    (w : List Bool) (hw : adjacencyCount w < 2 * m) (p : ShiftedWord L m w)
    (i : Fin (w.length + 1)) :
    (((shiftedWordArmEquiv L m hm w hw p).2.val i).val) =
      p.val.2.2.val + (p.val.1.val i).val := rfl

theorem shiftedWordArm_arm (L : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m)
    (w : List Bool) (hw : adjacencyCount w < 2 * m) (p : ShiftedWord L m w) :
    (shiftedWordArmEquiv L m hm w hw p).1 = p.val.2.1 := rfl

theorem shifted_degree_formula (L : Fin 3 → ℕ) (m n : ℕ) (hm : 0 < m)
    (p : ShiftedArmTuple L m n) (i : Fin (n + 1)) :
    armDegree L (shiftedTupleMap L m n hm p).1
      ((shiftedTupleMap L m n hm p).2.val i) =
    if atLeaf p.2 ∧ (p.1.val i).val = tupleWidth p.1 then 1 else 2 := by
  have ht : p.2.2.val < L p.2.1 - tupleWidth p.1 := p.2.2.isLt
  have hi := value_le_tupleWidth p.1 i
  have he : p.2.2.val + (p.1.val i).val + 1 = L p.2.1 ↔
      p.2.2.val + 1 = L p.2.1 - tupleWidth p.1 ∧ (p.1.val i).val = tupleWidth p.1 := by
    omega
  change (if p.2.2.val + (p.1.val i).val + 1 = L p.2.1 then (1 : ℤ) else 2) = _
  simp only [atLeaf, he]

def shiftedArmEquiv (L K : Fin 3 → ℕ) (m n : ℕ) (hm : 0 < m)
    (hL : ∀ a, m ≤ L a) (hK : ∀ a, m ≤ K a) (hs : (∑ a, L a) = ∑ a, K a) :
    ShiftedArmTuple L m n ≃ ShiftedArmTuple K m n :=
  Equiv.sigmaCongrRight (fun f => placementEquiv L K (tupleWidth f)
    (fun a => lt_of_lt_of_le (tupleWidth_lt hm f) (hL a))
    (fun a => lt_of_lt_of_le (tupleWidth_lt hm f) (hK a)) hs)

def shiftedWordEquiv (L K : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m) (w : List Bool)
    (hL : ∀ a, m ≤ L a) (hK : ∀ a, m ≤ K a) (hs : (∑ a, L a) = ∑ a, K a) :
    ShiftedWord L m w ≃ ShiftedWord K m w :=
  Equiv.subtypeEquiv (shiftedArmEquiv L K m w.length hm hL hK hs) (fun _ => Iff.rfl)

theorem shiftedWordEquiv_shape (L K : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m) (w : List Bool)
    (hL : ∀ a, m ≤ L a) (hK : ∀ a, m ≤ K a) (hs : (∑ a, L a) = ∑ a, K a)
    (p : ShiftedWord L m w) :
    (shiftedWordEquiv L K m hm w hL hK hs p).val.1 = p.val.1 := rfl

theorem shiftedWordEquiv_leaf (L K : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m) (w : List Bool)
    (hL : ∀ a, m ≤ L a) (hK : ∀ a, m ≤ K a) (hs : (∑ a, L a) = ∑ a, K a)
    (p : ShiftedWord L m w) :
    atLeaf (shiftedWordEquiv L K m hm w hL hK hs p).val.2 ↔ atLeaf p.val.2 :=
  placementEquiv_preserves_leaf L K (tupleWidth p.val.1) _ _ hs p.val.2

theorem lineWeight_pointwise_congr {V W : Type*} (d : V → ℤ) (e : W → ℤ)
    (w : List Bool) (x : Fin (w.length + 1) → V) (y : Fin (w.length + 1) → W)
    (h : ∀ i, d (x i) = e (y i)) : lineWeight d w x = lineWeight e w y := by
  induction w with
  | nil => rfl
  | cons b w ih =>
      cases b
      · exact ih (Fin.tail x) (Fin.tail y) (fun i => h i.succ)
      · change d (x 0) * lineWeight d w (Fin.tail x) =
          e (y 0) * lineWeight e w (Fin.tail y)
        rw [h 0, ih (Fin.tail x) (Fin.tail y) (fun i => h i.succ)]

theorem shiftedWordEquiv_weight (L K : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m) (w : List Bool)
    (hw : adjacencyCount w < 2 * m) (hL : ∀ a, m ≤ L a) (hK : ∀ a, m ≤ K a)
    (hs : (∑ a, L a) = ∑ a, K a) (p : ShiftedWord L m w) :
    armChainWeight L w (shiftedWordArmEquiv L m hm w hw p) =
      armChainWeight K w (shiftedWordArmEquiv K m hm w hw
        (shiftedWordEquiv L K m hm w hL hK hs p)) := by
  unfold armChainWeight
  apply lineWeight_pointwise_congr
  intro i
  change armDegree L (shiftedTupleMap L m w.length hm p.val).1
      ((shiftedTupleMap L m w.length hm p.val).2.val i) =
    armDegree K (shiftedTupleMap K m w.length hm
      (shiftedWordEquiv L K m hm w hL hK hs p).val).1
      ((shiftedTupleMap K m w.length hm
        (shiftedWordEquiv L K m hm w hL hK hs p).val).2.val i)
  rw [shifted_degree_formula, shifted_degree_formula]
  change (if atLeaf p.val.2 ∧ (p.val.1.val i).val = tupleWidth p.val.1 then 1 else 2) =
    (if atLeaf (shiftedWordEquiv L K m hm w hL hK hs p).val.2 ∧
      (p.val.1.val i).val = tupleWidth p.val.1 then 1 else 2)
  have he := shiftedWordEquiv_leaf L K m hm w hL hK hs p
  exact ite_cond_congr (propext (and_congr he.symm Iff.rfl))

theorem noncenter_sum_as_shifted (L : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m) (w : List Bool)
    (hw : adjacencyCount w < 2 * m) :
    (∑ p : NonCenterChain L w, lineWeight (fun v => (graph L).degree v) w p.val.val) =
      ∑ p : ShiftedWord L m w, armChainWeight L w (shiftedWordArmEquiv L m hm w hw p) := by
  symm
  apply Fintype.sum_equiv ((shiftedWordArmEquiv L m hm w hw).trans (armChainEquiv L w))
  intro p
  exact (armChainMap_weight L w (shiftedWordArmEquiv L m hm w hw p)).symm

theorem noncenter_chain_sum_eq (L K : Fin 3 → ℕ) (m : ℕ) (hm : 0 < m) (w : List Bool)
    (hw : adjacencyCount w < 2 * m) (hL : ∀ a, m ≤ L a) (hK : ∀ a, m ≤ K a)
    (hs : (∑ a, L a) = ∑ a, K a) :
    (∑ p : NonCenterChain L w, lineWeight (fun v => (graph L).degree v) w p.val.val) =
      ∑ p : NonCenterChain K w, lineWeight (fun v => (graph K).degree v) w p.val.val := by
  rw [noncenter_sum_as_shifted L m hm w hw, noncenter_sum_as_shifted K m hm w hw]
  exact Fintype.sum_equiv (shiftedWordEquiv L K m hm w hL hK hs) _ _
    (shiftedWordEquiv_weight L K m hm w hw hL hK hs)

#print axioms noncenter_chain_sum_eq
end
end ADComplete.SpiderGraph
