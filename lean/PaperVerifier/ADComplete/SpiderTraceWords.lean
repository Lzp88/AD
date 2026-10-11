import PaperVerifier.ADComplete.SpiderCenterChains
import PaperVerifier.ADComplete.SpiderArmWeights

/-! Complete short-word trace equality for actual finite spider graphs. -/
namespace ADComplete.SpiderGraph
noncomputable section
open ADClosedWalks
open scoped BigOperators

theorem trace_word_center_split (L : Fin 3 → ℕ) (w : List Bool) :
    Matrix.trace (wordMatrix (graph L) w) =
      (∑ p : CenterChain L w, lineWeight (fun v => (graph L).degree v) w p.val.val) +
      ∑ p : NonCenterChain L w, lineWeight (fun v => (graph L).degree v) w p.val.val := by
  classical
  rw [trace_word_flat_sum]
  exact (Fintype.sum_subtype_add_sum_subtype
    (fun p : FlatClosed (graph L).Adj w => ∃ i, p.val i = none)
    (fun p => lineWeight (fun v => (graph L).degree v) w p.val)).symm

theorem spider_short_word_trace_eq (L K : Fin 3 → ℕ) (m : ℕ) (hm : 2 ≤ m)
    (hL : ∀ a, m ≤ L a) (hK : ∀ a, m ≤ K a) (hs : (∑ a, L a) = ∑ a, K a)
    (w : List Bool) (hw : adjacencyCount w < 2 * m) :
    Matrix.trace (wordMatrix (graph L) w) = Matrix.trace (wordMatrix (graph K) w) := by
  rw [trace_word_center_split, trace_word_center_split,
    center_chain_sum L m hm hL w hw, center_chain_sum K m hm hK w hw,
    noncenter_chain_sum_eq L K m (by omega) w hw hL hK hs]

theorem left_lengths_ge (m : ℕ) : ∀ a, m ≤ leftLengths m a := by
  intro a
  fin_cases a <;> simp [leftLengths]

theorem right_lengths_ge (m : ℕ) : ∀ a, m ≤ rightLengths m a := by
  intro a
  fin_cases a <;> simp [rightLengths]

theorem witness_lengths_sum (m : ℕ) : (∑ a, leftLengths m a) = ∑ a, rightLengths m a := by
  have h := (witness_card_left m).trans (witness_card_right m).symm
  rw [card_vertices, card_vertices] at h
  omega

/-- The actual two nonisomorphic spider trees have identical traces for every
word with fewer than `2*m` A letters, with no bound on the number of D letters. -/
theorem witness_short_word_trace_eq (m : ℕ) (hm : 2 ≤ m) (w : List Bool)
    (hw : adjacencyCount w < 2 * m) :
    Matrix.trace (wordMatrix (graph (leftLengths m)) w) =
      Matrix.trace (wordMatrix (graph (rightLengths m)) w) :=
  spider_short_word_trace_eq _ _ m hm (left_lengths_ge m) (right_lengths_ge m)
    (witness_lengths_sum m) w hw

#print axioms spider_short_word_trace_eq
#print axioms witness_short_word_trace_eq
end
end ADComplete.SpiderGraph
