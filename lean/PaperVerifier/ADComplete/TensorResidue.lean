import PaperVerifier.ADComplete.Rigidity

/-! Additive tensor action of a real matrix, in finite coordinates. -/

namespace ADComplete.Rigidity

open Matrix
open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

/-- Apply the residue in one tensor position. -/
def tensorSlot (B : Matrix ι ι ℝ) (k : σ) (w : (σ → ι) → ℝ) : (σ → ι) → ℝ :=
  fun s => ∑ j, B (s k) j * w (Function.update s k j)

/-- The additive tensor action, rather than the multiplicative tensor power. -/
def tensorAdd (B : Matrix ι ι ℝ) (w : (σ → ι) → ℝ) : (σ → ι) → ℝ :=
  fun s => ∑ k, tensorSlot B k w s

/-- Reassemble one tensor coordinate and the remaining coordinates. -/
def insertSlot (k : σ) (a : ι) (rest : {j : σ // j ≠ k} → ι) : σ → ι :=
  (Equiv.funSplitAt k ι).symm (a, rest)

omit [Fintype ι] [Fintype σ] in
lemma insertSlot_self (k : σ) (a : ι) (rest : {j : σ // j ≠ k} → ι) :
    insertSlot k a rest k = a := by simp [insertSlot, Equiv.funSplitAt, Equiv.piSplitAt]

omit [Fintype ι] [Fintype σ] in
lemma update_insertSlot (k : σ) (a b : ι) (rest : {j : σ // j ≠ k} → ι) :
    Function.update (insertSlot k a rest) k b = insertSlot k b rest := by
  funext j
  by_cases h : j = k
  · subst j
    simp [insertSlot_self]
  · simp [insertSlot, Equiv.funSplitAt, Equiv.piSplitAt, h]

lemma tensorSlot_pairing (B : Matrix ι ι ℝ) (k : σ) (u w : (σ → ι) → ℝ) :
    pairing u (tensorSlot B k w) =
      ∑ rest : ({j : σ // j ≠ k} → ι),
        pairing (fun a => u (insertSlot k a rest))
          (B.mulVec (fun a => w (insertSlot k a rest))) := by
  classical
  unfold pairing
  rw [← (Equiv.funSplitAt k ι).symm.sum_comp]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  apply Finset.sum_congr rfl
  intro a _
  simp only [insertSlot, tensorSlot, Matrix.mulVec, dotProduct]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [← insertSlot, ← insertSlot, insertSlot_self, update_insertSlot]

lemma pairing_decompose (k : σ) (u w : (σ → ι) → ℝ) :
    pairing u w =
      ∑ rest : ({j : σ // j ≠ k} → ι),
        pairing (fun a => u (insertSlot k a rest))
          (fun a => w (insertSlot k a rest)) := by
  classical
  unfold pairing
  rw [← (Equiv.funSplitAt k ι).symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma tensorSlot_symmetric (B : Matrix ι ι ℝ) (hB : B.IsSymm) (k : σ)
    (u w : (σ → ι) → ℝ) :
    pairing u (tensorSlot B k w) = pairing w (tensorSlot B k u) := by
  classical
  rw [tensorSlot_pairing, tensorSlot_pairing]
  apply Finset.sum_congr rfl
  intro rest _
  exact pairing_mulVec_swap B hB _ _

lemma pairing_tensorAdd (B : Matrix ι ι ℝ) (u w : (σ → ι) → ℝ) :
    pairing u (tensorAdd B w) = ∑ k, pairing u (tensorSlot B k w) := by
  unfold pairing tensorAdd
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem tensorAdd_symmetric (B : Matrix ι ι ℝ) (hB : B.IsSymm)
    (u w : (σ → ι) → ℝ) :
    pairing u (tensorAdd B w) = pairing w (tensorAdd B u) := by
  classical
  rw [pairing_tensorAdd, pairing_tensorAdd]
  apply Finset.sum_congr rfl
  intro k _
  exact tensorSlot_symmetric B hB k u w

/-- The residue interval grows by at most the number of tensor positions.
This proves the required additive-power bound in actual finite coordinates;
it can subsequently be restricted to alternating Pluecker coordinates. -/
theorem tensorAdd_interval (B : Matrix ι ι ℝ) (lo hi : ℝ)
    (hB : ∀ u : ι → ℝ,
      lo * pairing u u ≤ pairing u (B.mulVec u) ∧
      pairing u (B.mulVec u) ≤ hi * pairing u u)
    (w : (σ → ι) → ℝ) :
    (Fintype.card σ : ℝ) * lo * pairing w w ≤ pairing w (tensorAdd B w) ∧
      pairing w (tensorAdd B w) ≤ (Fintype.card σ : ℝ) * hi * pairing w w := by
  classical
  have hslot (k : σ) :
      lo * pairing w w ≤ pairing w (tensorSlot B k w) ∧
        pairing w (tensorSlot B k w) ≤ hi * pairing w w := by
    rw [tensorSlot_pairing, pairing_decompose k w w]
    constructor
    · simpa only [Finset.mul_sum] using
        Finset.sum_le_sum (fun rest (_ : rest ∈ Finset.univ) =>
          (hB (fun a => w (insertSlot k a rest))).1)
    · simpa only [Finset.mul_sum] using
        Finset.sum_le_sum (fun rest (_ : rest ∈ Finset.univ) =>
          (hB (fun a => w (insertSlot k a rest))).2)
  rw [pairing_tensorAdd]
  constructor
  · have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => (hslot k).1)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h
  · have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => (hslot k).2)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h

#print axioms tensorAdd_symmetric
#print axioms tensorAdd_interval

end ADComplete.Rigidity
