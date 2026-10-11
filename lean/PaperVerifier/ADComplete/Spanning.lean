import Mathlib

/-! Actual seed vectors and the fixed triangular recurrence. -/

namespace ADComplete.Spanning

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Evaluate an adjacency-degree word on an arbitrary prescribed seed. -/
def wordVector (H K : Matrix ι ι ℝ) (v : ι → ℝ) : List Bool → (ι → ℝ)
  | [] => v
  | false :: w => H.mulVec (wordVector H K v w)
  | true :: w => K.mulVec (wordVector H K v w)

/-- The actual joint cyclic module, including the empty word. -/
def jointModule (H K : Matrix ι ι ℝ) (v : ι → ℝ) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ (Set.range (wordVector H K v))

lemma wordVector_mem (H K : Matrix ι ι ℝ) (v : ι → ℝ) (w : List Bool) :
    wordVector H K v w ∈ jointModule H K v :=
  Submodule.subset_span ⟨w, rfl⟩

lemma seed_mem (H K : Matrix ι ι ℝ) (v : ι → ℝ) : v ∈ jointModule H K v :=
  wordVector_mem H K v []

lemma jointModule_H (H K : Matrix ι ι ℝ) (v x : ι → ℝ)
    (hx : x ∈ jointModule H K v) : H.mulVec x ∈ jointModule H K v := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact wordVector_mem H K v (false :: w)
  | zero => simpa only [Matrix.mulVec_zero] using (jointModule H K v).zero_mem
  | add y z _ _ hy hz =>
      simpa only [Matrix.mulVec_add] using (jointModule H K v).add_mem hy hz
  | smul a y _ hy =>
      simpa only [Matrix.mulVec_smul] using (jointModule H K v).smul_mem a hy

lemma jointModule_K (H K : Matrix ι ι ℝ) (v x : ι → ℝ)
    (hx : x ∈ jointModule H K v) : K.mulVec x ∈ jointModule H K v := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨w, rfl⟩ := hy
      exact wordVector_mem H K v (true :: w)
  | zero => simpa only [Matrix.mulVec_zero] using (jointModule H K v).zero_mem
  | add y z _ _ hy hz =>
      simpa only [Matrix.mulVec_add] using (jointModule H K v).add_mem hy hz
  | smul a y _ hy =>
      simpa only [Matrix.mulVec_smul] using (jointModule H K v).smul_mem a hy

/-- The fixed triangular vectors, with the out-of-range zero convention.
The central scale is arbitrary; the submitted construction takes it to be N². -/
def probeVector (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ) : ℕ → ℕ → (ι → ℝ)
  | 0, j => if j = 0 then v else 0
  | k + 1, j => K.mulVec (probeVector κ H K v k j) +
      (κ * ((j : ℝ) - (k : ℝ))) • probeVector κ H K v k j +
      κ • H.mulVec (if j = 0 then 0 else probeVector κ H K v k (j - 1))

theorem probeVector_mem_jointModule (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ)
    (k j : ℕ) : probeVector κ H K v k j ∈ jointModule H K v := by
  induction k generalizing j with
  | zero =>
      by_cases hj : j = 0
      · simpa [probeVector, hj] using seed_mem H K v
      · simp [probeVector, hj]
  | succ k ih =>
      unfold probeVector
      apply (jointModule H K v).add_mem
      · exact (jointModule H K v).add_mem
          (jointModule_K H K v _ (ih j))
          ((jointModule H K v).smul_mem _ (ih j))
      · apply (jointModule H K v).smul_mem
        apply jointModule_H
        split_ifs
        · exact (jointModule H K v).zero_mem
        · exact ih (j - 1)

theorem probeVector_outside (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ)
    (k j : ℕ) (hj : k < j) : probeVector κ H K v k j = 0 := by
  induction k generalizing j with
  | zero => simp [probeVector, show j ≠ 0 by omega]
  | succ k ih =>
      have hj₀ : j ≠ 0 := by omega
      simp [probeVector, ih j (by omega), hj₀, ih (j - 1) (by omega)]

theorem triangular_span_le (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ) (N : ℕ) :
    Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k, z = probeVector κ H K v k j}
      ≤ jointModule H K v := by
  apply Submodule.span_le.mpr
  rintro z ⟨k, _, j, _, rfl⟩
  exact probeVector_mem_jointModule κ H K v k j

#print axioms probeVector_mem_jointModule
#print axioms triangular_span_le

end ADComplete.Spanning
