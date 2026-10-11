import PaperVerifier.ADComplete.PSDCyclic

/-! The actual square matrix advances through an orthogonal vector prefix. -/
namespace ADComplete.PSDCyclic

open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

theorem square_action (N : ℕ) (u : ℕ → ι → ℝ) (v : ι → ℝ) :
    (squareMatrix N u).mulVec v = ∑ j : Fin N,
      dotProduct (chainColumn u j.val) v • chainColumn u j.val := by
  rw [squareMatrix, ← Matrix.mulVec_mulVec]
  ext i
  simp only [Matrix.mulVec, dotProduct, chainMatrix, Matrix.transpose_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [Fintype ι] in
lemma prefix_mem (u : ℕ → ι → ℝ) {N k : ℕ} (hk : k < N) :
    u k ∈ prefixSpan N u := Submodule.subset_span ⟨k,hk,rfl⟩

omit [Fintype ι] in
lemma chainColumn_mem (u : ℕ → ι → ℝ) {N k : ℕ} (hk : k < N) :
    chainColumn u k ∈ prefixSpan N u := by
  unfold chainColumn
  split_ifs with h
  · exact prefix_mem u (by omega)
  · exact Submodule.add_mem _ (prefix_mem u (by omega)) (prefix_mem u hk)

/-- Modulo all preceding vectors, multiplying the k-th vector by the actual
sum of squares produces its successor with the nonzero squared-norm
coefficient. No tridiagonal formula is assumed. -/
theorem square_next_mod_prefix (N : ℕ) (u : ℕ → ι → ℝ)
    (horth : ∀ i j : ℕ, i ≠ j → dotProduct (u i) (u j) = 0)
    (k : ℕ) (hk : k+1 < N) :
    (squareMatrix N u).mulVec (u k) - dotProduct (u k) (u k) • u (k+1) ∈
      prefixSpan (k+1) u := by
  classical
  let f : Fin N → ι → ℝ := fun j =>
    dotProduct (chainColumn u j.val) (u k) • chainColumn u j.val
  let j₀ : Fin N := ⟨k+1,hk⟩
  have hnext : f j₀ = dotProduct (u k) (u k) • (u k + u (k+1)) := by
    simp only [f, j₀, chainColumn, Nat.add_eq_zero_iff, Nat.one_ne_zero,
      and_false, if_false, Nat.add_sub_cancel, add_dotProduct]
    rw [horth (k+1) k (by omega), add_zero]
  have hother : (∑ j ∈ Finset.univ.erase j₀, f j) ∈ prefixSpan (k+1) u := by
    apply Submodule.sum_mem
    intro j hj
    have hne := (Finset.mem_erase.mp hj).1
    by_cases hsmall : j.val ≤ k
    · exact Submodule.smul_mem _ _ (chainColumn_mem u (by omega))
    · have hfuture : k+1 < j.val := by
        have hnv : j.val ≠ k+1 := fun hh => hne (Fin.ext hh)
        omega
      have hzero : dotProduct (chainColumn u j.val) (u k) = 0 := by
        rw [chainColumn, if_neg (by omega), add_dotProduct,
          horth (j.val-1) k (by omega), horth j.val k (by omega), add_zero]
      simp only [f, hzero, zero_smul]
      exact Submodule.zero_mem _
  have hsum := Finset.sum_erase_add Finset.univ f (Finset.mem_univ j₀)
  rw [square_action]
  change (∑ j : Fin N, f j) - dotProduct (u k) (u k) • u (k+1) ∈ _
  rw [← hsum, hnext, smul_add, ← add_assoc, add_sub_cancel_right]
  exact Submodule.add_mem _ hother (Submodule.smul_mem _ _ (prefix_mem u (by omega)))

#print axioms square_action
#print axioms square_next_mod_prefix

end
end ADComplete.PSDCyclic
