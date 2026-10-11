import PaperVerifier.ADComplete.PSDResidual
import PaperVerifier.ADComplete.DifferentialKrylov

/-! The actual adjacent-sum square matrix has the required image and cyclic seed. -/
namespace ADComplete.PSDCyclic

open Matrix Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]

def chainColumn (u : ℕ → ι → ℝ) (j : ℕ) : ι → ℝ :=
  if j = 0 then u 0 else u (j-1) + u j

def chainMatrix (N : ℕ) (u : ℕ → ι → ℝ) : Matrix ι (Fin N) ℝ :=
  fun i j => chainColumn u j.val i

def squareMatrix (N : ℕ) (u : ℕ → ι → ℝ) : Matrix ι ι ℝ :=
  chainMatrix N u * (chainMatrix N u).transpose

def prefixSpan (N : ℕ) (u : ℕ → ι → ℝ) : Submodule ℝ (ι → ℝ) :=
  Submodule.span ℝ {v | ∃ j < N, v = u j}

omit [Fintype ι] in
theorem chain_range (N : ℕ) (u : ℕ → ι → ℝ) :
    LinearMap.range (chainMatrix N u).mulVecLin = prefixSpan N u := by
  classical
  apply le_antisymm
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    change chainColumn u j.val ∈ prefixSpan N u
    by_cases hj : j.val = 0
    · rw [chainColumn, if_pos hj]
      exact Submodule.subset_span ⟨0, by omega, rfl⟩
    · rw [chainColumn, if_neg hj]
      apply Submodule.add_mem
      · exact Submodule.subset_span ⟨j.val-1, by omega, rfl⟩
      · exact Submodule.subset_span ⟨j.val, j.isLt, rfl⟩
  · apply Submodule.span_le.mpr
    rintro v ⟨j, hj, rfl⟩
    have hcol (k : ℕ) (hk : k < N) : chainColumn u k ∈
        LinearMap.range (chainMatrix N u).mulVecLin := by
      refine ⟨Pi.single ⟨k,hk⟩ 1, ?_⟩
      exact Matrix.mulVec_single_one (chainMatrix N u) ⟨k,hk⟩
    induction j with
    | zero => simpa [chainColumn] using hcol 0 hj
    | succ j ih =>
      have hp := ih (by omega)
      have hc := hcol (j+1) hj
      simp only [chainColumn, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        if_false, Nat.add_sub_cancel] at hc
      have hs := (LinearMap.range (chainMatrix N u).mulVecLin).sub_mem hc hp
      change u (j+1) ∈ LinearMap.range (chainMatrix N u).mulVecLin
      simpa only [add_sub_cancel_left] using hs

theorem square_posSemidef (N : ℕ) (u : ℕ → ι → ℝ) :
    (squareMatrix N u).PosSemidef := by
  simpa [squareMatrix] using Matrix.posSemidef_self_mul_conjTranspose (chainMatrix N u)

theorem square_range (N : ℕ) (u : ℕ → ι → ℝ) :
    LinearMap.range (squareMatrix N u).mulVecLin = prefixSpan N u := by
  have hle : LinearMap.range (squareMatrix N u).mulVecLin ≤
      LinearMap.range (chainMatrix N u).mulVecLin := by
    rintro v ⟨x, rfl⟩
    refine ⟨(chainMatrix N u).transpose.mulVec x, ?_⟩
    exact Matrix.mulVec_mulVec x (chainMatrix N u) (chainMatrix N u).transpose
  have heq : LinearMap.range (squareMatrix N u).mulVecLin =
      LinearMap.range (chainMatrix N u).mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le hle
    change (chainMatrix N u).rank ≤ (squareMatrix N u).rank
    simpa only [squareMatrix, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.rank_self_mul_conjTranspose (chainMatrix N u)).ge
  exact heq.trans (chain_range N u)

#print axioms chain_range
#print axioms square_posSemidef
#print axioms square_range

end
end ADComplete.PSDCyclic
