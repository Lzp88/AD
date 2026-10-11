import PaperVerifier.ADComplete.TensorResidue
import PaperVerifier.ADComplete.PluckerConnection

/-! A genuine matrix for the additive tensor action and its self-adjoint interval. -/

namespace ADComplete.Rigidity

open Matrix
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

def tensorAddLinear (B : Matrix ι ι ℝ) : ((σ → ι) → ℝ) →ₗ[ℝ] ((σ → ι) → ℝ) where
  toFun := tensorAdd B
  map_add' u v := by
    ext s
    simp [tensorAdd, tensorSlot, mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    ext s
    simp [tensorAdd, tensorSlot, Finset.mul_sum, mul_left_comm]

def tensorMatrix (B : Matrix ι ι ℝ) : Matrix (σ → ι) (σ → ι) ℝ := by
  classical
  exact LinearMap.toMatrix' (tensorAddLinear B)

lemma tensorMatrix_mulVec (B : Matrix ι ι ℝ) (w : (σ → ι) → ℝ) :
    (tensorMatrix B).mulVec w = tensorAdd B w := by
  classical
  exact LinearMap.toMatrix'_mulVec (tensorAddLinear B) w

lemma tensorMatrix_action (B : Matrix ι ι ℝ) (w : (σ → ι) → ℝ) :
    (tensorMatrix B).mulVec w = ADComplete.PluckerConnection.tensorAction B w := by
  rw [tensorMatrix_mulVec]
  rfl

omit [Fintype σ] [DecidableEq σ] in
lemma pairing_single_left [DecidableEq ι] (i : ι) (v : ι → ℝ) : pairing (Pi.single i 1) v = v i := by
  classical
  simp [pairing, Pi.single_apply]

omit [Fintype σ] [DecidableEq σ] in
lemma matrix_symmetric_of_pairing (B : Matrix ι ι ℝ)
    (h : ∀ u v : ι → ℝ, pairing u (B.mulVec v) = pairing v (B.mulVec u)) : B.IsSymm := by
  classical
  ext i j
  have hij := h (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.mulVec_single_one, pairing_single_left, Matrix.col_apply] at hij
  exact hij.symm

theorem tensorMatrix_symmetric (B : Matrix ι ι ℝ) (hB : B.IsSymm) :
    (tensorMatrix (σ := σ) B).IsSymm := by
  apply matrix_symmetric_of_pairing
  intro u v
  rw [tensorMatrix_mulVec, tensorMatrix_mulVec]
  exact tensorAdd_symmetric B hB u v

theorem tensorMatrix_interval (B : Matrix ι ι ℝ) (lo hi : ℝ)
    (hB : ∀ u : ι → ℝ,
      lo * pairing u u ≤ pairing u (B.mulVec u) ∧
      pairing u (B.mulVec u) ≤ hi * pairing u u)
    (w : (σ → ι) → ℝ) :
    (Fintype.card σ : ℝ) * lo * pairing w w ≤ pairing w ((tensorMatrix B).mulVec w) ∧
      pairing w ((tensorMatrix B).mulVec w) ≤ (Fintype.card σ : ℝ) * hi * pairing w w := by
  rw [tensorMatrix_mulVec]
  exact tensorAdd_interval B lo hi hB w

#print axioms tensorMatrix_symmetric
#print axioms tensorMatrix_interval

end
end ADComplete.Rigidity
