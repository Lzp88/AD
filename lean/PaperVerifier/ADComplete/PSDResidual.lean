import Mathlib

/-! Actual fraction-free residuals, including singular Gram matrices. -/
namespace ADComplete.PSDResidual

open Matrix
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

def gram (K : Matrix ι σ ℝ) : Matrix σ σ ℝ := K.transpose * K

def residual (K : Matrix ι σ ℝ) (z : ι → ℝ) : ι → ℝ :=
  (gram K).det • z - K.mulVec ((gram K).adjugate.mulVec (K.transpose.mulVec z))

theorem residual_orthogonal (K : Matrix ι σ ℝ) (z : ι → ℝ) :
    K.transpose.mulVec (residual K z) = 0 := by
  rw [residual, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  change (gram K).det • K.transpose.mulVec z -
    (gram K * (gram K).adjugate).mulVec (K.transpose.mulVec z) = 0
  rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]

theorem residual_in_span (K : Matrix ι σ ℝ) (z : ι → ℝ)
    (S : Submodule ℝ (ι → ℝ)) (hK : LinearMap.range K.mulVecLin ≤ S) (hz : z ∈ S) :
    residual K z ∈ S := by
  apply S.sub_mem (S.smul_mem _ hz)
  exact hK ⟨_, rfl⟩

/-- Membership in the preceding column range makes the actual residual zero,
without any invertibility hypothesis. -/
theorem residual_zero_of_mem_range (K : Matrix ι σ ℝ) (z : ι → ℝ)
    (hz : z ∈ LinearMap.range K.mulVecLin) : residual K z = 0 := by
  obtain ⟨v, hv⟩ := hz
  change K.mulVec v = z at hv
  have hG : K.transpose.mulVec (K.mulVec v) = (gram K).mulVec v :=
    Matrix.mulVec_mulVec _ _ _
  have hadj : (gram K).adjugate.mulVec ((gram K).mulVec v) = (gram K).det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [← hv, residual, hG, hadj, Matrix.mulVec_smul, sub_self]

/-- The singular case uses the Gram kernel identity, rather than the false
claim that a singular matrix has zero adjugate. -/
theorem gram_singular_annihilates_adjugate (K : Matrix ι σ ℝ)
    (hdet : (gram K).det = 0) : K * (gram K).adjugate = 0 := by
  have hzero : gram K * (gram K).adjugate = 0 := by
    rw [Matrix.mul_adjugate, hdet, zero_smul]
  have hg : (K.conjTranspose * K) * (gram K).adjugate = 0 := by
    simpa [gram] using hzero
  exact (Matrix.conjTranspose_mul_self_mul_eq_zero K (gram K).adjugate).mp hg

theorem residual_zero_of_singular (K : Matrix ι σ ℝ) (z : ι → ℝ)
    (hdet : (gram K).det = 0) : residual K z = 0 := by
  rw [residual, hdet, zero_smul, Matrix.mulVec_mulVec,
    gram_singular_annihilates_adjugate K hdet, Matrix.zero_mulVec, sub_zero]

theorem gram_det_nonzero (K : Matrix ι σ ℝ) (hK : Function.Injective K.mulVec) :
    (gram K).det ≠ 0 := by
  have hpos : (gram K).PosDef := by
    simpa [gram] using Matrix.PosDef.conjTranspose_mul_self K hK
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det (gram K)).mp hpos.isUnit)

theorem residual_nonzero (K : Matrix ι σ ℝ) (z : ι → ℝ)
    (hK : Function.Injective K.mulVec) (hz : z ∉ LinearMap.range K.mulVecLin) :
    residual K z ≠ 0 := by
  intro hu
  have hd := gram_det_nonzero K hK
  have heq : (gram K).det • z =
      K.mulVec ((gram K).adjugate.mulVec (K.transpose.mulVec z)) :=
    sub_eq_zero.mp hu
  apply hz
  refine ⟨(gram K).det⁻¹ • (gram K).adjugate.mulVec (K.transpose.mulVec z), ?_⟩
  change K.mulVec _ = z
  rw [Matrix.mulVec_smul, ← heq, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem residual_column_pairing (K : Matrix ι σ ℝ) (z : ι → ℝ) (j : σ) :
    dotProduct (K.col j) (residual K z) = 0 := by
  exact congrFun (residual_orthogonal K z) j

theorem residual_pairing (K : Matrix ι σ ℝ) (z v : ι → ℝ)
    (hv : v ∈ LinearMap.range K.mulVecLin) : dotProduct v (residual K z) = 0 := by
  obtain ⟨c, rfl⟩ := hv
  change dotProduct (K.mulVec c) (residual K z) = 0
  rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec,
    residual_orthogonal, dotProduct_zero]

#print axioms residual_orthogonal
#print axioms residual_zero_of_mem_range
#print axioms gram_singular_annihilates_adjugate
#print axioms residual_nonzero

end
end ADComplete.PSDResidual
