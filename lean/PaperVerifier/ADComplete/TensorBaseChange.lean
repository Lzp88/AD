import PaperVerifier.ADComplete.TensorMatrix
import PaperVerifier.ADComplete.RationalLineNormalization

/-! Scalar extension of the additive tensor matrix and the rational connection. -/
namespace ADComplete.TensorBaseChange

open Matrix Polynomial
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι σ F : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ] [CommRing F]

theorem tensorMatrix_map_action (f : ℝ →+* F) (B : Matrix ι ι ℝ)
    (w : (σ → ι) → F) :
    ((Rigidity.tensorMatrix B).map f).mulVec w =
      PluckerConnection.tensorAction (B.map f) w := by
  classical
  ext s
  change (∑ t, f (∑ k, ∑ j, B (s k) j *
      ((Pi.single t (1 : ℝ)) : (σ → ι) → ℝ) (Function.update s k j)) * w t) =
    ∑ k, ∑ j, f (B (s k) j) * w (Function.update s k j)
  simp_rw [map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [Pi.single_apply, eq_comm]

abbrev RF := RatFunc ℝ

def realEmbedding : ℝ →+* RF := (algebraMap ℝ[X] RF).comp Polynomial.C

theorem tensor_rational_connection (B H : Matrix ι ι ℝ) (w : (σ → ι) → RF) :
    (RationalLineNormalization.rationalConnection
      (Rigidity.tensorMatrix B) (Rigidity.tensorMatrix H)).mulVec w =
      PluckerConnection.tensorAction
        (RationalLineNormalization.rationalConnection B H) w := by
  classical
  have hB := tensorMatrix_map_action realEmbedding B w
  have hH := tensorMatrix_map_action realEmbedding H w
  ext s
  have hBi := congrFun hB s
  have hHi := congrFun hH s
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
    PluckerConnection.tensorAction, realEmbedding, RingHom.comp_apply] at hBi hHi
  simp only [RationalLineNormalization.rationalConnection, Matrix.mulVec, dotProduct,
    PluckerConnection.tensorAction, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div,
    ← Finset.sum_div]
  rw [hBi, hHi]

#print axioms tensorMatrix_map_action
#print axioms tensor_rational_connection

end
end ADComplete.TensorBaseChange
