import MultiSymmetric.RigidityBasic
import MultiSymmetric.DescentBasic
import PaperVerifier.ADComplete.TensorBaseChange
set_option autoImplicit false

/-! Descent of actual multi-pole invariant constant frames. -/
namespace MultiSymmetric.Descent
open Matrix Polynomial
open scoped BigOperators
open MultiSymmetric.Rigidity
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {τ ι σ : Type*} [Fintype τ] [Fintype ι] [Fintype σ] [DecidableEq σ]

theorem rationalConnection_mulVec (a : τ → ℝ) (B : τ → Matrix ι ι ℝ)
    (H : Matrix ι ι ℝ) (v : ι → RF) :
    (rationalConnection a B H).mulVec v =
      (H.map (algebraMap ℝ RF)).mulVec v +
        ∑ k, ((algebraMap ℝ[X] RF (X-C (a k)))⁻¹ •
          ((B k).map (algebraMap ℝ RF)).mulVec v) := by
  classical
  ext i
  simp only [rationalConnection, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    add_mul, Finset.sum_add_distrib, Finset.sum_mul, div_eq_mul_inv,
    Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem map_denom_div_factor (a : τ → ℝ) (k : τ) :
    algebraMap ℝ[X] RF (denom a) /
      algebraMap ℝ[X] RF (X-C (a k)) =
        algebraMap ℝ[X] RF (cofactor a k) := by
  have hn : algebraMap ℝ[X] RF (X-C (a k)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero (a k))
  rw [← factor_mul_cofactor a k, map_mul]
  exact mul_div_cancel_left₀ _ hn

def clearedConstantAction (a : τ → ℝ) (B : τ → Matrix ι ι ℝ)
    (H : Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ[X] := fun i =>
  denom a * C (H.mulVec v i) + ∑ k, (cofactor a k * C ((B k).mulVec v i))

theorem clearedConstantAction_identity (a : τ → ℝ) (B : τ → Matrix ι ι ℝ)
    (H : Matrix ι ι ℝ) (v : ι → ℝ) :
    (fun i => algebraMap ℝ[X] RF (clearedConstantAction a B H v i)) =
      algebraMap ℝ[X] RF (denom a) •
        ADComplete.DifferentialKrylov.connection ADComplete.RationalDerivative.derivative
          (rationalConnection a B H) (ADComplete.ConstantFrame.embed v) := by
  have hc : ADComplete.DifferentialKrylov.connection ADComplete.RationalDerivative.derivative
      (rationalConnection a B H) (ADComplete.ConstantFrame.embed v) =
      (rationalConnection a B H).mulVec (ADComplete.ConstantFrame.embed v) := by
    ext i
    change ADComplete.RationalDerivative.derivative (algebraMap ℝ RF (v i)) + _ = _
    rw [Derivation.map_algebraMap, zero_add]
  rw [hc, rationalConnection_mulVec]
  rw [ADComplete.ConstantFrame.map_mulVec]
  simp_rw [ADComplete.ConstantFrame.map_mulVec]
  ext i
  simp only [clearedConstantAction, map_add, map_mul, map_sum,
    ADComplete.ConstantFrame.map_C, ADComplete.ConstantFrame.embed,
    Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul,
    mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc]
  rw [← div_eq_mul_inv, map_denom_div_factor]

theorem real_invariance (a : τ → ℝ) (ha : Function.Injective a)
    (R : Matrix ι σ ℝ) (s₀ : σ → ι) (hR : R.submatrix s₀ id = 1)
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ)
    (hV : ∀ v ∈ LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin,
      ADComplete.DifferentialKrylov.connection ADComplete.RationalDerivative.derivative
        (rationalConnection a B H) v ∈
          LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin)
    (v : ι → ℝ) (hv : v ∈ LinearMap.range R.mulVecLin) :
    H.mulVec v ∈ LinearMap.range R.mulVecLin ∧
      ∀ k, (B k).mulVec v ∈ LinearMap.range R.mulVecLin := by
  classical
  let p := clearedConstantAction a B H v
  have hpoly : (fun i => algebraMap ℝ[X] RF (p i)) ∈
      LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin := by
    rw [show (fun i => algebraMap ℝ[X] RF (p i)) =
      algebraMap ℝ[X] RF (denom a) •
        ADComplete.DifferentialKrylov.connection ADComplete.RationalDerivative.derivative
          (rationalConnection a B H) (ADComplete.ConstantFrame.embed v) from
      clearedConstantAction_identity a B H v]
    exact (LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin).smul_mem _
      (hV _ (ADComplete.ConstantFrame.embed_mem R v hv))
  constructor
  · have hd : (denom a).coeff (Fintype.card τ) = 1 := by
      rw [← denom_natDegree a, Polynomial.coeff_natDegree]
      exact (denom_monic a).leadingCoeff
    have hq (k : τ) : (cofactor a k).coeff (Fintype.card τ) = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [cofactor_natDegree]
      have hp : 0 < Fintype.card τ := Fintype.card_pos_iff.mpr ⟨k⟩
      omega
    have he : (fun i => (p i).coeff (Fintype.card τ)) = H.mulVec v := by
      ext i
      simp [p, clearedConstantAction, Polynomial.coeff_mul_C, hd, hq]
    rw [← he]
    exact ADComplete.ConstantFrame.polynomial_coeff_mem R s₀ hR p hpoly _
  · intro k
    have he : (fun i => (p i).eval (a k)) =
        (cofactor a k).eval (a k) • (B k).mulVec v := by
      ext i
      simp only [p, clearedConstantAction, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_finsetSum, eval_denom, zero_mul, zero_add,
        Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_eq_single k
        (fun b _ hbk => by rw [eval_cofactor_other a b k hbk]; simp) (by simp)
    have hm := polynomial_eval_mem R s₀ hR p hpoly (a k)
    rw [he] at hm
    have hn := eval_cofactor_ne a ha k
    have hs := (LinearMap.range R.mulVecLin).smul_mem
      ((cofactor a k).eval (a k))⁻¹ hm
    simpa [smul_smul, hn] using hs

#print axioms real_invariance

theorem tensorAction_add (A C : Matrix ι ι RF) (w : (σ → ι) → RF) :
    ADComplete.PluckerConnection.tensorAction (A+C) w =
      ADComplete.PluckerConnection.tensorAction A w +
        ADComplete.PluckerConnection.tensorAction C w := by
  classical
  ext s
  simp [ADComplete.PluckerConnection.tensorAction, add_mul, Finset.sum_add_distrib]

theorem tensorAction_smul (c : RF) (A : Matrix ι ι RF) (w : (σ → ι) → RF) :
    ADComplete.PluckerConnection.tensorAction (c • A) w =
      c • ADComplete.PluckerConnection.tensorAction A w := by
  classical
  ext s
  simp [ADComplete.PluckerConnection.tensorAction, Finset.mul_sum, mul_assoc]

theorem tensorAction_sum (A : τ → Matrix ι ι RF) (w : (σ → ι) → RF) :
    ADComplete.PluckerConnection.tensorAction (∑ k, A k) w =
      ∑ k, ADComplete.PluckerConnection.tensorAction (A k) w := by
  classical
  ext s
  simp only [ADComplete.PluckerConnection.tensorAction, Finset.sum_apply, Matrix.sum_apply,
    Finset.sum_mul]
  calc
    (∑ l, (∑ j, (∑ k, (A k (s l) j * w (Function.update s l j))))) =
        ∑ l, (∑ k, (∑ j, (A k (s l) j * w (Function.update s l j)))) := by
      apply Finset.sum_congr rfl
      intro l _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

omit [Fintype ι] in
theorem rationalConnection_eq (a : τ → ℝ) (B : τ → Matrix ι ι ℝ)
    (H : Matrix ι ι ℝ) :
    rationalConnection a B H = H.map (algebraMap ℝ RF) +
      ∑ k, ((algebraMap ℝ[X] RF (X-C (a k)))⁻¹ • (B k).map (algebraMap ℝ RF)) := by
  classical
  ext i j
  simp [rationalConnection, Matrix.sum_apply, div_eq_mul_inv, mul_comm]

theorem tensor_rational_connection (a : τ → ℝ) (B : τ → Matrix ι ι ℝ)
    (H : Matrix ι ι ℝ) (w : (σ → ι) → RF) :
    (rationalConnection a (fun k => ADComplete.Rigidity.tensorMatrix (B k))
      (ADComplete.Rigidity.tensorMatrix H)).mulVec w =
      ADComplete.PluckerConnection.tensorAction (rationalConnection a B H) w := by
  rw [rationalConnection_mulVec]
  simp_rw [ADComplete.TensorBaseChange.tensorMatrix_map_action]
  rw [rationalConnection_eq, tensorAction_add, tensorAction_sum]
  simp_rw [tensorAction_smul]

#print axioms tensor_rational_connection
end
end MultiSymmetric.Descent
