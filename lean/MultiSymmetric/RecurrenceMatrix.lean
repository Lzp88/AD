import MultiSymmetric.Recurrence
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

namespace MultiSymmetric.Recurrence
open scoped BigOperators
open Polynomial Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Mat := Matrix ι ι ℝ

def coordinateAction (H : Mat (ι := ι)) (p : ι → ℝ[X]) : ι → ℝ[X] :=
  fun i => ∑ j, C (H i j) * p j

def act (p : (Mat (ι := ι))[X]) (v : ι → ℝ) : ι → ℝ[X] :=
  (matPolyEquiv.symm p).mulVec (fun j => C (v j))

theorem act_coeff (p : (Mat (ι := ι))[X]) (v : ι → ℝ) (i : ι) (j : ℕ) :
    (act p v i).coeff j = (p.coeff j).mulVec v i := by
  simp [act, Matrix.mulVec, dotProduct, Polynomial.finsetSum_coeff,
    Polynomial.coeff_mul_C]

theorem act_one (v : ι → ℝ) : act (1 : (Mat (ι := ι))[X]) v = fun i => C (v i) := by
  simp [act]

theorem act_add (p q : (Mat (ι := ι))[X]) (v : ι → ℝ) :
    act (p + q) v = act p v + act q v := by
  ext i j
  simp [act_coeff, Matrix.add_mulVec]

theorem act_sub (p q : (Mat (ι := ι))[X]) (v : ι → ℝ) :
    act (p - q) v = act p v - act q v := by
  ext i j
  simp [act_coeff, Matrix.sub_mulVec]

theorem act_sum {α : Type*} (t : Finset α) (p : α → (Mat (ι := ι))[X])
    (v : ι → ℝ) : act (∑ b ∈ t, p b) v = ∑ b ∈ t, act (p b) v := by
  ext i j
  simp [act_coeff, Polynomial.finsetSum_coeff, Matrix.sum_mulVec]

theorem act_C_mul (H : Mat (ι := ι)) (p : (Mat (ι := ι))[X]) (v : ι → ℝ) :
    act (C H * p) v = coordinateAction H (act p v) := by
  ext i j
  rw [act_coeff, Polynomial.coeff_C_mul, ← Matrix.mulVec_mulVec]
  simp [Polynomial.finsetSum_coeff, coordinateAction,
    Matrix.mulVec, dotProduct, act_coeff]

theorem act_scalar_mul (q : ℝ[X]) (p : (Mat (ι := ι))[X]) (v : ι → ℝ) :
    act (q.map (algebraMap ℝ (Mat (ι := ι))) * p) v = fun i => q * act p v i := by
  have heq : matPolyEquiv.symm (q.map (algebraMap ℝ (Mat (ι := ι)))) =
      q • (1 : Matrix ι ι ℝ[X]) := by
    apply matPolyEquiv.injective
    simp
  simp only [act, map_mul, heq, smul_mul_assoc, one_mul]
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

theorem scalarPolynomial_matrix (q : ℤ[X]) :
    scalarPolynomial (R := Mat (ι := ι)) q =
      (scalarPolynomial (R := ℝ) q).map (algebraMap ℝ (Mat (ι := ι))) := by
  symm
  exact scalarPolynomial_map (algebraMap ℝ (Mat (ι := ι))) q

theorem act_scalarPolynomial_mul (q : ℤ[X]) (p : (Mat (ι := ι))[X]) (v : ι → ℝ) :
    act (scalarPolynomial q * p) v =
      fun i => scalarPolynomial (R := ℝ) q * act p v i := by
  rw [scalarPolynomial_matrix]
  exact act_scalar_mul _ _ _

theorem act_derivative (p : (Mat (ι := ι))[X]) (v : ι → ℝ) :
    act p.derivative v = fun i => (act p v i).derivative := by
  ext i j
  simp only [act_coeff, Polynomial.coeff_derivative]
  rw [← Nat.cast_add_one, ← Matrix.mulVec_mulVec, Matrix.natCast_mulVec,
    Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem act_int_C_mul (z : ℤ) (p : (Mat (ι := ι))[X]) (v : ι → ℝ) :
    act (C (z : Mat (ι := ι)) * p) v = fun i => C (z : ℝ) * act p v i := by
  have heq : C (z : Mat (ι := ι)) = (C (z : ℝ)).map (algebraMap ℝ (Mat (ι := ι))) := by
    simp
  rw [heq]
  exact act_scalar_mul _ _ _


#print axioms act_coeff
#print axioms act_derivative
end
end MultiSymmetric.Recurrence

