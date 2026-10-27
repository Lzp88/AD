import MultiSymmetric.RecurrenceMatrix
import MultiSymmetric.Krylov

namespace MultiSymmetric.Recurrence
open scoped BigOperators
open Polynomial Matrix
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalarProduct_eq_denom (s : ℕ) :
    scalarPolynomial (R := ℝ) (poleProduct s) =
      Rigidity.denom (fun i : Fin s => (i.val : ℝ)) := by
  simp [scalarPolynomial, poleProduct, Rigidity.denom, Polynomial.map_prod]

theorem scalarQuotient_eq_cofactor (s : ℕ) (i : Fin s) :
    scalarPolynomial (R := ℝ) (poleQuotient s i) =
      Rigidity.cofactor (fun j : Fin s => (j.val : ℝ)) i := by
  classical
  unfold scalarPolynomial poleQuotient Rigidity.cofactor
  rw [Polynomial.map_prod]
  apply Finset.prod_congr (by ext j; simp)
  intro j hj
  simp

theorem scalarProduct_derivative_eq (s : ℕ) :
    scalarPolynomial (R := ℝ) (poleProduct s).derivative =
      (Rigidity.denom (fun i : Fin s => (i.val : ℝ))).derivative := by
  simpa [scalarPolynomial] using congrArg Polynomial.derivative (scalarProduct_eq_denom s)

theorem row_act_eq_polynomialVector (s : ℕ) (κ : ℤ)
    (H : Mat (ι := ι)) (A : Fin s → Mat (ι := ι)) (v : ι → ℝ) (k : ℕ) :
    act (row s κ H A k) v =
      Krylov.polynomialVector (fun i : Fin s => (i.val : ℝ)) (κ : ℝ) H A v k := by
  induction k with
  | zero => exact act_one v
  | succ k ih =>
      rw [row_succ, step, Krylov.polynomialVector]
      simp only [mul_assoc, act_add, act_sub, act_sum, act_int_C_mul]
      simp only [act_scalarPolynomial_mul, act_C_mul, act_derivative]
      have hd : (scalarPolynomial (R := Mat (ι := ι)) (poleProduct s)).derivative =
          scalarPolynomial (R := Mat (ι := ι)) (poleProduct s).derivative := by
        simp [scalarPolynomial]
      simp only [hd, act_scalarPolynomial_mul]
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, ih,
        scalarProduct_eq_denom, scalarQuotient_eq_cofactor, scalarProduct_derivative_eq]
      simp only [coordinateAction, ADComplete.Rigidity.polynomialAction]
      push_cast
      ring

theorem row_coeff_mulVec (s : ℕ) (κ : ℤ)
    (H : Mat (ι := ι)) (A : Fin s → Mat (ι := ι)) (v : ι → ℝ)
    (k j : ℕ) (i : ι) :
    ((row s κ H A k).coeff j).mulVec v i =
      (Krylov.polynomialVector (fun b : Fin s => (b.val : ℝ)) (κ : ℝ) H A v k i).coeff j := by
  rw [← act_coeff, row_act_eq_polynomialVector]

theorem universal_probe_response (s N : ℕ)
    (H : Mat (ι := ι)) (A : Fin s → Mat (ι := ι)) (v : ι → ℝ) (idx : Index s N) :
    (FreeAlgebra.lift ℤ (Fin.cases H A) (probe s N idx)).mulVec v =
      fun i => (Krylov.polynomialVector (fun b : Fin s => (b.val : ℝ))
        (((s : ℤ) * (N : ℤ)^2 : ℤ) : ℝ) H A v idx.1.val i).coeff idx.2.val := by
  have hm := universalRow_evaluate s N idx.1.val (Fin.cases H A)
  have hc : FreeAlgebra.lift ℤ (Fin.cases H A)
      ((universalRow s N idx.1.val).coeff idx.2.val) =
      (row s ((s : ℤ) * (N : ℤ)^2) H A idx.1.val).coeff idx.2.val := by
    simpa using
      congrArg (fun p : (Mat (ι := ι))[X] => p.coeff idx.2.val) hm
  ext i
  change (FreeAlgebra.lift ℤ (Fin.cases H A)
    ((universalRow s N idx.1.val).coeff idx.2.val)).mulVec v i = _
  rw [hc]
  exact row_coeff_mulVec s ((s : ℤ) * (N : ℤ)^2) H A v idx.1.val idx.2.val i

#print axioms row_coeff_mulVec
#print axioms universal_probe_response
end
end MultiSymmetric.Recurrence

