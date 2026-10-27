import MultiSymmetric.Recurrence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

namespace MultiSymmetric.Recurrence
open scoped BigOperators
open Polynomial
noncomputable section
set_option autoImplicit false
variable {R : Type*} [Ring R]

@[simp] theorem poleProduct_one : poleProduct 1 = X := by
  simp [poleProduct]

@[simp] theorem poleQuotient_one (i : Fin 1) : poleQuotient 1 i = 1 := by
  fin_cases i
  simp [poleQuotient, Finset.univ_unique]

theorem row_one_step (κ : ℤ) (H K : R) (k : ℕ) :
    row 1 κ H (fun _ => K) (k+1) =
      C (κ : R) * X * (row 1 κ H (fun _ => K) k).derivative +
      C (κ : R) * X * C H * row 1 κ H (fun _ => K) k +
      C K * row 1 κ H (fun _ => K) k -
      C (((k : ℤ) * κ : ℤ) : R) * row 1 κ H (fun _ => K) k := by
  simp [row_succ, step, scalarPolynomial]

theorem coeff_X_derivative (p : R[X]) (j : ℕ) :
    (X * p.derivative).coeff j = (j : R) * p.coeff j := by
  cases j with
  | zero => simp
  | succ j =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      simpa using (Nat.cast_commute (j+1) (p.coeff (j+1))).eq.symm

theorem row_one_coeff (κ : ℤ) (H K : R) (k j : ℕ) :
    (row 1 κ H (fun _ => K) (k+1)).coeff j =
      (K + ((κ * ((j : ℤ) - k) : ℤ) : R)) *
        (row 1 κ H (fun _ => K) k).coeff j +
      (κ : R) * H *
        (if j = 0 then 0 else (row 1 κ H (fun _ => K) k).coeff (j-1)) := by
  rw [row_one_step]
  have hder : C (κ : R) * X * (row 1 κ H (fun _ => K) k).derivative =
      C (κ : R) * (X * (row 1 κ H (fun _ => K) k).derivative) := mul_assoc _ _ _
  have hh : C (κ : R) * X * C H * row 1 κ H (fun _ => K) k =
      C (κ : R) * (X * (C H * row 1 κ H (fun _ => K) k)) := by
    simp only [mul_assoc]
  rw [hder, hh]
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, coeff_X_derivative]
  have hcast : (((k : ℤ) * κ : ℤ) : R) = (κ : R) * (k : R) := by
    rw [Int.mul_comm]
    push_cast
    rfl
  rw [hcast]
  push_cast
  by_cases hj : j = 0
  · subst j
    simp only [Polynomial.coeff_X_mul_zero, if_true, Nat.cast_zero, zero_sub]
    noncomm_ring
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
      Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
    noncomm_ring

theorem row_one_coeff_zero (κ : ℤ) (H K : R) (j : ℕ) :
    (row 1 κ H (fun _ => K) 0).coeff j = if j = 0 then 1 else 0 := by
  simp [row, Polynomial.coeff_one]

#print axioms row_one_coeff
end
end MultiSymmetric.Recurrence

