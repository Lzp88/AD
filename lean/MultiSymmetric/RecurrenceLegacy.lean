import MultiSymmetric.RecurrenceSpecialization
import PaperVerifier.CircuitAudit.Degrees

namespace MultiSymmetric.Recurrence
open Polynomial
noncomputable section
set_option autoImplicit false
variable {R : Type*} [Ring R]

open CircuitAudit.Degrees

theorem row_one_eq_original (N k j : ℕ) (H K : R) :
    (row 1 ((N : ℤ)^2) H (fun _ => K) k).coeff j =
      (CircuitAudit.Degrees.probe N k j).eval H K := by
  induction k generalizing j with
  | zero =>
      by_cases hj : j = 0 <;>
        simp [CircuitAudit.Degrees.probe,
          CircuitAudit.Degrees.Expr.eval, Polynomial.coeff_one, hj]
  | succ k ih =>
      rw [row_one_coeff, ih]
      by_cases hbound : j ≤ k
      · by_cases hj : j = 0
        · subst j
          simp [CircuitAudit.Degrees.probe, CircuitAudit.Degrees.Expr.eval,
            hbound, zsmul_eq_mul]
        · have hjpos : 0 < j := by omega
          simp [CircuitAudit.Degrees.probe, CircuitAudit.Degrees.Expr.eval,
            hbound, hj, hjpos, ih,
            zsmul_eq_mul, mul_assoc]
      · have hz : (row 1 ((N : ℤ)^2) H (fun _ => K) k).coeff j = 0 :=
          row_coeff_outside _ _ _ _ k j (by omega)
        rw [ih] at hz
        have hj : j ≠ 0 := by omega
        have hjpos : 0 < j := by omega
        simp [CircuitAudit.Degrees.probe, CircuitAudit.Degrees.Expr.eval,
          hbound, hj, hjpos, ih, hz,
          zsmul_eq_mul, mul_assoc]


#print axioms row_one_eq_original
end
end MultiSymmetric.Recurrence

