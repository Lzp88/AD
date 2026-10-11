import PaperVerifier.ADComplete.Spanning
import PaperVerifier.ADComplete.PolynomialLine
import PaperVerifier.ADComplete.RationalLineNormalization
import PaperVerifier.ADComplete.DifferentialKrylov

/-! Polynomial coefficients of the actual fixed probe recurrence. -/

namespace ADComplete.Spanning

open Matrix Polynomial
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

def probePolynomial (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ)
    (k : ℕ) : ι → ℝ[X] := fun i =>
  ∑ j ∈ Finset.range (k + 1), monomial j (probeVector κ H K v k j i)

theorem probePolynomial_coeff (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ)
    (k j : ℕ) (i : ι) :
    (probePolynomial κ H K v k i).coeff j = probeVector κ H K v k j i := by
  by_cases hj : j < k + 1
  · simp [probePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hj]
  · have hout := probeVector_outside κ H K v k j (by omega)
    simp [probePolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      hj, hout]

theorem probePolynomial_zero (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) :
    probePolynomial κ H K v 0 i = C (v i) := by
  simp [probePolynomial, probeVector]

lemma coeff_X_derivative (p : ℝ[X]) (j : ℕ) :
    (X * p.derivative).coeff j = (j : ℝ) * p.coeff j := by
  cases j with
  | zero => simp
  | succ j => rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]; push_cast; ring

/-- The triangular recurrence is the coefficient expansion of the scaled
polynomial connection, including the derivative correction term. -/
theorem probePolynomial_step (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ)
    (k : ℕ) (i : ι) :
    probePolynomial κ H K v (k + 1) i =
      Rigidity.polynomialAction K (probePolynomial κ H K v k) i +
      C κ * (X * (probePolynomial κ H K v k i).derivative -
        C (k : ℝ) * probePolynomial κ H K v k i) +
      C κ * X * Rigidity.polynomialAction H (probePolynomial κ H K v k) i := by
  ext j
  rw [probePolynomial_coeff]
  have haction (M : Matrix ι ι ℝ) (t : ℕ) :
      (Rigidity.polynomialAction M (probePolynomial κ H K v k) i).coeff t =
        M.mulVec (probeVector κ H K v k t) i := by
    simp [Rigidity.polynomialAction, Polynomial.finsetSum_coeff,
      probePolynomial_coeff, Matrix.mulVec, dotProduct]
  rw [show C κ * X * Rigidity.polynomialAction H (probePolynomial κ H K v k) i =
      C κ * (X * Rigidity.polynomialAction H (probePolynomial κ H K v k) i) by ring]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
    coeff_X_derivative, haction, probePolynomial_coeff]
  change probeVector κ H K v (k + 1) j i = _
  by_cases hj : j = 0
  · subst j
    simp [probeVector]
    ring
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [Polynomial.coeff_X_mul, haction, probeVector, Nat.succ_ne_zero,
      ↓reduceIte, Nat.succ_sub_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

#print axioms probePolynomial_coeff
#print axioms probePolynomial_step

end
end ADComplete.Spanning
