import PaperVerifier.ADComplete.Rigidity

/-! Extracting the actual coefficient equations of a polynomial connection line. -/

namespace ADComplete.Rigidity

noncomputable section

open Polynomial Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def coefficientVector (w : ι → ℝ[X]) (k : ℕ) : ι → ℝ := fun i => (w i).coeff k

def polynomialAction (B : Matrix ι ι ℝ) (w : ι → ℝ[X]) : ι → ℝ[X] :=
  fun i => ∑ j, C (B i j) * w j

lemma coefficient_polynomialAction (B : Matrix ι ι ℝ) (w : ι → ℝ[X]) (k : ℕ) :
    coefficientVector (polynomialAction B w) k = B.mulVec (coefficientVector w k) := by
  ext i
  simp [coefficientVector, polynomialAction, Matrix.mulVec, dotProduct]

/-- An actual polynomial line with an affine scalar connection coefficient has
degree zero in a residue interval of width less than one. The primitive-vector
and rational-to-polynomial reductions are separate algebraic lemmas. -/
theorem affine_polynomial_line_degree_zero
    (B H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi α β : ℝ) (hgap : hi - lo < 1)
    (hB : ∀ u : ι → ℝ,
      lo * pairing u u ≤ pairing u (B.mulVec u) ∧
      pairing u (B.mulVec u) ≤ hi * pairing u u)
    (w : ι → ℝ[X]) (ell : ℕ)
    (hdegree : ∀ i, (w i).natDegree ≤ ell)
    (hconstant : coefficientVector w 0 ≠ 0)
    (hleading : coefficientVector w ell ≠ 0)
    (hline : ∀ i,
      X * (w i).derivative + polynomialAction B w i + X * polynomialAction H w i =
        (C α + X * C β) * w i) : ell = 0 := by
  cases ell with
  | zero => rfl
  | succ m =>
      have hvanish (i : ι) : (w i).coeff (m + 1 + 1) = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdegree i) (Nat.lt_succ_self _))
      have hBvanish : coefficientVector (polynomialAction B w) (m + 1 + 1) = 0 := by
        rw [coefficient_polynomialAction]
        have hw : coefficientVector w (m + 1 + 1) = 0 := funext hvanish
        rw [hw, Matrix.mulVec_zero]
      have hzero : B.mulVec (coefficientVector w 0) = α • coefficientVector w 0 := by
        rw [← coefficient_polynomialAction]
        ext i
        have h := congrArg (fun p : ℝ[X] => p.coeff 0) (hline i)
        simpa only [add_mul, mul_assoc, coeff_add, coeff_X_mul_zero, coeff_C_mul,
          zero_add, add_zero, coefficientVector, Pi.smul_apply, smul_eq_mul] using h
      have htop : H.mulVec (coefficientVector w (m + 1)) =
          β • coefficientVector w (m + 1) := by
        rw [← coefficient_polynomialAction]
        ext i
        have h := congrArg (fun p : ℝ[X] => p.coeff (m + 1 + 1)) (hline i)
        have hb := congrFun hBvanish i
        simp only [coefficientVector, Pi.zero_apply] at hb
        simpa only [add_mul, mul_assoc, coeff_add, coeff_X_mul, coeff_C_mul, coeff_derivative,
          hvanish, hb, zero_mul, mul_zero, zero_add, add_zero,
          coefficientVector, Pi.smul_apply, smul_eq_mul] using h
      have hnext : ((m + 1 : ℕ) : ℝ) • coefficientVector w (m + 1) +
          B.mulVec (coefficientVector w (m + 1)) + H.mulVec (coefficientVector w m) =
          α • coefficientVector w (m + 1) + β • coefficientVector w m := by
        rw [← coefficient_polynomialAction, ← coefficient_polynomialAction]
        ext i
        have h := congrArg (fun p : ℝ[X] => p.coeff (m + 1)) (hline i)
        simp only [add_mul, mul_assoc, coeff_add, coeff_X_mul, coeff_C_mul, coeff_derivative,
          coefficientVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          Nat.cast_add, Nat.cast_one] at h ⊢
        nlinarith [h]
      exact coefficient_rigidity B H hH lo hi α β hgap hB (m + 1)
        (coefficientVector w 0) (coefficientVector w (m + 1)) (coefficientVector w m)
        hconstant hleading hzero htop hnext

#print axioms affine_polynomial_line_degree_zero

end
end ADComplete.Rigidity
