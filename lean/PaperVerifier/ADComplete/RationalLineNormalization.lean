import PaperVerifier.ADComplete.RationalDerivative
import PaperVerifier.ADComplete.PrimitiveLine

/-! Rational connection lines and their primitive polynomial normalization. -/
namespace ADComplete.RationalLineNormalization

open Matrix Polynomial
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]
abbrev F := RatFunc ℝ

theorem normalize_connection_line (D : Derivation ℝ F F)
    (A : Matrix ι ι F) (v y : ι → F) (gamma q : F) (hq : q ≠ 0)
    (hrep : ∀ i, v i = q * y i)
    (hline : ∀ i, D (v i) + A.mulVec v i = gamma * v i) :
    ∀ i, D (y i) + A.mulVec y i = (gamma - D q / q) * y i := by
  have hv : v = q • y := by ext i; exact hrep i
  have hA : A.mulVec v = q • A.mulVec y := by rw [hv, Matrix.mulVec_smul]
  intro i
  have h := hline i
  rw [hrep i, Derivation.leibniz, hA] at h
  change q * D (y i) + y i * D q + q * A.mulVec y i = gamma * (q*y i) at h
  apply mul_left_cancel₀ hq
  field_simp
  linear_combination h

def rationalConnection (B H : Matrix ι ι ℝ) : Matrix ι ι F := fun i j =>
  algebraMap ℝ[X] F (C (B i j)) / algebraMap ℝ[X] F X +
    algebraMap ℝ[X] F (C (H i j))

theorem scaled_polynomial_connection (B H : Matrix ι ι ℝ) (w : ι → ℝ[X]) (i : ι) :
    algebraMap ℝ[X] F
      (X * (w i).derivative + Rigidity.polynomialAction B w i +
        X * Rigidity.polynomialAction H w i) =
      algebraMap ℝ[X] F X * (RationalDerivative.derivative
        (algebraMap ℝ[X] F (w i)) + (rationalConnection B H).mulVec
          (fun j => algebraMap ℝ[X] F (w j)) i) := by
  have hx : algebraMap ℝ[X] F X ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  rw [RationalDerivative.derivative_polynomial]
  simp only [Rigidity.polynomialAction, map_add, map_mul, map_sum,
    rationalConnection, Matrix.mulVec, dotProduct, mul_add]
  rw [add_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hx]

/-- An actual primitive polynomial representative of a rational connection
line is constant; its rational scalar may have arbitrary poles. -/
theorem primitive_representative_constant
    (B H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : ℝ) (hgap : hi-lo < 1)
    (hB : ∀ u : ι → ℝ,
      lo * Rigidity.pairing u u ≤ Rigidity.pairing u (B.mulVec u) ∧
      Rigidity.pairing u (B.mulVec u) ≤ hi * Rigidity.pairing u u)
    (v : ι → F) (w : ι → ℝ[X]) (q gamma : F) (hq : q ≠ 0)
    (hw : PolynomialPrimitivity.Primitive w)
    (hrep : ∀ i, v i = q * algebraMap ℝ[X] F (w i))
    (hline : ∀ i, RationalDerivative.derivative (v i) +
      (rationalConnection B H).mulVec v i = gamma * v i) :
    ∀ i, w i = C ((w i).coeff 0) := by
  have hn := normalize_connection_line RationalDerivative.derivative
    (rationalConnection B H) v (fun j => algebraMap ℝ[X] F (w j)) gamma q hq hrep hline
  apply PrimitiveLine.primitive_rational_line_constant B H hH lo hi hgap hB w hw
    (algebraMap ℝ[X] F X * (gamma - RationalDerivative.derivative q / q))
  intro i
  rw [scaled_polynomial_connection, hn i, mul_assoc]

#print axioms normalize_connection_line
#print axioms primitive_representative_constant

end
end ADComplete.RationalLineNormalization
