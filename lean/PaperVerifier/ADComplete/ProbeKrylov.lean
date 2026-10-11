import PaperVerifier.ADComplete.ProbePolynomial

/-! The fixed probe polynomials are scaled genuine rational Krylov vectors. -/

namespace ADComplete.Spanning

open Matrix Polynomial
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev F := RatFunc ℝ
variable {ι : Type*} [Fintype ι]

def rationalSeed (v : ι → ℝ) : ι → F := fun i => algebraMap ℝ F (v i)

def rationalKrylov (κ : ℝ) (H K : Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) : ι → F :=
  DifferentialKrylov.vector RationalDerivative.derivative
    (RationalLineNormalization.rationalConnection (κ⁻¹ • K) H) (rationalSeed v) k

lemma polynomialAction_smul (c : ℝ) (K : Matrix ι ι ℝ) (p : ι → ℝ[X]) (i : ι) :
    Rigidity.polynomialAction (c • K) p i = C c * Rigidity.polynomialAction K p i := by
  simp [Rigidity.polynomialAction, Finset.mul_sum, mul_assoc]

lemma rational_map_C (a : ℝ) : algebraMap ℝ[X] F (C a) = algebraMap ℝ F a :=
  (IsScalarTower.algebraMap_apply ℝ ℝ[X] F a).symm

theorem probePolynomial_connection_step (κ : ℝ) (hκ : κ ≠ 0)
    (H K : Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) (i : ι) :
    algebraMap ℝ[X] F (probePolynomial κ H K v (k + 1) i) =
      (algebraMap ℝ F κ * algebraMap ℝ[X] F X) *
        DifferentialKrylov.connection RationalDerivative.derivative
          (RationalLineNormalization.rationalConnection (κ⁻¹ • K) H)
          (fun j => algebraMap ℝ[X] F (probePolynomial κ H K v k j)) i -
      algebraMap ℝ F κ * (k : F) *
        algebraMap ℝ[X] F (probePolynomial κ H K v k i) := by
  let p := probePolynomial κ H K v k
  have hs := RationalLineNormalization.scaled_polynomial_connection (κ⁻¹ • K) H p i
  have hs' := congrArg (fun z : F => algebraMap ℝ F κ * z) hs
  rw [polynomialAction_smul] at hs'
  simp only [map_add, map_mul, rational_map_C, map_inv₀] at hs'
  have hκF : algebraMap ℝ F κ ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  rw [probePolynomial_step]
  simp only [map_add, map_sub, map_mul, rational_map_C, map_natCast]
  change _ = _ - _
  unfold DifferentialKrylov.connection
  dsimp only [p] at hs'
  field_simp at hs' ⊢
  linear_combination hs'

/-- This equality identifies the actual derivative iterates with the literal
probe polynomial recurrence, rather than positing a spanning property. -/
theorem probePolynomial_rationalKrylov (κ : ℝ) (hκ : κ ≠ 0)
    (H K : Matrix ι ι ℝ) (v : ι → ℝ) (k : ℕ) :
    (fun i => algebraMap ℝ[X] F (probePolynomial κ H K v k i)) =
      (algebraMap ℝ F κ * algebraMap ℝ[X] F X) ^ k • rationalKrylov κ H K v k := by
  induction k with
  | zero =>
      ext i
      simp [probePolynomial_zero, rationalKrylov, DifferentialKrylov.vector, rationalSeed]
  | succ k ih =>
      let a : F := algebraMap ℝ F κ * algebraMap ℝ[X] F X
      have hDa : RationalDerivative.derivative a = algebraMap ℝ F κ := by
        have hk : RationalDerivative.derivative (algebraMap ℝ F κ) = 0 :=
          Derivation.map_algebraMap RationalDerivative.derivative κ
        have hx : RationalDerivative.derivative (algebraMap ℝ[X] F X) = 1 := by
          rw [RationalDerivative.derivative_polynomial]
          simp
        dsimp only [a]
        rw [Derivation.leibniz]
        change algebraMap ℝ F κ * RationalDerivative.derivative (algebraMap ℝ[X] F X) +
          algebraMap ℝ[X] F X * RationalDerivative.derivative (algebraMap ℝ F κ) = _
        rw [hk, hx, mul_one, mul_zero, add_zero]
      have hpow : RationalDerivative.derivative (a ^ k) * a =
          algebraMap ℝ F κ * (k : F) * a ^ k := by
        cases k with
        | zero => simp
        | succ k =>
            rw [Derivation.leibniz_pow, hDa]
            simp only [Nat.succ_sub_one, smul_eq_mul, nsmul_eq_mul, Nat.cast_succ]
            ring
      ext i
      rw [probePolynomial_connection_step κ hκ H K v k i, ih,
        DifferentialKrylov.connection_smul]
      have hi : algebraMap ℝ[X] F (probePolynomial κ H K v k i) =
          a ^ k * rationalKrylov κ H K v k i := congrArg (fun y : ι → F => y i) ih
      rw [hi]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hstep : rationalKrylov κ H K v (k + 1) =
          DifferentialKrylov.connection RationalDerivative.derivative
            (RationalLineNormalization.rationalConnection (κ⁻¹ • K) H)
              (rationalKrylov κ H K v k) := by
        exact DifferentialKrylov.vector_succ _ _ _ _
      rw [hstep]
      change a * (RationalDerivative.derivative (a ^ k) * _ + a ^ k * _) -
        algebraMap ℝ F κ * (k : F) * (a ^ k * _) = a ^ (k + 1) * _
      rw [pow_succ]
      linear_combination (rationalKrylov κ H K v k i) * hpow

#print axioms probePolynomial_connection_step
#print axioms probePolynomial_rationalKrylov

end
end ADComplete.Spanning
