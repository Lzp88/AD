import PaperVerifier.ADComplete.PSDFoldedScaling
import PaperVerifier.ADComplete.PolynomialPrimitivity

/-! Constant reduction of actual rational lines under scaling by two. -/

namespace ADComplete.PSDFoldedScaling

open Polynomial
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- A primitive polynomial vector spanning a scaling-invariant rational line
is constant. The proportionality factor may initially be any rational function. -/
theorem primitive_scaling_line_constant (w : ι → ℝ[X])
    (hw : PolynomialPrimitivity.Primitive w) (gamma : F)
    (h : ∀ i, algebraMap ℝ[X] F (polynomialScale (w i)) =
      gamma * algebraMap ℝ[X] F (w i)) :
    ∀ i, w i = C ((w i).coeff 0) := by
  classical
  obtain ⟨a, ha⟩ := PolynomialPrimitivity.primitive_bezout w hw
  have hwne : ∃ i, w i ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz : (∑ i, a i * w i) = 0 := by simp [hn]
    rw [ha] at hz
    exact one_ne_zero hz
  obtain ⟨q, hq⟩ := PolynomialPrimitivity.rational_factor_is_polynomial
    w (fun i => polynomialScale (w i)) hw gamma h
  have heq (i : ι) : polynomialScale (w i) = q * w i := by
    apply RatFunc.algebraMap_injective ℝ
    rw [map_mul, hq]
    exact h i
  obtain ⟨i, hi⟩ := hwne
  have hqi : q ≠ 0 := by
    intro hz
    have hh := heq i
    rw [hz, zero_mul] at hh
    exact hi (polynomialScale.injective (by simpa using hh))
  have hqdeg : q.natDegree = 0 := by
    have hd := congrArg Polynomial.natDegree (heq i)
    rw [polynomialScale_natDegree, Polynomial.natDegree_mul hqi hi] at hd
    omega
  have hqC : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hqdeg
  obtain ⟨i₀, hi₀⟩ := PolynomialPrimitivity.primitive_has_nonzero_constant w hw
  have hqone : q.coeff 0 = 1 := by
    have hh := congrArg (fun p : ℝ[X] => p.coeff 0) (heq i₀)
    rw [polynomialScale_coeff, pow_zero, mul_one, hqC, Polynomial.coeff_C_mul] at hh
    exact mul_right_cancel₀ hi₀ (by simpa using hh.symm)
  have hfixed (i : ι) : polynomialScale (w i) = w i := by
    rw [heq, hqC, hqone, Polynomial.C_1, one_mul]
  intro i
  apply Polynomial.ext
  intro j
  cases j with
  | zero => simp
  | succ j =>
      have hh := congrArg (fun p : ℝ[X] => p.coeff (j+1)) (hfixed i)
      rw [polynomialScale_coeff] at hh
      have hpow : (2 : ℝ) ^ (j+1) ≠ 1 := ne_of_gt (one_lt_pow₀ (by norm_num) (by omega))
      have hc : (w i).coeff (j+1) = 0 := by
        by_contra hn
        exact hpow (mul_left_cancel₀ hn (by simpa using hh))
      simpa using hc

#print axioms primitive_scaling_line_constant

end
end ADComplete.PSDFoldedScaling
