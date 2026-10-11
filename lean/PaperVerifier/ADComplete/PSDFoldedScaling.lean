import Mathlib

/-! Actual rational scaling by two for the fixed folded frame. -/

namespace ADComplete.PSDFoldedScaling

open Polynomial
noncomputable section
abbrev F := RatFunc ℝ

def polynomialScale : ℝ[X] ≃ₐ[ℝ] ℝ[X] :=
  Polynomial.algEquivOfCompEqX (C 2 * X) (C (1/2 : ℝ) * X)
    (by simp [Polynomial.mul_comp, ← mul_assoc, ← Polynomial.C_mul])
    (by simp [Polynomial.mul_comp, ← mul_assoc, ← Polynomial.C_mul])

theorem polynomialScale_apply (p : ℝ[X]) : polynomialScale p = p.comp (C 2 * X) := by
  simp [polynomialScale, Polynomial.algEquivOfCompEqX_apply, Polynomial.comp_eq_aeval]

theorem polynomialScale_coeff (p : ℝ[X]) (j : ℕ) :
    (polynomialScale p).coeff j = p.coeff j * (2 : ℝ)^j := by
  rw [polynomialScale_apply, Polynomial.comp_C_mul_X_coeff]

theorem polynomialScale_natDegree (p : ℝ[X]) :
    (polynomialScale p).natDegree = p.natDegree := by
  rw [polynomialScale_apply, Polynomial.natDegree_comp]
  simp

lemma scaleMapNonzero : nonZeroDivisors ℝ[X] ≤
    (nonZeroDivisors ℝ[X]).comap polynomialScale.toAlgHom :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ polynomialScale.injective

def scale : F →ₐ[ℝ] F := RatFunc.mapAlgHom polynomialScale.toAlgHom scaleMapNonzero

theorem scale_injective : Function.Injective scale := by
  exact RatFunc.map_injective polynomialScale.toAlgHom scaleMapNonzero polynomialScale.injective

theorem scale_polynomial (p : ℝ[X]) :
    scale (algebraMap ℝ[X] F p) = algebraMap ℝ[X] F (polynomialScale p) := by
  change RatFunc.map polynomialScale.toAlgHom scaleMapNonzero (algebraMap ℝ[X] F p) = _
  simpa using RatFunc.map_apply_div polynomialScale.toAlgHom
    scaleMapNonzero p 1

theorem scale_real (a : ℝ) : scale (algebraMap ℝ F a) = algebraMap ℝ F a :=
  scale.commutes a

#print axioms scale_polynomial

end
end ADComplete.PSDFoldedScaling
