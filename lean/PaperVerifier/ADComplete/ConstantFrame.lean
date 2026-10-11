import PaperVerifier.ADComplete.PluckerDescent
import PaperVerifier.ADComplete.RationalLineNormalization
import PaperVerifier.ADComplete.DifferentialKrylov

/-! Coefficient descent and real invariance of a constant rational frame. -/

namespace ADComplete.ConstantFrame

open Matrix Polynomial
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev F := RatFunc ℝ
variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

def embed (v : ι → ℝ) : ι → F := fun i => algebraMap ℝ F (v i)

omit [Fintype ι] [Fintype σ] [DecidableEq σ] in
lemma map_C (a : ℝ) : algebraMap ℝ[X] F (C a) = algebraMap ℝ F a :=
  (IsScalarTower.algebraMap_apply ℝ ℝ[X] F a).symm

omit [Fintype ι] [DecidableEq σ] in
theorem map_mulVec (R : Matrix ι σ ℝ) (v : σ → ℝ) :
    (R.map (algebraMap ℝ F)).mulVec (embed v) = embed (R.mulVec v) := by
  ext i
  simp [embed, Matrix.mulVec, dotProduct, map_sum, map_mul]

omit [Fintype ι] in
/-- In a real frame with an identity row block, polynomial vectors in its
rational span have every coefficient in its real span. -/
theorem polynomial_coeff_mem (R : Matrix ι σ ℝ) (s₀ : σ → ι)
    (hR : R.submatrix s₀ id = 1) (p : ι → ℝ[X])
    (hp : (fun i => algebraMap ℝ[X] F (p i)) ∈
      LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin) (k : ℕ) :
    (fun i => (p i).coeff k) ∈ LinearMap.range R.mulVecLin := by
  classical
  obtain ⟨q, hq⟩ := hp
  change (R.map (algebraMap ℝ F)).mulVec q =
    (fun i => algebraMap ℝ[X] F (p i)) at hq
  have hR' : (R.map (algebraMap ℝ F)).submatrix s₀ id = 1 := by
    ext i j
    have hij := congrArg (fun T : Matrix σ σ ℝ => T i j) hR
    simpa only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.one_apply,
      apply_ite, map_one, map_zero] using congrArg (algebraMap ℝ F) hij
  have hq' : q = fun j => algebraMap ℝ[X] F (p (s₀ j)) := by
    have hh := congrArg (fun v : ι → F => v ∘ s₀) hq
    change ((R.map (algebraMap ℝ F)).submatrix s₀ id).mulVec q = _ at hh
    rwa [hR', Matrix.one_mulVec] at hh
  have hp' (i : ι) : ∑ j, C (R i j) * p (s₀ j) = p i := by
    apply RatFunc.algebraMap_injective ℝ
    have hi := congrArg (fun v : ι → F => v i) hq
    rw [hq'] at hi
    simpa only [map_sum, map_mul, map_C, Matrix.mulVec, dotProduct,
      Matrix.map_apply] using hi
  refine ⟨fun j => (p (s₀ j)).coeff k, ?_⟩
  ext i
  change ∑ j, R i j * (p (s₀ j)).coeff k = (p i).coeff k
  simpa only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
    using congrArg (fun t : ℝ[X] => t.coeff k) (hp' i)

omit [Fintype ι] in
theorem real_mem_of_embed_mem (R : Matrix ι σ ℝ) (s₀ : σ → ι)
    (hR : R.submatrix s₀ id = 1) (v : ι → ℝ)
    (hv : embed v ∈ LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin) :
    v ∈ LinearMap.range R.mulVecLin := by
  have hembed : embed v = (fun i => algebraMap ℝ F (v i)) := rfl
  rw [hembed] at hv
  have hv' : (fun i => algebraMap ℝ[X] F (C (v i))) ∈
      LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin := by
    simpa only [map_C] using hv
  simpa using polynomial_coeff_mem R s₀ hR (fun i => C (v i)) hv' 0

omit [Fintype ι] [DecidableEq σ] in
theorem embed_mem (R : Matrix ι σ ℝ) (v : ι → ℝ)
    (hv : v ∈ LinearMap.range R.mulVecLin) :
    embed v ∈ LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin := by
  obtain ⟨q, rfl⟩ := hv
  exact ⟨embed q, map_mulVec R q⟩

/-- Rational connection invariance of a constant frame implies preservation
of its real column span by both constant coefficient matrices. -/
theorem real_invariance (R : Matrix ι σ ℝ) (s₀ : σ → ι)
    (hR : R.submatrix s₀ id = 1) (B H : Matrix ι ι ℝ)
    (hV : ∀ v ∈ LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin,
      DifferentialKrylov.connection RationalDerivative.derivative
        (RationalLineNormalization.rationalConnection B H) v ∈
          LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin)
    (v : ι → ℝ) (hv : v ∈ LinearMap.range R.mulVecLin) :
    B.mulVec v ∈ LinearMap.range R.mulVecLin ∧
      H.mulVec v ∈ LinearMap.range R.mulVecLin := by
  let p : ι → ℝ[X] := fun i => C (B.mulVec v i) + X * C (H.mulVec v i)
  have hconn := hV (embed v) (embed_mem R v hv)
  have hscaled := (LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin).smul_mem
    (algebraMap ℝ[X] F X) hconn
  have hpoly : (fun i => algebraMap ℝ[X] F (p i)) ∈
      LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin := by
    have heq : (fun i => algebraMap ℝ[X] F (p i)) =
        algebraMap ℝ[X] F X • DifferentialKrylov.connection
          RationalDerivative.derivative (RationalLineNormalization.rationalConnection B H)
            (embed v) := by
      ext i
      have hs := RationalLineNormalization.scaled_polynomial_connection B H
        (fun j => C (v j)) i
      have haction (M : Matrix ι ι ℝ) :
          Rigidity.polynomialAction M (fun j => C (v j)) i = C (M.mulVec v i) := by
        simp [Rigidity.polynomialAction, Matrix.mulVec, dotProduct]
      simpa only [p, DifferentialKrylov.connection, Pi.smul_apply, smul_eq_mul,
        Polynomial.derivative_C, mul_zero, zero_add, Rigidity.polynomialAction,
        ← map_sum, ← Polynomial.C_mul, Matrix.mulVec, dotProduct,
        map_C, embed] using hs
    rw [heq]
    exact hscaled
  constructor
  · simpa [p] using polynomial_coeff_mem R s₀ hR p hpoly 0
  · simpa [p] using polynomial_coeff_mem R s₀ hR p hpoly 1

#print axioms polynomial_coeff_mem
#print axioms real_invariance

end
end ADComplete.ConstantFrame
