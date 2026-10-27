import PaperVerifier.ADComplete.ConstantFrame
set_option autoImplicit false

/-! Polynomial evaluation descent for actual constant real frames. -/
namespace MultiSymmetric.Descent
open Matrix Polynomial
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev RF := RatFunc ℝ
variable {ι σ : Type*} [Fintype ι] [Fintype σ] [DecidableEq σ]

omit [Fintype ι] in
theorem polynomial_eval_mem (R : Matrix ι σ ℝ) (s₀ : σ → ι)
    (hR : R.submatrix s₀ id = 1) (p : ι → ℝ[X])
    (hp : (fun i => algebraMap ℝ[X] RF (p i)) ∈
      LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin) (a : ℝ) :
    (fun i => (p i).eval a) ∈ LinearMap.range R.mulVecLin := by
  classical
  obtain ⟨q, hq⟩ := hp
  change (R.map (algebraMap ℝ RF)).mulVec q =
    (fun i => algebraMap ℝ[X] RF (p i)) at hq
  have hR' : (R.map (algebraMap ℝ RF)).submatrix s₀ id = 1 := by
    ext i j
    have hij := congrArg (fun T : Matrix σ σ ℝ => T i j) hR
    simpa only [Matrix.submatrix_apply, Matrix.map_apply, Matrix.one_apply,
      apply_ite, map_one, map_zero] using congrArg (algebraMap ℝ RF) hij
  have hq' : q = fun j => algebraMap ℝ[X] RF (p (s₀ j)) := by
    have hh := congrArg (fun v : ι → RF => v ∘ s₀) hq
    change ((R.map (algebraMap ℝ RF)).submatrix s₀ id).mulVec q = _ at hh
    rwa [hR', Matrix.one_mulVec] at hh
  have hp' (i : ι) : (∑ j, (C (R i j) * p (s₀ j))) = p i := by
    apply RatFunc.algebraMap_injective ℝ
    have hi := congrArg (fun v : ι → RF => v i) hq
    rw [hq'] at hi
    simpa only [map_sum, map_mul, ADComplete.ConstantFrame.map_C,
      Matrix.mulVec, dotProduct, Matrix.map_apply] using hi
  refine ⟨fun j => (p (s₀ j)).eval a, ?_⟩
  ext i
  change (∑ j, (R i j * (p (s₀ j)).eval a)) = (p i).eval a
  simpa only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
    using congrArg (fun t : ℝ[X] => t.eval a) (hp' i)

#print axioms polynomial_eval_mem
end
end MultiSymmetric.Descent
