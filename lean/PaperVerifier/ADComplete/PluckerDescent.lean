import PaperVerifier.ADComplete.PluckerConnection

/-! Cramer's rule descends a constant Pluecker line to a real column frame. -/

namespace ADComplete.PluckerConnection

open Matrix
open scoped BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {F ι σ : Type*} [Field F] [Algebra ℝ F]
  [Fintype ι] [Fintype σ] [DecidableEq σ]

def constantFrame (η : (σ → ι) → ℝ) (s₀ : σ → ι) : Matrix ι σ ℝ :=
  fun i j => η (Function.update s₀ j i) / η s₀

omit [Fintype ι] in
/-- When every actual maximal minor has the same nonzero rational factor,
the columns admit a real frame. Both factorizations are consequences of
Cramer's rule; constant column span is not an input assumption. -/
theorem constant_plucker_factorization (P : Matrix ι σ F)
    (c : F) (η : (σ → ι) → ℝ)
    (h : ∀ s, plucker P s = c * algebraMap ℝ F (η s))
    (s₀ : σ → ι) (hs₀ : plucker P s₀ ≠ 0) :
    let Q := P.submatrix s₀ id
    let R := (constantFrame η s₀).map (algebraMap ℝ F)
    P = R * Q ∧ R = Q.det⁻¹ • (P * Q.adjugate) := by
  classical
  dsimp only
  let Q := P.submatrix s₀ id
  let R := (constantFrame η s₀).map (algebraMap ℝ F)
  have hdet : Q.det ≠ 0 := hs₀
  have hη : η s₀ ≠ 0 := by
    intro hz
    apply hs₀
    rw [h s₀, hz, map_zero, mul_zero]
  have hc : c ≠ 0 := by
    intro hz
    apply hs₀
    rw [h s₀, hz, zero_mul]
  have hcramer : P * Q.adjugate = Q.det • R := by
    ext i j
    change (P * Q.adjugate) i j = Q.det * R i j
    have hrow : (P * Q.adjugate) i j = plucker P (Function.update s₀ j i) := by
      rw [plucker_update, det_updateRow_cofactor]
      change (∑ k, P i k * Q.adjugate k j) = ∑ k, Q.adjugate k j * P i k
      simp_rw [mul_comm]
    rw [hrow, h, show Q.det = c * algebraMap ℝ F (η s₀) from h s₀]
    change c * algebraMap ℝ F (η (Function.update s₀ j i)) =
      (c * algebraMap ℝ F (η s₀)) *
        algebraMap ℝ F (η (Function.update s₀ j i) / η s₀)
    rw [map_div₀]
    have hηF : algebraMap ℝ F (η s₀) ≠ 0 := (map_ne_zero _).mpr hη
    field_simp
  have hfactor : P = R * Q := by
    have heq := congrArg (fun T : Matrix ι σ F => T * Q) hcramer
    rw [Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul] at heq
    ext i j
    exact mul_left_cancel₀ hdet (congrArg (fun T : Matrix ι σ F => T i j) heq)
  constructor
  · exact hfactor
  · rw [hcramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]

omit [Fintype ι] in
/-- The rational column subspace is exactly the scalar extension of the
explicit real frame obtained from the minor ratios. -/
theorem constant_plucker_column_range (P : Matrix ι σ F)
    (c : F) (η : (σ → ι) → ℝ)
    (h : ∀ s, plucker P s = c * algebraMap ℝ F (η s))
    (s₀ : σ → ι) (hs₀ : plucker P s₀ ≠ 0) :
    LinearMap.range P.mulVecLin =
      LinearMap.range ((constantFrame η s₀).map (algebraMap ℝ F)).mulVecLin := by
  classical
  let Q := P.submatrix s₀ id
  let R := (constantFrame η s₀).map (algebraMap ℝ F)
  obtain ⟨hP, hR⟩ := constant_plucker_factorization P c η h s₀ hs₀
  change P = R * Q at hP
  change R = Q.det⁻¹ • (P * Q.adjugate) at hR
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    refine ⟨Q.mulVec v, ?_⟩
    change R.mulVec (Q.mulVec v) = P.mulVec v
    rw [Matrix.mulVec_mulVec, ← hP]
  · rintro x ⟨v, rfl⟩
    refine ⟨Q.det⁻¹ • Q.adjugate.mulVec v, ?_⟩
    change P.mulVec (Q.det⁻¹ • Q.adjugate.mulVec v) = R.mulVec v
    rw [hR, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_mulVec]

omit [Fintype ι] in
theorem constantFrame_selected_identity (P : Matrix ι σ F)
    (c : F) (η : (σ → ι) → ℝ)
    (h : ∀ s, plucker P s = c * algebraMap ℝ F (η s))
    (s₀ : σ → ι) (hs₀ : plucker P s₀ ≠ 0) :
    (constantFrame η s₀).submatrix s₀ id = 1 := by
  classical
  let Q := P.submatrix s₀ id
  let R := (constantFrame η s₀).map (algebraMap ℝ F)
  obtain ⟨_, hR⟩ := constant_plucker_factorization P c η h s₀ hs₀
  change R = Q.det⁻¹ • (P * Q.adjugate) at hR
  have hdet : Q.det ≠ 0 := hs₀
  have hRI : R.submatrix s₀ id = 1 := by
    calc
      R.submatrix s₀ id = Q.det⁻¹ • (Q * Q.adjugate) := by
        ext i j
        have hij := congrArg (fun T : Matrix ι σ F => T (s₀ i) j) hR
        change R (s₀ i) j = Q.det⁻¹ * (∑ k, P (s₀ i) k * Q.adjugate k j) at hij
        exact hij
      _ = 1 := by rw [Matrix.mul_adjugate, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  ext i j
  apply (algebraMap ℝ F).injective
  have hij := congrArg (fun T : Matrix σ σ F => T i j) hRI
  simpa [R, Matrix.one_apply] using hij

#print axioms constant_plucker_factorization
#print axioms constant_plucker_column_range
#print axioms constantFrame_selected_identity

end
end ADComplete.PluckerConnection
