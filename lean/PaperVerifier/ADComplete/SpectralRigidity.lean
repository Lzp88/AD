import PaperVerifier.ADComplete.SmallResidueRigidity
import PaperVerifier.ADComplete.SpectralBands
import PaperVerifier.ADComplete.ConstantFrame

/-! Both conclusions of small-residue rigidity: constancy of the actual
rational subspace and invariance of its descended real subspace. -/
namespace ADComplete.SmallResidueRigidity
open Matrix Module
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem constant_and_invariant_rank (B H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : ℝ) (hB : ∀ u : ι → ℝ,
      lo * Rigidity.pairing u u ≤ Rigidity.pairing u (B.mulVec u) ∧
      Rigidity.pairing u (B.mulVec u) ≤ hi * Rigidity.pairing u u)
    (V : Submodule RF (ι → RF)) (hgap : (finrank RF V : ℝ)*(hi-lo)<1)
    (hV : ∀ x ∈ V, DifferentialKrylov.connection RationalDerivative.derivative
      (RationalLineNormalization.rationalConnection B H) x ∈ V) :
    ∃ R : Matrix ι (Fin (finrank RF V)) ℝ, ∃ s₀ : Fin (finrank RF V) → ι,
      R.submatrix s₀ id=1 ∧ V=LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin ∧
      ∀ u ∈ LinearMap.range R.mulVecLin,
        B.mulVec u ∈ LinearMap.range R.mulVecLin ∧
        H.mulVec u ∈ LinearMap.range R.mulVecLin := by
  obtain ⟨R,s₀,hR,hVR⟩ := invariant_subspace_constant_rank B H hH lo hi hB V hgap hV
  refine ⟨R,s₀,hR,hVR,?_⟩
  have hInv : ∀ z ∈ LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin,
      DifferentialKrylov.connection RationalDerivative.derivative
        (RationalLineNormalization.rationalConnection B H) z ∈
          LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin := by
    intro z hz
    rw [← hVR] at hz ⊢
    exact hV z hz
  exact ConstantFrame.real_invariance R s₀ hR B H hInv

theorem small_residue_rigidity [Nonempty ι] (B H : Matrix ι ι ℝ)
    (hB : B.IsSymm) (hH : H.IsSymm) (V : Submodule RF (ι → RF))
    (hgap : (finrank RF V : ℝ) *
      (SpectralBands.eigenMax B (Matrix.isHermitian_iff_isSymm.mpr hB) -
        SpectralBands.eigenMin B (Matrix.isHermitian_iff_isSymm.mpr hB)) < 1)
    (hV : ∀ x ∈ V, DifferentialKrylov.connection RationalDerivative.derivative
      (RationalLineNormalization.rationalConnection B H) x ∈ V) :
    ∃ R : Matrix ι (Fin (finrank RF V)) ℝ, ∃ s₀ : Fin (finrank RF V) → ι,
      R.submatrix s₀ id=1 ∧ V=LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin ∧
      ∀ u ∈ LinearMap.range R.mulVecLin,
        B.mulVec u ∈ LinearMap.range R.mulVecLin ∧
        H.mulVec u ∈ LinearMap.range R.mulVecLin :=
  constant_and_invariant_rank B H hH _ _
    (SpectralBands.spectral_quadratic_interval B (Matrix.isHermitian_iff_isSymm.mpr hB))
    V hgap hV

#print axioms constant_and_invariant_rank
#print axioms small_residue_rigidity

end
end ADComplete.SmallResidueRigidity
