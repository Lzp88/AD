import PaperVerifier.ADComplete.DifferentialKrylov

/-! Actual basis matrices and connection coefficients of invariant subspaces. -/
namespace ADComplete.InvariantCoordinates

open Matrix Module
open scoped BigOperators
noncomputable section

variable {F ι : Type*} [Field F] [Algebra ℝ F] [Fintype ι]

def basisMatrix (V : Submodule F (ι → F)) :
    Matrix ι (Fin (Module.finrank F V)) F :=
  fun i j => ((Module.finBasis F V) j : ι → F) i

def connectionCoefficients (V : Submodule F (ι → F))
    (D : Derivation ℝ F F) (A : Matrix ι ι F)
    (hV : ∀ x ∈ V, DifferentialKrylov.connection D A x ∈ V) :
    Matrix (Fin (Module.finrank F V)) (Fin (Module.finrank F V)) F :=
  fun k j => (Module.finBasis F V).repr
    ⟨DifferentialKrylov.connection D A ((Module.finBasis F V) j),
      hV _ ((Module.finBasis F V) j).property⟩ k

theorem invariant_basis_connection (V : Submodule F (ι → F))
    (D : Derivation ℝ F F) (A : Matrix ι ι F)
    (hV : ∀ x ∈ V, DifferentialKrylov.connection D A x ∈ V) (i : ι)
    (j : Fin (Module.finrank F V)) :
    D (basisMatrix V i j) + (A * basisMatrix V) i j =
      (basisMatrix V * connectionCoefficients V D A hV) i j := by
  classical
  let b := Module.finBasis F V
  let x : V := ⟨DifferentialKrylov.connection D A (b j), hV _ (b j).property⟩
  have hx := b.sum_repr x
  have hi := congrArg (fun y : V => (y : ι → F) i) hx
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hi
  change (DifferentialKrylov.connection D A ((b j : V) : ι → F)) i =
    ∑ k, ((b k : V) : ι → F) i * (b.repr x) k
  simpa only [mul_comm] using hi.symm

omit [Algebra ℝ F] in
theorem basisMatrix_mulVec (V : Submodule F (ι → F))
    (c : Fin (Module.finrank F V) → F) :
    (basisMatrix V).mulVec c =
      (((Module.finBasis F V).equivFun.symm c : V) : ι → F) := by
  classical
  ext i
  rw [Basis.equivFun_symm_apply]
  simp [basisMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

omit [Algebra ℝ F] in
theorem basisMatrix_injective (V : Submodule F (ι → F)) :
    Function.Injective (basisMatrix V).mulVec := by
  intro c d h
  rw [basisMatrix_mulVec, basisMatrix_mulVec] at h
  exact (Module.finBasis F V).equivFun.symm.injective (Subtype.ext h)

omit [Algebra ℝ F] in
theorem basisMatrix_range (V : Submodule F (ι → F)) :
    LinearMap.range (basisMatrix V).mulVecLin = V := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    change (basisMatrix V).mulVec c ∈ V
    rw [basisMatrix_mulVec]
    exact ((Module.finBasis F V).equivFun.symm c).property
  · intro hx
    refine ⟨(Module.finBasis F V).equivFun ⟨x, hx⟩, ?_⟩
    change (basisMatrix V).mulVec _ = x
    rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]

#print axioms invariant_basis_connection
#print axioms basisMatrix_injective
#print axioms basisMatrix_range

end
end ADComplete.InvariantCoordinates
