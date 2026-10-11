import PaperVerifier.ADComplete.PSDFoldedLine
import PaperVerifier.ADComplete.PSDFoldedKrylov
import PaperVerifier.ADComplete.InvariantCoordinates
import PaperVerifier.ADComplete.PluckerNonzero
import PaperVerifier.ADComplete.PluckerDescent
import PaperVerifier.ADComplete.RationalCoordinates

/-! Constant frames for actual rational subspaces invariant under scaling. -/

namespace ADComplete.PSDFoldedSubspace

open Matrix Module Polynomial
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev F := RatFunc ℝ
variable {ι : Type*} [Fintype ι]

def scalingCoefficients (V : Submodule F (ι → F))
    (hV : ∀ z ∈ V, PSDFoldedKrylov.action PSDFoldedScaling.scale z ∈ V) :
    Matrix (Fin (finrank F V)) (Fin (finrank F V)) F :=
  fun k j => (Module.finBasis F V).repr
    ⟨PSDFoldedKrylov.action PSDFoldedScaling.scale ((Module.finBasis F V) j),
      hV _ ((Module.finBasis F V) j).property⟩ k

theorem scaling_basis_connection (V : Submodule F (ι → F))
    (hV : ∀ z ∈ V, PSDFoldedKrylov.action PSDFoldedScaling.scale z ∈ V)
    (i : ι) (j : Fin (finrank F V)) :
    PSDFoldedScaling.scale (InvariantCoordinates.basisMatrix V i j) =
      (InvariantCoordinates.basisMatrix V * scalingCoefficients V hV) i j := by
  classical
  let b := Module.finBasis F V
  let x : V := ⟨PSDFoldedKrylov.action PSDFoldedScaling.scale (b j),
    hV _ (b j).property⟩
  have hi := congrArg (fun y : V => (y : ι → F) i) (b.sum_repr x)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul] at hi
  change PSDFoldedScaling.scale (((b j : V) : ι → F) i) =
    ∑ k, ((b k : V) : ι → F) i * (b.repr x) k
  simpa only [mul_comm, x, PSDFoldedKrylov.action] using hi.symm

omit [Fintype ι] in
theorem scaling_plucker_line {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : Matrix ι σ F) (C : Matrix σ σ F)
    (h : ∀ i j, PSDFoldedScaling.scale (P i j) = (P*C) i j) (s : σ → ι) :
    PSDFoldedScaling.scale (PluckerConnection.plucker P s) =
      C.det * PluckerConnection.plucker P s := by
  unfold PluckerConnection.plucker
  rw [AlgHom.map_det]
  change ((P.submatrix s id).map PSDFoldedScaling.scale).det = _
  have hm : (P.submatrix s id).map PSDFoldedScaling.scale = (P.submatrix s id)*C := by
    ext i j
    exact h (s i) j
  rw [hm, Matrix.det_mul, mul_comm]

/-- The input is invariance under the actual map f(x)↦f(2x). Existence of a
constant frame and equality of subspaces are conclusions. -/
theorem scaling_invariant_subspace_constant (V : Submodule F (ι → F))
    (hV : ∀ z ∈ V, PSDFoldedKrylov.action PSDFoldedScaling.scale z ∈ V) :
    ∃ R : Matrix ι (Fin (finrank F V)) ℝ,
      ∃ s₀ : Fin (finrank F V) → ι,
        R.submatrix s₀ id = 1 ∧
        V = LinearMap.range (R.map (algebraMap ℝ F)).mulVecLin := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι)
    (Fintype.equivFin ι).injective
  let r := finrank F V
  let P := InvariantCoordinates.basisMatrix V
  let C := scalingCoefficients V hV
  obtain ⟨s₀, hs₀⟩ := PluckerConnection.exists_nonzero_plucker r P
    (InvariantCoordinates.basisMatrix_injective V)
  have hp : PluckerConnection.plucker P ≠ 0 := by
    intro hz
    exact hs₀ (congrFun hz s₀)
  obtain ⟨c, hc, w, hw, hrep⟩ := RationalCoordinates.primitive_representative
    (PluckerConnection.plucker P) hp
  have hscaleC : PSDFoldedScaling.scale c ≠ 0 :=
    fun hz => hc (PSDFoldedScaling.scale_injective (by simpa using hz))
  have hwline (s : Fin r → ι) :
      algebraMap ℝ[X] F (PSDFoldedScaling.polynomialScale (w s)) =
        (C.det*c/PSDFoldedScaling.scale c) * algebraMap ℝ[X] F (w s) := by
    have hh := scaling_plucker_line P C (scaling_basis_connection V hV) s
    rw [hrep s, map_mul, PSDFoldedScaling.scale_polynomial] at hh
    apply mul_left_cancel₀ hscaleC
    field_simp
    linear_combination hh
  have hwconst := PSDFoldedScaling.primitive_scaling_line_constant w hw
    (C.det*c/PSDFoldedScaling.scale c) hwline
  let η : (Fin r → ι) → ℝ := fun s => (w s).coeff 0
  have hreal (s : Fin r → ι) :
      PluckerConnection.plucker P s = c * algebraMap ℝ F (η s) := by
    rw [hrep s, hwconst s]
    congr 1
  refine ⟨PluckerConnection.constantFrame η s₀, s₀, ?_, ?_⟩
  · exact PluckerConnection.constantFrame_selected_identity P c η hreal s₀ hs₀
  · exact (InvariantCoordinates.basisMatrix_range V).symm.trans
      (PluckerConnection.constant_plucker_column_range P c η hreal s₀ hs₀)

#print axioms scaling_invariant_subspace_constant

end
end ADComplete.PSDFoldedSubspace
