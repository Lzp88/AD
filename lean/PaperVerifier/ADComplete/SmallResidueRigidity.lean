import PaperVerifier.ADComplete.InvariantCoordinates
import PaperVerifier.ADComplete.PluckerNonzero
import PaperVerifier.ADComplete.PluckerDescent
import PaperVerifier.ADComplete.RationalCoordinates
import PaperVerifier.ADComplete.TensorBaseChange

/-! Descent of actual invariant rational subspaces to constant real frames. -/
namespace ADComplete.SmallResidueRigidity

open Matrix Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι]
abbrev RF := RatFunc ℝ

/-- Every actual invariant rational subspace has a real frame when its rank
times the residue interval width is less than one. The selected-row identity
and the equality of subspaces are conclusions, not input assumptions. -/
theorem invariant_subspace_constant_rank
    (B H : Matrix ι ι ℝ) (hH : H.IsSymm) (lo hi : ℝ)
    (hB : ∀ u : ι → ℝ,
      lo * Rigidity.pairing u u ≤ Rigidity.pairing u (B.mulVec u) ∧
      Rigidity.pairing u (B.mulVec u) ≤ hi * Rigidity.pairing u u)
    (V : Submodule RF (ι → RF))
    (hgap : (finrank RF V : ℝ) * (hi-lo) < 1)
    (hV : ∀ x ∈ V, DifferentialKrylov.connection RationalDerivative.derivative
      (RationalLineNormalization.rationalConnection B H) x ∈ V) :
    ∃ R : Matrix ι (Fin (finrank RF V)) ℝ,
      ∃ s₀ : Fin (finrank RF V) → ι,
        R.submatrix s₀ id = 1 ∧
        V = LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι)
    (Fintype.equivFin ι).injective
  let r := finrank RF V
  let P := InvariantCoordinates.basisMatrix V
  let A := RationalLineNormalization.rationalConnection B H
  let C := InvariantCoordinates.connectionCoefficients V RationalDerivative.derivative A hV
  obtain ⟨s₀, hs₀⟩ := PluckerConnection.exists_nonzero_plucker r P
    (InvariantCoordinates.basisMatrix_injective V)
  have hp : PluckerConnection.plucker P ≠ 0 := by
    intro hz
    exact hs₀ (congrFun hz s₀)
  obtain ⟨c, hc, w, hw, hrep⟩ := RationalCoordinates.primitive_representative
    (PluckerConnection.plucker P) hp
  have hline (s : Fin r → ι) :
      RationalDerivative.derivative (PluckerConnection.plucker P s) +
        (RationalLineNormalization.rationalConnection
          (Rigidity.tensorMatrix (σ := Fin r) B)
          (Rigidity.tensorMatrix (σ := Fin r) H)).mulVec
            (PluckerConnection.plucker P) s =
        C.trace * PluckerConnection.plucker P s := by
    rw [TensorBaseChange.tensor_rational_connection]
    exact PluckerConnection.induced_connection_line RationalDerivative.derivative A P C
      (InvariantCoordinates.invariant_basis_connection V RationalDerivative.derivative A hV) s
  have hgap' : (r : ℝ) * hi - (r : ℝ) * lo < 1 := by
    change (r : ℝ) * (hi-lo) < 1 at hgap
    nlinarith
  have hwconst := RationalLineNormalization.primitive_representative_constant
    (Rigidity.tensorMatrix (σ := Fin r) B) (Rigidity.tensorMatrix (σ := Fin r) H)
    (Rigidity.tensorMatrix_symmetric H hH) ((r : ℝ)*lo) ((r : ℝ)*hi) hgap'
    (by simpa using Rigidity.tensorMatrix_interval (σ := Fin r) B lo hi hB)
    (PluckerConnection.plucker P) w c C.trace hc hw hrep hline
  let η : (Fin r → ι) → ℝ := fun s => (w s).coeff 0
  have hreal (s : Fin r → ι) :
      PluckerConnection.plucker P s = c * algebraMap ℝ RF (η s) := by
    rw [hrep s, hwconst s]
    congr 1
  refine ⟨PluckerConnection.constantFrame η s₀, s₀, ?_, ?_⟩
  · exact PluckerConnection.constantFrame_selected_identity P c η hreal s₀ hs₀
  · exact (InvariantCoordinates.basisMatrix_range V).symm.trans
      (PluckerConnection.constant_plucker_column_range P c η hreal s₀ hs₀)

/-- A dimension-only interval condition suffices for every invariant subspace,
including the zero subspace and an empty coordinate type. -/
theorem invariant_subspace_constant
    (B H : Matrix ι ι ℝ) (hH : H.IsSymm) (lo hi : ℝ)
    (hB : ∀ u : ι → ℝ,
      lo * Rigidity.pairing u u ≤ Rigidity.pairing u (B.mulVec u) ∧
      Rigidity.pairing u (B.mulVec u) ≤ hi * Rigidity.pairing u u)
    (hgap : (Fintype.card ι : ℝ) * (hi-lo) < 1)
    (V : Submodule RF (ι → RF))
    (hV : ∀ x ∈ V, DifferentialKrylov.connection RationalDerivative.derivative
      (RationalLineNormalization.rationalConnection B H) x ∈ V) :
    ∃ R : Matrix ι (Fin (finrank RF V)) ℝ,
      ∃ s₀ : Fin (finrank RF V) → ι,
        R.submatrix s₀ id = 1 ∧
        V = LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin := by
  apply invariant_subspace_constant_rank B H hH lo hi hB V _ hV
  have hd : (finrank RF V : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast (show finrank RF V ≤ Fintype.card ι from by simpa using V.finrank_le)
  have hr : (0 : ℝ) ≤ finrank RF V := Nat.cast_nonneg _
  by_cases hw : 0 ≤ hi-lo
  · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hd hw) hgap
  · have hh : (finrank RF V : ℝ) * (hi-lo) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hr (le_of_not_ge hw)
    linarith

#print axioms invariant_subspace_constant_rank
#print axioms invariant_subspace_constant

end
end ADComplete.SmallResidueRigidity
