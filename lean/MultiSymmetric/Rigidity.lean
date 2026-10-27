import MultiSymmetric.RigidityLine
import MultiSymmetric.Descent

namespace MultiSymmetric.Rigidity
open Matrix Module
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1000000
variable {τ ι : Type*} [Fintype τ] [Nonempty τ] [Fintype ι]

/-- Actual invariant rational subspace descent for finitely many distinct
real poles. The input is connection invariance, not a Pluecker certificate. -/
theorem invariant_subspace_constant_rank
    (a : τ → ℝ) (ha : Function.Injective a)
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : τ → ℝ)
    (hB : ∀ k u,
      lo k * ADComplete.Rigidity.pairing u u ≤ ADComplete.Rigidity.pairing u ((B k).mulVec u) ∧
      ADComplete.Rigidity.pairing u ((B k).mulVec u) ≤ hi k * ADComplete.Rigidity.pairing u u)
    (V : Submodule RF (ι → RF))
    (hgap : (finrank RF V : ℝ) * (∑ k, (hi k-lo k)) < 1)
    (hV : ∀ x ∈ V, ADComplete.DifferentialKrylov.connection
      ADComplete.RationalDerivative.derivative (rationalConnection a B H) x ∈ V) :
    ∃ R : Matrix ι (Fin (finrank RF V)) ℝ, ∃ s₀ : Fin (finrank RF V) → ι,
      R.submatrix s₀ id=1 ∧ V=LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin := by
  classical
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι)
    (Fintype.equivFin ι).injective
  let r := finrank RF V
  let P := ADComplete.InvariantCoordinates.basisMatrix V
  let A := rationalConnection a B H
  let C := ADComplete.InvariantCoordinates.connectionCoefficients V
    ADComplete.RationalDerivative.derivative A hV
  obtain ⟨s₀, hs₀⟩ := ADComplete.PluckerConnection.exists_nonzero_plucker r P
    (ADComplete.InvariantCoordinates.basisMatrix_injective V)
  have hp : ADComplete.PluckerConnection.plucker P ≠ 0 := by
    intro hz
    exact hs₀ (congrFun hz s₀)
  obtain ⟨c,hc,w,hw,hrep⟩ := ADComplete.RationalCoordinates.primitive_representative
    (ADComplete.PluckerConnection.plucker P) hp
  have hline (s : Fin r → ι) :
      ADComplete.RationalDerivative.derivative (ADComplete.PluckerConnection.plucker P s) +
      (rationalConnection a (fun k=>ADComplete.Rigidity.tensorMatrix (σ := Fin r) (B k))
        (ADComplete.Rigidity.tensorMatrix (σ := Fin r) H)).mulVec
          (ADComplete.PluckerConnection.plucker P) s =
        C.trace * ADComplete.PluckerConnection.plucker P s := by
    rw [MultiSymmetric.Descent.tensor_rational_connection]
    exact ADComplete.PluckerConnection.induced_connection_line
      ADComplete.RationalDerivative.derivative A P C
      (ADComplete.InvariantCoordinates.invariant_basis_connection V
        ADComplete.RationalDerivative.derivative A hV) s
  have hgap' : ∑ k, ((r : ℝ)*hi k-(r : ℝ)*lo k)<1 := by
    simpa only [← mul_sub, ← Finset.mul_sum] using hgap
  have hwconst := primitive_representative_constant a ha
    (fun k=>ADComplete.Rigidity.tensorMatrix (σ := Fin r) (B k))
    (ADComplete.Rigidity.tensorMatrix (σ := Fin r) H)
    (ADComplete.Rigidity.tensorMatrix_symmetric H hH)
    (fun k=>(r : ℝ)*lo k) (fun k=>(r : ℝ)*hi k) hgap'
    (fun k u => by
      simpa using (ADComplete.Rigidity.tensorMatrix_interval (σ := Fin r)
        (B k) (lo k) (hi k) (hB k) u))
    (ADComplete.PluckerConnection.plucker P) w c C.trace hc hw hrep hline
  let η : (Fin r → ι) → ℝ := fun s=>(w s).coeff 0
  have hreal (s : Fin r → ι) :
      ADComplete.PluckerConnection.plucker P s=c*algebraMap ℝ RF (η s) := by
    rw [hrep s,hwconst s]
    congr 1
  refine ⟨ADComplete.PluckerConnection.constantFrame η s₀,s₀,?_,?_⟩
  · exact ADComplete.PluckerConnection.constantFrame_selected_identity P c η hreal s₀ hs₀
  · exact (ADComplete.InvariantCoordinates.basisMatrix_range V).symm.trans
      (ADComplete.PluckerConnection.constant_plucker_column_range P c η hreal s₀ hs₀)

/-- Full multi-pole rigidity: a normalized constant frame and preservation by
every separate residue and by the constant generator. -/
theorem constant_and_invariant_rank
    (a : τ → ℝ) (ha : Function.Injective a)
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ) (hH : H.IsSymm)
    (lo hi : τ → ℝ)
    (hB : ∀ k u,
      lo k * ADComplete.Rigidity.pairing u u ≤ ADComplete.Rigidity.pairing u ((B k).mulVec u) ∧
      ADComplete.Rigidity.pairing u ((B k).mulVec u) ≤ hi k * ADComplete.Rigidity.pairing u u)
    (V : Submodule RF (ι → RF))
    (hgap : (finrank RF V : ℝ) * (∑ k, (hi k-lo k)) < 1)
    (hV : ∀ x ∈ V, ADComplete.DifferentialKrylov.connection
      ADComplete.RationalDerivative.derivative (rationalConnection a B H) x ∈ V) :
    ∃ R : Matrix ι (Fin (finrank RF V)) ℝ, ∃ s₀ : Fin (finrank RF V) → ι,
      R.submatrix s₀ id=1 ∧ V=LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin ∧
      ∀ v ∈ LinearMap.range R.mulVecLin,
        H.mulVec v∈LinearMap.range R.mulVecLin ∧
          ∀ k,(B k).mulVec v∈LinearMap.range R.mulVecLin := by
  obtain ⟨R,s₀,hR,hVR⟩ := invariant_subspace_constant_rank a ha B H hH lo hi hB V hgap hV
  refine ⟨R,s₀,hR,hVR,?_⟩
  have hInv : ∀ x∈LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin,
      ADComplete.DifferentialKrylov.connection ADComplete.RationalDerivative.derivative
        (rationalConnection a B H) x∈LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin := by
    intro x hx
    rw [← hVR] at hx ⊢
    exact hV x hx
  exact MultiSymmetric.Descent.real_invariance a ha R s₀ hR B H hInv

/-- Spectral-diameter formulation for real symmetric matrices. -/
theorem small_residue_rigidity [DecidableEq ι] [Nonempty ι]
    (a : τ → ℝ) (ha : Function.Injective a)
    (B : τ → Matrix ι ι ℝ) (H : Matrix ι ι ℝ)
    (hB : ∀ k,(B k).IsSymm) (hH : H.IsSymm)
    (V : Submodule RF (ι → RF))
    (hgap : (finrank RF V : ℝ) *
      (∑ k, (ADComplete.SpectralBands.eigenMax (B k)
          (Matrix.isHermitian_iff_isSymm.mpr (hB k)) -
        ADComplete.SpectralBands.eigenMin (B k)
          (Matrix.isHermitian_iff_isSymm.mpr (hB k)))) < 1)
    (hV : ∀ x ∈ V, ADComplete.DifferentialKrylov.connection
      ADComplete.RationalDerivative.derivative (rationalConnection a B H) x ∈ V) :
    ∃ R : Matrix ι (Fin (finrank RF V)) ℝ, ∃ s₀ : Fin (finrank RF V) → ι,
      R.submatrix s₀ id=1 ∧ V=LinearMap.range (R.map (algebraMap ℝ RF)).mulVecLin ∧
      ∀ v ∈ LinearMap.range R.mulVecLin,
        H.mulVec v∈LinearMap.range R.mulVecLin ∧
          ∀ k,(B k).mulVec v∈LinearMap.range R.mulVecLin :=
  constant_and_invariant_rank a ha B H hH _ _
    (fun k=>ADComplete.SpectralBands.spectral_quadratic_interval
      (B k) (Matrix.isHermitian_iff_isSymm.mpr (hB k))) V hgap hV

#print axioms small_residue_rigidity

#print axioms invariant_subspace_constant_rank
#print axioms constant_and_invariant_rank
end
end MultiSymmetric.Rigidity
