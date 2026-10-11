import PaperVerifier.ADComplete.Rigidity

/-! The actual real-symmetric spectrum supplies the quadratic residue bounds. -/
namespace ADComplete.SpectralBands

open Matrix Unitary
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem eigenvalue_quadratic_interval (K : Matrix ι ι ℝ) (hK : K.IsHermitian)
    (lo hi : ℝ) (hlo : ∀ i, lo ≤ hK.eigenvalues i)
    (hhi : ∀ i, hK.eigenvalues i ≤ hi) (v : ι → ℝ) :
    lo * Rigidity.pairing v v ≤ Rigidity.pairing v (K.mulVec v) ∧
      Rigidity.pairing v (K.mulVec v) ≤ hi * Rigidity.pairing v v := by
  let φ := conjStarAlgAut ℝ (Matrix ι ι ℝ) hK.eigenvectorUnitary
  have hdiag (c : ℝ) :
      Matrix.diagonal (fun i => hK.eigenvalues i - c) =
        Matrix.diagonal hK.eigenvalues - c • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have hspec : K = φ (Matrix.diagonal hK.eigenvalues) := by
    simpa [φ] using hK.spectral_theorem
  have hscalar (c : ℝ) : φ (c • (1 : Matrix ι ι ℝ)) = c • 1 := by simp [φ]
  have hlow : (K - lo • (1 : Matrix ι ι ℝ)).PosSemidef := by
    have hd : (Matrix.diagonal (fun i => hK.eigenvalues i - lo)).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hlo i))
    have heq : K - lo • (1 : Matrix ι ι ℝ) =
        φ (Matrix.diagonal (fun i => hK.eigenvalues i - lo)) := by
      rw [hdiag, map_sub, hscalar, ← hspec]
    rw [heq]
    simpa [φ, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hd.mul_mul_conjTranspose_same (hK.eigenvectorUnitary : Matrix ι ι ℝ)
  have hupp : (hi • (1 : Matrix ι ι ℝ) - K).PosSemidef := by
    have hd : (Matrix.diagonal (fun i => hi - hK.eigenvalues i)).PosSemidef :=
      Matrix.posSemidef_diagonal_iff.mpr (fun i => sub_nonneg.mpr (hhi i))
    have heq : hi • (1 : Matrix ι ι ℝ) - K =
        φ (Matrix.diagonal (fun i => hi - hK.eigenvalues i)) := by
      have hh : Matrix.diagonal (fun i => hi - hK.eigenvalues i) =
          hi • (1 : Matrix ι ι ℝ) - Matrix.diagonal hK.eigenvalues := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
      rw [hh, map_sub, hscalar, ← hspec]
    rw [heq]
    simpa [φ, conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hd.mul_mul_conjTranspose_same (hK.eigenvectorUnitary : Matrix ι ι ℝ)
  have hl := hlow.dotProduct_mulVec_nonneg v
  have hu := hupp.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at hl hu
  change lo * dotProduct v v ≤ dotProduct v (K.mulVec v) ∧
    dotProduct v (K.mulVec v) ≤ hi * dotProduct v v
  constructor <;> linarith

def eigenMin [Nonempty ι] (K : Matrix ι ι ℝ) (hK : K.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hK.eigenvalues

def eigenMax [Nonempty ι] (K : Matrix ι ι ℝ) (hK : K.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hK.eigenvalues

theorem spectral_quadratic_interval [Nonempty ι]
    (K : Matrix ι ι ℝ) (hK : K.IsHermitian) (v : ι → ℝ) :
    eigenMin K hK * Rigidity.pairing v v ≤ Rigidity.pairing v (K.mulVec v) ∧
      Rigidity.pairing v (K.mulVec v) ≤ eigenMax K hK * Rigidity.pairing v v := by
  apply eigenvalue_quadratic_interval
  · intro i
    exact Finset.inf'_le _ (Finset.mem_univ i)
  · intro i
    exact Finset.le_sup' _ (Finset.mem_univ i)

#print axioms eigenvalue_quadratic_interval
#print axioms spectral_quadratic_interval

end
end ADComplete.SpectralBands
